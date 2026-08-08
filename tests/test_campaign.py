"""Tests for reproducible campaign orchestration and artifacts."""

import json
from pathlib import Path

import pytest

from chimera.core.campaign import CampaignConfig, CampaignRunner, replay_artifact
from chimera.core.solver_manager import SolverConfig, SolverOutcome, SolverResult
from chimera.engines.base import Exhausted, GeneratedCase, Skipped


class OneCaseProducer:
    name = "test-producer"

    def __init__(self) -> None:
        self.calls = 0
        self.seeds = []

    def preflight(self):
        return []

    def generate_case(self, rng, seed):
        self.calls += 1
        self.seeds.append(seed)
        if self.calls > 1:
            return Exhausted("one test case")
        return GeneratedCase(
            "(set-logic QF_LIA)\n(assert true)\n(check-sat)",
            logic="QF_LIA",
            provenance={"record": "test"},
            rng_seed=seed,
        )


def test_campaign_config_round_trip(tmp_path: Path) -> None:
    config = CampaignConfig(
        engine="test",
        solvers=(
            SolverConfig("a", "/usr/bin/true"),
            SolverConfig("b", "/usr/bin/true"),
        ),
        output_dir=str(tmp_path / "out"),
        temp_dir=str(tmp_path / "tmp"),
        iterations=2,
        seed=42,
    )
    path = tmp_path / "campaign.json"
    config.write(path)
    assert CampaignConfig.read(path).to_dict() == config.to_dict()


def test_runner_compares_all_solver_pairs_and_writes_manifest(tmp_path, monkeypatch) -> None:
    producer = OneCaseProducer()
    solvers = tuple(SolverConfig(name, "/usr/bin/true") for name in ("a", "b", "c"))
    config = CampaignConfig(
        engine="test",
        solvers=solvers,
        output_dir=str(tmp_path / "out"),
        temp_dir=str(tmp_path / "tmp"),
        iterations=1,
        seed=123,
    )

    def fake_run_solver(solver, smt_path, *, timeout):
        outcome = SolverOutcome.SAT if solver.name == "a" else SolverOutcome.UNSAT
        return SolverResult(
            outcome=outcome,
            stdout=outcome.name.lower(),
            exit_code=0,
            command=solver.name,
            smt_path=smt_path,
        )

    monkeypatch.setattr("chimera.core.campaign.run_solver", fake_run_solver)
    stats = CampaignRunner(producer, config).run()
    assert stats.formulas_generated == 1
    assert stats.bugs_found == 2
    manifests = list((tmp_path / "out" / "cases").glob("*/manifest.json"))
    assert len(manifests) == 1
    manifest = json.loads(manifests[0].read_text())
    assert len(manifest["findings"]) == 2
    assert len(manifest["solvers"]) == 3
    assert len(manifest["comparisons"]) == 3
    assert manifest["checksums"]["config_sha256"]
    assert set(manifest["checksums"]["solver_outputs_sha256"]) == {"a", "b", "c"}
    assert set(manifest["tool"]["solvers"]) == {"a", "b", "c"}
    assert manifest["tool"]["solvers"]["a"]["base_args"] == []
    assert len(producer.seeds) == 1
    replayed = replay_artifact(manifests[0])
    assert set(replayed["results"]) == {"a", "b", "c"}
    assert {result.command for result in replayed["results"].values()} == {"a", "b", "c"}


def test_unlimited_campaign_has_consecutive_failure_breaker(tmp_path: Path) -> None:
    class EmptyProducer:
        name = "empty"

        def preflight(self):
            return []

        def generate_case(self, _rng, _seed):
            return Skipped("no input")

    config = CampaignConfig(
        engine="test",
        solvers=(
            SolverConfig("a", "/usr/bin/true"),
            SolverConfig("b", "/usr/bin/true"),
        ),
        output_dir=str(tmp_path / "out"),
        temp_dir=str(tmp_path / "tmp"),
        max_consecutive_failures=3,
    )
    stats = CampaignRunner(EmptyProducer(), config).run()
    assert stats.iterations == 3
    assert stats.skipped == 3
    assert stats.exhausted == 1


def test_campaign_resume_restores_summary_and_rng_state(tmp_path: Path, monkeypatch) -> None:
    class RepeatProducer:
        name = "resume"

        def preflight(self):
            return []

        def generate_case(self, _rng, seed):
            return GeneratedCase("(assert true)", logic="QF_BOOL", rng_seed=seed)

    def fake_run_solver(solver, smt_path, *, timeout):
        return SolverResult(
            outcome=SolverOutcome.SAT,
            stdout="sat",
            exit_code=0,
            command=solver.name,
            smt_path=smt_path,
        )

    monkeypatch.setattr("chimera.core.campaign.run_solver", fake_run_solver)
    output = tmp_path / "out"
    config = CampaignConfig(
        engine="resume",
        solvers=(SolverConfig("a", "/usr/bin/true"), SolverConfig("b", "/usr/bin/true")),
        output_dir=str(output),
        temp_dir=str(tmp_path / "tmp"),
        iterations=1,
        seed=99,
    )
    CampaignRunner(RepeatProducer(), config).run()

    resumed_config = CampaignConfig.from_dict({**config.to_dict(), "iterations": 2})
    stats = CampaignRunner(RepeatProducer(), resumed_config).run(resume=True)
    assert stats.iterations == 2
    summary = json.loads((output / "campaign-summary.json").read_text())
    assert summary["resume"]["iterations"] == 2


def test_resume_rejects_changed_semantic_configuration(tmp_path: Path, monkeypatch) -> None:
    class RepeatProducer:
        name = "resume"

        def preflight(self):
            return []

        def generate_case(self, _rng, seed):
            return GeneratedCase("(assert true)", rng_seed=seed)

    monkeypatch.setattr(
        "chimera.core.campaign.run_solver",
        lambda solver, smt_path, **_kwargs: SolverResult(
            outcome=SolverOutcome.SAT, stdout="sat", exit_code=0,
            command=solver.name, smt_path=smt_path,
        ),
    )
    config = CampaignConfig(
        engine="resume",
        solvers=(SolverConfig("a", "/usr/bin/true"), SolverConfig("b", "/usr/bin/true")),
        output_dir=str(tmp_path / "out"), temp_dir=str(tmp_path / "tmp"), iterations=1,
    )
    CampaignRunner(RepeatProducer(), config).run()
    changed = CampaignConfig.from_dict({
        **config.to_dict(),
        "solvers": [
            {"name": "a", "binary": "/usr/bin/true", "base_args": ["--changed"], "extra_args": []},
            {"name": "b", "binary": "/usr/bin/true", "base_args": [], "extra_args": []},
        ],
        "iterations": 2,
    })
    with pytest.raises(ValueError, match="semantic campaign configuration"):
        CampaignRunner(RepeatProducer(), changed).run(resume=True)


def test_artifacts_are_distinct_for_different_semantic_configs(tmp_path: Path, monkeypatch) -> None:
    producer = OneCaseProducer()
    monkeypatch.setattr(
        "chimera.core.campaign.run_solver",
        lambda solver, smt_path, **_kwargs: SolverResult(
            outcome=SolverOutcome.SAT, stdout="sat", exit_code=0,
            command=solver.name, smt_path=smt_path,
        ),
    )
    common = {
        "engine": "test",
        "solvers": (SolverConfig("a", "/usr/bin/true"), SolverConfig("b", "/usr/bin/true")),
        "output_dir": str(tmp_path / "out"), "temp_dir": str(tmp_path / "tmp"),
        "iterations": 1, "seed": 1,
    }
    CampaignRunner(producer, CampaignConfig(**common)).run()
    changed = CampaignConfig.from_dict({
        **CampaignConfig(**common).to_dict(),
        "oracle": {"detect_crashes": False, "detect_soundness": True,
                   "detect_invalid_models": True, "detect_performance": False,
                   "performance_ratio": 2.0},
    })
    CampaignRunner(OneCaseProducer(), changed).run()
    manifests = list((tmp_path / "out" / "cases").glob("*/manifest.json"))
    assert len(manifests) == 2
