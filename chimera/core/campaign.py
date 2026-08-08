"""Reproducible multi-solver campaign orchestration.

The existing engine classes remain usable through :class:`StrategyCaseProducer`.
New engines can implement :class:`CaseProducer` directly and return the
structured outcomes defined in ``chimera.engines.base``.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import logging
import os
import random
import subprocess
import sys
from dataclasses import asdict, dataclass, field, fields
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Protocol, Sequence, Tuple, cast

from chimera.core.differential_oracle import BugKind, BugReport, OracleConfig, compare
from chimera.core.solver_manager import SolverConfig, SolverResult, run_solver
from chimera.engines.base import (
    Exhausted,
    FuzzStats,
    GeneratedCase,
    GenerationOutcome,
    Misconfigured,
    RetriableFailure,
    Skipped,
)

logger = logging.getLogger(__name__)

CAMPAIGN_CONFIG_VERSION = 1
ARTIFACT_FORMAT_VERSION = 1


def _solver_to_dict(config: SolverConfig) -> Dict[str, Any]:
    return {
        "name": config.name,
        "binary": config.binary,
        "base_args": list(config.base_args),
        "extra_args": list(config.extra_args),
    }


def _solver_from_dict(data: Mapping[str, Any]) -> SolverConfig:
    return SolverConfig(
        name=str(data["name"]),
        binary=str(data["binary"]),
        base_args=[str(arg) for arg in data.get("base_args", [])],
        extra_args=[str(arg) for arg in data.get("extra_args", [])],
    )


def _solver_metadata(config: SolverConfig) -> dict[str, Any]:
    """Capture reproducible solver invocation and version information."""
    metadata: dict[str, Any] = {
        "name": config.name,
        "binary": str(Path(config.binary).resolve()),
        "base_args": list(config.base_args),
        "extra_args": list(config.extra_args),
    }
    try:
        result = subprocess.run(
            [config.binary, "--version"],
            capture_output=True,
            text=True,
            timeout=2.0,
            check=False,
        )
        version_text = (result.stdout or result.stderr).strip()
        metadata["version"] = version_text.splitlines()[0] if version_text else None
        metadata["version_exit_code"] = result.returncode
    except (OSError, subprocess.SubprocessError) as exc:
        metadata["version"] = None
        metadata["version_error"] = str(exc)
    return metadata


def _resource_metadata(settings: Mapping[str, Any]) -> dict[str, Any]:
    """Record configured engine resource paths and file checksums."""
    resources: dict[str, Any] = {}
    for key in ("corpus_dir", "generator_dir", "rules_csv", "config_dir"):
        value = settings.get(key)
        if not value:
            continue
        path = Path(str(value))
        item: dict[str, Any] = {"path": str(path.resolve()), "exists": path.exists()}
        if path.is_file():
            digest = hashlib.sha256()
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
            item["sha256"] = digest.hexdigest()
        elif path.is_dir():
            manifest = path / "manifest.json"
            if manifest.is_file():
                item["manifest_sha256"] = hashlib.sha256(manifest.read_bytes()).hexdigest()
        resources[key] = item
    return resources


@dataclass(frozen=True)
class CampaignConfig:
    """Versioned, JSON-serializable campaign configuration."""

    engine: str
    solvers: Tuple[SolverConfig, ...]
    engine_settings: Mapping[str, Any] = field(default_factory=dict)
    oracle: OracleConfig = field(default_factory=OracleConfig)
    output_dir: str = "./chimera_bugs"
    temp_dir: str = "./chimera_temp"
    timeout: float = 10.0
    iterations: Optional[int] = None
    seed: int = 0
    max_consecutive_failures: int = 50
    version: int = CAMPAIGN_CONFIG_VERSION

    def __post_init__(self) -> None:
        if self.version != CAMPAIGN_CONFIG_VERSION:
            raise ValueError(f"unsupported campaign config version: {self.version}")
        if len(self.solvers) < 2:
            raise ValueError("campaigns require at least two solvers")
        names = [solver.name for solver in self.solvers]
        if len(set(names)) != len(names):
            raise ValueError("campaign solver names must be unique")
        if self.timeout <= 0:
            raise ValueError("campaign timeout must be positive")
        if self.iterations is not None and self.iterations < 0:
            raise ValueError("iterations cannot be negative")
        if self.max_consecutive_failures <= 0:
            raise ValueError("max_consecutive_failures must be positive")

    def to_dict(self) -> Dict[str, Any]:
        return {
            "version": self.version,
            "engine": self.engine,
            "engine_settings": dict(self.engine_settings),
            "solvers": [_solver_to_dict(solver) for solver in self.solvers],
            "oracle": asdict(self.oracle),
            "output_dir": self.output_dir,
            "temp_dir": self.temp_dir,
            "timeout": self.timeout,
            "iterations": self.iterations,
            "seed": self.seed,
            "max_consecutive_failures": self.max_consecutive_failures,
        }

    @classmethod
    def from_dict(cls, data: Mapping[str, Any]) -> "CampaignConfig":
        version = int(data.get("version", 0))
        if version != CAMPAIGN_CONFIG_VERSION:
            raise ValueError(f"unsupported campaign config version: {version}")
        oracle_data = data.get("oracle") or {}
        raw_iterations = data.get("iterations")
        return cls(
            version=version,
            engine=str(data["engine"]),
            engine_settings=dict(data.get("engine_settings", {})),
            solvers=tuple(_solver_from_dict(item) for item in data["solvers"]),
            oracle=OracleConfig(**dict(oracle_data)),
            output_dir=str(data.get("output_dir", "./chimera_bugs")),
            temp_dir=str(data.get("temp_dir", "./chimera_temp")),
            timeout=float(data.get("timeout", 10.0)),
            iterations=None if raw_iterations is None else int(raw_iterations),
            seed=int(data.get("seed", 0)),
            max_consecutive_failures=int(data.get("max_consecutive_failures", 50)),
        )

    @classmethod
    def read(cls, path: str | Path) -> "CampaignConfig":
        with Path(path).open(encoding="utf-8") as stream:
            return cls.from_dict(json.load(stream))

    def write(self, path: str | Path) -> None:
        destination = Path(path)
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("w", encoding="utf-8") as stream:
            json.dump(self.to_dict(), stream, indent=2, sort_keys=True)
            stream.write("\n")


class CaseProducer(Protocol):
    """Protocol implemented by campaign case producers."""

    @property
    def name(self) -> str: ...

    def preflight(self) -> List[Misconfigured]: ...

    def generate_case(self, rng: random.Random, seed: int) -> GenerationOutcome: ...


class StrategyCaseProducer:
    """Adapt a legacy ``FuzzingStrategy`` to the P2 producer protocol."""

    def __init__(self, strategy: Any) -> None:
        self.strategy = strategy

    @property
    def name(self) -> str:
        return str(self.strategy.name)

    def preflight(self) -> List[Misconfigured]:
        return list(self.strategy.preflight())

    def generate_case(self, rng: random.Random, seed: int) -> GenerationOutcome:
        # Native strategies receive the injected RNG and can attach structured
        # provenance.  Third-party strategy objects retain the old adapter
        # behavior so the public migration remains backwards compatible.
        try:
            producer = getattr(self.strategy, "generate_case_for_campaign", None)
            if callable(producer):
                outcome = cast(GenerationOutcome, producer(rng, seed))
            else:
                previous = random.getstate()
                random.setstate(rng.getstate())
                try:
                    outcome = cast(GenerationOutcome, self.strategy.generate_case())
                    rng.setstate(random.getstate())
                finally:
                    random.setstate(previous)
        except Exception as exc:
            logger.debug("%s: campaign generation failed", self.name, exc_info=True)
            return RetriableFailure(str(exc) or type(exc).__name__)
        if isinstance(outcome, GeneratedCase):
            return GeneratedCase(
                text=outcome.text,
                logic=outcome.logic,
                provenance=outcome.provenance or {"engine": self.name},
                rng_seed=seed,
            )
        return outcome


def _json_safe(value: Any) -> Any:
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, Mapping):
        return {str(k): _json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [_json_safe(item) for item in value]
    return str(value)


def _result_to_dict(result: SolverResult) -> Dict[str, Any]:
    return {
        "outcome": result.outcome.name,
        "stdout": result.stdout,
        "stderr": result.stderr,
        "exit_code": result.exit_code,
        "wall_seconds": result.wall_seconds,
        "command": result.command,
        "smt_path": result.smt_path,
    }


def _sha256_json(value: Any) -> str:
    payload = json.dumps(_json_safe(value), sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _bug_to_dict(bug: BugReport, pair: Tuple[str, str]) -> Dict[str, Any]:
    return {
        "kind": bug.kind.name,
        "description": bug.description,
        "pair": list(pair),
    }


class ArtifactStore:
    """Persist deterministic case artifacts and atomic campaign summaries."""

    def __init__(self, root: str | Path) -> None:
        self.root = Path(root)
        self.cases = self.root / "cases"
        self._solver_metadata_cache: dict[
            tuple[str, str, tuple[str, ...], tuple[str, ...]], dict[str, Any]
        ] = {}

    def solver_metadata(self, config: SolverConfig) -> dict[str, Any]:
        key = (config.name, config.binary, tuple(config.base_args), tuple(config.extra_args))
        if key not in self._solver_metadata_cache:
            self._solver_metadata_cache[key] = _solver_metadata(config)
        return dict(self._solver_metadata_cache[key])

    @staticmethod
    def case_id(case: GeneratedCase) -> str:
        payload = json.dumps(
            {
                "text": case.text,
                "logic": case.logic,
                "provenance": _json_safe(case.provenance),
                "rng_seed": case.rng_seed,
            },
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()[:24]

    def save_case(
        self,
        case: GeneratedCase,
        results: Mapping[str, SolverResult],
        findings: Sequence[Tuple[Tuple[str, str], BugReport]],
        config: CampaignConfig,
        comparisons: Optional[Sequence[Mapping[str, Any]]] = None,
    ) -> Path:
        self.cases.mkdir(parents=True, exist_ok=True)
        case_id = self.case_id(case)
        destination = self.cases / case_id
        if destination.exists():
            existing = destination / "manifest.json"
            if existing.is_file():
                return destination
            suffix = 1
            while (self.cases / f"{case_id}-{suffix}").exists():
                suffix += 1
            destination = self.cases / f"{case_id}-{suffix}"
        destination.mkdir(parents=True, exist_ok=False)
        formula_path = destination / "formula.smt2"
        formula_path.write_text(case.text, encoding="utf-8")
        solver_payload = {name: _result_to_dict(result) for name, result in results.items()}
        config_payload = config.to_dict()
        solver_metadata = {
            solver.name: self.solver_metadata(solver) for solver in config.solvers
        }
        manifest = {
            "artifact_version": ARTIFACT_FORMAT_VERSION,
            "case_id": destination.name,
            "formula_sha256": hashlib.sha256(case.text.encode("utf-8")).hexdigest(),
            "formula": str(formula_path.name),
            "logic": case.logic,
            "provenance": _json_safe(case.provenance),
            "rng_seed": case.rng_seed,
            "config": config_payload,
            "solvers": solver_payload,
            "comparisons": [_json_safe(item) for item in (comparisons or [])],
            "findings": [_bug_to_dict(bug, pair) for pair, bug in findings],
            "checksums": {
                "formula_sha256": hashlib.sha256(case.text.encode("utf-8")).hexdigest(),
                "config_sha256": _sha256_json(config_payload),
                "solver_outputs_sha256": {
                    name: _sha256_json(result) for name, result in solver_payload.items()
                },
            },
            "tool": {
                "name": "chimera",
                "version": "2.0.0",
                "python": sys.version.split()[0],
                "solvers": solver_metadata,
                "resources": _resource_metadata(config.engine_settings),
            },
        }
        manifest_path = destination / "manifest.json"
        temporary = destination / f".manifest.json.tmp-{os.getpid()}"
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(manifest, stream, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, manifest_path)
        return destination

    def write_summary(self, summary: Mapping[str, Any]) -> Path:
        self.root.mkdir(parents=True, exist_ok=True)
        destination = self.root / "campaign-summary.json"
        temporary = destination.with_name(f".{destination.name}.tmp-{os.getpid()}")
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(_json_safe(summary), stream, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, destination)
        return destination


class CampaignRunner:
    """Run generated cases against every unordered solver pair."""

    def __init__(
        self,
        producer: CaseProducer,
        config: CampaignConfig,
        *,
        artifact_store: Optional[ArtifactStore] = None,
    ) -> None:
        self.producer = producer
        self.config = config
        self.artifacts = artifact_store or ArtifactStore(config.output_dir)
        self.stats = FuzzStats()
        self.rng = random.Random(config.seed)

    def preflight(self) -> List[Misconfigured]:
        issues = list(self.producer.preflight())
        for solver in self.config.solvers:
            if not os.path.isfile(solver.binary):
                issues.append(Misconfigured(f"solver binary does not exist: {solver.binary}"))
            elif not os.access(solver.binary, os.X_OK):
                issues.append(Misconfigured(f"solver binary is not executable: {solver.binary}"))
        for directory in (self.config.output_dir, self.config.temp_dir):
            path = Path(directory)
            try:
                path.mkdir(parents=True, exist_ok=True)
            except OSError as exc:
                issues.append(Misconfigured(f"directory is not writable: {directory} ({exc})"))
            else:
                if not os.access(path, os.W_OK):
                    issues.append(Misconfigured(f"directory is not writable: {directory}"))
        return issues

    def _resume_from_summary(self) -> int:
        """Restore counters and RNG state from the previous summary."""
        summary_path = self.artifacts.root / "campaign-summary.json"
        if not summary_path.is_file():
            raise ValueError(f"cannot resume: missing campaign summary {summary_path}")
        with summary_path.open(encoding="utf-8") as stream:
            summary = json.load(stream)
        if summary.get("config", {}).get("engine") != self.config.engine:
            raise ValueError("cannot resume: campaign engine does not match summary")
        saved_config = summary.get("config", {})
        if saved_config.get("seed") != self.config.seed:
            raise ValueError("cannot resume: campaign seed does not match summary")
        stats_payload = summary.get("stats", {})
        stat_names = {item.name for item in fields(FuzzStats)}
        for name in stat_names:
            if name == "start_time" or name not in stats_payload:
                continue
            setattr(self.stats, name, int(stats_payload[name]))
        resume = summary.get("resume", {})
        if "rng_state" not in resume:
            raise ValueError("cannot resume: summary has no RNG state")
        state = resume["rng_state"]
        if not isinstance(state, list) or len(state) != 3:
            raise ValueError("cannot resume: invalid RNG state")
        self.rng.setstate((int(state[0]), tuple(int(item) for item in state[1]), state[2]))
        return int(self.stats.iterations)

    def run(self, max_iterations: Optional[int] = None, *, resume: bool = False) -> FuzzStats:
        issues = self.preflight()
        if issues:
            self.stats.misconfigurations += len(issues)
            raise ValueError("campaign preflight failed: " + "; ".join(item.reason for item in issues))
        limit = self.config.iterations if max_iterations is None else max_iterations
        if limit == 0:
            limit = None
        start_iteration = self._resume_from_summary() if resume else 0
        interrupted = False
        try:
            iteration = start_iteration
            consecutive_failures = 0
            while limit is None or iteration < limit:
                seed = self.rng.getrandbits(64)
                outcome = self.producer.generate_case(self.rng, seed)
                self.stats.iterations += 1
                if not isinstance(outcome, GeneratedCase):
                    if isinstance(outcome, Skipped):
                        self.stats.skipped += 1
                    elif isinstance(outcome, Exhausted):
                        self.stats.exhausted += 1
                        break
                    elif isinstance(outcome, Misconfigured):
                        self.stats.misconfigurations += 1
                        break
                    else:
                        self.stats.retriable_failures += 1
                    consecutive_failures += 1
                    if isinstance(outcome, (Exhausted, Misconfigured)):
                        break
                    if consecutive_failures >= self.config.max_consecutive_failures:
                        self.stats.exhausted += 1
                        logger.error(
                            "%s campaign stopped after %d consecutive generation failures",
                            self.producer.name,
                            consecutive_failures,
                        )
                        break
                    iteration += 1
                    continue
                consecutive_failures = 0
                self._run_case(outcome, iteration)
                iteration += 1
        except KeyboardInterrupt:
            interrupted = True
            logger.info("Campaign interrupted")
        finally:
            self.artifacts.write_summary(
                {
                    "config": self.config.to_dict(),
                    "stats": asdict(self.stats),
                    "interrupted": interrupted,
                    "resume": {
                        "iterations": self.stats.iterations,
                        "rng_state": _json_safe(self.rng.getstate()),
                    },
                }
            )
        return self.stats

    def _run_case(self, case: GeneratedCase, iteration: int) -> None:
        self.stats.formulas_generated += 1
        temp = Path(self.config.temp_dir)
        temp.mkdir(parents=True, exist_ok=True)
        formula_path = temp / f"case-{iteration}-{self.artifacts.case_id(case)}.smt2"
        formula_path.write_text(case.text, encoding="utf-8")
        results = {
            solver.name: run_solver(solver, str(formula_path), timeout=self.config.timeout)
            for solver in self.config.solvers
        }
        findings: List[Tuple[Tuple[str, str], BugReport]] = []
        comparisons: List[Dict[str, Any]] = []
        names = list(results)
        for left, right in itertools.combinations(names, 2):
            pair_findings = compare(results[left], results[right], config=self.config.oracle)
            comparisons.append({
                "pair": [left, right],
                "findings": [finding.kind.name for finding in pair_findings],
            })
            for finding in pair_findings:
                findings.append(((left, right), finding))
                self.stats.bugs_found += 1
                if finding.kind == BugKind.CRASH:
                    self.stats.crashes += 1
                elif finding.kind == BugKind.SOUNDNESS:
                    self.stats.soundness_bugs += 1
                elif finding.kind == BugKind.INVALID_MODEL:
                    self.stats.invalid_models += 1
        self.artifacts.save_case(case, results, findings, self.config, comparisons)
        if not findings:
            try:
                formula_path.unlink()
            except OSError:
                pass


def replay_artifact(manifest_path: str | Path) -> Dict[str, Any]:
    """Replay a saved formula against the recorded solver configuration."""
    manifest_file = Path(manifest_path)
    with manifest_file.open(encoding="utf-8") as stream:
        manifest = json.load(stream)
    if manifest.get("artifact_version") != ARTIFACT_FORMAT_VERSION:
        raise ValueError("unsupported artifact version")
    formula_path = manifest_file.parent / manifest["formula"]
    formula = formula_path.read_text(encoding="utf-8")
    digest = hashlib.sha256(formula.encode("utf-8")).hexdigest()
    if digest != manifest["formula_sha256"]:
        raise ValueError("artifact formula checksum mismatch")
    checksums = manifest.get("checksums", {})
    if checksums.get("formula_sha256") and checksums["formula_sha256"] != digest:
        raise ValueError("artifact formula checksum mismatch")
    config = CampaignConfig.from_dict(manifest["config"])
    results = {
        solver.name: run_solver(solver, str(formula_path), timeout=config.timeout)
        for solver in config.solvers
    }
    findings: Dict[str, List[Dict[str, Any]]] = {}
    for left, right in itertools.combinations(results, 2):
        pair = f"{left}::{right}"
        findings[pair] = [
            {"kind": finding.kind.name, "description": finding.description}
            for finding in compare(results[left], results[right], config=config.oracle)
        ]
    return {"manifest": manifest, "results": results, "findings": findings}


__all__ = [
    "ARTIFACT_FORMAT_VERSION",
    "CAMPAIGN_CONFIG_VERSION",
    "ArtifactStore",
    "CampaignConfig",
    "CampaignRunner",
    "CaseProducer",
    "StrategyCaseProducer",
    "replay_artifact",
]
