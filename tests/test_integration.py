"""Integration coverage for the canonical Chimera APIs.

Solver-backed tests skip when the corresponding executable is unavailable.
The remaining tests exercise the parser, corpus, generator, and artifact
pipelines without relying on local solver installations.
"""

from __future__ import annotations

import shutil
import subprocess

import pytest

from tests.conftest import SAMPLE_FORMULAS, write_smt2_file

pytestmark = pytest.mark.integration


class TestSolverIntegration:
    """Basic executable-level solver checks."""

    @pytest.mark.skipif(not shutil.which("z3"), reason="z3 not installed")
    def test_z3_basic_sat(self, temp_dir):
        smt_file = write_smt2_file(SAMPLE_FORMULAS["simple_sat"], temp_dir, "sat.smt2")
        result = subprocess.run(["z3", str(smt_file)], capture_output=True, text=True, timeout=30)
        assert result.returncode == 0
        assert result.stdout.strip().splitlines()[0].lower() == "sat"

    @pytest.mark.skipif(not shutil.which("z3"), reason="z3 not installed")
    def test_z3_basic_unsat(self, temp_dir):
        smt_file = write_smt2_file(SAMPLE_FORMULAS["simple_unsat"], temp_dir, "unsat.smt2")
        result = subprocess.run(["z3", str(smt_file)], capture_output=True, text=True, timeout=30)
        assert result.returncode == 0
        assert result.stdout.strip().splitlines()[0].lower() == "unsat"

    @pytest.mark.skipif(not shutil.which("cvc5"), reason="cvc5 not installed")
    def test_cvc5_basic_sat(self, temp_dir):
        smt_file = write_smt2_file(SAMPLE_FORMULAS["simple_sat"], temp_dir, "sat.smt2")
        result = subprocess.run(
            ["cvc5", "--strings-exp", str(smt_file)],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode == 0
        assert result.stdout.strip().splitlines()[0].lower() == "sat"

    @pytest.mark.skipif(
        not (shutil.which("z3") and shutil.which("cvc5")),
        reason="both z3 and cvc5 required",
    )
    def test_differential_agreement(self, temp_dir):
        smt_file = write_smt2_file(SAMPLE_FORMULAS["simple_sat"], temp_dir, "sat.smt2")
        z3 = subprocess.run(["z3", str(smt_file)], capture_output=True, text=True, timeout=30)
        cvc5 = subprocess.run(
            ["cvc5", "--strings-exp", str(smt_file)],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert z3.stdout.strip().splitlines()[0].lower() == "sat"
        assert cvc5.stdout.strip().splitlines()[0].lower() == "sat"


class TestCanonicalPipelines:
    """Non-solver end-to-end tests for migrated architecture paths."""

    def test_formula_generation_pipeline(self, temp_dir):
        from chimera.engines.once4all_engine import GeneratorRegistry
        from chimera.utils import format_smt_string

        registry = GeneratorRegistry()
        assert registry.load_from_directory("generators") > 0
        for theory in registry.theory_keys[:3]:
            result = registry.get(theory)()
            assert result is not None
            declarations, body = result
            content = "(set-logic ALL)\n"
            if declarations:
                content += str(declarations) + "\n"
            content += f"(assert {body})\n(check-sat)\n"
            output = temp_dir / f"{theory}.smt2"
            output.write_text(format_smt_string(content), encoding="utf-8")
            assert output.stat().st_size > 0

    def test_skeleton_extraction_pipeline(self, temp_dir):
        from chimera.history.extractor import LogicAwareExtractor

        path = write_smt2_file(SAMPLE_FORMULAS["simple_sat"], temp_dir, "seed.smt2")
        corpus = LogicAwareExtractor().extract_all([str(path)])
        stats = corpus.statistics()
        assert stats["total_skeletons"] >= 1
        assert stats["total_blocks"] >= 1

    def test_building_blocks_extraction(self, temp_dir):
        from chimera.history.extractor import LogicAwareExtractor

        path = write_smt2_file(SAMPLE_FORMULAS["simple_sat"], temp_dir, "seed.smt2")
        corpus = LogicAwareExtractor().extract_all([str(path)])
        blocks = corpus.get_blocks()
        assert blocks
        assert all(block.term_smt2 for block in blocks)

    def test_mutation_pipeline(self):
        from chimera.core.smt_parser import parse_string

        script, _ = parse_string(SAMPLE_FORMULAS["simple_sat"])
        assert script is not None
        assert len(script.assert_cmd) == 3

    def test_corpus_loading(self, bug_formulas_dir):
        from chimera.history.streaming import export_corpus, load_corpus, validate_corpus

        destination = bug_formulas_dir / "published-corpus"
        export_corpus(bug_formulas_dir, destination, source_revision="integration")
        manifest = validate_corpus(destination)
        assert manifest["source"]["file_count"] == 10
        assert load_corpus(destination).statistics()["total_skeletons"] > 0

    def test_logic_compatibility_checking(self):
        from chimera.core.logic_analyzer import is_logic_compatible

        assert is_logic_compatible("QF_LIA", "QF_LIA")
        assert is_logic_compatible("QF_LIA", "QF_NIA")
        assert not is_logic_compatible("QF_BV", "QF_LIA")
        assert not is_logic_compatible("LIA", "QF_LIA")

    def test_formula_construction_from_corpus(self):
        from chimera.history.corpus import BuildingBlock, Corpus, Skeleton

        corpus = Corpus()
        corpus.add_block(BuildingBlock("x", "QF_LIA", var_decls={"x": "Int"}))
        corpus.add_skeleton(Skeleton("(> (hole 0) 0)", "QF_LIA", hole_types=["Int"]))
        assert corpus.sample_skeleton(logic="QF_LIA", quantified=False) is not None
        block = corpus.sample_block(sort_hint="Int", logic="QF_LIA")
        assert block is not None and block.term_obj is not None

    def test_record_bug_creates_directory(self, temp_dir):
        from chimera.core.differential_oracle import BugKind, BugReport, save_bug
        from chimera.core.solver_manager import SolverOutcome, SolverResult

        formula = write_smt2_file("(assert true)\n(check-sat)\n", temp_dir, "bug.smt2")
        sat = SolverResult(SolverOutcome.SAT, stdout="sat", command="a", smt_path=str(formula))
        unsat = SolverResult(SolverOutcome.UNSAT, stdout="unsat", command="b", smt_path=str(formula))
        report = BugReport(BugKind.SOUNDNESS, str(formula), sat, unsat, "test")
        output = save_bug(report, temp_dir / "bugs")
        assert (output / "error_log.txt").is_file()
        assert any(path.suffix == ".smt2" for path in output.iterdir())

    def test_skeleton_based_generation(self, temp_dir):
        from chimera.history.extractor import LogicAwareExtractor

        path = write_smt2_file(SAMPLE_FORMULAS["simple_sat"], temp_dir, "seed.smt2")
        corpus = LogicAwareExtractor().extract_all([str(path)])
        skeleton = corpus.sample_skeleton(quantified=False)
        assert skeleton is not None
        assert skeleton.collect_holes()
