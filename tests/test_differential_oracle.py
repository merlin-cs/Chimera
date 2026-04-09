"""
Unit tests for differential_oracle module (chimera/core/differential_oracle.py).

Tests cover:
- Bug classification (Soundness, Crash, Invalid Model, etc.)
- Oracle configuration
- compare function for result comparison
- BugReport creation and serialization
- save_bug file handling
"""

import pytest
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock

from chimera.core.differential_oracle import (
    BugKind,
    BugReport,
    OracleConfig,
    compare,
    save_bug,
)
from chimera.core.solver_manager import SolverOutcome, SolverResult


class TestBugKind:
    """Tests for BugKind enum."""

    def test_bug_kinds_exist(self):
        """Test that all bug kinds are defined."""
        assert BugKind.SOUNDNESS
        assert BugKind.CRASH
        assert BugKind.INVALID_MODEL
        assert BugKind.ASSERT_VIOLATION
        assert BugKind.PERFORMANCE
        assert BugKind.NONE


class TestOracleConfig:
    """Tests for OracleConfig dataclass."""

    def test_default_config(self):
        """Test default oracle configuration."""
        config = OracleConfig()
        assert config.detect_crashes is True
        assert config.detect_soundness is True
        assert config.detect_invalid_models is True
        assert config.detect_performance is False
        assert config.performance_ratio == 10.0

    def test_custom_config(self):
        """Test custom oracle configuration."""
        config = OracleConfig(
            detect_crashes=False,
            detect_soundness=True,
            detect_invalid_models=True,
            detect_performance=True,
            performance_ratio=5.0,
        )
        assert config.detect_crashes is False
        assert config.detect_soundness is True
        assert config.detect_performance is True
        assert config.performance_ratio == 5.0


class TestBugReport:
    """Tests for BugReport dataclass."""

    @pytest.fixture
    def sample_results(self):
        """Create sample solver results for testing."""
        return (
            SolverResult(
                outcome=SolverOutcome.SAT,
                stdout="sat\n",
                stderr="",
                exit_code=0,
                wall_seconds=1.0,
                command="z3 test.smt2",
                smt_path="/path/to/test.smt2",
            ),
            SolverResult(
                outcome=SolverOutcome.UNSAT,
                stdout="unsat\n",
                stderr="",
                exit_code=0,
                wall_seconds=1.5,
                command="cvc5 test.smt2",
                smt_path="/path/to/test.smt2",
            ),
        )

    def test_bug_report_creation(self, sample_results):
        """Test basic bug report creation."""
        result1, result2 = sample_results
        report = BugReport(
            kind=BugKind.SOUNDNESS,
            smt_path="/path/to/test.smt2",
            solver1_result=result1,
            solver2_result=result2,
            description="Soundness bug: sat vs unsat",
        )
        assert report.kind == BugKind.SOUNDNESS
        assert report.smt_path == "/path/to/test.smt2"
        assert report.solver1_result == result1
        assert report.solver2_result == result2

    def test_bug_report_summary(self, sample_results):
        """Test bug report summary string."""
        result1, result2 = sample_results
        report = BugReport(
            kind=BugKind.SOUNDNESS,
            smt_path="/path/to/test.smt2",
            solver1_result=result1,
            solver2_result=result2,
            description="Soundness bug: sat vs unsat",
        )
        summary = report.summary()
        assert "SOUNDNESS" in summary
        assert "/path/to/test.smt2" in summary
        assert "SAT" in summary
        assert "UNSAT" in summary

    def test_bug_report_frozen(self, sample_results):
        """Test that BugReport is immutable."""
        result1, result2 = sample_results
        report = BugReport(
            kind=BugKind.SOUNDNESS,
            smt_path="/path/to/test.smt2",
            solver1_result=result1,
            solver2_result=result2,
        )
        with pytest.raises(AttributeError):
            report.kind = BugKind.CRASH


class TestCompare:
    """Tests for compare function."""

    def _make_result(self, outcome, answer=None, stdout="", stderr="", wall_seconds=1.0, smt_path="/test.smt2"):
        """Helper to create SolverResult."""
        return SolverResult(
            outcome=outcome,
            stdout=stdout,
            stderr=stderr,
            wall_seconds=wall_seconds,
            command="solver test.smt2",
            smt_path=smt_path,
        )

    def test_soundness_bug_sat_unsat(self):
        """Test detection of sat vs unsat soundness bug."""
        result1 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")
        result2 = self._make_result(SolverOutcome.UNSAT, "unsat", stdout="unsat\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 1
        assert bugs[0].kind == BugKind.SOUNDNESS
        assert "sat vs unsat" in bugs[0].description.lower()

    def test_soundness_bug_unsat_sat(self):
        """Test detection of unsat vs sat soundness bug."""
        result1 = self._make_result(SolverOutcome.UNSAT, "unsat", stdout="unsat\n")
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 1
        assert bugs[0].kind == BugKind.SOUNDNESS

    def test_no_bug_consistent_results(self):
        """Test no bug when results agree."""
        result1 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 0

    def test_no_bug_both_unknown(self):
        """Test no bug when both return unknown."""
        result1 = self._make_result(SolverOutcome.UNKNOWN, "unknown", stdout="unknown\n")
        result2 = self._make_result(SolverOutcome.UNKNOWN, "unknown", stdout="unknown\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 0

    def test_crash_detection(self):
        """Test crash bug detection."""
        result1 = self._make_result(SolverOutcome.CRASH, stdout="", stderr="Segmentation fault")
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 1
        assert bugs[0].kind == BugKind.CRASH

    def test_segfault_detection(self):
        """Test segfault detection."""
        result1 = self._make_result(SolverOutcome.SEGFAULT, stdout="", stderr="")
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 1
        assert bugs[0].kind == BugKind.CRASH

    def test_assertion_violation_detection(self):
        """Test assertion violation detection."""
        result1 = self._make_result(SolverOutcome.ASSERT_VIOLATION, stdout="", stderr="ASSERTION VIOLATION")
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 1
        assert bugs[0].kind == BugKind.ASSERT_VIOLATION

    def test_invalid_model_detection(self):
        """Test invalid model detection."""
        result1 = self._make_result(SolverOutcome.INVALID_MODEL, stdout="", stderr="invalid model")
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2)
        assert len(bugs) == 1
        assert bugs[0].kind == BugKind.INVALID_MODEL

    def test_timeout_ignored(self):
        """Test that timeouts don't trigger bugs."""
        result1 = self._make_result(SolverOutcome.TIMEOUT)
        result2 = self._make_result(SolverOutcome.TIMEOUT)

        bugs = compare(result1, result2)
        assert len(bugs) == 0

    def test_timeout_vs_answer(self):
        """Test timeout vs answer - no soundness bug."""
        result1 = self._make_result(SolverOutcome.TIMEOUT)
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2)
        # Timeout is in ignorables, so no soundness bug
        soundness_bugs = [b for b in bugs if b.kind == BugKind.SOUNDNESS]
        assert len(soundness_bugs) == 0

    def test_performance_detection_enabled(self):
        """Test performance bug detection when enabled."""
        config = OracleConfig(detect_performance=True, performance_ratio=5.0)
        result1 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n", wall_seconds=10.0)
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n", wall_seconds=1.0)

        bugs = compare(result1, result2, config=config)
        assert len(bugs) == 1
        assert bugs[0].kind == BugKind.PERFORMANCE
        assert "slower" in bugs[0].description.lower()

    def test_performance_detection_disabled(self):
        """Test performance detection is off by default."""
        config = OracleConfig(detect_performance=False)
        result1 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n", wall_seconds=100.0)
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n", wall_seconds=1.0)

        bugs = compare(result1, result2, config=config)
        performance_bugs = [b for b in bugs if b.kind == BugKind.PERFORMANCE]
        assert len(performance_bugs) == 0

    def test_crash_detection_disabled(self):
        """Test crash detection can be disabled."""
        config = OracleConfig(detect_crashes=False)
        result1 = self._make_result(SolverOutcome.CRASH, stdout="", stderr="crash")
        result2 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")

        bugs = compare(result1, result2, config=config)
        assert len(bugs) == 0

    def test_soundness_detection_disabled(self):
        """Test soundness detection can be disabled."""
        config = OracleConfig(detect_soundness=False)
        result1 = self._make_result(SolverOutcome.SAT, "sat", stdout="sat\n")
        result2 = self._make_result(SolverOutcome.UNSAT, "unsat", stdout="unsat\n")

        bugs = compare(result1, result2, config=config)
        assert len(bugs) == 0

    def test_multiple_bugs(self):
        """Test detection of multiple bugs in one comparison."""
        # One crashes, other returns wrong answer
        result1 = self._make_result(SolverOutcome.CRASH, stdout="", stderr="crash")
        result2 = self._make_result(SolverOutcome.INVALID_MODEL, stdout="", stderr="invalid model")

        bugs = compare(result1, result2)
        # Both crashes should be detected
        assert len(bugs) >= 1


class TestSaveBug:
    """Tests for save_bug function."""

    @pytest.fixture
    def bug_report(self, temp_dir):
        """Create a sample bug report with SMT file."""
        # Create the SMT file
        smt_path = temp_dir / "bug.smt2"
        smt_path.write_text("(set-logic QF_LIA)\n(assert false)\n(check-sat)\n")

        result1 = SolverResult(
            outcome=SolverOutcome.SAT,
            stdout="sat\n",
            stderr="",
            exit_code=0,
            wall_seconds=1.0,
            command="z3 bug.smt2",
            smt_path=str(smt_path),
        )
        result2 = SolverResult(
            outcome=SolverOutcome.UNSAT,
            stdout="unsat\n",
            stderr="",
            exit_code=0,
            wall_seconds=1.5,
            command="cvc5 bug.smt2",
            smt_path=str(smt_path),
        )

        return BugReport(
            kind=BugKind.SOUNDNESS,
            smt_path=str(smt_path),
            solver1_result=result1,
            solver2_result=result2,
            description="Soundness bug: sat vs unsat",
        )

    def test_save_bug_creates_directory(self, bug_report, temp_dir):
        """Test that save_bug creates the bug directory."""
        output_dir = temp_dir / "bugs"
        bug_dir = save_bug(bug_report, str(output_dir))

        assert bug_dir.exists()
        assert bug_dir.is_dir()
        assert "soundness" in str(bug_dir).lower()

    def test_save_bug_creates_log_file(self, bug_report, temp_dir):
        """Test that save_bug creates an error log."""
        output_dir = temp_dir / "bugs"
        bug_dir = save_bug(bug_report, str(output_dir))

        log_file = bug_dir / "error_log.txt"
        assert log_file.exists()

        content = log_file.read_text()
        assert "SOUNDNESS" in content
        assert "Soundness bug" in content
        assert "z3" in content
        assert "cvc5" in content

    def test_save_bug_copies_smt_file(self, bug_report, temp_dir):
        """Test that save_bug copies the SMT file."""
        output_dir = temp_dir / "bugs"
        bug_dir = save_bug(bug_report, str(output_dir))

        # Should copy the SMT file
        smt_files = list(bug_dir.glob("*.smt2"))
        assert len(smt_files) == 1
        assert smt_files[0].read_text().startswith("(set-logic")

    def test_save_bug_increments_index(self, bug_report, temp_dir):
        """Test that saving multiple bugs increments the index."""
        output_dir = temp_dir / "bugs"

        # Save first bug
        bug_dir1 = save_bug(bug_report, str(output_dir))
        # Save second bug (modify description to make it different)
        result1 = SolverResult(
            outcome=SolverOutcome.SAT, stdout="sat\n", stderr="",
            wall_seconds=1.0, command="z3 bug.smt2", smt_path=bug_report.smt_path
        )
        result2 = SolverResult(
            outcome=SolverOutcome.UNSAT, stdout="unsat\n", stderr="",
            wall_seconds=1.5, command="cvc5 bug.smt2", smt_path=bug_report.smt_path
        )
        bug_report2 = BugReport(
            kind=BugKind.SOUNDNESS,
            smt_path=bug_report.smt_path,
            solver1_result=result1,
            solver2_result=result2,
            description="Another soundness bug",
        )
        bug_dir2 = save_bug(bug_report2, str(output_dir))

        # Second bug should have higher index
        idx1 = int(bug_dir1.name)
        idx2 = int(bug_dir2.name)
        assert idx2 > idx1

    def test_save_bug_handles_missing_smt(self, temp_dir):
        """Test that save_bug handles missing SMT file gracefully."""
        result1 = SolverResult(
            outcome=SolverOutcome.SAT, stdout="sat\n", stderr="",
            wall_seconds=1.0, command="z3 missing.smt2", smt_path="/nonexistent/missing.smt2"
        )
        result2 = SolverResult(
            outcome=SolverOutcome.UNSAT, stdout="unsat\n", stderr="",
            wall_seconds=1.5, command="cvc5 missing.smt2", smt_path="/nonexistent/missing.smt2"
        )
        report = BugReport(
            kind=BugKind.SOUNDNESS,
            smt_path="/nonexistent/missing.smt2",
            solver1_result=result1,
            solver2_result=result2,
            description="Soundness bug",
        )

        output_dir = temp_dir / "bugs"
        bug_dir = save_bug(report, str(output_dir))

        # Should still create the directory and log
        assert bug_dir.exists()
        log_file = bug_dir / "error_log.txt"
        assert log_file.exists()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
