"""
Unit tests for solver_manager module (chimera/core/solver_manager.py).

Tests cover:
- SolverConfig creation and validation
- SolverOutcome classification
- SolverResult properties
- run_solver execution (with mocked solvers)
- Error pattern detection
- Timeout handling
"""

import os
import signal
import subprocess
import tempfile
import time
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock, PropertyMock

from chimera.core.solver_manager import (
    SolverConfig,
    SolverResult,
    SolverOutcome,
    run_solver,
    run_solver_incremental,
    default_z3_args,
    default_cvc5_args,
    _classify_output,
    _kill_process_group,
)


class TestSolverOutcome:
    """Tests for SolverOutcome enum."""

    def test_from_stdout_sat(self):
        """Test classification of 'sat' result."""
        assert SolverOutcome.from_stdout("sat") == SolverOutcome.SAT
        assert SolverOutcome.from_stdout("  sat  ") == SolverOutcome.SAT
        assert SolverOutcome.from_stdout("SAT") != SolverOutcome.SAT  # Case-sensitive

    def test_from_stdout_unsat(self):
        """Test classification of 'unsat' result."""
        assert SolverOutcome.from_stdout("unsat") == SolverOutcome.UNSAT
        assert SolverOutcome.from_stdout("  unsat\n") == SolverOutcome.UNSAT

    def test_from_stdout_unknown(self):
        """Test classification of 'unknown' result."""
        assert SolverOutcome.from_stdout("unknown") == SolverOutcome.UNKNOWN
        assert SolverOutcome.from_stdout("  unknown  ") == SolverOutcome.UNKNOWN

    def test_from_stdout_error(self):
        """Test classification of unrecognized output."""
        assert SolverOutcome.from_stdout("") == SolverOutcome.ERROR
        assert SolverOutcome.from_stdout("error") == SolverOutcome.ERROR
        assert SolverOutcome.from_stdout("model:") == SolverOutcome.ERROR
        assert SolverOutcome.from_stdout("random text") == SolverOutcome.ERROR


class TestSolverResult:
    """Tests for SolverResult dataclass."""

    def test_result_creation(self):
        """Test basic result creation."""
        result = SolverResult(
            outcome=SolverOutcome.SAT,
            stdout="sat\n",
            stderr="",
            exit_code=0,
            wall_seconds=1.5,
            command="z3 test.smt2",
            smt_path="/path/to/test.smt2",
        )
        assert result.outcome == SolverOutcome.SAT
        assert result.stdout == "sat\n"
        assert result.exit_code == 0
        assert result.wall_seconds == 1.5

    def test_is_normal_property(self):
        """Test is_normal property for normal outcomes."""
        sat_result = SolverResult(outcome=SolverOutcome.SAT)
        unsat_result = SolverResult(outcome=SolverOutcome.UNSAT)
        unknown_result = SolverResult(outcome=SolverOutcome.UNKNOWN)
        timeout_result = SolverResult(outcome=SolverOutcome.TIMEOUT)
        crash_result = SolverResult(outcome=SolverOutcome.CRASH)

        assert sat_result.is_normal is True
        assert unsat_result.is_normal is True
        assert unknown_result.is_normal is True
        assert timeout_result.is_normal is False
        assert crash_result.is_normal is False

    def test_answer_property(self):
        """Test answer property returns correct strings."""
        assert SolverResult(outcome=SolverOutcome.SAT).answer == "sat"
        assert SolverResult(outcome=SolverOutcome.UNSAT).answer == "unsat"
        assert SolverResult(outcome=SolverOutcome.UNKNOWN).answer == "unknown"
        assert SolverResult(outcome=SolverOutcome.TIMEOUT).answer is None
        assert SolverResult(outcome=SolverOutcome.CRASH).answer is None

    def test_result_frozen(self):
        """Test that SolverResult is immutable (frozen dataclass)."""
        result = SolverResult(outcome=SolverOutcome.SAT)
        with pytest.raises(AttributeError):
            result.outcome = SolverOutcome.UNSAT


class TestSolverConfig:
    """Tests for SolverConfig dataclass."""

    def test_basic_config(self):
        """Test basic solver configuration."""
        config = SolverConfig(name="z3", binary="/usr/bin/z3")
        assert config.name == "z3"
        assert config.binary == "/usr/bin/z3"
        assert config.base_args == []
        assert config.extra_args == []

    def test_config_with_args(self):
        """Test configuration with arguments."""
        config = SolverConfig(
            name="cvc5",
            binary="/usr/bin/cvc5",
            base_args=["--strings-exp", "-q"],
            extra_args=["--check-models"],
        )
        assert config.name == "cvc5"
        assert "--strings-exp" in config.base_args
        assert "--check-models" in config.extra_args

    def test_command_building(self):
        """Test command line construction."""
        config = SolverConfig(
            name="z3",
            binary="/usr/bin/z3",
            base_args=["model_validate=true"],
        )
        cmd = config.command("test.smt2")
        assert "/usr/bin/z3" in cmd
        assert "model_validate=true" in cmd
        assert "test.smt2" in cmd

    def test_command_with_extra_args(self):
        """Test command with extra arguments."""
        config = SolverConfig(
            name="z3",
            binary="/usr/bin/z3",
            base_args=["-in"],
            extra_args=["model_validate=true"],
        )
        cmd = config.command("formula.smt2")
        assert "-in" in cmd
        assert "model_validate=true" in cmd
        assert "formula.smt2" in cmd


class TestClassifyOutput:
    """Tests for _classify_output function."""

    def test_segfault_detection(self):
        """Test segmentation fault pattern detection."""
        assert _classify_output("", "Segmentation fault") == SolverOutcome.SEGFAULT
        assert _classify_output("", "segmentation fault") == SolverOutcome.SEGFAULT
        assert _classify_output("SIGSEGV", "") == SolverOutcome.SEGFAULT

    def test_assertion_violation_detection(self):
        """Test assertion violation pattern detection."""
        assert _classify_output("ASSERTION VIOLATION", "") == SolverOutcome.ASSERT_VIOLATION
        assert _classify_output("", "AssertionError: foo") == SolverOutcome.ASSERT_VIOLATION

    def test_invalid_model_detection(self):
        """Test invalid model pattern detection."""
        assert _classify_output("invalid model", "") == SolverOutcome.INVALID_MODEL
        assert _classify_output("", "ERRORS SATISFYING") == SolverOutcome.INVALID_MODEL
        assert _classify_output("model doesn't satisfy", "") == SolverOutcome.INVALID_MODEL

    def test_parse_error_detection(self):
        """Test parse error pattern detection."""
        assert _classify_output("Parse Error: line 5", "") == SolverOutcome.PARSE_ERROR
        assert _classify_output("", "unsupported reserved word") == SolverOutcome.PARSE_ERROR
        assert _classify_output("option parsing failed", "") == SolverOutcome.ERROR

    def test_normal_output_no_match(self):
        """Test that normal output returns None."""
        assert _classify_output("sat", "") is None
        assert _classify_output("unsat", "") is None
        assert _classify_output("unknown", "") is None
        assert _classify_output("", "") is None

    def test_crash_patterns(self):
        """Test general crash pattern detection."""
        assert _classify_output("NullPointerException", "") == SolverOutcome.CRASH


class TestDefaultArgs:
    """Tests for default argument builders."""

    def test_default_z3_args_basic(self):
        """Test basic Z3 default arguments."""
        args = default_z3_args()
        assert isinstance(args, list)
        assert len(args) > 0

    def test_default_z3_args_timeout(self):
        """Test Z3 timeout argument."""
        args = default_z3_args(timeout_ms=5000)
        # Timeout should be in seconds for Z3's -T flag
        assert any("-T:" in arg or "-T " in arg for arg in args)

    def test_default_z3_args_incremental(self):
        """Test Z3 incremental mode."""
        args = default_z3_args(incremental=True)
        assert "-in" in args

    def test_default_z3_args_check_models(self):
        """Test Z3 model validation."""
        args = default_z3_args(check_models=True)
        assert any("model_validate" in arg for arg in args)

    def test_default_cvc5_args_basic(self):
        """Test basic cvc5 default arguments."""
        args = default_cvc5_args()
        assert isinstance(args, list)
        assert "-q" in args
        assert "--strings-exp" in args

    def test_default_cvc5_args_incremental(self):
        """Test cvc5 incremental mode."""
        args = default_cvc5_args(incremental=True)
        assert "-i" in args

    def test_default_cvc5_args_check_models(self):
        """Test cvc5 model checking."""
        args = default_cvc5_args(check_models=True)
        assert "--check-models" in args

    def test_default_cvc5_args_timeout(self):
        """Test cvc5 timeout argument."""
        args = default_cvc5_args(timeout_ms=5000)
        assert any("--tlimit" in arg for arg in args)


class TestRunSolver:
    """Tests for run_solver function (mocked)."""

    @pytest.fixture
    def mock_smt_file(self, temp_dir):
        """Create a simple SMT file for testing."""
        smt_path = temp_dir / "test.smt2"
        smt_path.write_text("(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n(check-sat)\n")
        return str(smt_path)

    def test_binary_not_found(self, mock_smt_file):
        """Test handling when solver binary doesn't exist."""
        config = SolverConfig(name="fake-solver", binary="/nonexistent/solver")
        result = run_solver(config, mock_smt_file, timeout=5.0)

        assert result.outcome == SolverOutcome.ERROR
        assert "not found" in result.stderr.lower() or "Binary not found" in result.stderr

    def test_successful_sat_result(self, mock_smt_file):
        """Test successful solver run returning sat."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.returncode = 0
            mock_proc.communicate.return_value = ("sat\n", "")
            mock_popen.return_value = mock_proc

            result = run_solver(config, mock_smt_file, timeout=5.0)

            assert result.outcome == SolverOutcome.SAT
            assert result.answer == "sat"

    def test_successful_unsat_result(self, mock_smt_file):
        """Test successful solver run returning unsat."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.returncode = 0
            mock_proc.communicate.return_value = ("unsat\n", "")
            mock_popen.return_value = mock_proc

            result = run_solver(config, mock_smt_file, timeout=5.0)

            assert result.outcome == SolverOutcome.UNSAT
            assert result.answer == "unsat"

    def test_timeout_result(self, mock_smt_file):
        """Test timeout handling."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.pid = 12345
            mock_proc.communicate.side_effect = subprocess.TimeoutExpired(cmd="mock", timeout=5)
            mock_popen.return_value = mock_proc

            with patch("chimera.core.solver_manager._kill_process_group"):
                result = run_solver(config, mock_smt_file, timeout=5.0)

            assert result.outcome == SolverOutcome.TIMEOUT

    def test_crash_from_exit_code(self, mock_smt_file):
        """Test crash detection from exit code."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.returncode = -signal.SIGSEGV  # Segfault signal
            mock_proc.communicate.return_value = ("", "")
            mock_popen.return_value = mock_proc

            result = run_solver(config, mock_smt_file, timeout=5.0)

            assert result.outcome == SolverOutcome.SEGFAULT

    def test_abort_signal(self, mock_smt_file):
        """Test abort signal detection."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.returncode = -signal.SIGABRT
            mock_proc.communicate.return_value = ("", "")
            mock_popen.return_value = mock_proc

            result = run_solver(config, mock_smt_file, timeout=5.0)

            assert result.outcome == SolverOutcome.ASSERT_VIOLATION


class TestRunSolverIncremental:
    """Tests for run_solver_incremental function."""

    @pytest.fixture
    def mock_smt_file(self, temp_dir):
        """Create an incremental SMT file."""
        smt_path = temp_dir / "incremental.smt2"
        smt_path.write_text("(set-logic QF_LIA)\n(push)\n(check-sat)\n(pop)\n")
        return str(smt_path)

    def test_multiple_check_sat_results(self, mock_smt_file):
        """Test incremental mode returns multiple results."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.returncode = 0
            mock_proc.communicate.return_value = ("sat\nunsat\nsat\n", "")
            mock_popen.return_value = mock_proc

            results = run_solver_incremental(config, mock_smt_file, timeout=5.0)

            assert len(results) == 3
            assert results[0].outcome == SolverOutcome.SAT
            assert results[1].outcome == SolverOutcome.UNSAT
            assert results[2].outcome == SolverOutcome.SAT

    def test_single_result_non_incremental(self, mock_smt_file):
        """Test non-incremental mode returns single result."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.returncode = 0
            mock_proc.communicate.return_value = ("sat\n", "")
            mock_popen.return_value = mock_proc

            results = run_solver_incremental(config, mock_smt_file, timeout=5.0)

            assert len(results) == 1
            assert results[0].outcome == SolverOutcome.SAT

    def test_error_returns_single_result(self, mock_smt_file):
        """Test that error outcomes return single result."""
        config = SolverConfig(name="mock-solver", binary="/usr/bin/true")

        with patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.returncode = 0
            mock_proc.communicate.return_value = ("Segmentation fault\n", "")
            mock_popen.return_value = mock_proc

            results = run_solver_incremental(config, mock_smt_file, timeout=5.0)

            assert len(results) == 1
            assert results[0].outcome == SolverOutcome.SEGFAULT


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
