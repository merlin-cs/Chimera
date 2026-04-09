"""
Unit tests for solver_manager module (chimera.core.solver_manager).

Tests cover:
- Solver configuration and execution
- Result classification
- Timeout handling
- Error detection

Note: The API has changed significantly from src.run_solver.
The new module uses SolverConfig, SolverResult, and run_solver().
Tests have been updated to match the new API where possible.
"""

import os
import tempfile
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from chimera.core.solver_manager import (
    SolverConfig,
    SolverResult,
    SolverOutcome,
    run_solver,
    run_solver_incremental,
    default_z3_args,
    default_cvc5_args,
)


class TestSolverConfig:
    """Tests for SolverConfig dataclass."""

    def test_basic_config(self):
        """Test basic solver configuration."""
        config = SolverConfig(
            name="z3",
            binary="/usr/bin/z3",
            base_args=["-in"],
            extra_args=[],
        )
        assert config.name == "z3"
        assert config.binary == "/usr/bin/z3"
        assert "-in" in config.base_args

    def test_command_building(self):
        """Test command line construction."""
        config = SolverConfig(
            name="z3",
            binary="/usr/bin/z3",
            base_args=["model_validate=true"],
            extra_args=["-T:10"],
        )
        cmd = config.command("test.smt2")

        assert "/usr/bin/z3" in cmd
        assert "model_validate=true" in cmd
        assert "-T:10" in cmd
        assert "test.smt2" in cmd

    def test_cvc5_config(self):
        """Test cvc5 configuration."""
        config = SolverConfig(
            name="cvc5",
            binary="/usr/bin/cvc5",
            base_args=["--strings-exp"],
            extra_args=[],
        )
        cmd = config.command("test.smt2")

        assert "/usr/bin/cvc5" in cmd
        assert "--strings-exp" in cmd


class TestSolverOutcome:
    """Tests for SolverOutcome enum."""

    def test_from_stdout_sat(self):
        """Test SAT detection from output."""
        assert SolverOutcome.from_stdout("sat") == SolverOutcome.SAT

    def test_from_stdout_unsat(self):
        """Test UNSAT detection from output."""
        assert SolverOutcome.from_stdout("unsat") == SolverOutcome.UNSAT

    def test_from_stdout_unknown(self):
        """Test UNKNOWN detection from output."""
        assert SolverOutcome.from_stdout("unknown") == SolverOutcome.UNKNOWN

    def test_from_stdout_error(self):
        """Test ERROR for unrecognized output."""
        assert SolverOutcome.from_stdout("error") == SolverOutcome.ERROR
        assert SolverOutcome.from_stdout("") == SolverOutcome.ERROR


class TestSolverResult:
    """Tests for SolverResult dataclass."""

    def test_is_normal_for_sat(self):
        """Test is_normal property for SAT."""
        result = SolverResult(outcome=SolverOutcome.SAT)
        assert result.is_normal is True

    def test_is_normal_for_unsat(self):
        """Test is_normal property for UNSAT."""
        result = SolverResult(outcome=SolverOutcome.UNSAT)
        assert result.is_normal is True

    def test_is_normal_for_timeout(self):
        """Test is_normal property for TIMEOUT."""
        result = SolverResult(outcome=SolverOutcome.TIMEOUT)
        assert result.is_normal is False

    def test_is_normal_for_crash(self):
        """Test is_normal property for CRASH."""
        result = SolverResult(outcome=SolverOutcome.CRASH)
        assert result.is_normal is False

    def test_answer_property(self):
        """Test answer property returns correct strings."""
        assert SolverResult(outcome=SolverOutcome.SAT).answer == "sat"
        assert SolverResult(outcome=SolverOutcome.UNSAT).answer == "unsat"
        assert SolverResult(outcome=SolverOutcome.UNKNOWN).answer == "unknown"
        assert SolverResult(outcome=SolverOutcome.TIMEOUT).answer is None


class TestDefaultArgs:
    """Tests for default argument functions."""

    def test_default_z3_args_basic(self):
        """Test basic Z3 arguments."""
        args = default_z3_args(timeout_ms=10000)
        assert "model_validate=true" in args

    def test_default_z3_args_incremental(self):
        """Test Z3 incremental mode."""
        args = default_z3_args(incremental=True)
        assert "-in" in args

    def test_default_cvc5_args_basic(self):
        """Test basic cvc5 arguments."""
        args = default_cvc5_args(timeout_ms=10000)
        assert "--strings-exp" in args
        assert "-q" in args

    def test_default_cvc5_args_incremental(self):
        """Test cvc5 incremental mode."""
        args = default_cvc5_args(incremental=True)
        assert "-i" in args

    def test_default_cvc5_args_check_models(self):
        """Test cvc5 check-models option."""
        args = default_cvc5_args(check_models=True)
        assert "--check-models" in args


# TODO: Update for new chimera.core.solver_manager API
# The old src.run_solver functions command_line, read_result, check_crash,
# check_result, z3_tactic, add_specific_tactic, record_bug have been
# replaced with SolverConfig, SolverResult, and run_solver().
# Integration tests should be added to test the full solver execution.


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
