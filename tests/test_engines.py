"""
Unit tests for fuzzing engines (chimera/engines/).

Tests cover:
- FuzzingStrategy base class
- FuzzStats statistics tracking
- Engine configuration and initialization
"""

import pytest
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock

from chimera.engines.base import (
    FuzzStats,
    FuzzingStrategy,
)
from chimera.core.solver_manager import SolverConfig, SolverOutcome, SolverResult


@pytest.fixture
def solver1():
    """Create solver 1 config."""
    return SolverConfig(name="z3", binary="/usr/bin/z3")


@pytest.fixture
def solver2():
    """Create solver 2 config."""
    return SolverConfig(name="cvc5", binary="/usr/bin/cvc5", base_args=["--strings-exp"])


class TestFuzzStats:
    """Tests for FuzzStats dataclass."""

    def test_default_stats(self):
        """Test default statistics initialization."""
        stats = FuzzStats()
        assert stats.iterations == 0
        assert stats.formulas_generated == 0
        assert stats.bugs_found == 0
        assert stats.crashes == 0
        assert stats.soundness_bugs == 0
        assert stats.invalid_models == 0
        assert stats.parse_failures == 0

    def test_elapsed_time(self):
        """Test elapsed time calculation."""
        import time

        stats = FuzzStats()
        time.sleep(0.1)  # Small delay

        elapsed = stats.elapsed
        assert elapsed >= 0.1

    def test_summary(self):
        """Test summary string generation."""
        stats = FuzzStats(
            iterations=100,
            formulas_generated=95,
            bugs_found=5,
            crashes=2,
            soundness_bugs=2,
            invalid_models=1,
            parse_failures=5,
        )

        summary = stats.summary()
        assert "iters=100" in summary
        assert "generated=95" in summary
        assert "bugs=5" in summary
        assert "crashes=2" in summary


class ConcreteStrategy(FuzzingStrategy):
    """Concrete implementation of FuzzingStrategy for testing."""

    @property
    def name(self) -> str:
        return "test-strategy"

    def generate(self):
        """Generate a simple test formula."""
        return "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n(check-sat)"


class TestFuzzingStrategy:
    """Tests for FuzzingStrategy base class."""

    @pytest.fixture
    def temp_dirs(self):
        """Create temporary directories."""
        output_dir = tempfile.mkdtemp(prefix="chimera_output_")
        temp_dir = tempfile.mkdtemp(prefix="chimera_temp_")
        yield output_dir, temp_dir
        shutil.rmtree(output_dir, ignore_errors=True)
        shutil.rmtree(temp_dir, ignore_errors=True)

    def test_strategy_initialization(self, solver1, solver2, temp_dirs):
        """Test strategy initialization."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        assert strategy.solver1 == solver1
        assert strategy.solver2 == solver2
        assert strategy.output_dir == output_dir
        assert strategy.temp_dir == temp_dir
        assert strategy.stats is not None

    def test_strategy_name(self, solver1, solver2, temp_dirs):
        """Test strategy name property."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(solver1=solver1, solver2=solver2)
        assert strategy.name == "test-strategy"

    def test_strategy_directories_created(self, solver1, solver2):
        """Test that output and temp directories are created."""
        output_dir = tempfile.mkdtemp(prefix="chimera_test_")
        temp_dir = tempfile.mkdtemp(prefix="chimera_test_")

        # Remove them first
        shutil.rmtree(output_dir)
        shutil.rmtree(temp_dir)

        # Strategy should create them
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        assert Path(output_dir).exists()
        assert Path(temp_dir).exists()

        # Cleanup
        shutil.rmtree(output_dir, ignore_errors=True)
        shutil.rmtree(temp_dir, ignore_errors=True)

    def test_run_iteration_no_formula(self, solver1, solver2, temp_dirs):
        """Test run_iteration when generate returns None."""
        output_dir, temp_dir = temp_dirs

        class NoFormulaStrategy(FuzzingStrategy):
            @property
            def name(self):
                return "no-formula"

            def generate(self):
                return None

        strategy = NoFormulaStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        bugs = strategy.run_iteration(0)

        assert bugs == []
        assert strategy.stats.parse_failures == 1

    def test_run_iteration_with_mocked_solvers(self, solver1, solver2, temp_dirs):
        """Test run_iteration with mocked solver results."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
            timeout=10.0,
        )

        # Mock run_solver to return consistent results
        with patch("chimera.engines.base.run_solver") as mock_run:
            mock_run.side_effect = [
                SolverResult(
                    outcome=SolverOutcome.SAT,
                    stdout="sat\n",
                    stderr="",
                    exit_code=0,
                    wall_seconds=1.0,
                    command="z3 test.smt2",
                    smt_path="test.smt2",
                ),
                SolverResult(
                    outcome=SolverOutcome.SAT,
                    stdout="sat\n",
                    stderr="",
                    exit_code=0,
                    wall_seconds=1.0,
                    command="cvc5 test.smt2",
                    smt_path="test.smt2",
                ),
            ]

            bugs = strategy.run_iteration(0)

            # Both solvers agree, no bugs
            assert bugs == []
            assert strategy.stats.iterations == 1
            assert strategy.stats.formulas_generated == 1

    def test_run_iteration_detects_soundness_bug(self, solver1, solver2, temp_dirs):
        """Test run_iteration detects soundness bugs."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        with patch("chimera.engines.base.run_solver") as mock_run:
            mock_run.side_effect = [
                SolverResult(
                    outcome=SolverOutcome.SAT,
                    stdout="sat\n",
                    stderr="",
                    exit_code=0,
                    wall_seconds=1.0,
                    command="z3 test.smt2",
                    smt_path="test.smt2",
                ),
                SolverResult(
                    outcome=SolverOutcome.UNSAT,
                    stdout="unsat\n",
                    stderr="",
                    exit_code=0,
                    wall_seconds=1.0,
                    command="cvc5 test.smt2",
                    smt_path="test.smt2",
                ),
            ]

            bugs = strategy.run_iteration(0)

            # Should detect soundness bug
            assert len(bugs) == 1
            assert strategy.stats.bugs_found == 1
            assert strategy.stats.soundness_bugs == 1

    def test_run_iteration_detects_crash(self, solver1, solver2, temp_dirs):
        """Test run_iteration detects crashes."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        with patch("chimera.engines.base.run_solver") as mock_run:
            mock_run.side_effect = [
                SolverResult(
                    outcome=SolverOutcome.CRASH,
                    stdout="",
                    stderr="Segmentation fault",
                    exit_code=-11,
                    wall_seconds=1.0,
                    command="z3 test.smt2",
                    smt_path="test.smt2",
                ),
                SolverResult(
                    outcome=SolverOutcome.SAT,
                    stdout="sat\n",
                    stderr="",
                    exit_code=0,
                    wall_seconds=1.0,
                    command="cvc5 test.smt2",
                    smt_path="test.smt2",
                ),
            ]

            bugs = strategy.run_iteration(0)

            # Should detect crash
            assert len(bugs) >= 1
            assert strategy.stats.crashes >= 1

    def test_run_campaign_limited_iterations(self, solver1, solver2, temp_dirs):
        """Test run_campaign with limited iterations."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        with patch.object(strategy, "run_iteration") as mock_iter:
            mock_iter.return_value = []

            stats = strategy.run_campaign(max_iterations=5)

            assert mock_iter.call_count == 5
            # stats.iterations is 0 because the mock bypasses the real run_iteration
            # which increments the counter; verify via call_count instead

    def test_run_campaign_keyboard_interrupt(self, solver1, solver2, temp_dirs):
        """Test run_campaign handles keyboard interrupt."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        call_count = [0]

        def interrupt_after_two(*args):
            call_count[0] += 1
            strategy.stats.iterations += 1  # simulate the real method's counter
            if call_count[0] == 2:
                raise KeyboardInterrupt()
            return []

        with patch.object(strategy, "run_iteration", side_effect=interrupt_after_two):
            stats = strategy.run_campaign(max_iterations=10)

            # Should stop after interrupt
            assert stats.iterations == 2

    def test_run_campaign_unlimited(self, solver1, solver2, temp_dirs):
        """Test run_campaign with unlimited iterations (max_iterations=None)."""
        output_dir, temp_dir = temp_dirs
        strategy = ConcreteStrategy(
            solver1=solver1,
            solver2=solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
        )

        call_count = [0]

        def stop_after_10(*args):
            call_count[0] += 1
            strategy.stats.iterations += 1  # simulate the real method's counter
            if call_count[0] >= 10:
                raise KeyboardInterrupt()
            return []

        with patch.object(strategy, "run_iteration", side_effect=stop_after_10):
            stats = strategy.run_campaign(max_iterations=None)

            # Should run until interrupted
            assert stats.iterations == 10


class TestFuzzingStrategyAbstractMethods:
    """Tests for abstract method requirements."""

    def test_name_must_be_implemented(self, solver1, solver2):
        """Test that name property must be implemented."""

        class IncompleteStrategy(FuzzingStrategy):
            def generate(self):
                return "(check-sat)"

        with pytest.raises(TypeError):
            IncompleteStrategy(solver1=solver1, solver2=solver2)

    def test_generate_must_be_implemented(self, solver1, solver2):
        """Test that generate method must be implemented."""

        class IncompleteStrategy(FuzzingStrategy):
            @property
            def name(self):
                return "incomplete"

            # Missing generate()

        with pytest.raises(TypeError):
            IncompleteStrategy(solver1=solver1, solver2=solver2)


class TestStrategyTimeout:
    """Tests for strategy timeout handling."""

    @pytest.fixture
    def solver1(self):
        return SolverConfig(name="z3", binary="/usr/bin/z3")

    @pytest.fixture
    def solver2(self):
        return SolverConfig(name="cvc5", binary="/usr/bin/cvc5")

    def test_timeout_passed_to_solver(self, solver1, solver2):
        """Test that timeout is passed correctly to run_solver."""
        output_dir = tempfile.mkdtemp(prefix="chimera_test_")
        temp_dir = tempfile.mkdtemp(prefix="chimera_test_")

        try:
            strategy = ConcreteStrategy(
                solver1=solver1,
                solver2=solver2,
                output_dir=output_dir,
                temp_dir=temp_dir,
                timeout=5.0,
            )

            with patch("chimera.engines.base.run_solver") as mock_run:
                mock_run.return_value = SolverResult(
                    outcome=SolverOutcome.SAT,
                    stdout="sat\n",
                    stderr="",
                    command="solver test.smt2",
                )

                strategy.run_iteration(0)

                # Check timeout was passed
                for call in mock_run.call_args_list:
                    assert "timeout" in call.kwargs
                    assert call.kwargs["timeout"] == 5.0
        finally:
            shutil.rmtree(output_dir, ignore_errors=True)
            shutil.rmtree(temp_dir, ignore_errors=True)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
