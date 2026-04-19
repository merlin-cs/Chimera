"""
Test fixtures and utilities for Chimera test suite.

Provides:
- Sample SMT2 formulas for testing
- Mock solver configurations
- Temporary directory fixtures
- Common assertion helpers
"""

import os
import sys
import tempfile
import shutil
from pathlib import Path
from typing import Tuple, List

# Handle pytest import gracefully for standalone usage
try:
    import pytest
    PYTEST_AVAILABLE = True
except ImportError:
    PYTEST_AVAILABLE = False
    # Create dummy pytest fixture decorator
    class pytest:
        @staticmethod
        def fixture(func):
            return func


# =============================================================================
# Sample SMT2 Formulas for Testing
# =============================================================================

SAMPLE_FORMULAS = {
    "simple_sat": """(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (< y 10))
(assert (= (+ x y) 15))
(check-sat)
""",
    "simple_unsat": """(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
""",
    "bv_formula": """(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (= (bvadd a b) #x00000001))
(assert (= a b))
(check-sat)
""",
    "array_formula": """(set-logic QF_ALIA)
(declare-fun arr () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)
(assert (= (select arr i) v))
(assert (= (select arr (+ i 1)) (+ v 1)))
(check-sat)
""",
    "string_formula": """(set-logic QF_S)
(declare-fun s () String)
(declare-fun t () String)
(assert (= (str.++ s t) "hello world"))
(assert (str.prefixof "hel" s))
(check-sat)
""",
    "quantified": """(set-logic LIA)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (p x) (p (+ x 1)))))
(assert (exists ((y Int)) (p y)))
(check-sat)
""",
    "invalid_syntax": """(set-logic QF_LIA)
(declare-fun x () Int
(assert (> x 0)
(check-sat)
""",
    "with_let": """(set-logic QF_LIA)
(declare-fun x () Int)
(let ((y (+ x 1)))
  (assert (> y 0)))
(check-sat)
""",
    "incremental": """(set-logic QF_LIA)
(declare-fun x () Int)
(push)
(assert (> x 5))
(check-sat)
(pop)
(push)
(assert (< x 3))
(check-sat)
(pop)
""",
    "named_assertion": """(set-logic QF_LIA)
(declare-fun x () Int)
(assert (! (> x 0) :named pos-x))
(check-sat)
""",
    "with_check_sat_using": """(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat-using smt)
""",
}


def write_smt2_file(content: str, directory: Path, filename: str) -> Path:
    """Write SMT2 content to a file in the given directory."""
    filepath = directory / filename
    filepath.write_text(content, encoding="utf-8")
    return filepath


# =============================================================================
# Fixtures
# =============================================================================

@pytest.fixture
def temp_dir():
    """Create a temporary directory that is cleaned up after the test."""
    td = tempfile.mkdtemp(prefix="chimera_test_")
    yield Path(td)
    shutil.rmtree(td, ignore_errors=True)


@pytest.fixture
def sample_smt2_file(temp_dir):
    """Create a sample SMT2 file for testing."""
    content = SAMPLE_FORMULAS["simple_sat"]
    filepath = write_smt2_file(content, temp_dir, "test_formula.smt2")
    yield filepath
    # Cleanup is handled by temp_dir fixture


@pytest.fixture
def sample_smt2_files(temp_dir):
    """Create multiple sample SMT2 files for testing."""
    files = {}
    for name, content in SAMPLE_FORMULAS.items():
        if name not in ["invalid_syntax"]:
            files[name] = write_smt2_file(content, temp_dir, f"{name}.smt2")
    return files


@pytest.fixture
def bug_formulas_dir(temp_dir):
    """Create a directory structure mimicking bug-triggering formulas."""
    # Create logic-based subdirectories
    logics = ["QF_LIA", "QF_BV", "QF_ALIA", "QF_S", "LIA"]

    for logic in logics:
        logic_dir = temp_dir / logic
        logic_dir.mkdir(exist_ok=True)

        # Add sample formulas
        if logic == "QF_LIA":
            content = SAMPLE_FORMULAS["simple_sat"]
        elif logic == "QF_BV":
            content = SAMPLE_FORMULAS["bv_formula"]
        else:
            content = SAMPLE_FORMULAS["simple_sat"]

        for i in range(2):
            filepath = logic_dir / f"bug_{i}.smt2"
            filepath.write_text(content, encoding="utf-8")

    return temp_dir


@pytest.fixture
def skeleton_file(temp_dir):
    """Create a sample skeleton file for history-based fuzzing."""
    skeletons = [
        "(assert (and VAR0 TYPE0 VAR1 TYPE1))\n",
        "(assert (or VAR0 TYPE0 VAR1 TYPE1))\n",
        "(assert (=> VAR0 TYPE0 VAR1 TYPE1))\n",
        "(assert (not VAR0 TYPE0))\n",
        "(assert (= VAR0 TYPE0 VAR1 TYPE1))\n",
    ]
    filepath = temp_dir / "skeletons.smt2"
    filepath.write_text("".join(skeletons), encoding="utf-8")
    return filepath


@pytest.fixture
def building_blocks_file(temp_dir):
    """Create a sample building blocks file for history-based fuzzing."""
    content = """% var_Bool
(> var0 var1); var0, Int; var1, Int;
% var_Int
(+ var0 var1); var0, Int; var1, Int;
(* var0 42); var0, Int;
% var_BV
(bvadd var0 var1); var0, (_ BitVec 32); var1, (_ BitVec 32);
"""
    filepath = temp_dir / "building_blocks.txt"
    filepath.write_text(content, encoding="utf-8")
    return filepath


@pytest.fixture
def mock_solver_config():
    """Return a mock solver configuration for testing."""
    try:
        from chimera.core.solver_manager import SolverConfig
        return SolverConfig(
            name="mock-solver",
            binary="/usr/bin/true",  # Always succeeds
            base_args=[]
        )
    except ImportError:
        # Return a simple mock object if chimera is not available
        class MockConfig:
            name = "mock-solver"
            binary = "/usr/bin/true"
            base_args = []
        return MockConfig()


# =============================================================================
# Helper Classes
# =============================================================================

class MockProcessResult:
    """Mock result from subprocess.Popen."""
    def __init__(self, stdout: bytes = b"sat", stderr: bytes = b"", returncode: int = 0):
        self.stdout = stdout
        self.stderr = stderr
        self.returncode = returncode


class MockSolver:
    """Mock solver for testing without actual solver binaries."""

    def __init__(self, result: str = "sat", stderr: str = ""):
        self.result = result
        self.stderr = stderr

    def run(self, smt_file: str, timeout: float = 10.0) -> Tuple[str, str, float]:
        """Simulate running a solver on an SMT file."""
        return self.result, self.stderr, 0.1


# =============================================================================
# Assertion Helpers
# =============================================================================

def assert_valid_smt2(content: str):
    """Assert that content looks like valid SMT2 syntax."""
    assert "(set-logic" in content or "(assert" in content, "Missing SMT2 commands"
    assert content.count("(") >= content.count(")"), "Unbalanced parentheses (more closes)"
    assert content.count("(") <= content.count(")") + 5, "Unbalanced parentheses (more opens)"


def assert_file_exists(filepath: Path):
    """Assert that a file exists and is non-empty."""
    assert filepath.exists(), f"File does not exist: {filepath}"
    assert filepath.stat().st_size > 0, f"File is empty: {filepath}"


def assert_solver_result_valid(result: str):
    """Assert that a solver result is one of the expected values."""
    valid_results = {"sat", "unsat", "unknown", "timeout", "error", "parseerror"}
    assert result in valid_results, f"Unexpected solver result: {result}"
