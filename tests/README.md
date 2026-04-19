# Chimera Test Suite

This directory contains the comprehensive test suite for the Chimera SMT Solver Fuzzer.

## Test Structure

```
tests/
├── __init__.py              # Package initialization
├── conftest.py              # Pytest fixtures and utilities
├── run_tests.py             # Test runner script
│
├── test_core_fuzzer.py      # Tests for core fuzzing logic
├── test_run_solver.py       # Tests for solver interaction
├── test_history.py          # Tests for history-based fuzzing
├── test_parsing.py          # Tests for SMT-LIB parser
├── test_utils.py            # Tests for utility modules
├── test_generator.py        # Tests for formula generators
├── test_cli.py              # Tests for CLI interface
└── test_integration.py      # Integration tests (require solvers)
```

## Running Tests

### Quick Start

```bash
# Run all unit tests (fast, no solver required)
python -m pytest tests/ -v

# Or use the test runner
python tests/run_tests.py
```

### Test Categories

```bash
# Unit tests only (default)
python tests/run_tests.py

# Integration tests (requires Z3 and/or cvc5)
python tests/run_tests.py --integration

# All tests
python tests/run_tests.py --all

# Quick smoke tests (stop on first failure)
python tests/run_tests.py --quick

# With coverage report
python tests/run_tests.py --coverage
```

### Running Specific Tests

```bash
# Run specific test file
python -m pytest tests/test_core_fuzzer.py -v

# Run specific test class
python -m pytest tests/test_core_fuzzer.py::TestLogicCompatibility -v

# Run specific test
python -m pytest tests/test_core_fuzzer.py::TestLogicCompatibility::test_quantifier_restriction -v

# Run tests matching pattern
python -m pytest tests/ -k "logic" -v
```

### Parallel Execution

```bash
# Run tests in parallel (requires pytest-xdist)
python -m pytest tests/ -n auto
```

## Test Requirements

### Unit Tests

Unit tests have no external dependencies beyond the Python packages in `requirements-test.txt`:

```bash
pip install -r requirements-test.txt
```

### Integration Tests

Integration tests require SMT solver binaries to be installed:

- **Z3**: https://github.com/Z3Prover/z3
- **cvc5**: https://cvc5.github.io/

Install with:
```bash
# macOS
brew install z3 cvc5

# Ubuntu/Debian
sudo apt-get install z3 cvc5

# Or download binaries and add to PATH
```

## Test Fixtures

Key fixtures defined in `conftest.py`:

| Fixture | Description |
|---------|-------------|
| `temp_dir` | Temporary directory for test artifacts |
| `sample_smt2_file` | Sample SMT2 file for testing |
| `sample_smt2_files` | Multiple SMT2 files with different logics |
| `bug_formulas_dir` | Directory with bug-triggering formulas |
| `skeleton_file` | Sample skeleton file for history fuzzing |
| `building_blocks_file` | Sample building blocks corpus |
| `mock_solver_config` | Mock solver configuration |

## Sample Formulas

The `conftest.py` file defines sample SMT2 formulas for testing:

- `simple_sat` - Satisfiable LIA formula
- `simple_unsat` - Unsatisfiable LIA formula
- `bv_formula` - Bitvector formula
- `array_formula` - Array formula
- `string_formula` - String formula
- `quantified` - Formula with quantifiers
- `incremental` - Incremental script with push/pop
- `with_let` - Formula using let expressions
- `named_assertion` - Formula with named assertions

## Writing New Tests

### Unit Test Template

```python
import pytest
from src.module import function

class TestMyFeature:
    """Tests for MyFeature."""

    def test_basic_functionality(self, temp_dir):
        """Test basic functionality."""
        result = function("input")
        assert result == "expected"

    def test_edge_case(self):
        """Test edge case handling."""
        with pytest.raises(ValueError):
            function("invalid")

    @pytest.mark.slow
    def test_slow_operation(self):
        """Test slow operation."""
        # This test is marked as slow
        pass
```

### Integration Test Template

```python
import pytest

pytestmark = pytest.mark.integration

class TestMyIntegration:
    """Integration tests for MyFeature."""

    @pytest.mark.skipif(not shutil.which("z3"), reason="z3 not installed")
    def test_with_z3(self, temp_dir):
        """Test with actual Z3 solver."""
        import subprocess
        # ... test code ...
```

## Coverage

Generate coverage report:

```bash
python tests/run_tests.py --coverage
```

This creates:
- Terminal output with line coverage
- `htmlcov/` directory with HTML report

## Continuous Integration

For CI pipelines:

```yaml
# Example GitHub Actions
- name: Run tests
  run: python tests/run_tests.py --quick --coverage

- name: Upload coverage
  uses: codecov/codecov-action@v3
```

## Debugging Tests

```bash
# Run with verbose output and show prints
python -m pytest tests/test_file.py -v -s

# Run and enter debugger on failure
python -m pytest tests/test_file.py --pdb

# Run with detailed traceback
python -m pytest tests/test_file.py -v --tb=long
```

## Common Issues

### Import Errors

If you see import errors, ensure the project root is in the Python path:

```bash
export PYTHONPATH="${PYTHONPATH}:$(pwd)"
python -m pytest tests/
```

### Solver Not Found

Integration tests will be skipped if solvers are not installed. Check with:

```bash
which z3
which cvc5
```

### Timeout Issues

Some tests may timeout on slow systems. Increase timeout:

```bash
python -m pytest tests/ --timeout=60
```
