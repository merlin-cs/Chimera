#!/usr/bin/env python3
"""
Test runner script for Chimera test suite.

Usage:
    python tests/run_tests.py                    # Run all unit tests
    python tests/run_tests.py --integration      # Run integration tests (requires solvers)
    python tests/run_tests.py --all              # Run all tests
    python tests/run_tests.py --coverage         # Run with coverage report
    python tests/run_tests.py --quick            # Run quick smoke tests
"""

import sys
import subprocess
import argparse
from pathlib import Path


def run_tests(
    test_type: str = "unit",
    coverage: bool = False,
    verbose: bool = True,
    extra_args: list = None
) -> int:
    """Run tests using pytest."""
    cmd = ["pytest"]

    # Add verbosity
    if verbose:
        cmd.append("-v")

    # Select test type
    if test_type == "unit":
        cmd.extend(["-m", "not integration and not slow"])
    elif test_type == "integration":
        cmd.extend(["-m", "integration"])
    elif test_type == "all":
        pass  # Run all tests
    elif test_type == "quick":
        cmd.extend(["-m", "not slow", "-x", "--tb=short"])

    # Add coverage
    if coverage:
        cmd.extend([
            "--cov=src",
            "--cov=chimera",
            "--cov-report=term-missing",
            "--cov-report=html:htmlcov"
        ])

    # Add extra arguments
    if extra_args:
        cmd.extend(extra_args)

    # Run from project root
    project_root = Path(__file__).parent.parent
    print(f"Running: {' '.join(cmd)}")
    print(f"Working directory: {project_root}")

    result = subprocess.run(cmd, cwd=project_root)
    return result.returncode


def main():
    parser = argparse.ArgumentParser(
        description="Chimera test runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python tests/run_tests.py                    # Unit tests only
    python tests/run_tests.py --integration      # Integration tests
    python tests/run_tests.py --all              # All tests
    python tests/run_tests.py --coverage         # With coverage
    python tests/run_tests.py --quick            # Quick smoke test
    python tests/run_tests.py -k "test_logic"    # Run specific tests
        """
    )

    parser.add_argument(
        "--integration", "-i",
        action="store_true",
        help="Run integration tests (requires solver binaries)"
    )
    parser.add_argument(
        "--all", "-a",
        action="store_true",
        help="Run all tests including integration"
    )
    parser.add_argument(
        "--quick", "-q",
        action="store_true",
        help="Run quick smoke tests (stop on first failure)"
    )
    parser.add_argument(
        "--coverage", "-c",
        action="store_true",
        help="Generate coverage report"
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Reduce output verbosity"
    )
    parser.add_argument(
        "extra_args",
        nargs="*",
        help="Additional arguments to pass to pytest"
    )

    args = parser.parse_args()

    # Determine test type
    if args.all:
        test_type = "all"
    elif args.integration:
        test_type = "integration"
    elif args.quick:
        test_type = "quick"
    else:
        test_type = "unit"

    # Run tests
    return_code = run_tests(
        test_type=test_type,
        coverage=args.coverage,
        verbose=not args.quiet,
        extra_args=args.extra_args
    )

    sys.exit(return_code)


if __name__ == "__main__":
    main()
