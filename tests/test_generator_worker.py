"""Tests for external Once4All generator isolation."""

from pathlib import Path
import random

import pytest

from chimera.core.solver_manager import SolverConfig
from chimera.engines.once4all_engine import GeneratorRegistry, Once4AllStrategy


def test_external_generator_is_not_imported_during_discovery(tmp_path: Path) -> None:
    marker = tmp_path / "imported"
    module = tmp_path / "toy_generator.py"
    module.write_text(
        "from pathlib import Path\n"
        f"Path({str(marker)!r}).write_text('imported')\n"
        "def generate_toy_formula_with_decls():\n"
        "    return '(declare-const x Int)', '(> x 0)'\n",
        encoding="utf-8",
    )
    registry = GeneratorRegistry()
    assert registry.load_from_directory(tmp_path, isolated=True) == 1
    assert not marker.exists()
    assert registry.get("toy") is not None
    assert registry.get("toy")() == ("(declare-const x Int)", "(> x 0)")
    assert marker.exists()


def test_external_generator_timeout_is_reported_clearly(tmp_path: Path) -> None:
    module = tmp_path / "slow_generator.py"
    module.write_text(
        "import time\n"
        "def generate_slow_formula_with_decls():\n"
        "    time.sleep(0.2)\n"
        "    return '', 'true'\n",
        encoding="utf-8",
    )
    registry = GeneratorRegistry()
    assert registry.load_from_directory(tmp_path, isolated=True, timeout=0.01) == 1
    with pytest.raises(RuntimeError, match="timed out"):
        registry.get("slow")()


def test_external_generator_preserves_plain_text_and_campaign_seed(tmp_path: Path) -> None:
    module = tmp_path / "plain_generator.py"
    module.write_text(
        "import random\n"
        "def generate_plain_formula():\n"
        "    return f'(assert (= {random.randrange(1000000)} 0))'\n",
        encoding="utf-8",
    )
    registry = GeneratorRegistry()
    assert registry.load_from_directory(tmp_path, isolated=True) == 1
    generator = registry.get("plain")
    assert generator is not None
    random.seed(73)
    first = generator()
    random.seed(73)
    second = generator()
    assert isinstance(first, str)
    assert first == second


def test_once4all_blocks_solver_specific_generators_for_every_solver() -> None:
    solvers = (
        SolverConfig("cvc5-old", "/usr/bin/true"),
        SolverConfig("cvc5-new", "/usr/bin/true"),
        SolverConfig("z3", "/usr/bin/true"),
    )
    blocked = Once4AllStrategy._incompatible_theories_for_solvers(solvers)
    assert "bags" in blocked
    assert "z3seq" in blocked
