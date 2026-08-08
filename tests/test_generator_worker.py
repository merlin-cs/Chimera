"""Tests for external Once4All generator isolation."""

from pathlib import Path

import pytest

from chimera.engines.once4all_engine import GeneratorRegistry


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
