"""Discovery of supported Chimera extension entry points."""

from __future__ import annotations

from importlib import metadata
from typing import Any, List


def _group(name: str) -> List[Any]:
    entries = metadata.entry_points()
    if hasattr(entries, "select"):
        return list(entries.select(group=name))
    return list(entries.get(name, []))


def discover_case_producers() -> List[Any]:
    """Return registered case-producer entry points without instantiating them."""
    return _group("chimera.case_producers")


def discover_generator_providers() -> List[Any]:
    """Return registered generator-provider entry points."""
    return _group("chimera.generator_providers")


__all__ = ["discover_case_producers", "discover_generator_providers"]
