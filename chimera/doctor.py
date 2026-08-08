"""Capability diagnostics for installed Chimera deployments."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
from typing import Any, Dict, Optional

from chimera.config.generator_config import NEW_GENERATORS_PATH
from chimera.history.streaming import packaged_corpus_path, validate_corpus
from chimera.resources import REWRITE_RULES_CSV


def _executable(path: Optional[str]) -> Dict[str, Any]:
    if not path:
        return {"path": None, "ok": False, "reason": "not configured"}
    value = Path(path)
    if not value.is_file():
        return {"path": path, "ok": False, "reason": "file does not exist"}
    if not os.access(value, os.X_OK):
        return {"path": path, "ok": False, "reason": "not executable"}
    return {"path": path, "ok": True}


def collect_capabilities(
    *,
    solver_paths: Optional[Dict[str, str]] = None,
    generator_dir: Optional[str] = None,
    artifact_dir: str = "./chimera_bugs",
) -> Dict[str, Any]:
    """Return JSON-serializable capability information."""
    corpus = packaged_corpus_path()
    corpus_status: Dict[str, Any] = {"path": str(corpus), "ok": False}
    if corpus.is_dir():
        try:
            manifest = validate_corpus(corpus)
            corpus_status.update({"ok": True, "format_version": manifest["format_version"]})
        except (OSError, ValueError) as exc:
            corpus_status["reason"] = str(exc)
    generators = Path(generator_dir) if generator_dir else Path(NEW_GENERATORS_PATH)
    generator_files = sorted(generators.rglob("*_generator.py")) if generators.is_dir() else []
    egraph_rules = False
    egraph_reason = "snake_egg or rewrite rules unavailable"
    snake_egg_available = importlib.util.find_spec("snake_egg") is not None
    if snake_egg_available:
        try:
            from chimera.engines.aries_engine import EqualitySaturationRewriter

            rewriter = EqualitySaturationRewriter()
            egraph_rules = rewriter.available
            if egraph_rules:
                egraph_reason = "available"
        except Exception as exc:
            egraph_reason = str(exc)
    else:
        egraph_reason = "snake_egg is not installed"
    return {
        "solvers": {
            name: _executable(path) for name, path in (solver_paths or {}).items()
        },
        "corpus": corpus_status,
        "aries": {
            "rules_csv": str(REWRITE_RULES_CSV),
            "rules_available": REWRITE_RULES_CSV.is_file(),
            "snake_egg_available": snake_egg_available,
            "egraph_rules_available": egraph_rules,
            "egraph_reason": egraph_reason,
        },
        "generators": {
            "directory": str(generators),
            "candidate_files": len(generator_files),
            "available": bool(generator_files),
        },
        "artifacts": {
            "directory": artifact_dir,
            "writable": os.access(artifact_dir, os.W_OK) if Path(artifact_dir).exists() else os.access(Path(artifact_dir).parent or Path("."), os.W_OK),
        },
    }


__all__ = ["collect_capabilities"]
