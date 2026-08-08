"""JSON worker for one external Once4All generator invocation."""

from __future__ import annotations

import importlib.util
import json
import random
import sys
from pathlib import Path
from typing import Any, Tuple


def _names(module_base: str) -> Tuple[str, ...]:
    return (
        f"generate_{module_base}_formula_with_decls",
        f"generate_{module_base}_formula",
        "generate_formula_with_decls",
        "generate_formula",
    )


def main() -> int:
    request = json.load(sys.stdin)
    # Seed before importing the external module as generator modules sometimes
    # create random data at import time.  The parent supplies this from the
    # injected campaign RNG, not from OS entropy.
    if "seed" in request:
        random.seed(int(request["seed"]))
    path = Path(request["path"])
    module_base = str(request["module_base"])
    spec = importlib.util.spec_from_file_location(
        f"chimera_external_{module_base}", str(path)
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load generator: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    fn: Any = None
    for name in _names(module_base):
        candidate = getattr(module, name, None)
        if callable(candidate):
            fn = candidate
            break
    if fn is None:
        raise RuntimeError(f"no generator entry point in {path}")
    result = fn()
    if isinstance(result, str):
        payload = {"ok": True, "result": result}
    elif isinstance(result, (tuple, list)) and len(result) >= 2:
        payload = {
            "ok": True,
            "result": [str(result[0]), str(result[1])],
        }
    else:
        raise RuntimeError("generator returned neither SMT-LIB text nor (declarations, body)")
    json.dump(
        payload,
        sys.stdout,
        sort_keys=True,
        separators=(",", ":"),
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        json.dump({"ok": False, "error": str(exc)}, sys.stdout)
        raise SystemExit(1) from None
