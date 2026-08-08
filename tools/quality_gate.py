"""Fail CI only when Ruff or mypy diagnostics exceed the checked baseline."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Dict


ROOT = Path(__file__).resolve().parents[1]
BASELINE_PATH = Path(__file__).with_name("quality_baseline.json")


def _ruff_counts() -> Counter[str]:
    result = subprocess.run(
        ["ruff", "check", "chimera", "tests", "--output-format", "json"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode not in (0, 1):
        raise RuntimeError(result.stderr.strip() or "ruff failed")
    if not result.stdout.strip():
        return Counter()
    diagnostics = json.loads(result.stdout)
    return Counter(item["code"] for item in diagnostics)


def _mypy_counts() -> Counter[str]:
    result = subprocess.run(
        ["mypy", "chimera", "--no-error-summary"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode not in (0, 1):
        raise RuntimeError(result.stderr.strip() or "mypy failed")
    return Counter(
        match.group(1)
        for line in (result.stdout + result.stderr).splitlines()
        if (match := re.search(r"\[([^\]]+)\]$", line))
    )


def _new_diagnostics(actual: Counter[str], baseline: Dict[str, int]) -> Dict[str, int]:
    return {
        code: count - baseline.get(code, 0)
        for code, count in actual.items()
        if count > baseline.get(code, 0)
    }


def main() -> int:
    baseline: Dict[str, Any] = json.loads(BASELINE_PATH.read_text(encoding="utf-8"))
    try:
        ruff_new = _new_diagnostics(_ruff_counts(), baseline["ruff"])
        mypy_new = _new_diagnostics(_mypy_counts(), baseline["mypy"])
    except (OSError, RuntimeError, json.JSONDecodeError) as exc:
        print(f"quality tool failed: {exc}")
        return 2
    if ruff_new or mypy_new:
        print("new quality diagnostics detected:")
        if ruff_new:
            print("  ruff:", ruff_new)
        if mypy_new:
            print("  mypy:", mypy_new)
        return 1
    print("quality diagnostics are at or below baseline")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
