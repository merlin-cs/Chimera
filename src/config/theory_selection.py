"""Solver-compatible generator theory selection.

This module centralizes the logic for deciding which generator theory keys
should be enabled for a given solver (or solver pair).

Why this exists:
- Different solvers support different SMT theories.
- We want to enable only *compatible* generators when running experiments.
- We also want to support optional LLM-only generators when available.

The returned theory keys are the ones used by `generator_loader.GENERATORS`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Sequence


@dataclass(frozen=True)
class SolverTheoryProfile:
    general: Sequence[str]
    z3_only: Sequence[str]
    cvc5_only: Sequence[str]
    bitwuzla_only: Sequence[str]


DEFAULT_PROFILE = SolverTheoryProfile(
    # Theories broadly used across solvers in this repo (see chimera.py)
    general=(
        "fp",
        "int",
        "real",
        "core",
        "strings",
        "bv",
        "array",
        "reals_ints",
    ),
    # Z3-specific extras.
    z3_only=(
        "z3_seq",
        # LLM-produced Z3 generators that may exist:
        "z3seq",
        "z3characters",
        "z3relation",
    ),
    # CVC5-specific extras.
    cvc5_only=(
        "bag",
        "datatype",
        "ff",
        "seq",
        "set",
        "ho",
        "trans",
        "sep",
        "cvc5strings",
    ),
    # Bitwuzla is intentionally small in chimera.py.
    bitwuzla_only=(
        "core",
        "fp",
        "bv",
        "array",
    ),
)


def _norm_solver(name: str | None) -> str:
    return (name or "").strip().lower()


def _unique_preserve_order(items: Iterable[str]) -> List[str]:
    seen = set()
    out: List[str] = []
    for x in items:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def get_compatible_theories(
    solver1: str,
    solver2: str | None = None,
    *,
    profile: SolverTheoryProfile = DEFAULT_PROFILE,
) -> List[str]:
    """Return generator theory keys compatible with the chosen solver(s).

    Rules (mirrors chimera.py intent):
    - If either solver is bitwuzla: restrict to the bitwuzla-safe subset.
    - If using two different solvers (z3 vs cvc5): keep only general theories.
    - If z3==z3: enable z3_only + general.
    - If cvc5==cvc5: enable cvc5_only + general.

    Note: This returns *theory keys*; whether a theory key resolves to a
    generator is handled by generator_loader (new vs original fallback).
    """

    s1 = _norm_solver(solver1)
    s2 = _norm_solver(solver2) if solver2 is not None else s1

    if "bitwuzla" in (s1, s2):
        return _unique_preserve_order(profile.bitwuzla_only)

    if s1 in ("z3", "cvc5") and s2 in ("z3", "cvc5") and s1 != s2:
        return _unique_preserve_order(profile.general)

    if s1 == s2 == "z3":
        return _unique_preserve_order([*profile.z3_only, *profile.general])

    if s1 == s2 == "cvc5":
        return _unique_preserve_order([*profile.cvc5_only, *profile.general])

    # Fallback: be conservative.
    return _unique_preserve_order(profile.general)
