"""
Once4All engine — LLM-synthesised generator integration.

Algorithm Overview
------------------
1. Dynamically load theory-specific generator functions produced by an LLM
   (e.g. ``generate_bv_formula_with_decls``).
2. For each iteration:
   a. Pick a random theory compatible with the target solvers.
   b. Invoke the corresponding generator to obtain a formula string
      (with ``declare-*`` commands).
   c. Parse the generated string into a ``Script``.
   d. (Optionally) extract a skeleton and fill holes from the parsed
      formula, combining generative + skeleton-enumeration strategies.
   e. Emit the final SMT-LIB string.

The engine is designed to be *robust* against flaky LLM generators — any
generation or parsing failure is logged and skipped without crashing the
campaign.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import importlib.util
import logging
import random
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from chimera.core.smt_ast import (
    Assert,
    CheckSat,
    Script,
    SkeletonExtractor,
    Term,
)
from chimera.core.smt_parser import parse_string
from chimera.core.solver_manager import SolverConfig
from chimera.core.differential_oracle import OracleConfig
from chimera.engines.base import FuzzingStrategy

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Generator registry
# ---------------------------------------------------------------------------

GeneratorFn = Callable[[], Tuple[str, str]]  # () -> (declarations, body)


class GeneratorRegistry:
    """Lazily-loaded collection of LLM generator functions.

    Each entry maps a **theory key** (e.g. ``"bv"``, ``"int"``) to a
    callable that returns ``(declarations_str, body_str)`` when invoked.
    """

    def __init__(self) -> None:
        self._registry: Dict[str, GeneratorFn] = {}

    # -- loading -------------------------------------------------------------

    def register(self, theory_key: str, fn: GeneratorFn) -> None:
        self._registry[theory_key] = fn

    def load_from_directory(
        self,
        directory: str | Path,
        *,
        theory_keys: Optional[Sequence[str]] = None,
    ) -> int:
        """Auto-discover and load generator modules from *directory* and subdirs.

        Searches the root directory and known backend subdirectories
        (``general``, ``cvc5``, ``z3``).
        """
        root = Path(directory)
        if not root.is_dir():
            logger.warning("Generator directory does not exist: %s", root)
            return 0

        loaded = 0
        # Scan root AND known backend subdirectories
        search_dirs = [root]
        for subdir in ("general", "cvc5", "z3"):
            sub = root / subdir
            if sub.is_dir():
                search_dirs.append(sub)

        for search_dir in search_dirs:
            for py_file in sorted(search_dir.glob("*_generator.py")):
                module_base = py_file.stem.replace("_generator", "")
                if theory_keys and module_base not in theory_keys:
                    continue
                fn = _load_generator_function(py_file, module_base)
                if fn is not None:
                    self._registry[module_base] = fn
                    loaded += 1

        logger.info(
            "Loaded %d generators from %s",
            loaded,
            root,
        )
        return loaded

    def load_from_existing_loader(self, generators_dict: Dict[str, Any]) -> int:
        """Import generators from the legacy ``GENERATORS`` dict.

        This bridges the existing ``src.config.generator_loader.GENERATORS``
        mapping into the new registry without duplicating discovery logic.
        """
        loaded = 0
        for key, fn in generators_dict.items():
            if callable(fn):
                self._registry[key] = fn
                loaded += 1
        logger.info("Imported %d generators from legacy loader", loaded)
        return loaded

    # -- retrieval -----------------------------------------------------------

    @property
    def theory_keys(self) -> List[str]:
        return list(self._registry.keys())

    def get(self, theory_key: str) -> Optional[GeneratorFn]:
        return self._registry.get(theory_key)

    def sample_key(self, candidates: Optional[Sequence[str]] = None) -> Optional[str]:
        """Return a random theory key from *candidates* (or all keys)."""
        pool = (
            [k for k in candidates if k in self._registry]
            if candidates
            else list(self._registry.keys())
        )
        return random.choice(pool) if pool else None


# ---------------------------------------------------------------------------
# Module loader helper
# ---------------------------------------------------------------------------

_CANDIDATE_SUFFIXES = (
    "formula_with_decls",
    "formula",
)


def _candidate_function_names(module_base: str) -> List[str]:
    names: List[str] = []
    for suffix in _CANDIDATE_SUFFIXES:
        names.append(f"generate_{module_base}_{suffix}")
    names.extend(["generate_formula_with_decls", "generate_formula"])
    return names


def _load_generator_function(
    path: Path,
    module_base: str,
) -> Optional[GeneratorFn]:
    """Load a single generator function from *path*."""
    try:
        spec = importlib.util.spec_from_file_location(
            f"{module_base}_generator", str(path)
        )
        if spec is None or spec.loader is None:
            return None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        for func_name in _candidate_function_names(module_base):
            fn = getattr(module, func_name, None)
            if callable(fn):
                # Type: we know fn is Callable[[], Tuple[str, str]] from generator contract
                return fn  # type: ignore[no-any-return]

        logger.debug("No suitable entry-point in %s", path)
        return None
    except Exception:
        logger.debug("Failed to load generator from %s", path, exc_info=True)
        return None


# ---------------------------------------------------------------------------
# Once4All Strategy
# ---------------------------------------------------------------------------

class Once4AllStrategy(FuzzingStrategy):
    """Generative fuzzer driven by LLM-synthesised formula generators.

    Parameters
    ----------
    solver1, solver2 : SolverConfig
        Solvers under differential testing.
    generator_dir : str, optional
        Path to the directory containing ``*_generator.py`` modules.
    compatible_theories : List[str], optional
        Restrict generation to these theory keys.
    legacy_generators : dict, optional
        Pre-loaded ``GENERATORS`` dict from ``src.config.generator_loader``.
    merge_skeletons : bool
        If ``True``, additionally extract a skeleton from the LLM output
        and re-fill holes (diversity amplification).
    """

    # Backend subdirectories scanned during generator discovery.
    _BACKEND_DIRS = ("general", "cvc5", "z3")

    @property
    def name(self) -> str:
        return "once4all"

    def __init__(
        self,
        solver1: SolverConfig,
        solver2: SolverConfig,
        *,
        generator_dir: Optional[str] = None,
        compatible_theories: Optional[List[str]] = None,
        legacy_generators: Optional[Dict[str, Any]] = None,
        merge_skeletons: bool = False,
        output_dir: str = "./chimera_bugs",
        temp_dir: str = "./chimera_temp",
        timeout: float = 10.0,
        oracle_config: Optional[OracleConfig] = None,
    ) -> None:
        super().__init__(
            solver1,
            solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
            timeout=timeout,
            oracle_config=oracle_config,
        )
        self._theories = compatible_theories
        self._merge_skeletons = merge_skeletons
        self._registry = GeneratorRegistry()

        # Populate the registry — directory loading now searches subdirs
        if legacy_generators:
            self._registry.load_from_existing_loader(legacy_generators)
        if generator_dir:
            self._registry.load_from_directory(
                generator_dir, theory_keys=compatible_theories
            )

        logger.info(
            "Once4All initialised: %d generators, theories=%s",
            len(self._registry.theory_keys),
            self._registry.theory_keys,
        )

    # -- generation ----------------------------------------------------------

    def generate(self, max_retries: int = 5) -> Optional[str]:
        """Invoke a random generator, validate output, and return an SMT-LIB string."""
        for _ in range(max_retries):
            theory_key = self._registry.sample_key(self._theories)
            if theory_key is None:
                logger.warning("Once4All: no generators available")
                return None

            gen_fn = self._registry.get(theory_key)
            if gen_fn is None:
                return None

            try:
                result = gen_fn()
            except Exception:
                logger.debug("Generator '%s' raised an exception", theory_key, exc_info=True)
                continue

            formula_str = self._unpack_generator_result(result)
            if formula_str is None:
                continue

            # Ensure check-sat is present
            if "(check-sat)" not in formula_str:
                formula_str += "\n(check-sat)"

            if self._merge_skeletons:
                formula_str = self._skeleton_amplify(formula_str) or formula_str

            # Validate the generated formula
            if self._validate_formula(formula_str):
                return formula_str

            logger.debug("Once4All: rejected formula from generator '%s'", theory_key)

        return None

    @staticmethod
    def _validate_formula(formula: str) -> bool:
        """Return True if *formula* has valid SMT-LIB2 syntax."""
        # Parenthesis balance
        depth = 0
        for ch in formula:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            if depth < 0:
                return False
        if depth != 0:
            return False

        # Reject leaked placeholders
        for bad in ("any_int", "any_bool", "real.pi"):
            if bad in formula:
                return False

        return True

    # -- helpers -------------------------------------------------------------

    @staticmethod
    def _unpack_generator_result(result: Any) -> Optional[str]:
        """Normalise generator output into a single SMT-LIB string.

        Generators may return:
        - ``(declarations_str, body_str)``
        - a plain ``str``
        - ``None``
        """
        if result is None:
            return None
        if isinstance(result, str):
            return result.strip() if result.strip() else None
        if isinstance(result, (tuple, list)) and len(result) >= 2:
            decls = str(result[0]).strip()
            body = str(result[1]).strip()
            if not body:
                return None
            parts: List[str] = []
            if decls:
                parts.append(decls)
            if not body.startswith("(assert"):
                body = f"(assert {body})"
            parts.append(body)
            return "\n".join(parts)
        return None

    def _skeleton_amplify(self, formula_str: str) -> Optional[str]:
        """Extract a skeleton from *formula_str*, then re-fill holes.

        This gives extra structural diversity even when the underlying
        generator is deterministic.
        """
        parsed = parse_string(formula_str, silent=True)
        if parsed is None:
            return None
        script, _globs = parsed

        extractor = SkeletonExtractor(rename_quantified=False)
        new_commands: list = []
        for cmd in script.commands:
            if isinstance(cmd, Assert):
                skeleton = extractor.transform(cmd.term)
                # For now, just emit the skeleton directly (holes are
                # already replaced with generic names).  A future version
                # can wire in the HistFuzz BuildingBlockPool here.
                new_commands.append(Assert(skeleton))
            else:
                new_commands.append(cmd)

        script.commands = new_commands
        return str(script)
