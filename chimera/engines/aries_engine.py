"""
Aries engine — mimetic mutation + deductive rewriting (equality saturation).

Algorithm Overview
------------------
1. Parse a seed ``.smt2`` file.
2. **Mimetic mutation** (inductive):
   a. Collect all operator / variable / constant occurrences from the AST.
   b. Match each occurrence against a catalogue of CSV-encoded rewrite rules
      (``res/RewriteRule.csv``).
   c. Apply a matched rewrite rule by substituting sub-terms, injecting
      fresh variables where required.
3. **Equality saturation** (deductive):
   a. Pick an assertion term and convert it to an IR understood by the
      ``snake_egg`` EGraph library.
   b. Insert the IR into an EGraph, run the rewrite-rule set.
   c. Extract a random equivalent expression, convert back to SMT-LIB.
4. Emit the mutated formula.

Both mutation stages are *optional* — the engine attempts mimetic mutation
first, then equality saturation, and emits whatever succeeds.

Copyright (c) 2024-2026 The Chimera authors.
SPDX-License-Identifier: MIT
"""

from __future__ import annotations

import csv
import logging
import os
import random
import shutil
import string
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from chimera.core.smt_ast import (
    Assert,
    CheckSat,
    DeclareConst,
    DeclareFun,
    Script,
    Term,
)
from chimera.core.smt_parser import parse_file, parse_string
from chimera.core.solver_manager import SolverConfig
from chimera.core.differential_oracle import OracleConfig
from chimera.engines.base import FuzzingStrategy

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Mimetic mutation (adapted from src/rewrite/mutate.py)
# ---------------------------------------------------------------------------

def _random_var_name() -> str:
    """Generate a random variable name like ``var38201``."""
    return "var" + "".join(random.choices(string.digits, k=5))


class MimeticMutator:
    """Apply mimetic (pattern-directed) mutation to an SMT ``Script``.

    Wraps the logic of the original ``Mutate`` class in a cleaner
    interface:

    * ``match_rules(term)`` — find which CSV rewrite rules apply to *term*.
    * ``apply_rule(term, rule_id)`` — rewrite *term* according to rule.
    * ``mutate(script)`` — perform a single random mutation.

    Parameters
    ----------
    rules_csv : str
        Path to ``RewriteRule.csv``.
    config_dir : str
        Directory containing ``config.txt``, ``ops.txt``, ``coversion.txt``.
    """

    def __init__(
        self,
        rules_csv: str,
        config_dir: Optional[str] = None,
    ) -> None:
        self._rules = self._load_csv(rules_csv)
        self._op_map: Dict[str, Any] = {}
        self._conversions: Dict[str, Dict[str, str]] = {}
        if config_dir:
            self._load_operator_config(config_dir)

        # Pre-parse rule patterns
        self._parsed_patterns: List[Any] = []
        for rule in self._rules:
            self._parsed_patterns.append(
                self._instantiate_pattern(rule.get("Target", ""))
            )

    # -- CSV / config loading ------------------------------------------------

    @staticmethod
    def _load_csv(path: str) -> List[Dict[str, str]]:
        try:
            with open(path, newline="", encoding="utf-8") as fh:
                return list(csv.DictReader(fh))
        except FileNotFoundError:
            logger.warning("Rewrite-rule CSV not found: %s", path)
            return []

    def _load_operator_config(self, config_dir: str) -> None:
        """Load operator type / conversion maps from plain-text configs."""
        config_path = os.path.join(config_dir, "config.txt")
        conversion_path = os.path.join(config_dir, "coversion.txt")  # sic (original typo)

        if os.path.isfile(config_path):
            self._op_map = _parse_config_txt(config_path)
        if os.path.isfile(conversion_path):
            self._conversions = _parse_conversion_txt(conversion_path)

    @staticmethod
    def _instantiate_pattern(target_str: str) -> Any:
        """Parse a CSV rule *Target* column into an AST fragment.

        Returns ``Script | Term | None`` depending on the pattern shape.
        """
        if not target_str:
            return None
        try:
            if "_Const" in target_str:
                parts = target_str.split(":")
                from chimera.core.smt_ast import Const
                return Const(parts[0], type=parts[1].replace("_Const", ""))
            if ";" in target_str:
                smt2 = _rule_to_smt2(target_str)
                result = parse_string(smt2, silent=True, prepare=False)
                if result:
                    return result[0]  # Script
            return None
        except Exception:
            return None

    # -- matching / mutation -------------------------------------------------

    def match_rules(self, term: Term, globs: dict) -> Tuple[int, ...]:
        """Return indices of CSV rules whose pattern matches *term*."""
        if not isinstance(term, Term):
            return ()
        ids: List[int] = []
        for idx, pattern in enumerate(self._parsed_patterns):
            if pattern is None:
                continue
            if isinstance(pattern, Term) and term.is_const:
                if term.type == pattern.type and str(term) == str(pattern):
                    ids.append(idx)
            elif isinstance(pattern, Script):
                if self._structural_match(term, pattern, globs):
                    ids.append(idx)
        return tuple(ids)

    def _structural_match(self, term: Term, pattern_script: Script, globs: dict) -> bool:
        """Check whether *term* structurally matches the assert body of *pattern_script*."""
        try:
            assert_cmds = [c for c in pattern_script.commands if isinstance(c, Assert)]
            if not assert_cmds:
                return False
            pattern_term = assert_cmds[0].term
            return self._compare_terms(term, pattern_term, globs)
        except Exception:
            return False

    def _compare_terms(self, t1: Term, t2: Term, globs: dict) -> bool:
        """Recursively compare *t1* against pattern *t2*."""
        if not isinstance(t2, Term):
            return False

        if t2.op is not None:
            if not isinstance(t1, Term) or t1.op != t2.op:
                return False
            if not t1.subterms or not t2.subterms:
                return False
            if len(t1.subterms) != len(t2.subterms):
                return False
            for i, sub2 in enumerate(t2.subterms):
                sub1 = t1.subterms[i]
                if isinstance(sub2, Term) and sub2.op is not None:
                    if isinstance(sub1, Term):
                        if not self._compare_terms(sub1, sub2, globs):
                            return False
                    else:
                        return False
                else:
                    if isinstance(sub1, str) and not isinstance(sub2, str):
                        return False
                    if isinstance(sub1, Term) and isinstance(sub2, Term):
                        if sub1.is_const != sub2.is_const:
                            return False
            return True

        # t2 has no op — it is a leaf
        if t1.op is not None:
            # Could still match if the return type equals t2.type
            if isinstance(t1.op, str):
                return_type = self._op_return_type(t1.op)
                return return_type == t2.type if return_type else False
            return False
        return t1.type == t2.type

    def _op_return_type(self, op: str) -> Optional[str]:
        info = self._op_map.get(op)
        if info is None:
            return None
        rt = info.get("return_type")
        if isinstance(rt, list):
            return None  # ambiguous
        if isinstance(rt, str):
            return rt
        return None

    def mutate(
        self,
        script: Script,
        globs: dict,
        *,
        max_substitutions: int = 3,
    ) -> bool:
        """Apply one random mimetic mutation to *script* **in-place**.

        Returns ``True`` if a mutation was performed.
        """
        terms = self._collect_terms(script)
        if not terms:
            return False

        random.shuffle(terms)
        for term in terms:
            rule_ids = self.match_rules(term, globs)
            if not rule_ids:
                continue
            rule_id = random.choice(rule_ids)
            return self._apply_rule(script, globs, term, rule_id, max_substitutions)
        return False

    def _apply_rule(
        self,
        script: Script,
        globs: dict,
        term: Term,
        rule_id: int,
        max_subs: int,
    ) -> bool:
        """Rewrite *term* in *script* according to rule *rule_id*."""
        rule = self._rules[rule_id]
        target_str = rule.get("Original", "")
        if not target_str:
            return False

        try:
            smt2 = _rule_to_smt2(target_str)
            result = parse_string(smt2, silent=True, prepare=False)
            if result is None:
                return False
            new_script, _new_globs = result
        except Exception:
            return False

        new_asserts = [c for c in new_script.commands if isinstance(c, Assert)]
        if not new_asserts:
            return False
        new_term = new_asserts[0].term
        if not isinstance(new_term, Term):
            return False

        # Wire free variables from the new rule into the existing script
        new_free_vars = [
            v for v in (new_script.free_var_occs if hasattr(new_script, "free_var_occs") else [])
            if isinstance(v, Term)
        ]
        existing_vars = {v.name: v for v in (script.free_var_occs if hasattr(script, "free_var_occs") else []) if isinstance(v, Term)}

        for nv in new_free_vars:
            if nv.name and nv.name in existing_vars:
                existing_var = existing_vars[nv.name]
                if isinstance(existing_var, Term) and existing_var.type == nv.type and nv.type:
                    new_term.substitute(nv, existing_var)
            elif nv.name and nv.type:
                fresh = Term()
                fresh_name = _random_var_name()
                fresh._initialize(name=fresh_name, type=nv.type, is_var=True)
                new_term.substitute(nv, fresh)
                script.commands.insert(0, DeclareFun(fresh_name, "", nv.type))
                globs[fresh_name] = nv.type

        # Substitute in assert commands (respect max_subs)
        n = random.randint(1, max_subs)
        for cmd in script.commands:
            if isinstance(cmd, Assert) and isinstance(cmd.term, Term):
                cmd.term.substitute_n(term, new_term, n)

        return True

    @staticmethod
    def _collect_terms(script: Script) -> List[Term]:
        terms: List[Term] = []
        if hasattr(script, "op_occs"):
            terms.extend(script.op_occs)
        if hasattr(script, "free_var_occs"):
            terms.extend(script.free_var_occs)
        if hasattr(script, "const_occs"):
            terms.extend(script.const_occs)
        return terms


# ---------------------------------------------------------------------------
# Equality-saturation rewriter (adapted from helper.py)
# ---------------------------------------------------------------------------

class EqualitySaturationRewriter:
    """Deductive rewriter powered by ``snake_egg`` EGraphs.

    Converts an SMT ``Term`` to the intermediate representation (IR)
    understood by ``snake_egg``, runs the rewrite rules, then converts
    back to an SMT-LIB string.

    Parameters
    ----------
    rules
        A list of ``snake_egg.Rewrite`` objects.  If ``None``, attempts
        to import the ``ALL_RULES`` set from the existing helper module.
    sample_size, attempts
        Tuning knobs for extraction diversity (see ``RewriteEGG``).
    """

    def __init__(
        self,
        rules: Optional[list] = None,
        sample_size: int = 1,
        attempts: int = 10,
    ) -> None:
        self._sample_size = sample_size
        self._attempts = attempts

        if rules is not None:
            self._rules = rules
        else:
            self._rules = self._import_default_rules()

    @staticmethod
    def _import_default_rules() -> list:
        """Try to import ``ALL_RULES`` from the existing helper module."""
        try:
            from chimera.engines.egraph.rewriter import ALL_RULES
            return ALL_RULES
        except ImportError:
            logger.warning("Could not import ALL_RULES — equality saturation disabled")
            return []

    def rewrite_term(self, term: Term, script: Script) -> Optional[str]:
        """Rewrite *term* via equality saturation.

        Returns the rewritten SMT-LIB sub-expression string, or ``None``
        if rewriting failed or produced no novel expression.
        """
        if not self._rules:
            return None

        try:
            from chimera.engines.egraph.rewriter import (
                convert_to_IR,
                convert_IR_to_str,
                RewriteEGG,
            )
        except ImportError:
            logger.debug("EGraph helpers not available")
            return None

        try:
            ir = convert_to_IR(term)
        except Exception:
            logger.debug("Failed to convert term to IR", exc_info=True)
            return None

        # Collect original sub-expressions for diversity scoring
        orig_sexprs: Set[str] = set()
        if hasattr(term, "get_all_subterms"):
            for st in term.get_all_subterms():
                orig_sexprs.add(str(st))

        try:
            results = RewriteEGG(
                ir,
                self._rules,
                list(orig_sexprs),
                sample_size=self._sample_size,
                attempts=self._attempts,
            )
        except Exception:
            logger.debug("RewriteEGG failed", exc_info=True)
            return None

        if not results:
            return None

        rewritten_ir = results[0]
        try:
            return convert_IR_to_str(rewritten_ir)
        except Exception:
            return None

    def rewrite_script(self, script: Script, globs: dict) -> bool:
        """Apply equality-saturation rewriting to one random assert in *script*.

        Mutates *script* in-place.  Returns ``True`` on success.
        """
        assert_cmds = [c for c in script.commands if isinstance(c, Assert)]
        if not assert_cmds:
            return False

        random.shuffle(assert_cmds)
        for cmd in assert_cmds:
            if not isinstance(cmd.term, Term) or cmd.term.op is None:
                continue
            new_str = self.rewrite_term(cmd.term, script)
            if new_str is None:
                continue

            # Handle symbolic placeholders from equality saturation
            new_str = self._resolve_symbolic_terms(new_str, globs)

            # Parse the new expression back into an AST
            wrapped = f"(assert {new_str})"
            result = parse_string(wrapped, silent=True, prepare=False)
            if result is None:
                continue
            new_script, _ = result
            new_asserts = [c for c in new_script.commands if isinstance(c, Assert)]
            if new_asserts and isinstance(new_asserts[0].term, Term):
                cmd.term = new_asserts[0].term
                return True
        return False

    @staticmethod
    def _resolve_symbolic_terms(expr_str: str, globs: dict) -> str:
        """Replace ``any_int`` / ``any_bool`` placeholders with concrete values.

        Also catches egraph/mimetic placeholder names like RewriteX, RewriteZ,
        or any symbol matching ^Rewrite[A-Z]\d*$ that would otherwise leak
        into the output as undeclared variables.
        """
        import re

        if "any_int" in expr_str:
            # Fall back to a literal
            expr_str = expr_str.replace("any_int", str(random.randint(0, 100)))

        if "any_bool" in expr_str:
            expr_str = expr_str.replace("any_bool", random.choice(["true", "false"]))

        # Strip egraph placeholder names (RewriteA, RewriteZ, RewriteX, etc.)
        # Replace with a safe concrete value (0 for Int context, true for Bool)
        expr_str = re.sub(r"\bRewrite[A-Z]\w*\b", "0", expr_str)

        return expr_str


# ---------------------------------------------------------------------------
# Small config-file parsers (from src/rewrite/mutate.py)
# ---------------------------------------------------------------------------

def _parse_config_txt(path: str) -> Dict[str, Dict[str, Any]]:
    config: Dict[str, Dict[str, Any]] = {}
    try:
        with open(path, "r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip().strip("()")
                if not line or line.startswith(";"):
                    continue
                tokens = line.split()
                if ":" in tokens[-1]:
                    tokens.pop()
                if len(tokens) < 2:
                    continue
                op_name = tokens[0]
                return_type = tokens[-1]
                operands = tokens[1:-1] if len(tokens) > 2 else []
                if op_name not in config:
                    config[op_name] = {"return_type": return_type, "operands": operands}
                else:
                    existing_rt = config[op_name]["return_type"]
                    if isinstance(existing_rt, list):
                        if return_type not in existing_rt:
                            existing_rt.append(return_type)
                    elif existing_rt != return_type:
                        config[op_name]["return_type"] = [existing_rt, return_type]
    except FileNotFoundError:
        pass
    return config


def _parse_conversion_txt(path: str) -> Dict[str, Dict[str, str]]:
    conversions: Dict[str, Dict[str, str]] = {}
    try:
        with open(path, "r", encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line or line.startswith(";"):
                    continue
                parts = line.split(" -> ")
                if len(parts) != 2:
                    continue
                before = parts[0]
                after_parts = parts[1].split(": ")
                if len(after_parts) != 2:
                    continue
                conversions.setdefault(before, {})[after_parts[0]] = after_parts[1]
    except FileNotFoundError:
        pass
    return conversions


def _rule_to_smt2(target_str: str) -> str:
    """Convert a CSV rule's *Target* or *Original* column into an SMT-LIB string."""
    parts = target_str.split(";")
    smt2 = ""
    for idx, part in enumerate(parts):
        if idx == 0:
            smt2 += f"(assert {part})"
        else:
            decl_parts = part.split(":")
            if len(decl_parts) >= 2:
                smt2 = f"(declare-fun {decl_parts[0]} () {decl_parts[1]})\n" + smt2
    return smt2


# ---------------------------------------------------------------------------
# Aries Strategy
# ---------------------------------------------------------------------------

class AriesStrategy(FuzzingStrategy):
    """Mimetic-mutation + equality-saturation fuzzer.

    Parameters
    ----------
    solver1, solver2 : SolverConfig
        Solvers for differential testing.
    seed_dir : str
        Directory of seed ``.smt2`` files.
    rules_csv : str
        Path to ``RewriteRule.csv`` for mimetic mutation.
    config_dir : str, optional
        Directory with operator / conversion config files.
    mimetic_rounds : int
        Number of mimetic mutation rounds per seed.
    use_egraph : bool
        Whether to apply equality-saturation after mimetic mutation.
    """

    @property
    def name(self) -> str:
        return "aries"

    def __init__(
        self,
        solver1: SolverConfig,
        solver2: SolverConfig,
        *,
        seed_dir: str = "",
        rules_csv: str = "",
        config_dir: Optional[str] = None,
        mimetic_rounds: int = 3,
        use_egraph: bool = True,
        output_dir: str = "./chimera_bugs",
        temp_dir: str = "./chimera_temp",
        timeout: float = 10.0,
        oracle_config: Optional[OracleConfig] = None,
    ) -> None:
        # Aries may emit push/pop or multiple check-sat commands,
        # so cvc5 needs --incremental mode.
        solver1, solver2 = self._ensure_incremental(solver1, solver2)

        super().__init__(
            solver1,
            solver2,
            output_dir=output_dir,
            temp_dir=temp_dir,
            timeout=timeout,
            oracle_config=oracle_config,
        )
        self._seed_paths = self._discover_smt_files(seed_dir) if seed_dir else []
        self._mimetic_rounds = mimetic_rounds
        self._use_egraph = use_egraph

        # Mimetic mutator
        self._mutator = MimeticMutator(rules_csv, config_dir) if rules_csv else None

        # Equality-saturation rewriter
        self._egraph: Optional[EqualitySaturationRewriter] = None
        if use_egraph:
            self._egraph = EqualitySaturationRewriter()

        logger.info(
            "Aries initialised: %d seeds, mimetic=%s, egraph=%s",
            len(self._seed_paths),
            self._mutator is not None,
            self._egraph is not None,
        )

    # -- generation ----------------------------------------------------------

    def generate(self, max_retries: int = 10) -> Optional[str]:
        """Mutate a random seed and return the resulting SMT-LIB string."""
        for _ in range(max_retries):
            formula_str = self._generate_once()
            if formula_str is None:
                continue
            if self._validate_formula_static(formula_str):
                return formula_str
            logger.debug("Aries: rejected formula (static check)")
        return None

    @staticmethod
    def _validate_formula_static(formula: str) -> bool:
        """Quick static check before running solvers."""
        # Check parentheses balance
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

        # Reject known unsupported constants
        for bad in ("real.pi", "any_int", "any_bool"):
            if bad in formula:
                return False

        return True

    def _generate_once(self) -> Optional[str]:
        """Internal: perform one mutation attempt."""
        if not self._seed_paths:
            logger.warning("Aries: no seed files")
            return None

        seed_path = random.choice(self._seed_paths)
        result = parse_file(seed_path, silent=True)
        if result is None:
            return None
        script, globs = result

        mutated = False

        # Phase 1: mimetic mutation
        if self._mutator is not None:
            for _ in range(self._mimetic_rounds):
                if self._mutator.mutate(script, globs):
                    mutated = True

        # Phase 2: equality saturation
        if self._egraph is not None:
            if self._egraph.rewrite_script(script, globs):
                mutated = True

        if not mutated:
            # At least shuffle assertions for minimal diversity
            asserts = [c for c in script.commands if isinstance(c, Assert)]
            if len(asserts) > 1:
                random.shuffle(asserts)

        # Ensure check-sat
        has_checksat = any(isinstance(c, CheckSat) for c in script.commands)
        if not has_checksat:
            script.commands.append(CheckSat())

        formula_str = str(script)

        # Final sanitization: catch any leaked placeholder names that slipped
        # through mimetic mutation or egraph rewriting.
        formula_str = self._sanitize_output(formula_str, globs)

        return formula_str if formula_str.strip() else None

    # -- helpers -------------------------------------------------------------

    @staticmethod
    def _discover_smt_files(directory: str) -> List[str]:
        result: List[str] = []
        for root, _dirs, files in os.walk(directory):
            for f in files:
                if f.endswith(".smt2"):
                    result.append(os.path.join(root, f))
        return result

    @staticmethod
    def _ensure_incremental(
        s1: SolverConfig, s2: SolverConfig
    ) -> Tuple[SolverConfig, SolverConfig]:
        """Ensure both solvers can handle push/pop in generated formulas.

        For cvc5: add ``-i`` (incremental mode) — required for push/pop.
        For z3: no extra flag needed — z3 handles push/pop in files natively.
                (``-in`` would read from stdin, conflicting with file input.)
        """

        def with_incremental(cfg: SolverConfig) -> SolverConfig:
            basename = os.path.basename(cfg.binary).lower()
            if "cvc5" in basename or basename.startswith("cvc"):
                # Preserve any caller-supplied base_args and extra_args.
                # Only add -i if the existing args don't already contain it.
                existing_args = list(cfg.base_args)
                if "-i" not in existing_args and "--incremental" not in existing_args:
                    existing_args.append("-i")
                return SolverConfig(
                    name=cfg.name,
                    binary=cfg.binary,
                    base_args=existing_args,
                    extra_args=list(cfg.extra_args),
                )
            # z3 doesn't need an incremental flag for file-based push/pop
            return cfg

        return with_incremental(s1), with_incremental(s2)

    @staticmethod
    def _sanitize_output(formula_str: str, globs: dict) -> str:
        """Remove any leaked placeholder names from the final SMT-LIB string.

        This catches:
        - ``Rewrite[A-Z]...`` egraph/mimetic placeholder names (only if NOT
          declared — legitimate user symbols are preserved)
        - ``any_int`` / ``any_bool`` that slipped through egraph resolution
        - Unfilled ``hole`` placeholders from incomplete mutation

        Each occurrence is replaced with a concrete value (0 for Int, true for Bool).
        """
        import re

        # Collect declared symbol names so we don't corrupt legitimate
        # user-defined constants that happen to match Rewrite* patterns.
        declared_names: set = set()
        for line in formula_str.splitlines():
            m = re.match(r"\(declare-(?:const|fun)\s+(\S+)\s+", line.strip())
            if m:
                declared_names.add(m.group(1))

        # Replace egraph placeholder names only when they are NOT declared.
        def rewrite_placeholder(m: re.Match) -> str:
            name = m.group(0)
            if name in declared_names:
                return name  # preserve legitimate user symbols
            return "0"

        formula_str = re.sub(r"\bRewrite[A-Z]\w*\b", rewrite_placeholder, formula_str)

        # Replace any_int/any_bool leftovers
        formula_str = formula_str.replace("any_int", "0")
        formula_str = formula_str.replace("any_bool", "true")

        # Replace unfilled hole placeholders (e.g. "hole 0", "hole 1")
        formula_str = re.sub(r"\bhole\s+\d+\b", "true", formula_str)

        return formula_str
