import os
import random
import re
import multiprocessing
import traceback
import time
import shutil
import subprocess
import sys
import signal
import logging
from copy import deepcopy
from typing import Optional, List, Any, Dict, Tuple, Union

from src.config.generator_loader import GENERATORS
from src.parsing.Parse import parse_file, parse_str
from src.formula_utils import get_all_basic_subformula
from src.utils.smt_handlers import format_smt_string
from src.run_solver import solver_runner, run_solver, record_bug
from src.constants import SAMPLE_SIZE, MAX_ITERATIONS, DEFAULT_STANDALONE_ITERATIONS

# Imports for History Fuzzing
from src.history.skeleton import Skeleton, obtain_hole, obtain_local_domain
from src.history.building_blocks import BuggySeed
from src.parsing.Ast import DeclareFun

# Imports for Rewrite Fuzzing
from src.rewrite.mutate import Mutate, mimetic_mutation
from src.utils.file_handlers import get_all_smt_files_recursively as recursively_get_files
from src.rewrite.equality_saturation.helper import RewriteEGG, convert_to_IR, convert_IR_to_str, ALL_RULES
from src.parsing.TimeoutDecorator import exit_after

# ---------------------------------------------------------------------------
# Debug infrastructure – activated by ``--debug`` on the Chimera CLI.
# ---------------------------------------------------------------------------
_FUZZER_DEBUG = False
_fuzzer_logger = logging.getLogger("chimera.fuzzer")


def enable_fuzzer_debug() -> None:
    """Turn on verbose debug logging for the fuzzer module."""
    global _FUZZER_DEBUG
    _FUZZER_DEBUG = True
    _fuzzer_logger.setLevel(logging.DEBUG)
    if not _fuzzer_logger.handlers:
        handler = logging.StreamHandler()
        handler.setFormatter(logging.Formatter("%(asctime)s [DEBUG] %(message)s"))
        _fuzzer_logger.addHandler(handler)


def _debug_enabled() -> bool:
    return _FUZZER_DEBUG


def _debug_log(msg: str, *args) -> None:
    if _FUZZER_DEBUG:
        _fuzzer_logger.debug(msg, *args)


def _strip_named_annotation(expr: str) -> str:
    """Strip ``(! expr :named label)`` wrapping from an SMT expression.

    Corpus building-block expressions are sometimes wrapped with
    ``:named`` annotations from the original source file.  When these
    fragments are inserted into skeleton holes the annotation becomes a
    nested annotation that many solvers reject.  This function removes
    the outermost ``(! … :named …)`` layer (if present) leaving just the
    inner expression.

    Examples
    --------
    >>> _strip_named_annotation("(! (=> a b) :named IP_1)")
    '(=> a b)'
    >>> _strip_named_annotation("(+ x 1)")
    '(+ x 1)'
    """
    stripped = expr.strip()
    if stripped.startswith("(!") and ":named" in stripped:
        # Pattern: (! <inner-expr> :named <label>)
        m = re.match(r'^\(\!\s+(.*?)\s+:named\s+\S+\s*\)$', stripped, re.DOTALL)
        if m:
            return m.group(1).strip()
    return expr


def _extract_func_name(decl: str) -> Optional[str]:
    """Return the symbol name from a ``declare-fun/declare-const`` string.

    Returns *None* if the declaration cannot be parsed.
    """
    m = re.search(
        r'\((?:declare-fun|define-fun|declare-const|define-const)\s+([^\s)]+)', decl
    )
    return m.group(1) if m else None


# Built-in SMT-LIB sorts that never need a ``declare-sort``.
_BUILTIN_SORTS = frozenset({
    "Bool", "Int", "Real", "String", "RegLan", "RoundingMode",
    # Z3/SMT 2.6 extensions
    "Seq",
    # These appear as indexed families – we also accept the *base* name.
    "BitVec", "FloatingPoint", "Float16", "Float32", "Float64", "Float128",
    "Array",
})


def _is_builtin_sort(sort_name: str) -> bool:
    """Return *True* if *sort_name* is a built-in SMT-LIB sort.

    Handles indexed sorts such as ``(_ BitVec 32)`` and ``(_ FloatingPoint 8 24)``.
    """
    name = sort_name.strip()
    if name in _BUILTIN_SORTS:
        return True
    # Indexed family: (_ BitVec 32)  →  base name is BitVec
    if name.startswith("(_"):
        parts = name.split()
        if len(parts) >= 2 and parts[1] in _BUILTIN_SORTS:
            return True
    # Parametric sorts written inline, e.g. (Array Int Int)
    if name.startswith("("):
        inner = name.lstrip("(").split()[0]
        if inner in _BUILTIN_SORTS:
            return True
    return False


def _extract_sorts_from_decl(decl: str) -> List[str]:
    """Extract all sort tokens from a ``declare-fun`` / ``declare-const`` string.

    For ``(declare-fun f (S1 S2) S3)`` returns ``['S1', 'S2', 'S3']``.
    For ``(declare-const c S)`` returns ``['S']``.
    Handles nested parametric sorts like ``(Array Int S)``.
    Returns only the *leaf* sort names (non-built-in identifiers that
    would need a ``declare-sort``).
    """
    # Tokenize by splitting on parens/spaces but keep compound sorts
    # Strategy: find all identifiers that appear in sort positions.
    # We strip the leading (declare-fun name part, then scan the remainder.
    sorts: List[str] = []

    # Remove the command keyword and symbol name
    m = re.match(
        r'\((?:declare-fun|define-fun|declare-const|define-const)\s+\S+\s*', decl
    )
    if not m:
        return sorts
    remainder = decl[m.end():]

    # Tokenize: split by whitespace and parens, keeping paren chars
    tokens = re.findall(r'[()]|[^\s()]+', remainder)

    for tok in tokens:
        if tok in ('(', ')') or tok == '_':
            continue
        # Skip numeric tokens (arity, bitvec width, etc.)
        if tok.isdigit():
            continue
        # Skip SMT keywords
        if tok in ('!', ':named', 'NUMERAL', 'par'):
            continue
        # This is a potential sort name
        if not _is_builtin_sort(tok):
            sorts.append(tok)
    return sorts


def _smt_paren_depth(text: str) -> int:
    """Return net parenthesis depth (positive = more opens than closes).

    Respects SMT-LIB string literals (delimited by ``"``).
    """
    depth = 0
    in_string = False
    prev = ''
    for ch in text:
        if ch == '"' and prev != '\\':
            in_string = not in_string
        elif not in_string:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
        prev = ch
    return depth

def generator_wrapper(generator: str) -> Optional[Tuple[Any, Any]]:
    """
    Wrapper function to call the appropriate generator.
    Now uses the flexible generator loader system.
    
    Args:
        generator: Name of the generator to use.
        
    Returns:
        A tuple of (declarations, formula) or None if generator not found or failed.
    """
    generator_func = GENERATORS.get(generator)
    if generator_func:
        return generator_func()
    else:
        print(f"Warning: No generator found for type '{generator}'")
        return None

def print_stats(stats: Dict[str, int], lock: Any) -> None:
    """
    Print statistics periodically.
    
    Args:
        stats: Managed dictionary containing statistics.
        lock: Multiprocessing lock.
    """
    start_time = time.time()
    while True:
        time.sleep(5)
        elapsed = time.time() - start_time
        with lock:
            print(f"\n[Stats] Elapsed: {elapsed:.2f}s")
            print(f"  Files Processed: {stats.get('files_processed', 0)}")
            print(f"  Mutations: {stats.get('mutations', 0)}")
            print(f"  Bugs Found: {stats.get('bugs', 0)}")
            print(f"  Invalid: {stats.get('invalid', 0)}")

def _extract_script_components(script: Any) -> Tuple[List[Any], str, str]:
    """
    Extract assertions and other commands from a parsed script.
    
    Args:
        script: The parsed script object.
        
    Returns:
        Tuple containing:
        - assertions: List of assertion objects
        - assertions_text: String representation of assertions
        - other_cmd_text: String representation of other commands (declarations, etc.)
    """
    assertions = script.assert_cmd
    assertions_text = "\n".join([assertion.__str__() for assertion in assertions])
    other_cmd_text = ""
    for cmd in script.commands:
        cmd_str = cmd.__str__()
        if (
            cmd not in assertions
            and cmd_str not in assertions_text
            and not cmd_str.startswith("(set-logic")
            and not cmd_str.startswith("(exit")
            and not cmd_str.startswith("(check-sat")
            and not cmd_str.startswith("(set-info")
            and not cmd_str.startswith("(set-option")
            and not cmd_str.startswith("(pop")
            and not cmd_str.startswith("(push")
        ):
            other_cmd_text += cmd_str + "\n"
    return assertions, assertions_text, other_cmd_text

def _perform_mutation(removed_exprs: List[Any], generator_types: List[str]) -> Tuple[List[str], bool]:
    """
    Perform mutation on the selected expressions.
    
    Args:
        removed_exprs: List of expressions to mutate.
        generator_types: List of available generator types.
        
    Returns:
        Tuple containing:
        - List of new declarations generated during mutation.
        - Boolean indicating if 'ho' generator was used.
    """
    all_new_declarations = []
    has_ho = False
    
    for expr in removed_exprs:
        generator_type = random.choice(generator_types)
        if generator_type == "ho":
            has_ho = True
            
        mutation_result = generator_wrapper(generator_type)

        if mutation_result is None:
            continue

        new_decl, new_formula = mutation_result

        if isinstance(new_formula, list):
            new_formula = "\n".join(new_formula)

        # Replace in AST
        if new_formula is not None:
            try:
                # Parse new_formula into a Term
                dummy_script_str = f"(assert {new_formula})"
                dummy_script, _ = parse_str(dummy_script_str, silent=True)
                if dummy_script and dummy_script.assert_cmd:
                    new_term = dummy_script.assert_cmd[0].term
                    
                    # Modify expr[0] in place
                    expr[0]._initialize(
                        name=new_term.name,
                        type=new_term.type,
                        is_const=new_term.is_const,
                        is_var=new_term.is_var,
                        label=new_term.label,
                        indices=new_term.indices,
                        quantifier=new_term.quantifier,
                        quantified_vars=new_term.quantified_vars,
                        var_binders=new_term.var_binders,
                        let_terms=new_term.let_terms,
                        op=new_term.op,
                        subterms=new_term.subterms,
                        is_indexed_id=new_term.is_indexed_id,
                        parent=expr[0].parent
                    )
                    expr[0]._add_parent_pointer()
            except Exception as e:
                # print(f"Failed to parse/replace: {e}")
                pass
        
        # Collect new declarations from this mutation
        if isinstance(new_decl, str):
            new_decl = new_decl.strip().split("\n")
        if isinstance(new_decl, list):
            new_declarations = [
                decl for decl in new_decl 
                if decl.strip()
            ]
            all_new_declarations.extend(new_declarations)
            
    return all_new_declarations, has_ho

def process_target_file(args):
    """Worker function that randomly selects a target file and processes all iterations for it"""
    (smt_files, generator_types, base_folder_name, worker_id,
     solver1_path, solver2_path, timeout, incremental, solver1, solver2,
     theory, add_option, temp, lock, stats) = args

    process_id = multiprocessing.current_process().pid
    process_folder = f'{base_folder_name}/process_{process_id}'

    try:
        # Create process folder if it doesn't exist (thread-safe)
        if not os.path.exists(process_folder):
            with lock:
                if not os.path.exists(process_folder):
                    os.makedirs(process_folder, exist_ok=True)

        random.shuffle(smt_files)

        # for target_file_path in smt_files:
        while smt_files:
            try:
                target_file_path = random.choice(smt_files)
                try:
                    current_script, _ = parse_file(target_file_path, silent=True)
                    expr_list = get_all_basic_subformula(current_script, rename_flag=False)
                    script_text = current_script.__str__()
                    
                    # Split assertions and other commands
                    assertions, assertions_text, other_cmd_text = _extract_script_components(current_script)

                except Exception as e:
                    # with lock:
                    #     print(f"Process {process_id}: Failed to parse initial file {target_file_path}: {e}")
                    continue  # Skip to the next file

                results = []

                with lock:
                    stats['files_processed'] += 1

                for iteration in range(MAX_ITERATIONS):
                    try:
                        if not expr_list:
                            # with lock:
                            #     print(f"Process {process_id}: No expressions to mutate in {target_file_path}, stopping iterations for this file.")
                            break

                        # --- Mutation Phase ---
                        removed_exprs = random.sample(expr_list, min(SAMPLE_SIZE, len(expr_list)))
                        # intermediate_formula = assertions_text
                        all_new_declarations, has_ho = _perform_mutation(removed_exprs, generator_types)
                        
                        # Regenerate assertions text from modified AST
                        intermediate_formula = "\n".join([assertion.__str__() for assertion in assertions])
                        
                        # Prepare original declarations (excluding duplicates)
                        original_decl_list = other_cmd_text.strip().split("\n")
                        original_decl_text = ""
                        for decl in original_decl_list:
                            if decl.strip() and decl.strip() not in intermediate_formula:
                                original_decl_text += decl.strip() + "\n"

                        # Remove duplicates from new declarations against original declarations
                        all_new_declarations = [
                            decl for decl in all_new_declarations 
                            if decl.strip() not in original_decl_text
                        ]
                        
                        # Build final formula: new_declarations + original_declarations + mutated_assertions + check-sat
                        final_formula_parts = []
                        
                        # Add HO logic if needed
                        if has_ho:
                            has_logic = any("(set-logic" in part for part in [original_decl_text, intermediate_formula] + all_new_declarations)
                            if not has_logic:
                                final_formula_parts.append("(set-logic HO_ALL)")
                        
                        if all_new_declarations:
                            final_formula_parts.append("\n".join(all_new_declarations))
                        
                        if original_decl_text.strip():
                            final_formula_parts.append(original_decl_text.strip())
                        
                        final_formula_parts.append(intermediate_formula)
                        final_formula_parts.append("(check-sat)")
                        
                        intermediate_formula = "\n".join(final_formula_parts)

                        # --- File Writing Phase ---
                        smt_file_name = f'{process_folder}/mutant_{worker_id}_{iteration + 1}.smt2'

                        # Ensure proper logic declaration placement for HO logic
                        if has_ho or "(set-logic HO_ALL)" in intermediate_formula:
                            if "(set-logic" not in intermediate_formula:
                                intermediate_formula = "(set-logic HO_ALL)\n" + intermediate_formula
                            else:
                                lines = intermediate_formula.split('\n')
                                set_logic_line = None
                                other_lines = []
                                for line in lines:
                                    if line.strip().startswith("(set-logic"):
                                        set_logic_line = "(set-logic HO_ALL)"
                                    else:
                                        other_lines.append(line)
                                if set_logic_line:
                                    intermediate_formula = set_logic_line + '\n' + '\n'.join(other_lines)

                        # Format and write the mutated formula
                        formatted_formula = format_smt_string(intermediate_formula)
                        with open(smt_file_name, 'w', encoding='utf-8') as f:
                            f.write(formatted_formula)

                        # with lock:
                        #     print(f"Process {process_id}: Generated {smt_file_name} from {target_file_path}")

                        with lock:
                            stats['mutations'] += 1

                        # --- Solver and Update Phase ---
                        solver_result = solver_runner(
                            solver1_path, solver2_path, smt_file_name, timeout,
                            incremental, solver1, solver2, theory, add_option, temp, None
                        )
                        results.append(solver_result)

                        if solver_result == "bug":
                            with lock:
                                stats['bugs'] += 1
                        elif solver_result == "invalid":
                            with lock:
                                stats['invalid'] += 1

                        # Update expression list for the next iteration
                        try:
                            current_script, _ = parse_file(smt_file_name, silent=True)
                            new_expr_list = get_all_basic_subformula(current_script, rename_flag=False)
                            if new_expr_list:
                                expr_list = new_expr_list
                                script_text = current_script.__str__()
                                # Update the assertions and other command texts for the next iteration
                                assertions, assertions_text, other_cmd_text = _extract_script_components(current_script)
                            else:
                                # If no expressions found in the new file, break the iteration loop
                                # with lock:
                                #     print(f"Process {process_id}: No expressions found in mutated file {smt_file_name}, stopping iterations for this file.")
                                break
                        except Exception as e:
                            # If parsing the new file fails, log the error and break the iteration loop
                            # with lock:
                            #     print(f"Process {process_id}: Failed to parse mutated file {smt_file_name} in iteration {iteration}: {e}")
                            #     print(f"Process {process_id}: Stopping iterations for this file to avoid incorrect replacements")
                            break

                        # --- Cleanup ---
                        if os.path.exists(smt_file_name):
                            os.remove(smt_file_name)
                            # pass

                    except Exception as e:
                        # with lock:
                        #     print(f"Process {process_id}: Error in iteration {iteration} for {target_file_path}: {e}")
                        #     print(traceback.format_exc())
                        results.append(None)

                # with lock:
                #     successful_iterations = sum(1 for r in results if r is not None)
                #     print(f"Process {process_id}: Completed {successful_iterations}/{len(results)} iterations for {target_file_path}")
            except KeyboardInterrupt:
                raise
            except Exception as e:
                continue

        return results

    except KeyboardInterrupt:
        raise
    except Exception as e:
        # with lock:
        #     print(f"Process {process_id}: A critical error occurred: {e}")
        #     print(traceback.format_exc())
        return [None] * MAX_ITERATIONS

def process_standalone_generation(args):
    """Worker function that generates formulas from scratch using generators"""
    (num_iterations, generator_types, base_folder_name, worker_id,
     solver1_path, solver2_path, timeout, incremental, solver1, solver2,
     theory, add_option, temp, lock, stats) = args

    process_id = multiprocessing.current_process().pid
    process_folder = f'{base_folder_name}/process_{process_id}'

    try:
        # Create process folder if it doesn't exist (thread-safe)
        if not os.path.exists(process_folder):
            with lock:
                if not os.path.exists(process_folder):
                    os.makedirs(process_folder, exist_ok=True)

        for i in range(num_iterations):
            try:
                # Select generator
                generator_type = random.choice(generator_types)
                mutation_result = generator_wrapper(generator_type)

                if mutation_result is None:
                    continue

                new_decl, new_formula = mutation_result

                if isinstance(new_formula, list):
                    new_formula = "\n".join(new_formula)
                
                if isinstance(new_decl, list):
                    new_decl = "\n".join(new_decl)
                elif isinstance(new_decl, str):
                    pass # it is string
                
                # Construct SMT content
                content = ""
                if new_decl:
                    content += new_decl + "\n"
                
                # Ensure proper logic declaration placement for HO logic
                if generator_type == "ho" or "(set-logic HO_ALL)" in content or "(set-logic HO_ALL)" in new_formula:
                     if "(set-logic" not in content:
                         content = "(set-logic HO_ALL)\n" + content

                content += f"(assert {new_formula})\n"
                content += "(check-sat)"
                
                # Format and write the formula
                formatted_formula = format_smt_string(content)
                smt_file_name = f'{process_folder}/gen_{worker_id}_{i}.smt2'
                
                with open(smt_file_name, 'w', encoding='utf-8') as f:
                    f.write(formatted_formula)

                with lock:
                    stats['mutations'] += 1 # Count generations as mutations for stats

                # --- Solver and Update Phase ---
                solver_result = solver_runner(
                    solver1_path, solver2_path, smt_file_name, timeout,
                    incremental, solver1, solver2, theory, add_option, temp, None
                )

                if solver_result == "bug":
                    with lock:
                        stats['bugs'] += 1
                elif solver_result == "invalid":
                    with lock:
                        stats['invalid'] += 1

                # --- Cleanup ---
                if os.path.exists(smt_file_name):
                    os.remove(smt_file_name)

            except Exception as e:
                # with lock:
                #     print(f"Process {process_id}: Error in generation {i}: {e}")
                pass

    except KeyboardInterrupt:
        raise
    except Exception as e:
        return

# -----------------------------------------------------------------------------
# History Fuzzing Logic
# -----------------------------------------------------------------------------

def analyze_logic_capabilities(logic_name):
    """
    Parse logic name to set of capabilities.
    """
    caps = set()
    name = logic_name.upper()
    
    # Quantifiers
    if name.startswith("QF_"):
        caps.add("QF")
        body = name[3:]
    else:
        # If not explicitly QF, it allows quantifiers
        caps.add("QUANTIFIERS")
        body = name

    # Sorts/Theories
    if "BV" in body: caps.add("BV")
    if "FP" in body: caps.add("FP")
    
    # Arrays often denoted by 'A' at start of body, e.g. AB, AUF, A
    # or inside e.g. QF_ABV
    # Check for 'A' not part of RA, IA, NA
    # Heuristic: 'A' that is not followed by 'I' or 'R' or 'L' might be array?
    # Better: explicit check for known array patterns or just containment of 'A' excluding 'IA', 'RA' 
    # But 'LIA' has 'IA'. 'NRA' has 'RA'.
    # A simple but not perfect check:
    # Remove known arithmetic suffixes first
    temp_body = body
    if "IRA" in temp_body: temp_body = temp_body.replace("IRA", "")
    elif "IA" in temp_body: temp_body = temp_body.replace("IA", "")
    elif "RA" in temp_body: temp_body = temp_body.replace("RA", "")
    
    # Now check for Arrays
    if "A" in temp_body:
        caps.add("ARRAYS")

    # Arithmetic Types
    if "IRA" in body:
        caps.add("INT")
        caps.add("REAL")
    elif "IA" in body:
        caps.add("INT")
    elif "RA" in body:
        caps.add("REAL")
        
    # Difference Logic
    if "IDL" in body:
        caps.add("INT")
        caps.add("DL")
    if "RDL" in body:
        caps.add("REAL")
        caps.add("DL")

    # Linearity
    # If N (nonlinear) is present
    if "N" in body and ("IA" in body or "RA" in body):
        caps.add("NONLINEAR")
    # Note: If not nonlinear, and has arithmetic, it's Linear or DL. 
    # We treat Linear as default for arithmetic unless DL is specific.

    # Uninterpreted Functions
    if "UF" in body:
        caps.add("UF")
    
    # Edge case: Empty body or just 'UF' -> QF_UF has no arithmetic
    
    return caps

def is_logic_compatible(candidate_logic, target_logic):
    """
    Returns True if candidate_logic components can be used in target_logic.
    Rule: Target must support all features required by Candidate.
    """
    if candidate_logic == target_logic:
        return True
    
    cand_caps = analyze_logic_capabilities(candidate_logic)
    targ_caps = analyze_logic_capabilities(target_logic)
    
    # 1. Quantifier Restriction
    # If Target is QF (and thus has 'QF' in caps), Candidate CANNOT have Quantifiers.
    # Candidates with 'QF' are safe for QF targets.
    # Candidates with 'QUANTIFIERS' are NOT safe for QF targets (Targets with 'QF' cap).
    if "QF" in targ_caps and "QUANTIFIERS" in cand_caps:
        return False
        
    # 2. Sort Compatibility (BV, FP, Arrays)
    for sort in ["BV", "FP", "ARRAYS"]:
        if sort in cand_caps and sort not in targ_caps:
            return False
            
    # 3. Arithmetic Sorts (Int, Real)
    # If candidate needs Int, Target must support Int
    if "INT" in cand_caps and "INT" not in targ_caps:
        # Exception: Some logics mix them, but strictly SMT-LIB separates them.
        return False
        
    if "REAL" in cand_caps and "REAL" not in targ_caps:
        return False
        
    # 4. Arithmetic Expressiveness (Linear vs NonLinear vs DiffLogic)
    # Hierarchy: DiffLogic < Linear < NonLinear
    
    # If Candidate is NonLinear, Target must be NonLinear
    if "NONLINEAR" in cand_caps and "NONLINEAR" not in targ_caps:
        return False
        
    # If Candidate is Linear (default if Int/Real and not DL/NonLinear)
    # And Target is DiffLogic -> Incompatible (Candidate is too expressive)
    cand_is_arith = ("INT" in cand_caps or "REAL" in cand_caps)
    cand_is_dl = "DL" in cand_caps
    cand_is_nl = "NONLINEAR" in cand_caps
    # Candidate is "Standard Linear" if Arith + !DL + !NL
    cand_is_linear = cand_is_arith and not cand_is_dl and not cand_is_nl
    
    targ_is_dl = "DL" in targ_caps
    
    if cand_is_linear and targ_is_dl:
        return False
        
    # 5. Uninterpreted Functions
    if "UF" in cand_caps and "UF" not in targ_caps:
        return False
        
    return True

def _merge_corpus_data(buggy_corpus: 'BuggySeed', logics: List[str]) -> Dict[str, Dict]:
    """Merge corpus entries for *logics* into a single unified corpus dict (DRY)."""
    merged: Dict[str, Dict] = {
        'formula': {},
        'formula_type': {},
        'var': {},
        'formula_sort': {},
        'formula_func': {},
    }
    for logic in logics:
        data = buggy_corpus.corpus[logic]
        for typ, exprs in data['formula'].items():
            merged['formula'].setdefault(typ, []).extend(exprs)
        merged['formula_type'].update(data['formula_type'])
        merged['var'].update(data['var'])
        merged['formula_sort'].update(data['formula_sort'])
        merged['formula_func'].update(data['formula_func'])
    return merged


def process_history_fuzz(args):
    """
    Worker function for history-based fuzzing.
    """
    (skeleton_path, solver1, solver2, solver1_path, solver2_path, timeout, 
     incremental, core, add_option_flag, rules, buggy, temp, argument) = args
    
    mutant = None 
    tactic = None

    associate_rule = None
    skeleton_obj = Skeleton(skeleton_path)
    initial_skeletons = skeleton_obj.skeleton_list
    dynamic_list = deepcopy(initial_skeletons)
    buggy_corpus = BuggySeed(buggy)
    file_count = 0
    bug_count = 0
    temp_dir = temp
    temp_core_dir = temp_dir + "/scripts/core" + str(core)
    if os.path.exists(temp_core_dir):
        shutil.rmtree(temp_core_dir)
    os.makedirs(temp_core_dir)
    start_time = time.time()
    total_count = 0
    
    available_logics = list(buggy_corpus.corpus.keys())
    user_logic = argument.get("logic") if argument else None
    
    target_corpus_data = None
    fixed_theory = None

    _debug_log("process_history_fuzz[core=%d]: %d available logics: %s",
               core, len(available_logics), available_logics[:10])

    if user_logic and user_logic in available_logics:
        fixed_theory = user_logic
        compatible_logics = [l for l in available_logics if is_logic_compatible(l, user_logic)]
        target_corpus_data = _merge_corpus_data(buggy_corpus, compatible_logics)
        # Fallback to self if no compatible formulas found
        if not target_corpus_data['formula']:
            target_corpus_data = buggy_corpus.corpus[user_logic]

    elif available_logics:
        fixed_theory = None
        target_corpus_data = _merge_corpus_data(buggy_corpus, available_logics)
    else:
        fixed_theory = random.choice(["int", "real", "string", "bv", "fp", "array"])

    sort_list = []
    type_expr, expr_type, expr_var, seed_sort, seed_func = None, None, None, None, None
    
    while True:
        try:
            if incremental == "random":
                incremental_mode = random.choice(["incremental", "non-incremental"])
            else:
                incremental_mode = incremental
            skeleton_list, dynamic_list = skeleton_obj.choose_skeleton_and_remove(dynamic_list, incremental_mode)
            
            if target_corpus_data:
                buggy_typ_expr = target_corpus_data['formula']
                buggy_expr_typ = target_corpus_data['formula_type']
                buggy_expr_var = target_corpus_data['var']
                buggy_expr_sort = target_corpus_data['formula_sort']
                buggy_expr_func = target_corpus_data['formula_func']
                
                if fixed_theory:
                    theory = fixed_theory
                elif available_logics:
                    theory = random.choice(available_logics)
                else:
                     theory = "unknown"
            else: 
                dynamic_list = deepcopy(initial_skeletons)
                continue

            new_ast, ast_var, corpus_sorts, func_list = construct_formula(skeleton_list, type_expr, expr_type, expr_var,
                                                               buggy_typ_expr, buggy_expr_typ, buggy_expr_var,
                                                               buggy_expr_sort, buggy_expr_func, associate_rule)

            if new_ast is not None:
                if isinstance(func_list, list) and isinstance(seed_func, list):
                    func_list += seed_func
                
                # Merge corpus sorts from construct_formula with any
                # previously accumulated sort_list (seed sorts, etc.)
                sorts = list(sort_list) if sort_list else []
                if corpus_sorts:
                    sorts += corpus_sorts
                funcs = func_list if func_list is not None else []
                # Filter empty entries that may have slipped through
                funcs = [f for f in funcs if f.strip()] if funcs else []
                sorts = [s for s in sorts if s.strip()] if sorts else []

                _debug_log("process_history_fuzz: constructing script with %d assertions, %d vars, %d sorts, %d funcs",
                           len(new_ast), len(ast_var) if ast_var else 0, len(sorts), len(funcs))

                new_formula = construct_scripts(new_ast, ast_var, sorts, funcs, incremental_mode, argument)

                # -- Pre-export validation: skip structurally invalid formulas --
                if not _validate_smt_formula(new_formula):
                    _debug_log("process_history_fuzz: SKIPPING invalid formula (pre-validation failed)")
                    continue

                smt_file = export_smt2(new_formula, temp_core_dir, file_count)
                if smt_file is not None:
                    bug_flag = solver_runner(solver1_path, solver2_path, smt_file, timeout, incremental_mode,
                                             solver1, solver2, theory, add_option_flag, temp, tactic)

                    # -- Debug: log when solver rejects the formula --------
                    if bug_flag == "invalid" and _debug_enabled():
                        _debug_log("process_history_fuzz: solver returned 'invalid' for %s", smt_file)
                        try:
                            with open(smt_file, "r", encoding="utf-8", errors="replace") as _f:
                                head = "".join(_f.readlines()[:20])
                            _debug_log("  first 20 lines:\n%s", head)
                        except OSError:
                            pass

                    file_count += 1
                    total_count += 1
                    if bug_flag:
                        bug_count += 1
                    if time.time() - start_time > 10:
                        start_time = time.time()
                        if bug_count == 1 or bug_count == 0:
                            print(str(total_count) + " test instances solved  |  " + str(bug_count) + " bug found")
                        else:
                            print(str(total_count) + " test instances solved  |  " + str(bug_count) + " bugs found")
                    
                if file_count > 1000:
                    shutil.rmtree(temp_core_dir)
                    os.makedirs(temp_core_dir)
                    file_count = 0
                    if mutant is not None:
                        return

            if dynamic_list is None:
                sort_list = []
                type_expr, expr_type, expr_var, seed_sort, seed_func = None, None, None, None, None
                dynamic_list = deepcopy(initial_skeletons)
        except (KeyboardInterrupt, SystemExit):
            print("bye!")
            break
        except Exception:
            traceback.print_exc()
            try:
                with open("exception.txt", "a", encoding="utf-8") as e:
                    e.write(traceback.format_exc())
            except OSError:
                pass
            time.sleep(1)
            dynamic_list = deepcopy(initial_skeletons)


def construct_formula(skeleton, seed_type_expr, seed_expr_type, seed_var, bug_type_formula, bug_formula_typ,
                      bug_formula_var, bug_formula_sort, bug_formula_func, bug_association):
    sort_list = list()
    func_list = list()
    ast_lists = list()
    var_lists = list()
    abstract_set = set()
    if seed_type_expr is None:
        seed_type_expr = dict()
        seed_expr_type = dict()
    if seed_var is None:
        seed_var = dict()
    if skeleton is not None:
        for ske_idx, ske in enumerate(skeleton):
            local_var = list()
            blanks = obtain_hole(ske)
            local_domain = obtain_local_domain(ske)
            hole_replacer_dic = dict()
            assertion = str(ske)
            _debug_log("construct_formula: skeleton[%d] has %d holes, initial: %.120s…",
                       ske_idx, len(blanks), assertion)
            while len(blanks) > 0:
                blank = random.choice(blanks)
                replacer_type = random.choice(["seed", "seed", "seed", "buggy"])
                if replacer_type == "seed" and len(list(seed_var.keys())) > 0:
                    replacer = random.choice(list(seed_var.keys()))
                    replacer = _strip_named_annotation(replacer)
                    single_hole_var = seed_var.get(replacer, seed_var.get(
                        random.choice(list(seed_var.keys())), []))
                    if seed_expr_type.get(replacer) and bug_association and seed_expr_type[replacer] in bug_association.rule_set:
                        abstract_set.add(seed_expr_type[replacer])
                else:
                    if len(list(bug_formula_var.keys())) > 0:
                        orig_replacer = random.choice(list(bug_formula_var.keys()))
                        replacer = _strip_named_annotation(orig_replacer)
                        single_hole_var = bug_formula_var[orig_replacer]
                        # Filter empty sort/func entries from corpus
                        sort_list += [s for s in bug_formula_sort.get(orig_replacer, []) if s.strip()]
                        func_list += [f for f in bug_formula_func.get(orig_replacer, []) if f.strip()]
                        if bug_association and bug_formula_typ.get(orig_replacer) and bug_formula_typ[orig_replacer] in bug_association.rule_set:
                            abstract_set.add(bug_formula_typ[orig_replacer])
                    else:
                        single_hole_var = []
                        replacer = "true"
                
                assertion = assertion.replace(str(blank), replacer)
                hole_replacer_dic[str(blank)] = single_hole_var
                local_var += single_hole_var
                if blank in blanks:
                    blanks.remove(blank)

            if local_domain:
                for local in local_domain.keys():
                    single_local_var = local.split(" ")
                    candidate_var = []
                    for hole in local_domain[local]:
                         if hole in hole_replacer_dic:
                            candidate_var += hole_replacer_dic[hole]
                    for var in single_local_var:
                        if var != "":
                            replacee = var + " " + var.replace("VAR", "TYPE")
                            if len(candidate_var) > 0:
                                replace_local_var = random.choice(candidate_var).split(", ")
                                if random.choice([True, False]):
                                    replace_format = replace_local_var[0].upper() + " " + replace_local_var[1]
                                else:
                                    replace_format = replace_local_var[0] + " " + replace_local_var[1]
                                assertion = assertion.replace(replacee, replace_format)
                            else:
                                assertion = assertion.replace(replacee, var + " " + "Bool")
            var_lists += local_var
            var_lists = list(set(var_lists))
            # Validate that the filled assertion is paren-balanced
            depth = _smt_paren_depth(assertion)
            if depth != 0:
                _debug_log("construct_formula: UNBALANCED assertion after hole-fill (depth=%d): %.120s…",
                           depth, assertion)
                # Attempt to fix minor imbalances (missing closing parens)
                if depth > 0:
                    assertion = assertion + (")" * depth)
                    _debug_log("construct_formula: auto-appended %d closing parens", depth)
            ast_lists.append(assertion)
        # Filter empty/whitespace entries from sort and func lists
        clean_sorts = list({s.strip() for s in sort_list if s.strip()})
        clean_funcs = list({f.strip() for f in func_list if f.strip()})
        return ast_lists, var_lists, clean_sorts, clean_funcs
    else:
        return None, None, None, None


def variable_translocation(ast, ast_var: dict):
    """Randomly swap variables of the same type within assertion strings.

    Uses word-boundary-aware replacement to avoid corrupting identifiers
    that share a common prefix (e.g. ``var1`` vs ``var12``).
    """
    if ast_var:
        replace_time = random.randint(1, 10)
        while replace_time > 0:
            if not list(ast_var.keys()):
                break
            replace_type = random.choice(list(ast_var.keys()))
            if not ast: break
            replace_ast_index = random.randint(0, len(ast) - 1)
            if ast_var.get(replace_type):
                for var in ast_var[replace_type]:
                    # Use regex for word-boundary-aware replacement to
                    # prevent partial matches (e.g. var1 inside var12).
                    pattern = re.compile(
                        r'(?<=[\s(])' + re.escape(var) + r'(?=[\s)])'
                    )
                    match = pattern.search(ast[replace_ast_index])
                    if match:
                        replacement = random.choice(ast_var[replace_type])
                        ast[replace_ast_index] = pattern.sub(
                            replacement, ast[replace_ast_index], count=1
                        )
                        replace_time -= 1
                        break
    return ast


def _build_type_var(var_list) -> Dict[str, list]:
    """Build a ``{type: [name, ...]}`` dict from corpus variable entries."""
    type_var: Dict[str, list] = {}
    if var_list:
        for v in var_list:
            if ", " in v:
                name = v.split(", ")[0].strip()
                typ = v.split(", ")[1].strip()
                if name and typ:
                    type_var.setdefault(typ, []).append(name)
    return type_var


def construct_scripts(ast, var_list, sort, func, incremental, argument):
    """Assemble the final SMT-LIB script from assertions, vars, sorts, funcs.

    Key validity improvements:
    * Sort declarations are collected first.
    * Func/Var declarations with unresolved sorts are dropped.
    * Assertions using dropped symbols are removed to prevent "unknown constant".
    * Sorts provided by user/corpus are only emitted if used.
    """
    seen_names: set = set()        # track declared symbol *names*
    seen_decl_strs: set = set()    # track exact declaration strings

    # ------------------------------------------------------------------
    # 1. Collect ALL candidate sort declarations and build a set of
    #    available sort names.
    # ------------------------------------------------------------------
    available_sorts: set = set()    # sort names that will be declared
    sort_decl_map: Dict[str, str] = {}  # sort_name -> declaration string

    if sort:
        for s in sort:
            s = s.replace("\n", "").strip()
            if not s:
                continue
            sname_m = re.search(r'\((?:declare-sort|define-sort)\s+([^\s)]+)', s)
            key = sname_m.group(1) if sname_m else None
            if key and key not in sort_decl_map:
                sort_decl_map[key] = s
                available_sorts.add(key)

    # ------------------------------------------------------------------
    # 2. Pre-filter Variable Declarations based on Sort Availability
    # ------------------------------------------------------------------
    clean_var_list = []
    dropped_symbols = set() # Vars or Funcs we can't declare

    if var_list:
        for v in var_list:
            if ", " not in v:
                continue
            name = v.split(", ")[0].strip()
            typ = v.split(", ")[1].strip()
            if not name or not typ:
                continue
            
            # Check sorts
            var_sorts = _extract_sorts_from_decl(f"(declare-fun {name} () {typ})")
            unresolved = [vs for vs in var_sorts
                          if vs not in available_sorts and not _is_builtin_sort(vs)]
            
            if unresolved:
                _debug_log("construct_scripts: DROPPING var %s (%s) – unresolved sorts: %s",
                           name, typ, unresolved)
                dropped_symbols.add(name)
            else:
                clean_var_list.append(v)

    # ------------------------------------------------------------------
    # 3. Pre-filter Function Declarations based on Sort Availability
    #    (We don't check body usage yet, just sorts)
    # ------------------------------------------------------------------
    potential_func_decls = []
    
    if func:
        for f in func:
            f = f.replace(";", "").strip()
            if not f: 
                continue
            fname = _extract_func_name(f)
            if fname is None:
                continue
            
            required_sorts = _extract_sorts_from_decl(f)
            unresolved = [rs for rs in required_sorts
                          if rs not in available_sorts and not _is_builtin_sort(rs)]
            
            if unresolved:
                _debug_log("construct_scripts: DROPPING func %s – unresolved sorts: %s",
                           fname, unresolved)
                dropped_symbols.add(fname)
            else:
                potential_func_decls.append(f)

    # ------------------------------------------------------------------
    # 4. Prepare AST: Strip :named, Filter dropped symbols, Translocate
    # ------------------------------------------------------------------
    ast = [_strip_named_annotation(a) for a in ast]

    # Filter assertions that use dropped symbols
    if dropped_symbols:
        clean_ast = []
        for assertion in ast:
            # Simple tokenization: match SMT symbols
            tokens = set(re.findall(r'[a-zA-Z0-9_.~!@$%^&*+=<>.?/-]+', assertion))
            if not tokens.isdisjoint(dropped_symbols):
                inter = tokens.intersection(dropped_symbols)
                _debug_log("construct_scripts: REMOVING assertion using dropped symbol(s): %s", inter)
                continue
            clean_ast.append(assertion)
        ast = clean_ast

    # Allow variable swapping (only using valid variables)
    ast = variable_translocation(ast, _build_type_var(clean_var_list))

    if incremental == "incremental":
        ast = insert_push_and_pop(ast)
    else:
        ast.append("(check-sat)")

    body_text = "\n".join(ast)

    # ------------------------------------------------------------------
    # 5. Emit Function Declarations (only if used in body)
    # ------------------------------------------------------------------
    func_decls: list = []
    func_needed_sorts: set = set()

    for f in potential_func_decls:
        if f in seen_decl_strs:
            continue
        fname = _extract_func_name(f)
        if fname in seen_names:
            continue
        
        # Only emit if referenced
        if fname not in body_text:
            continue
            
        func_decls.append(f)
        seen_names.add(fname)
        seen_decl_strs.add(f)
        func_needed_sorts.update(_extract_sorts_from_decl(f))

    # ------------------------------------------------------------------
    # 6. Emit Variable Declarations
    # ------------------------------------------------------------------
    var_decls: list = []
    
    # helper for variable types mapping
    for v in clean_var_list:
        name = v.split(", ")[0].strip()
        typ = v.split(", ")[1].strip()
        
        decl = str(DeclareFun(name, '', typ))
        if name not in seen_names:
            var_decls.append(decl)
            seen_names.add(name)
            seen_decl_strs.add(decl)

    # ------------------------------------------------------------------
    # 7. Emit Sort Declarations (only needed ones)
    # ------------------------------------------------------------------
    sort_decls: list = []
    var_needed_sorts: set = set()
    for vd in var_decls:
        var_needed_sorts.update(
            s for s in _extract_sorts_from_decl(vd) if not _is_builtin_sort(s)
        )

    all_needed_sorts = func_needed_sorts | var_needed_sorts
    for sname, sdecl in sort_decl_map.items():
        if sname in all_needed_sorts and sname not in seen_names:
            sort_decls.append(sdecl)
            seen_names.add(sname)
            seen_decl_strs.add(sdecl)

    # ------------------------------------------------------------------
    # 8. Assemble
    # ------------------------------------------------------------------
    formula = sort_decls + func_decls + var_decls + ast

    # Filter out empty lines
    formula = [line for line in formula if line.strip()]

    s = "(set-logic ALL)\n"
    for content in formula:
        s = s + content + "\n"

    # -- Debug --
    if _debug_enabled():
        depth = _smt_paren_depth(s)
        if depth != 0:
            _debug_log("construct_scripts: UNBALANCED output (depth=%d)", depth)
        else:
            _debug_log("construct_scripts: OK (%d sorts, %d funcs, %d vars)",
                       len(sort_decls), len(func_decls), len(var_decls))

    return s


def insert_push_and_pop(ast_list):
    """Wrap assertion strings in push/pop pairs for incremental mode.

    Ensures that pop counts never exceed the current stack depth and that
    every push is matched by a pop by the end.
    """
    ast_stack = 0
    new_ast = []
    left_count = len(ast_list)
    while left_count > 0:
        if left_count > 2:
            push_count = random.randint(1, 3)
        else:
            push_count = left_count
        left_count -= push_count
        new_ast.append("(push " + str(push_count) + ")")
        ast_stack += push_count
        for i in range(push_count):
            if ast_list:
                new_ast.append(ast_list.pop())
            else:
                break
        new_ast.append("(check-sat)")
        if ast_stack > 0:
            pop_count = random.randint(1, ast_stack)
            ast_stack -= pop_count
            new_ast.append("(pop " + str(pop_count) + ")")
    # Ensure final stack is balanced
    if ast_stack > 0:
        new_ast.append("(pop " + str(ast_stack) + ")")
    return new_ast


def collect_sort(file):
    sort_list = []
    with open(file, "r", encoding="utf-8", errors="replace") as smt_file:
        for line in smt_file:
            if "declare-sort" in line or "define-sort" in line:
                sort_list.append(line)
    return sort_list


def _validate_smt_formula(script: str) -> bool:
    """Lightweight pre-export validation of an SMT-LIB formula.

    Checks:
    1. Parenthesis balance (respecting string literals).
    2. Presence of ``(check-sat)`` (or ``(push`` for incremental).
    3. No stray ``(! … :named …)`` annotations at the assertion level
       (these often indicate an un-stripped corpus fragment).
    4. Every ``(assert ...)`` is properly closed.

    Returns *True* when the formula looks structurally valid, *False*
    otherwise.  This is intentionally a *lightweight* check – it won't
    catch all semantic problems, but it's fast enough to run on every
    generated formula.
    """
    # 1. Paren balance
    if _smt_paren_depth(script) != 0:
        _debug_log("_validate_smt_formula: FAIL – unbalanced parentheses")
        return False

    # 2. Must have check-sat or be incremental (push)
    if "(check-sat)" not in script and "(push" not in script:
        _debug_log("_validate_smt_formula: FAIL – no (check-sat) or (push")
        return False

    # 3. Check each line for common issues
    for line in script.split("\n"):
        stripped = line.strip()
        # Bare :named at assertion level is suspicious
        if stripped.startswith("(assert") and ":named" in stripped:
            # Check if :named is directly inside assert (not inside a deeper subexpr)
            # Quick heuristic: count parens before :named — if depth is 2 it's
            # (assert (! expr :named …)) which is legal; depth 1 would be broken.
            idx = stripped.find(":named")
            prefix = stripped[:idx]
            d = prefix.count("(") - prefix.count(")")
            if d < 2:
                _debug_log("_validate_smt_formula: FAIL – :named at wrong depth in: %.100s", stripped)
                return False

    return True


def export_smt2(script, direct, index):
    os.makedirs(direct, exist_ok=True)
    file_path = os.path.join(direct, f"case{index}.smt2")

    # -- Debug: validate the formula before writing --------------------------
    if _debug_enabled():
        depth = _smt_paren_depth(script)
        if depth != 0:
            _debug_log("export_smt2: UNBALANCED formula written to %s (depth=%d)",
                       file_path, depth)
        if "(check-sat)" not in script:
            _debug_log("export_smt2: WARNING no (check-sat) in %s", file_path)

    with open(file_path, "w", encoding="utf-8") as f:
        f.write(script)
    return file_path

# -----------------------------------------------------------------------------
# Rewrite Fuzzing Logic
# -----------------------------------------------------------------------------

def process_rewrite_fuzz(args):
    """
    Worker function for rewrite-based fuzzing.
    """
    (seeds, solver, solver_bin, temp_dir, modulo, max_iter, core, bug_type, mimetic) = args
    
    @exit_after(300)
    def fuzz_each_file(seed_file, solver, solver_bin, temp_dir, modulo=2, max_iter=10, core=0, bug_type="common"):
        """
        Fuzz a seed file.
        """
        script_dir = "{}/script/core{}/{}/".format(temp_dir, str(core), seed_file.split('/')[-1].replace('.smt2', ''))
        os.makedirs(script_dir, exist_ok=True)
        initial_seed_filename = seed_file.split("/")[-1]
        
        logic = None 
        if logic is None:
            logic = "(set-logic ALL)"
        orig_file_path = seed_file

        if mimetic >= 0:
            original_smt2 = os.path.join(script_dir, "original.smt2")

            if not os.path.exists(original_smt2):
                shutil.copy(seed_file, original_smt2)
            
            for mimetic_iter in range(mimetic):
                mutation_flag = mimetic_mutation(seed_file, original_smt2)
                if not mutation_flag:
                    seed_file = original_smt2
                    orig_file_path = seed_file
                else:
                    pass

        temp_output = script_dir + "/temp.txt"
        orig_output, _, orig_time, command = run_solver(solver_bin, solver, seed_file, 10, "incremental", temp_output, temp_dir, "None", default=True)

        if orig_output == "timeout":
            pass
        
        new_script = []
        
        for iter in range(max_iter):
            rewrite_type = "egg"
            
            max_retries = 10
            retry_count = 0
            mutated_formula = None
            applied_rules = ""
            
            while retry_count < max_retries:
                mutated_formula = None
                if rewrite_type == "egg":
                    TargetScript, TargetGlobal = parse_file(seed_file)
                    if TargetScript is None:
                        return
                    current_ast = TargetScript.assert_cmd
                    
                    if hasattr(TargetScript, 'op_occs') and TargetScript.op_occs:
                        num_replace = 3 if len(TargetScript.op_occs) > 3 else len(TargetScript.op_occs)
                        replacee_terms = random.sample(TargetScript.op_occs, num_replace)
                        replace_pairs = []
                        attempts = 0
                        max_attempts = len(TargetScript.op_occs) * 2

                        while len(replace_pairs) < 3 and attempts < max_attempts:
                            if not replacee_terms:
                                break
                            
                            term = replacee_terms.pop(0)
                            attempts += 1
                            
                            term_ir = convert_to_IR(term)
                            term_str = str(term)
                            
                            transformed_irs = RewriteEGG(term_ir, ALL_RULES, [], 1)
                            if transformed_irs is None or len(transformed_irs) == 0:
                                continue
                            
                            transformed_ir = transformed_irs[0]
                            new_term_str = convert_IR_to_str(transformed_ir)
                            
                            if new_term_str is None or new_term_str == term_str:
                                continue
                            
                            if "None" in str(new_term_str) or new_term_str.strip() == "":
                                continue
                            
                            replace_pairs.append((term_str, new_term_str))

                        if replace_pairs:
                            current_ast_str = "\\n".join([str(cmd) for cmd in current_ast])
                            for old, new in replace_pairs:
                                current_ast_str = current_ast_str.replace(old, new, 1)

                            mutated_formula = "\\n".join(new_script) + "\\n" + current_ast_str + "\\n(check-sat)"

                            if "None" in mutated_formula:
                                retry_count += 1
                                continue
                            
                        else:
                            retry_count += 1
                            continue
                    else:
                        break 
                
                if mutated_formula is None:
                    retry_count += 1
                    continue

                mutant_path = script_dir + "/{}_mutant_{}.smt2".format(initial_seed_filename, str(iter))
                with open(mutant_path, "w", encoding="utf-8") as f:
                    f.write(mutated_formula)
                
                try:
                    parse_cmd = [solver_bin, mutant_path, "--parse-only", "-q"] if "cvc5" in solver_bin else ["cvc5", mutant_path, "--parse-only"]
                    
                    try:
                        process = subprocess.run(parse_cmd, capture_output=True, text=True, timeout=10)
                        if "(error \"Parse Error:" in process.stderr or "(error \"Parse Error:" in process.stdout:
                            retry_count += 1
                            continue
                        else:
                            break
                    except FileNotFoundError:
                        break 
                except Exception:
                    break

            if mutated_formula is None:
                continue
            
            mutant_path = script_dir + "/{}_mutant_{}.smt2".format(initial_seed_filename, str(iter))

            default = True if bug_type == "all" else False
            
            mutant_output, _, mutant_time, command = run_solver(solver_bin, solver, mutant_path, 10, "incremental", temp_output, temp_dir, "None", default=default, rules=applied_rules)
            
            if bug_type == "all":
                pass 

            if mutant_output not in [orig_output, "crash", "parseerror", "timeout", "error"]:
                 if isinstance(orig_output, list) and isinstance(mutant_output, list):
                     pass
            
            seed_file = mutant_path
            orig_file_path = mutant_path

    # Main loop for process_rewrite_fuzz
    os.makedirs(temp_dir, exist_ok=True)
    os.makedirs(f"{temp_dir}/script", exist_ok=True)
    
    script_core_dir = f"{temp_dir}/script/core{core}"
    if os.path.exists(script_core_dir):
        shutil.rmtree(script_core_dir)
    os.makedirs(script_core_dir)
    
    try:
        for seed in seeds:
            try:
                fuzz_each_file(seed, solver, solver_bin, temp_dir, modulo, max_iter, core, bug_type)
            except AssertionError:
                continue
            except KeyboardInterrupt:
                break
            except Exception as e:
                with open(f"{temp_dir}/exception_core_{core}.txt", "w", encoding="utf-8") as f:
                    f.write(str(e))
                    f.write(traceback.format_exc())
                continue
    except KeyboardInterrupt:
        pass


