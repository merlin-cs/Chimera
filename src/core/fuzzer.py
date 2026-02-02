import os
import random
import multiprocessing
import traceback
import time
import shutil
import subprocess
import sys
import signal
from copy import deepcopy

from src.config.generator_loader import GENERATORS
from src.parsing.Parse import parse_file, parse_str
from src.formula_utils import get_all_basic_subformula
from src.utils.smt_handlers import format_smt_string
from src.run_solver import solver_runner, run_solver, record_bug
from src.constants import SAMPLE_SIZE, MAX_ITERATIONS, DEFAULT_STANDALONE_ITERATIONS

# Imports for History Fuzzing
from src.history.skeleton import Skeleton, obtain_hole, obtain_local_domain
from src.history.building_blocks import BuggySeed, rename_variable_in_a_file, rule
from src.parsing.Ast import DeclareFun, CheckSat, Assert

# Imports for Rewrite Fuzzing
from src.rewrite.mutate import Mutate, mimetic_mutation
from src.utils.file_handlers import get_all_smt_files_recursively as recursively_get_files
from src.rewrite.equality_saturation.helper import RewriteEGG, convert_to_IR, convert_IR_to_str, ALL_RULES
from src.parsing.TimeoutDecorator import exit_after

def generator_wrapper(generator):
    """
    Wrapper function to call the appropriate generator.
    Now uses the flexible generator loader system.
    """
    generator_func = GENERATORS.get(generator)
    if generator_func:
        return generator_func()
    else:
        print(f"Warning: No generator found for type '{generator}'")
        return None

def print_stats(stats, lock):
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
                    assertions = current_script.assert_cmd
                    assertions_text = "\n".join([assertion.__str__() for assertion in assertions])
                    other_cmd_text = ""
                    for cmd in current_script.commands:
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
                        all_new_declarations = []

                        for expr in removed_exprs:
                            generator_type = random.choice(generator_types)
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
                        if generator_type == "ho" or "(set-logic HO_ALL)" in intermediate_formula:
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
                        with open(smt_file_name, 'w') as f:
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
                                assertions = current_script.assert_cmd
                                assertions_text = "\n".join([assertion.__str__() for assertion in assertions])
                                other_cmd_text = ""
                                for cmd in current_script.commands:
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
                
                with open(smt_file_name, 'w') as f:
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
    theory = random.choice(["int", "real", "string", "bv", "fp", "array"])
    sort_list = []
    type_expr, expr_type, expr_var, seed_sort, seed_func = None, None, None, None, None
    
    while True:
        try:
            if incremental == "random":
                incremental_mode = random.choice(["incremental", "non-incremental"])
            else:
                incremental_mode = incremental
            skeleton_list, dynamic_list = skeleton_obj.choose_skeleton_and_remove(dynamic_list, incremental_mode)
            
            if theory == "real":
                buggy_typ_expr = buggy_corpus.real_formula
                buggy_expr_typ = buggy_corpus.real_formula_type
                buggy_expr_var = buggy_corpus.real_var
                buggy_expr_sort = buggy_corpus.real_formula_sort
                buggy_expr_func = buggy_corpus.real_formula_func
            elif theory == "int":
                buggy_typ_expr = buggy_corpus.int_formula
                buggy_expr_typ = buggy_corpus.int_formula_type
                buggy_expr_var = buggy_corpus.int_var
                buggy_expr_sort = buggy_corpus.int_formula_sort
                buggy_expr_func = buggy_corpus.int_formula_func
            elif theory == "string":
                buggy_typ_expr = buggy_corpus.string_formula
                buggy_expr_typ = buggy_corpus.string_formula_type
                buggy_expr_var = buggy_corpus.string_var
                buggy_expr_sort = buggy_corpus.string_formula_sort
                buggy_expr_func = buggy_corpus.string_formula_func
            elif theory == "bv":
                buggy_typ_expr = buggy_corpus.bv_formula
                buggy_expr_typ = buggy_corpus.bv_formula_type
                buggy_expr_var = buggy_corpus.bv_var
                buggy_expr_sort = buggy_corpus.bv_formula_sort
                buggy_expr_func = buggy_corpus.bv_formula_func
            elif theory == "fp":
                buggy_typ_expr = buggy_corpus.fp_formula
                buggy_expr_typ = buggy_corpus.fp_formula_type
                buggy_expr_var = buggy_corpus.fp_var
                buggy_expr_sort = buggy_corpus.fp_formula_sort
                buggy_expr_func = buggy_corpus.fp_formula_func
            elif theory == "array":
                buggy_typ_expr = buggy_corpus.array_formula
                buggy_expr_typ = buggy_corpus.array_formula_type
                buggy_expr_var = buggy_corpus.array_var
                buggy_expr_sort = buggy_corpus.array_formula_sort
                buggy_expr_func = buggy_corpus.array_formula_func
            else: 
                dynamic_list = deepcopy(initial_skeletons)
                theory = random.choice(["int", "real", "string", "bv", "fp", "array"])
                continue

            new_ast, ast_var, _, func_list = construct_formula(skeleton_list, type_expr, expr_type, expr_var,
                                                               buggy_typ_expr, buggy_expr_typ, buggy_expr_var,
                                                               buggy_expr_sort, buggy_expr_func, associate_rule)

            if new_ast is not None:
                if isinstance(func_list, list) and isinstance(seed_func, list):
                    func_list += seed_func
                
                sorts = sort_list if sort_list is not None else []
                funcs = func_list if func_list is not None else []

                new_formula = construct_scripts(new_ast, ast_var, sorts, funcs, incremental_mode, argument)
                smt_file = export_smt2(new_formula, temp_core_dir, file_count)
                if smt_file is not None:
                    bug_flag = solver_runner(solver1_path, solver2_path, smt_file, timeout, incremental_mode,
                                             solver1, solver2, theory, add_option_flag, temp, tactic)
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
                theory = random.choice(["int", "real", "string", "bv", "fp", "array"])
                sort_list = []
                type_expr, expr_type, expr_var, seed_sort, seed_func = None, None, None, None, None
                dynamic_list = deepcopy(initial_skeletons)
        except (KeyboardInterrupt, SystemExit):
            print("bye!")
            break
        except Exception:
            traceback.print_exc()
            try:
                with open("exception.txt", "a") as e:
                    e.write(traceback.format_exc())
            except:
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
        for ske in skeleton:
            local_var = list()
            blanks = obtain_hole(ske)
            local_domain = obtain_local_domain(ske)
            hole_replacer_dic = dict()
            assertion = str(ske)
            while len(blanks) > 0:
                blank = random.choice(blanks)
                candidate = None
                if candidate is not None:
                    pass
                else:
                    replacer_type = random.choice(["seed", "seed", "seed", "buggy"])
                    if replacer_type == "seed" and len(list(seed_var.keys())) > 0:
                        replacer = random.choice(list(seed_var.keys()))
                        single_hole_var = seed_var[replacer]
                        if seed_expr_type.get(replacer) and bug_association and seed_expr_type[replacer] in bug_association.rule_set:
                            abstract_set.add(seed_expr_type[replacer])
                    else:
                        if len(list(bug_formula_var.keys())) > 0:
                            replacer = random.choice(list(bug_formula_var.keys()))
                            single_hole_var = bug_formula_var[replacer]
                            sort_list += bug_formula_sort.get(replacer, [])
                            func_list += bug_formula_func.get(replacer, [])
                            if bug_association and bug_formula_typ.get(replacer) and bug_formula_typ[replacer] in bug_association.rule_set:
                                abstract_set.add(bug_formula_typ[replacer])
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
            ast_lists.append(assertion)
        return ast_lists, var_lists, list(set(sort_list)), list(set(func_list))
    else:
        return None, None, None, None


def variable_translocation(ast, ast_var: dict):
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
                    if " " + var + " " in ast[replace_ast_index] or " " + var + ")" in ast[replace_ast_index]:
                        if " " + var + " " in ast[replace_ast_index]:
                            ast[replace_ast_index] = ast[replace_ast_index].replace(" " + var + " ", " " + random.choice(
                                ast_var[replace_type]) + " ", 1)
                            replace_time -= 1
                        if " " + var + ")" in ast[replace_ast_index]:
                            ast[replace_ast_index] = ast[replace_ast_index].replace(" " + var + ")", " " + random.choice(
                                ast_var[replace_type]) + ")", 1)
                            replace_time -= 1
                        break
    return ast


def construct_scripts(ast, var_list, sort, func, incremental, argument):
    formula = list()
    type_var = {}

    if sort:
        for i, s in enumerate(sort):
            sort[i] = s.replace("\n", "")
        formula += list(set(sort))
    
    if func:
        for i, f in enumerate(func):
            func[i] = f.replace(";", "")
        formula += list(set(func))

    if var_list and len(var_list) > 0:
        for v in var_list:
            if ", " in v:
                name = v.split(", ")[0]
                typ = v.split(", ")[1]
                type_var.setdefault(typ, []).append(name)
                formula.append(str(DeclareFun(name, '', typ)))

    ast = variable_translocation(ast, type_var)

    if incremental == "incremental":
        ast = insert_push_and_pop(ast)
    else:
        ast.append("(check-sat)")

    formula = formula + ast

    s = "(set-logic ALL)\n"
    for content in formula:
        s = s + content + "\n"

    return s


def insert_push_and_pop(ast_list):
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
            new_ast.append(ast_list.pop())
        new_ast.append("(check-sat)")
        pop_count = random.randint(1, ast_stack)
        ast_stack -= pop_count
        new_ast.append("(pop " + str(pop_count) + ")")
    return new_ast


def collect_sort(file):
    sort_list = []
    with open(file, "r") as smt_file:
        content = smt_file.readlines()
        for line in content:
            if "declare-sort" in line or "define-sort" in line:
                sort_list.append(line)
    return sort_list

def export_smt2(script, direct, index):
    if not os.path.exists(direct):
        os.mkdir(direct)
    file_path = direct + "/case" + str(index) + ".smt2"
    with open(file_path, "w") as f:
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
        if not os.path.exists(script_dir):
            os.makedirs(script_dir)
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
                with open(mutant_path, "w") as f:
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
    if not os.path.exists(temp_dir):
        os.makedirs(temp_dir)
    if not os.path.exists("{}/script".format(temp_dir)):
        os.mkdir("{}/script".format(temp_dir))
    
    script_core_dir = "{}/script/core{}".format(temp_dir, str(core))
    if os.path.exists(script_core_dir):
        shutil.rmtree(script_core_dir)
    os.mkdir(script_core_dir)
    
    try:
        for seed in seeds:
            try:
                fuzz_each_file(seed, solver, solver_bin, temp_dir, modulo, max_iter, core, bug_type)
            except AssertionError:
                continue
            except KeyboardInterrupt:
                break
            except Exception as e:
                with open(f"{temp_dir}/exception_core_{core}.txt", "w") as f:
                    f.write(str(e))
                    f.write(traceback.format_exc())
                continue
    except KeyboardInterrupt:
        pass


