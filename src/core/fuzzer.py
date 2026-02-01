import os
import random
import multiprocessing
import traceback
import time as time_module
from src.config.generator_loader import GENERATORS
from src.parsing.Parse import parse_file, parse_str
from src.formula_utils import get_all_basic_subformula
from src.utils.smt_handlers import format_smt_string
from src.run_solver import solver_runner
from src.constants import SAMPLE_SIZE, MAX_ITERATIONS, DEFAULT_STANDALONE_ITERATIONS


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
    start_time = time_module.time()
    while True:
        time_module.sleep(5)
        elapsed = time_module.time() - start_time
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


