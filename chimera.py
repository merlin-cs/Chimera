
import random

import os
import datetime
import signal
import sys
import argparse
import shutil
import traceback
from pathlib import Path
import subprocess
import multiprocessing
from multiprocessing import Pool, Manager, Lock
import time as time_module


path = Path(__file__)
rootpath = str(path.parent.absolute())
sys.path.append(rootpath)

current_dir = os.getcwd()


from src.formula_utils import get_all_basic_subformula
from src.parsing.Parse import parse_file
from src.parsing.TimeoutDecorator import exit_after
from src.run_solver import solver_runner
from src.argument_parser.parser import MainArgumentParser

# Use the new flexible generator loader system
from config.generator_loader import GENERATORS, get_generator_function
from config.generator_config import get_generator_version

# Print which generator version is being used
print(f"Using {get_generator_version()} generators")


GENERAL_THEORYS = [
    # "datatype",
    "fp",
    "int",
    "real",
    "core",
    "strings",
    "bv",
    "array",
    "reals_ints",
]

Z3_THEORYS = [
    "z3_seq",
]

CVC5_THEORYS = [
    "bag",
    "datatype",
    "ff",
    "seq",
    "set",
    "ho",
    "trans",  # transcendentals (newly added)
    "sep",    # separation logic (newly added)
]

BITWUZLA_THEORYS = ["core", "fp", "bv", "array"]

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
    


# Constants
ALARM_TIME = 60
MAX_ITERATIONS = 10
SAMPLE_SIZE = 3
OPTIMIZATION_THRESHOLD = 3
STOP_THRESHOLD = 5
MAX_INDEX = 1000
DEFAULT_TIMEOUT = 10
DEFAULT_INCREMENTAL = "incremental"
DEFAULT_THEORY = "all"
DEFAULT_ADD_OPTION = "default"
TEMP_DIRECTORY = "./temp/"
CORRECTION_THRESHOLD = 0
CHECKER_PATH = "/home/cvc5-Linux"

class TimeoutException(Exception): 
    pass 

# Define the handler function
def handler(signum, frame): 
    raise TimeoutException()

# Register the handler function
signal.signal(signal.SIGALRM, handler)

def get_all_smt_files_recursively(path_to_directory):
    file_paths = list()
    for r, d, f in os.walk(path_to_directory):
        for file in f:
            if ".smt20" in file:
                continue
            if ".smt2" in file:
                file_paths.append(os.path.join(r, file))

    return file_paths



def formula_mutation(smt_file):
    with open(smt_file, "r") as f:
        text = f.read()
    try:
        script, glob = parse_file(smt_file, silent=True)
        expr_list = get_all_basic_subformula(script, rename_flag=True)
        if len(expr_list) == 0:
            return text, text
        else:
            original_text = text
            placeholder = random.sample(expr_list, random.randint(1, len(expr_list)))
            new_text = text
            assert_text = ""
            for assert_cmd in script.assert_cmd:
                assert_text += assert_cmd.__str__() + "\n"
            new_assert_text = assert_text
            for ph in placeholder:
                if " " + ph[0].__str__() + " " in new_assert_text:
                    new_assert_text = new_assert_text.replace(" " + ph[0].__str__() + " ", " <placeholder> ", 1)
                elif " " + ph[0].__str__() + ")" in new_assert_text:
                    new_assert_text = new_assert_text.replace(" " + ph[0].__str__() + ")", " <placeholder>)", 1)
                elif "(" + ph[0].__str__() + " " in new_assert_text:
                    new_assert_text = new_assert_text.replace("(" + ph[0].__str__() + " ", "(<placeholder> ", 1)
            new_text = new_text.replace(assert_text.strip(), new_assert_text.strip())
            return original_text, new_text
    except Exception as e:
        # print(e)
        return text, text


def _format_smt_string(smt_string):
    """Cleans up an SMT-LIB string by removing redundant whitespace and empty lines."""
    lines = smt_string.split('\n')
    # Strip whitespace from each line and remove empty lines
    stripped_lines = [line.strip() for line in lines if line.strip()]
    # Join lines with a single newline, which is standard
    return '\n'.join(stripped_lines)


def process_target_file(args):
    """Worker function that randomly selects a target file and processes all iterations for it"""
    (smt_files, generator_types, base_folder_name, worker_id,
     solver1_path, solver2_path, timeout, incremental, solver1, solver2,
     theory, add_option, temp, lock, max_iterations) = args

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
                with lock:
                    print(f"Process {process_id}: Failed to parse initial file {target_file_path}: {e}")
                continue  # Skip to the next file

            results = []

            for iteration in range(max_iterations):
                try:
                    if not expr_list:
                        with lock:
                            print(f"Process {process_id}: No expressions to mutate in {target_file_path}, stopping iterations for this file.")
                        break

                    # --- Mutation Phase ---
                    removed_exprs = random.sample(expr_list, min(SAMPLE_SIZE, len(expr_list)))
                    intermediate_formula = assertions_text
                    all_new_declarations = []

                    for expr in removed_exprs:
                        generator_type = random.choice(generator_types)
                        mutation_result = generator_wrapper(generator_type)

                        if mutation_result is None:
                            continue

                        new_decl, new_formula = mutation_result

                        if isinstance(new_formula, list):
                            new_formula = "\n".join(new_formula)

                        # Replace in assertions text to avoid affecting declarations
                        if new_formula is not None:
                            intermediate_formula = intermediate_formula.replace(expr[0].__str__(), new_formula, 1)
                        
                        # Collect new declarations from this mutation
                        if isinstance(new_decl, str):
                            new_decl = new_decl.strip().split("\n")
                        if isinstance(new_decl, list):
                            new_declarations = [
                                decl for decl in new_decl 
                                if decl.strip() and decl.strip() not in intermediate_formula
                            ]
                            all_new_declarations.extend(new_declarations)
                    
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

                    # if isinstance(new_decl, str):
                    #     new_decl = new_decl.strip().split("\n")
                    # if isinstance(new_decl, list):
                    #     new_declarations = [
                    #         decl for decl in new_decl if decl.strip() and decl.strip() not in intermediate_formula
                    #     ]
                    #     if new_declarations:
                    #         intermediate_formula = "\n".join(new_declarations) + "\n" + intermediate_formula

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
                    formatted_formula = _format_smt_string(intermediate_formula)
                    with open(smt_file_name, 'w') as f:
                        f.write(formatted_formula)

                    with lock:
                        print(f"Process {process_id}: Generated {smt_file_name} from {target_file_path}")

                    # --- Solver and Update Phase ---
                    solver_result = solver_runner(
                        solver1_path, solver2_path, smt_file_name, timeout,
                        incremental, solver1, solver2, theory, add_option, temp, None
                    )
                    results.append(solver_result)

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
                            with lock:
                                print(f"Process {process_id}: No expressions found in mutated file {smt_file_name}, stopping iterations for this file.")
                            break
                    except Exception as e:
                        # If parsing the new file fails, log the error and break the iteration loop
                        with lock:
                            print(f"Process {process_id}: Failed to parse mutated file {smt_file_name} in iteration {iteration}: {e}")
                            print(f"Process {process_id}: Stopping iterations for this file to avoid incorrect replacements")
                        break

                    # --- Cleanup ---
                    if os.path.exists(smt_file_name):
                        os.remove(smt_file_name)
                        # pass

                except Exception as e:
                    with lock:
                        print(f"Process {process_id}: Error in iteration {iteration} for {target_file_path}: {e}")
                        print(traceback.format_exc())
                    results.append(None)

            with lock:
                successful_iterations = sum(1 for r in results if r is not None)
                print(f"Process {process_id}: Completed {successful_iterations}/{len(results)} iterations for {target_file_path}")

        return results

    except KeyboardInterrupt:
        raise
    except Exception as e:
        with lock:
            print(f"Process {process_id}: A critical error occurred: {e}")
            print(traceback.format_exc())
        return [None] * max_iterations


def main():
    # Parse command line arguments
    arguments = MainArgumentParser()
    arguments.parse_arguments(argparse.ArgumentParser())
    parsed_arguments = arguments.get_arguments()
    
    # Retrieve parsed command line arguments
    solver1 = parsed_arguments["solver1"]
    solver2 = parsed_arguments["solver2"]
    solver1_path = parsed_arguments["solverbin1"]
    solver2_path = parsed_arguments["solverbin2"]
    add_option = parsed_arguments["option"]
    timeout = parsed_arguments["timeout"]
    incremental = DEFAULT_INCREMENTAL
    theory = DEFAULT_THEORY
    temp = "./temp/"
    
    # Get number of processes from arguments or use CPU count
    num_processes = parsed_arguments["processes"]
    if num_processes is None:
        num_processes = os.cpu_count() or 4
    
    # Create temporary directory if it doesn't exist
    if not os.path.exists(TEMP_DIRECTORY):
        os.mkdir(TEMP_DIRECTORY)

    # Get the list of smt files
    files_path = parsed_arguments["bugs"]
    if files_path is None:
        files_path = rootpath + "/bug_triggering_formulas"
    if not os.path.exists(files_path):
        print("bugs path does not exist")
        exit(0)
    file_list = get_all_smt_files_recursively(files_path)
    print(f"Found {len(file_list)} SMT files in {files_path}")
    smt_files = file_list

    # Create a new directory for the current run
    time = datetime.datetime.now()
    base_folder_name = time.strftime("%Y-%m-%d-%H-%M-%S")
    
    # Create base directory if it doesn't exist
    if not os.path.exists(base_folder_name):
        os.mkdir(base_folder_name)

    # Pre-compute generator types for better performance
    if "bitwuzla" in [solver1, solver2]:
        generator_types = BITWUZLA_THEORYS
    elif solver1 in ["z3", "cvc5"] and solver2 in ["z3", "cvc5"] and solver1 != solver2:
        generator_types = GENERAL_THEORYS
    elif solver1 == solver2 and solver1 == "z3":
        generator_types = Z3_THEORYS + GENERAL_THEORYS
    elif solver1 == solver2 and solver1 == "cvc5":
        generator_types = CVC5_THEORYS + GENERAL_THEORYS

    # Split file list among processes
    def split_files(files, num_proc):
        """Split files into roughly equal chunks for each process"""
        chunk_size = len(files) // num_proc
        remainder = len(files) % num_proc
        
        chunks = []
        start = 0
        for i in range(num_proc):
            # Add one extra file to first 'remainder' processes
            extra = 1 if i < remainder else 0
            end = start + chunk_size + extra
            chunks.append(files[start:end])
            start = end
        return chunks

    file_chunks = split_files(smt_files, num_processes)
    print(f"Split {len(smt_files)} files into {num_processes} chunks: {[len(chunk) for chunk in file_chunks]}")

    # Create a multiprocessing manager for shared resources
    manager = Manager()
    lock = manager.Lock()
    
    # Get max iterations from arguments
    max_iterations = parsed_arguments["iterations"]

    print(f"Starting multiprocessing with {num_processes} processes, {max_iterations} iterations per seed")
    
    try:
        with Pool(processes=num_processes) as pool:
            # Prepare arguments for multiprocessing - each worker gets its own file chunk
            for i in range(num_processes):
                task_args = (
                    file_chunks[i], generator_types, base_folder_name, 
                    f"worker_{i}", solver1_path, solver2_path, timeout, 
                    incremental, solver1, solver2, theory, add_option, temp, lock,
                    max_iterations
                )
                pool.apply_async(process_target_file, args=(task_args,))
            
            # Close the pool and wait for all tasks to complete
            pool.close()
            pool.join()
        
        print("All workers completed successfully.")
    
    except KeyboardInterrupt:
        print("\nTerminating processes...")
        pool.terminate()
        pool.join()
        print("Bye!")
    except Exception as e:
        print(f"Error in main loop: {e}")
        print(traceback.format_exc())
        pool.terminate()
        pool.join()

if __name__ == "__main__":
    main()

