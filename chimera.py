import os
import sys
import datetime
import argparse
import traceback
import multiprocessing
from pathlib import Path
from multiprocessing import Pool, Manager

# Set up path
path = Path(__file__)
rootpath = str(path.parent.absolute())
sys.path.append(rootpath)

from src.argument_parser.parser import MainArgumentParser
from src.utils.file_handlers import get_all_smt_files_recursively, split_files
from src.utils.timeout import register_timeout_handler
from src.core.fuzzer import process_target_file, process_standalone_generation, print_stats
from src.constants import (
    TEMP_DIRECTORY, DEFAULT_INCREMENTAL, DEFAULT_THEORY, DEFAULT_STANDALONE_ITERATIONS
)
from src.config.generator_config import get_generator_version
from src.config.theory_selection import get_compatible_theories
from src.history.fuzz import fuzz as history_fuzz
from src.rewrite.rewrite import fuzz as rewrite_fuzz


def main():
    # Register timeout handler
    register_timeout_handler()

    # Parse command line arguments
    arguments = MainArgumentParser()
    arguments.parse_arguments(argparse.ArgumentParser())
    parsed_arguments = arguments.get_arguments()

    generator_path = parsed_arguments.get("generator_path")
    if generator_path:
        os.environ["NEW_GENERATORS_PATH"] = generator_path
        os.environ["USE_NEW_GENERATORS"] = "true"
        import importlib
        import src.config.generator_config
        import src.config.generator_loader
        importlib.reload(src.config.generator_config)
        importlib.reload(src.config.generator_loader)

    # Print which generator version is being used
    from src.config.generator_config import get_generator_version
    print(f"Using {get_generator_version()} generators")
    
    # Retrieve parsed command line arguments
    solver1 = parsed_arguments["solver1"]
    solver2 = parsed_arguments["solver2"]
    solver1_path = parsed_arguments["solverbin1"]
    solver2_path = parsed_arguments["solverbin2"]
    add_option = parsed_arguments["option"]
    timeout = parsed_arguments["timeout"]
    incremental = DEFAULT_INCREMENTAL
    theory = DEFAULT_THEORY
    temp = parsed_arguments.get("temp", TEMP_DIRECTORY)
    standalone = parsed_arguments.get("standalone", False)
    history_mode = parsed_arguments.get("history", False)
    rewrite_mode = parsed_arguments.get("rewrite", False)
    
    # Get number of processes from arguments or use CPU count
    num_processes = parsed_arguments["processes"]
    if num_processes is None:
        num_processes = os.cpu_count() or 4
    
    # Create temporary directory if it doesn't exist
    if not os.path.exists(temp):
        os.mkdir(temp)

    # Get the list of smt files
    smt_files = []
    if not standalone and not history_mode:
        files_path = parsed_arguments["bugs"]
        if files_path is None:
            files_path = rootpath + "/bug_triggering_formulas"
        if not os.path.exists(files_path):
            print("bugs path does not exist")
            exit(0)
        file_list = get_all_smt_files_recursively(files_path)
        print(f"Found {len(file_list)} SMT files in {files_path}")
        smt_files = file_list
    else:
        if history_mode:
            print("Running in history mode")
        else:
            print("Running in standalone mode")

    # Create a new directory for the current run
    current_time = datetime.datetime.now()
    base_folder_name = current_time.strftime("%Y-%m-%d-%H-%M-%S")
    
    # Create base directory if it doesn't exist
    if not os.path.exists(base_folder_name):
        os.mkdir(base_folder_name)

    # Pre-compute generator types for better performance
    generator_types = get_compatible_theories(solver1, solver2)

    file_chunks = []
    if not standalone and not history_mode:
        file_chunks = split_files(smt_files, num_processes)
        print(f"Split {len(smt_files)} files into {num_processes} chunks: {[len(chunk) for chunk in file_chunks]}")

    # Create a multiprocessing manager for shared resources
    manager = Manager()
    lock = manager.Lock()
    stats = manager.dict()
    stats['files_processed'] = 0
    stats['mutations'] = 0
    stats['bugs'] = 0
    stats['invalid'] = 0
    
    # Get max iterations from arguments (ignored in standalone mode if using default mostly)
    # The snippet used a constant, but we can reuse this if needed, 
    # but fuzzer now uses MAX_ITERATIONS constant.
    
    print(f"Starting multiprocessing with {num_processes} processes")
    
    pool = None
    try:
        # Start stats printer thread
        stats_process = multiprocessing.Process(target=print_stats, args=(stats, lock))
        stats_process.daemon = True
        stats_process.start()

        pool = Pool(processes=num_processes)
        # Prepare arguments for multiprocessing - each worker gets its own file chunk
        for i in range(num_processes):
            if history_mode:
                # History mode arguments
                skeleton_path = rootpath + "/src/history/resource/skeleton.smt2"
                buggy_path = rootpath + "/src/history/resource/"
                rules = None # No rules for now as requested
                
                # fuzz(skeleton_path, solver1, solver2, solver1_path, solver2_path, timeout, incremental, core, add_option_flag, rules, buggy, temp, argument, mutant=None, tactic=None)
                # Note: core corresponds to 'i' (worker id)
                task_args = (
                    skeleton_path, solver1, solver2, solver1_path, solver2_path, timeout,
                    incremental, i, add_option, rules, buggy_path, temp, parsed_arguments
                )
                pool.apply_async(history_fuzz, args=task_args)
            elif standalone:
                task_args = (
                    DEFAULT_STANDALONE_ITERATIONS, generator_types, base_folder_name, 
                    f"worker_{i}", solver1_path, solver2_path, timeout, 
                    incremental, solver1, solver2, theory, add_option, temp, lock, stats
                )
                pool.apply_async(process_standalone_generation, args=(task_args,))
            elif rewrite_mode:
                 task_args = (
                    file_chunks[i], solver1, solver1_path, temp, 2, parsed_arguments["iterations"], i, parsed_arguments["bug_type"], parsed_arguments["mimetic"]
                )
                 pool.apply_async(rewrite_fuzz, args=task_args)
        
        # Close the pool and wait for all tasks to complete
        pool.close()
        pool.join()
        
        print("All workers completed successfully.")
    
    except KeyboardInterrupt:
        print("\nTerminating processes...")
        if pool:
            pool.terminate()
            pool.join()
        print("Bye!")
    except Exception as e:
        print(f"Error in main loop: {e}")
        print(traceback.format_exc())
        if pool:
            pool.terminate()
            pool.join()

if __name__ == "__main__":
    main()

