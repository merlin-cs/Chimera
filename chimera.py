"""
Chimera – grammar-based SMT solver fuzzer.

Entry point: orchestrates worker processes for mutation-based,
standalone, history-based, and rewrite-based fuzzing.
"""

import os
import sys
import glob
import datetime
import traceback
import multiprocessing
from pathlib import Path
from copy import deepcopy
from multiprocessing import Pool, Manager

# Set up path
ROOT_PATH = str(Path(__file__).parent.resolve())
if ROOT_PATH not in sys.path:
    sys.path.append(ROOT_PATH)

from src.argument_parser.parser import MainArgumentParser
from src.utils.file_handlers import get_all_smt_files_recursively, split_files
from src.utils.timeout import register_timeout_handler
from src.core.fuzzer import (
    process_target_file, process_standalone_generation, print_stats,
    process_history_fuzz, process_rewrite_fuzz,
)
from src.constants import (
    TEMP_DIRECTORY, DEFAULT_INCREMENTAL, DEFAULT_THEORY, DEFAULT_STANDALONE_ITERATIONS,
)
from src.config.generator_config import get_generator_version
from src.config.theory_selection import get_compatible_theories


def _configure_generators(parsed_arguments: dict) -> None:
    """Hot-reload generator modules if a custom path was supplied."""
    generator_path = parsed_arguments.get("generator_path")
    if not generator_path:
        return
    os.environ["NEW_GENERATORS_PATH"] = generator_path
    os.environ["USE_NEW_GENERATORS"] = "true"
    import importlib
    import src.config.generator_config
    import src.config.generator_loader
    importlib.reload(src.config.generator_config)
    importlib.reload(src.config.generator_loader)


def _discover_skeletons(resource_dir: str, fallback: str):
    """Return a list of skeleton .smt2 paths found in *resource_dir*."""
    skeletons = []
    if os.path.isdir(resource_dir):
        skeletons = glob.glob(os.path.join(resource_dir, "skeleton*.smt2"))
    return skeletons if skeletons else [fallback]


def main() -> None:
    register_timeout_handler()

    # Parse CLI
    import argparse
    arguments = MainArgumentParser()
    arguments.parse_arguments(argparse.ArgumentParser())
    parsed = arguments.get_arguments()

    # Hot-reload generators if needed
    _configure_generators(parsed)
    print(f"Using {get_generator_version()} generators")

    # Unpack arguments
    solver1 = parsed["solver1"]
    solver2 = parsed["solver2"]
    solver1_path = parsed["solverbin1"]
    solver2_path = parsed["solverbin2"]
    add_option = parsed["option"]
    timeout = parsed["timeout"]
    incremental = DEFAULT_INCREMENTAL
    theory = DEFAULT_THEORY
    temp = parsed.get("temp", TEMP_DIRECTORY)
    standalone = parsed.get("standalone", False)
    history_mode = parsed.get("history", False)
    rewrite_mode = parsed.get("rewrite", False)

    num_processes = parsed["processes"] or (os.cpu_count() or 4)
    os.makedirs(temp, exist_ok=True)

    # ── Seed file discovery ──────────────────────────────────────────────
    smt_files = []
    if not standalone and not history_mode:
        files_path = parsed.get("bugs") or os.path.join(ROOT_PATH, "bug_triggering_formulas")
        if not os.path.isdir(files_path):
            print(f"bugs path does not exist: {files_path}")
            sys.exit(1)
        smt_files = get_all_smt_files_recursively(files_path)
        print(f"Found {len(smt_files)} SMT files in {files_path}")
    else:
        print(f"Running in {'history' if history_mode else 'standalone'} mode")

    # Output directory
    base_folder = datetime.datetime.now().strftime("%Y-%m-%d-%H-%M-%S")
    os.makedirs(base_folder, exist_ok=True)

    generator_types = get_compatible_theories(solver1, solver2)

    file_chunks = []
    if not standalone and not history_mode:
        file_chunks = split_files(smt_files, num_processes)
        print(f"Split {len(smt_files)} files into {num_processes} chunks: {[len(c) for c in file_chunks]}")

    # ── Shared state via Manager ─────────────────────────────────────────
    manager = Manager()
    lock = manager.Lock()
    stats = manager.dict(files_processed=0, mutations=0, bugs=0, invalid=0)

    print(f"Starting multiprocessing with {num_processes} processes")

    pool = None
    try:
        # Background stats printer
        stats_proc = multiprocessing.Process(target=print_stats, args=(stats, lock), daemon=True)
        stats_proc.start()

        pool = Pool(processes=num_processes)

        for i in range(num_processes):
            if history_mode:
                resource_dir = os.path.join(ROOT_PATH, "src", "history", "resource")
                skeleton_fallback = os.path.join(resource_dir, "skeleton.smt2")
                skeletons = _discover_skeletons(resource_dir, skeleton_fallback)

                task_args = (
                    skeletons, solver1, solver2, solver1_path, solver2_path, timeout,
                    incremental, i, add_option, None, resource_dir, temp, parsed,
                )
                pool.apply_async(process_history_fuzz, args=(task_args,))

            elif standalone:
                task_args = (
                    DEFAULT_STANDALONE_ITERATIONS, generator_types, base_folder,
                    f"worker_{i}", solver1_path, solver2_path, timeout,
                    incremental, solver1, solver2, theory, add_option, temp, lock, stats,
                )
                pool.apply_async(process_standalone_generation, args=(task_args,))

            elif rewrite_mode:
                task_args = (
                    file_chunks[i], solver1, solver1_path, temp, 2,
                    parsed["iterations"], i, parsed["bug_type"], parsed["mimetic"],
                )
                pool.apply_async(process_rewrite_fuzz, args=(task_args,))

            else:
                task_args = (
                    file_chunks[i], generator_types, base_folder,
                    f"worker_{i}", solver1_path, solver2_path, timeout,
                    incremental, solver1, solver2, theory, add_option, temp, lock, stats,
                )
                pool.apply_async(process_target_file, args=(task_args,))

        pool.close()
        pool.join()
        print("All workers completed successfully.")

    except KeyboardInterrupt:
        print("\nTerminating processes…")
        if pool:
            pool.terminate()
            pool.join()
        print("Bye!")
    except Exception as exc:
        print(f"Error in main loop: {exc}")
        print(traceback.format_exc())
        if pool:
            pool.terminate()
            pool.join()


if __name__ == "__main__":
    main()

