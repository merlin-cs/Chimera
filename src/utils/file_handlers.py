"""
File discovery and splitting utilities.

DRY: one generic walker parameterised by extension; callers just pass
the suffix they need.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import List


def _find_files_by_suffix(directory: str, suffix: str) -> List[str]:
    """Recursively collect files ending with *suffix* under *directory*.

    Skips filenames that contain the suffix twice (e.g. ``.smt20``).
    """
    # Resolve the path to prevent directory-traversal surprises.
    root = Path(directory).resolve()
    if not root.is_dir():
        return []
    results: List[str] = []
    for path in root.rglob(f"*{suffix}"):
        # Guard against partial-suffix matches like ".smt20"
        if path.suffix == suffix:
            results.append(str(path))
    return results


def get_all_smt_files_recursively(path_to_directory: str) -> List[str]:
    """Return all ``.smt2`` files under *path_to_directory*."""
    return _find_files_by_suffix(path_to_directory, ".smt2")


def get_txt_files_list(path_to_directory: str) -> List[str]:
    """Return all ``.txt`` files under *path_to_directory*."""
    return _find_files_by_suffix(path_to_directory, ".txt")


def split_files(file_list: List[str], num_chunks: int) -> List[List[str]]:
    """Split *file_list* into *num_chunks* roughly-equal chunks.

    Always returns exactly *num_chunks* lists (some may be empty).
    """
    if num_chunks <= 0:
        raise ValueError("num_chunks must be positive")
    if not file_list:
        return [[] for _ in range(num_chunks)]

    avg = len(file_list) / num_chunks
    chunks: List[List[str]] = []
    last = 0.0
    while last < len(file_list):
        end = last + avg
        chunks.append(file_list[int(last):int(end)])
        last = end
    # Pad if rounding produced fewer chunks
    while len(chunks) < num_chunks:
        chunks.append([])
    return chunks
