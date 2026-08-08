"""Streaming, versioned HistFuzz corpus storage.

The historical corpus is large enough that extraction must not retain every
parsed AST in memory.  This module deliberately keeps extraction and runtime
loading separate: extraction writes canonical JSONL records incrementally,
while :class:`~chimera.history.corpus.Corpus` remains the convenient in-memory
runtime representation for a loaded corpus.
"""

from __future__ import annotations

import hashlib
import json
import logging
import os
import selectors
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, cast

from chimera.history.corpus import BuildingBlock, Corpus, Skeleton
from chimera.history.extractor import FileExtraction, LogicAwareExtractor

logger = logging.getLogger(__name__)

CORPUS_FORMAT_VERSION = 1
MANIFEST_NAME = "manifest.json"


class CorpusIntegrityError(ValueError):
    """Raised when a corpus manifest or shard does not validate."""


def _canonical_json(value: Mapping[str, Any]) -> bytes:
    """Return one deterministic UTF-8 JSONL record."""
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode(
        "utf-8"
    )


def _safe_shard_name(logic: str) -> str:
    """Map a logic label to a stable, filesystem-safe shard name."""
    cleaned = "".join(ch if ch.isalnum() or ch in "_-" else "_" for ch in logic.upper())
    return cleaned or "UNKNOWN"


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _source_files(input_dir: str | Path) -> List[Path]:
    root = Path(input_dir)
    return sorted(path for path in root.rglob("*.smt2") if path.is_file())


class _ShardWriter:
    """Incrementally write one JSONL shard and track its integrity metadata."""

    def __init__(self, path: Path, *, append: bool = False) -> None:
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.stream = path.open("ab" if append else "wb")
        self.count = 0
        if append and path.stat().st_size:
            with path.open("rb") as existing:
                self.count = sum(1 for line in existing if line.strip())

    def write(self, value: Mapping[str, Any]) -> None:
        self.stream.write(_canonical_json(value))
        self.count += 1

    def close(self) -> None:
        self.stream.flush()
        os.fsync(self.stream.fileno())
        self.stream.close()

    def metadata(self, root: Path) -> Dict[str, Any]:
        return {
            "path": str(self.path.relative_to(root)),
            "count": self.count,
            "sha256": _sha256(self.path),
        }


class _ExtractionWorker:
    """Persistent worker process for safe extraction of large formulas."""

    def __init__(self, timeout: float) -> None:
        self.timeout = timeout
        self.process = subprocess.Popen(
            [sys.executable, "-m", "chimera.history.extraction_worker", "--serve"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
            encoding="utf-8",
        )

    def extract(self, path: Path, logic: str) -> FileExtraction:
        if self.process.stdin is None or self.process.stdout is None:
            raise RuntimeError("corpus extraction worker pipes are unavailable")
        self.process.stdin.write(json.dumps({"path": str(path), "logic": logic}) + "\n")
        self.process.stdin.flush()
        selector = selectors.DefaultSelector()
        selector.register(self.process.stdout, selectors.EVENT_READ)
        ready = selector.select(self.timeout)
        selector.close()
        if not ready:
            raise TimeoutError(f"worker extraction timed out after {self.timeout}s")
        # A crashed worker returns EOF and is reported below.
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError(f"worker exited with {self.process.poll()}")
        payload = json.loads(line)
        if not payload.get("ok", True):
            raise RuntimeError(payload.get("error", "worker extraction failed"))
        return FileExtraction(
            logic=logic,
            skeletons=[Skeleton.from_dict(item) for item in payload.get("skeletons", [])],
            blocks=[BuildingBlock.from_dict(item) for item in payload.get("blocks", [])],
            parse_errors=list(payload.get("parse_errors", [])),
        )

    def close(self) -> None:
        if self.process.stdin is not None:
            self.process.stdin.close()
        try:
            self.process.wait(timeout=self.timeout)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()


def _write_records(
    extractor: LogicAwareExtractor,
    file_paths: Sequence[Path],
    staging: Path,
    *,
    append: bool = False,
    isolate_bytes: int = 8192,
    worker_timeout: float = 10.0,
) -> Dict[str, Any]:
    writers: Dict[tuple[str, str], _ShardWriter] = {}
    worker: Optional[_ExtractionWorker] = None
    stats: Dict[str, Any] = {
        "files_seen": len(file_paths),
        "files_processed": 0,
        "files_failed": 0,
        "skeletons_extracted": 0,
        "blocks_extracted": 0,
        "files_with_quantifiers": 0,
        "isolated_files": 0,
        "isolated_failures": 0,
    }

    try:
        for index, path in enumerate(file_paths, start=1):
            logic = extractor._get_logic_for_file(str(path))
            if path.stat().st_size >= isolate_bytes:
                stats["isolated_files"] += 1
                try:
                    if worker is None:
                        worker = _ExtractionWorker(worker_timeout)
                    extraction = worker.extract(path, logic)
                except (
                    OSError,
                    RuntimeError,
                    TimeoutError,
                    ValueError,
                    subprocess.TimeoutExpired,
                ) as exc:
                    stats["isolated_failures"] += 1
                    if worker is not None:
                        worker.close()
                        worker = None
                    extraction = FileExtraction(
                        logic=logic,
                        skeletons=[],
                        blocks=[],
                        parse_errors=[f"isolated extraction failed: {exc}"],
                    )
            else:
                extraction = extractor._extract_from_file(str(path), logic)
            if extraction.parse_errors:
                stats["files_failed"] += 1
                logger.debug("Skipping %s: %s", path, "; ".join(extraction.parse_errors))
            else:
                stats["files_processed"] += 1
                stats["skeletons_extracted"] += len(extraction.skeletons)
                stats["blocks_extracted"] += len(extraction.blocks)
                if any(item.is_quantified for item in extraction.skeletons):
                    stats["files_with_quantifiers"] += 1

            for block in extraction.blocks:
                shard_logic = _safe_shard_name(block.logic)
                key = ("blocks", shard_logic)
                writer = writers.get(key)
                if writer is None:
                    writer = _ShardWriter(
                        staging / "blocks" / f"{shard_logic}.jsonl", append=append
                    )
                    writers[key] = writer
                writer.write(block.to_dict())

            for skeleton in extraction.skeletons:
                shard_logic = _safe_shard_name(skeleton.logic)
                key = ("skeletons", shard_logic)
                writer = writers.get(key)
                if writer is None:
                    writer = _ShardWriter(
                        staging / "skeletons" / f"{shard_logic}.jsonl", append=append
                    )
                    writers[key] = writer
                writer.write(skeleton.to_dict())

            if index % 100 == 0 or index == len(file_paths):
                logger.info("Extracted %d/%d corpus inputs", index, len(file_paths))
    finally:
        for writer in writers.values():
            writer.close()
        if worker is not None:
            worker.close()

    shards: Dict[str, Dict[str, Any]] = {"blocks": {}, "skeletons": {}}
    for (kind, logic), writer in sorted(writers.items()):
        shards[kind][logic] = writer.metadata(staging)

    stats["shards"] = shards
    return stats


def _publish(staging: Path, target: Path, *, replace: bool) -> None:
    """Atomically publish a complete staging directory.

    Existing targets are moved aside before the new directory is made visible;
    the backup is removed only after the replacement succeeds.  A failed
    replacement attempts to restore the previous target.
    """
    target.parent.mkdir(parents=True, exist_ok=True)
    backup: Optional[Path] = None
    if target.exists():
        if not replace:
            raise FileExistsError(f"corpus output already exists: {target}")
        backup = target.with_name(f".{target.name}.backup-{os.getpid()}")
        os.replace(target, backup)
    try:
        os.replace(staging, target)
    except Exception:
        if backup is not None and not target.exists():
            os.replace(backup, target)
        raise
    if backup is not None:
        shutil.rmtree(backup)


def validate_corpus(directory: str | Path) -> Dict[str, Any]:
    """Validate manifest, shard counts, checksums, and record decoding."""
    root = Path(directory)
    manifest_path = root / MANIFEST_NAME
    if not manifest_path.is_file():
        raise CorpusIntegrityError(f"missing corpus manifest: {manifest_path}")
    with manifest_path.open(encoding="utf-8") as stream:
        manifest = json.load(stream)
    if manifest.get("format_version") != CORPUS_FORMAT_VERSION:
        raise CorpusIntegrityError(
            f"unsupported corpus format: {manifest.get('format_version')}"
        )

    for kind, shards in manifest.get("shards", {}).items():
        for logic, metadata in shards.items():
            path = root / metadata["path"]
            if not path.is_file():
                raise CorpusIntegrityError(f"missing {kind}/{logic} shard: {path}")
            if _sha256(path) != metadata["sha256"]:
                raise CorpusIntegrityError(f"checksum mismatch: {path}")
            records = 0
            with path.open(encoding="utf-8") as stream:
                for line in stream:
                    if not line.strip():
                        continue
                    json.loads(line)
                    records += 1
            if records != metadata["count"]:
                raise CorpusIntegrityError(
                    f"record count mismatch for {path}: {records} != {metadata['count']}"
                )
    return cast(Dict[str, Any], manifest)


def export_corpus(
    input_dir: str | Path,
    output_dir: str | Path,
    *,
    source_revision: str = "unknown",
    replace: bool = False,
    batch_size: int = 100,
    isolate_bytes: int = 8192,
    worker_timeout: float = 10.0,
    logic_mapping: Optional[Dict[str, List[str]]] = None,
) -> Dict[str, Any]:
    """Stream *input_dir* into a validated, atomically published corpus."""
    input_root = Path(input_dir)
    target = Path(output_dir)
    if not input_root.is_dir():
        raise FileNotFoundError(f"corpus source directory does not exist: {input_root}")
    file_paths = _source_files(input_root)
    if not file_paths:
        raise ValueError(f"corpus source contains no .smt2 files: {input_root}")
    # ``mkdtemp`` does not create its parent.  Create it before staging so a
    # valid extraction can target a brand-new nested directory.
    target.parent.mkdir(parents=True, exist_ok=True)
    extractor = LogicAwareExtractor(logic_mapping=logic_mapping)
    staging = Path(tempfile.mkdtemp(prefix=f".{target.name}.staging-", dir=target.parent))
    try:
        if batch_size <= 0:
            raise ValueError("batch_size must be positive")
        stats: Dict[str, Any] = {
            "files_seen": len(file_paths),
            "files_processed": 0,
            "files_failed": 0,
            "skeletons_extracted": 0,
            "blocks_extracted": 0,
            "files_with_quantifiers": 0,
            "isolated_files": 0,
            "isolated_failures": 0,
        }
        for start in range(0, len(file_paths), batch_size):
            batch_stats = _write_records(
                extractor,
                file_paths[start : start + batch_size],
                staging,
                append=start > 0,
                isolate_bytes=isolate_bytes,
                worker_timeout=worker_timeout,
            )
            for key in (
                "files_processed",
                "files_failed",
                "skeletons_extracted",
                "blocks_extracted",
                "files_with_quantifiers",
                "isolated_files",
                "isolated_failures",
            ):
                stats[key] += batch_stats[key]

        shards: Dict[str, Dict[str, Any]] = {"blocks": {}, "skeletons": {}}
        for kind in shards:
            shard_dir = staging / kind
            if shard_dir.is_dir():
                for shard_path in sorted(shard_dir.glob("*.jsonl")):
                    logic = shard_path.stem
                    with shard_path.open("rb") as stream:
                        count = sum(1 for line in stream if line.strip())
                    shards[kind][logic] = {
                        "path": str(shard_path.relative_to(staging)),
                        "count": count,
                        "sha256": _sha256(shard_path),
                    }
        manifest = {
            "format_version": CORPUS_FORMAT_VERSION,
            "source_revision": source_revision,
            "source": {"file_count": len(file_paths)},
            "extraction_stats": stats,
            "shards": shards,
        }
        with (staging / MANIFEST_NAME).open("w", encoding="utf-8") as stream:
            json.dump(manifest, stream, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        validate_corpus(staging)
        _publish(staging, target, replace=replace)
        return manifest
    except Exception:
        if staging.exists():
            shutil.rmtree(staging)
        raise


def load_corpus(
    directory: str | Path,
    *,
    validate: bool = True,
    max_record_bytes: int = 16_384,
) -> Corpus:
    """Validate and load a canonical JSONL corpus into the runtime model."""
    if validate:
        validate_corpus(directory)
    return Corpus.load(str(directory), max_record_bytes=max_record_bytes)


def packaged_corpus_path() -> Path:
    """Locate the bundled corpus in source, editable, or wheel installs."""
    # Return the canonical location even before a source checkout has been
    # populated.  The engine's preflight then reports the actionable missing
    # resource instead of failing during object construction.
    return Path(__file__).resolve().parents[1] / "resources" / "histfuzz"


__all__ = [
    "CORPUS_FORMAT_VERSION",
    "CorpusIntegrityError",
    "export_corpus",
    "load_corpus",
    "packaged_corpus_path",
    "validate_corpus",
]
