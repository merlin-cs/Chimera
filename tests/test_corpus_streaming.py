"""Tests for the versioned streaming HistFuzz corpus."""

import json
from pathlib import Path

from chimera.history.streaming import export_corpus, load_corpus, validate_corpus


def test_streaming_export_is_valid_and_loadable(tmp_path: Path) -> None:
    source = tmp_path / "source"
    source.mkdir()
    (source / "one.smt2").write_text(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        encoding="utf-8",
    )
    destination = tmp_path / "corpus"
    manifest = export_corpus(
        source,
        destination,
        source_revision="test-revision",
        batch_size=1,
    )
    assert manifest["format_version"] == 1
    assert validate_corpus(destination)["source_revision"] == "test-revision"
    corpus = load_corpus(destination)
    assert corpus.statistics()["total_skeletons"] > 0
    assert corpus.statistics()["total_blocks"] > 0


def test_manifest_checksum_detects_tampering(tmp_path: Path) -> None:
    source = tmp_path / "source"
    source.mkdir()
    (source / "one.smt2").write_text("(assert true)\n(check-sat)\n", encoding="utf-8")
    destination = tmp_path / "corpus"
    export_corpus(source, destination)
    shard = next((destination / "skeletons").glob("*.jsonl"))
    shard.write_text(shard.read_text() + "{}\n", encoding="utf-8")
    try:
        validate_corpus(destination)
    except ValueError as exc:
        assert "checksum" in str(exc)
    else:
        raise AssertionError("tampered corpus unexpectedly validated")


def test_streaming_export_is_deterministic(tmp_path: Path) -> None:
    source = tmp_path / "source"
    source.mkdir()
    (source / "one.smt2").write_text(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        encoding="utf-8",
    )
    first = export_corpus(source, tmp_path / "first", source_revision="fixed")
    second = export_corpus(source, tmp_path / "second", source_revision="fixed")
    assert json.dumps(first, sort_keys=True) == json.dumps(second, sort_keys=True)
