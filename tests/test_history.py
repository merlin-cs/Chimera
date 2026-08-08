"""Tests for the canonical logic-aware HistFuzz corpus API."""

from pathlib import Path

from chimera.core.smt_parser import parse_string
from chimera.history.corpus import BuildingBlock, Corpus, Skeleton
from chimera.history.extractor import LogicAwareExtractor
from chimera.history.streaming import export_corpus, load_corpus, validate_corpus


def _term(text: str):
    result = parse_string(f"(assert {text})", silent=True)
    assert result is not None
    return result[0].assert_cmd[0].term


def test_corpus_round_trip_preserves_logic_and_dependencies() -> None:
    corpus = Corpus()
    corpus.add_block(BuildingBlock("x", "QF_LIA", var_decls={"x": "Int"}))
    corpus.add_skeleton(
        Skeleton("(and (hole 0) (hole 1))", "QF_LIA", hole_types=["Bool", "Bool"])
    )
    loaded = Corpus.from_json(corpus.to_json())
    assert loaded.blocks["LIA"][0].var_decls == {"x": "Int"}
    assert loaded.skeletons["QF_LIA"][0].num_holes == 2


def test_skeleton_holes_are_parseable_and_collectable() -> None:
    skeleton = Skeleton("(or hole 0 hole 1)", "QF_UF", hole_types=["Bool", "Bool"])
    holes = skeleton.collect_holes()
    assert len(holes) == 2


def test_logic_inference_for_core_theories() -> None:
    extractor = LogicAwareExtractor()
    assert extractor._infer_logic_from_term(_term("(+ 0 1)")) == "QF_LIA"
    assert extractor._infer_logic_from_term(_term("(bvadd (_ bv1 8) (_ bv2 8))")) == "QF_BV"
    assert extractor._infer_logic_from_term(_term('(str.len "abc")')) == "QF_S"
    assert extractor._infer_logic_from_term(_term("(and true false)")) == "QF_UF"


def test_compact_historical_logic_labels_are_normalized() -> None:
    corpus = Corpus()
    corpus.add_skeleton(Skeleton("(> 0 1)", "LIA"))
    assert "QF_LIA" in corpus.skeletons
    assert corpus.sample_skeleton(logic="QF_LIA", quantified=False) is not None


def test_bare_qf_records_are_classified_before_compatibility_filtering() -> None:
    corpus = Corpus()
    corpus.add_block(BuildingBlock('(str.contains "a" "a")', "QF"))
    corpus.add_skeleton(Skeleton('(= hole 0 hole 1)', "QF", hole_types=["String", "String"]))

    assert "S" in corpus.blocks
    assert "QF_S" in corpus.skeletons
    assert corpus.sample_block(logic="QF_BV") is None
    assert corpus.sample_skeleton(logic="QF_S", quantified=False) is not None


def test_streamed_extraction_can_be_loaded_by_histfuzz(tmp_path: Path) -> None:
    source = tmp_path / "seeds"
    source.mkdir()
    (source / "seed.smt2").write_text(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        encoding="utf-8",
    )
    destination = tmp_path / "corpus"
    export_corpus(source, destination, source_revision="test")
    assert validate_corpus(destination)["format_version"] == 1
    loaded = load_corpus(destination)
    assert loaded.statistics()["total_skeletons"] == 1
