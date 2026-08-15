"""The Wolpert 2018 inventory gate must fail on the defects it was written for.

The gate it replaced carried a nineteen-item allowlist of the physical-knowledge
cluster and printed `19 scoped items`. Nothing outside that list could fail it,
so §III of the paper — Definitions 4 and 6 through 9, Propositions 7 through 14 —
was not recorded as missing; it was not recorded at all. The thing worth
asserting is therefore not that the tree passes today but that each way of
misreporting coverage fails tomorrow.

Three defect classes are covered here:

* a status whose row shape contradicts it — `NOT-MECHANIZED` naming a
  declaration, or a mechanized status naming none;
* a `NOT-MECHANIZED` row that records absence without a reason;
* a parser that reads the wrong rows — either sweeping a second table in the
  same document, or tearing a cell apart on the escaped pipes that cardinality
  bars are written with.

The last one is not hypothetical: the first run of this gate dropped six §III
rows because `|Γ(U)| ≥ 3` splits into three columns under a naive split.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from check_wolpert_2018_status_table import (  # noqa: E402
    EXPECTED,
    MECHANIZED,
    MIN_REASON_CHARS,
    SCOPE_DELTA_TOKEN,
    UNMECHANIZED,
    check_shape,
    check_via_2008,
    rows_in_section,
)

HEADING = "## 0. Complete source inventory"
KNOWN = {"realDecl", "otherDecl"}


def _table(*rows: str) -> str:
    return HEADING + "\n" + "".join(f"{row}\n" for row in rows)


def test_unmechanized_row_may_not_name_a_declaration() -> None:
    errors = check_shape("X", "NOT-MECHANIZED", "`realDecl`", "r" * 80, KNOWN)
    assert any("empty Lean cell" in error for error in errors)


def test_unmechanized_row_needs_a_stated_reason() -> None:
    errors = check_shape("X", "NOT-MECHANIZED", "—", "missing", KNOWN)
    assert any("stated reason" in error for error in errors)


def test_a_reason_at_the_threshold_passes() -> None:
    assert check_shape("X", "NOT-MECHANIZED", "—", "r" * MIN_REASON_CHARS, KNOWN) == []


def test_mechanized_row_must_name_a_declaration() -> None:
    errors = check_shape("X", "VIA-2008", "—", "2008 Def. 1", KNOWN)
    assert any("names no declaration" in error for error in errors)


def test_mechanized_row_may_not_name_a_ghost() -> None:
    errors = check_shape("X", "SOURCE-EXACT", "`ghostDecl`", "note", KNOWN)
    assert any("unknown declarations" in error for error in errors)


def test_every_row_needs_a_note() -> None:
    assert any("empty note" in error for error in check_shape("X", "INTERPRETATION", "—", "", KNOWN))


def test_well_formed_rows_pass() -> None:
    assert check_shape("X", "VIA-2008", "`realDecl`", "2008 Def. 1", KNOWN) == []
    assert check_shape("X", "INTERPRETATION", "—", "no claim", KNOWN) == []


def test_parser_is_scoped_to_its_section() -> None:
    text = _table("| A | VIA-2008 | `realDecl` | n |") + (
        "## 9. Other\n| B | VIA-2008 | `realDecl` | n |\n"
    )
    assert set(rows_in_section(text, HEADING)) == {"A"}


def test_parser_survives_escaped_cardinality_bars() -> None:
    text = _table("| C | NOT-MECHANIZED | — | needs \\|Γ(U)\\| ≥ 3 to hold |")
    rows = rows_in_section(text, HEADING)
    assert rows["C"][0] == "NOT-MECHANIZED"
    assert "|Γ(U)|" in rows["C"][2]


def test_every_status_in_the_expected_map_is_a_declared_status() -> None:
    assert set(EXPECTED.values()) <= MECHANIZED | UNMECHANIZED


def test_the_inventory_covers_the_whole_paper() -> None:
    """The allowlist defect, asserted directly.

    Definitions 1-11, results 1-25 with their printed sub-parts, and the §III
    items the previous gate could not see. If a future edit shrinks `EXPECTED`
    back to a cluster, this fails rather than reporting a smaller denominator.
    """
    for item in (
        *(f"Def. {index}" for index in range(1, 12)),
        "Prop. 7(1)",
        "Prop. 7(2)",
        "Prop. 8",
        "Prop. 9",
        "Prop. 10",
        "Prop. 11",
        "Prop. 12",
        "Prop. 13",
        "Prop. 14",
    ):
        assert item in EXPECTED, f"{item} dropped from the inventory"
    assert len(EXPECTED) > 19, "the inventory has shrunk back toward an allowlist"


# `VIA-2008` says "already proved over there". That is the whole truth only when
# the 2008 row it points at is itself SOURCE-EXACT; routing through a
# SPECIALIZED row moves a narrowed scope into the mechanized column and records
# it against a different paper. Proposition 13 shipped exactly that way.
STATUSES_2008 = {
    ("Thm", "1", ""): "SOURCE-EXACT",
    ("Thm", "4", ""): "SPECIALIZED",
    ("Cor", "1", "ii"): "REFUTED",
}


def test_via_2008_through_an_exact_row_is_clean() -> None:
    assert check_via_2008("Prop. 2", "2008 Thm 1", STATUSES_2008) == []


def test_via_2008_through_a_specialized_row_must_state_the_delta() -> None:
    errors = check_via_2008("Prop. 13", "this is 2008 Thm 4 at the measure length", STATUSES_2008)
    assert len(errors) == 1
    assert "SPECIALIZED" in errors[0]


def test_via_2008_accepts_a_specialized_row_once_the_delta_is_stated() -> None:
    note = f"this is 2008 Thm 4 at the measure length. {SCOPE_DELTA_TOKEN} setup ranges are finite"
    assert check_via_2008("Prop. 13", note, STATUSES_2008) == []


def test_via_2008_through_a_refuted_row_is_caught() -> None:
    errors = check_via_2008("Some item", "2008 Cor 1(ii)", STATUSES_2008)
    assert len(errors) == 1
    assert "REFUTED" in errors[0]


def test_via_2008_flags_a_reference_the_2008_table_has_no_row_for() -> None:
    errors = check_via_2008("Some item", "2008 Thm 9", STATUSES_2008)
    assert len(errors) == 1
    assert "no row" in errors[0]


def test_sub_part_references_resolve() -> None:
    assert check_via_2008("x", "2008 Cor. 1(ii)", STATUSES_2008)[0].startswith("x:")
