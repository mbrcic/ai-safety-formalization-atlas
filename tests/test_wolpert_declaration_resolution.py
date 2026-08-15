"""The 2008 gate must resolve declaration names, not merely recognize suffixes.

`check_wolpert_status_table.py` decides whether a provenance row names a real
declaration. Two properties of that check were weak enough to fail open, and an
adversarial review of the coverage tables found both:

* **One-of-N.** A row passed when *any* one of its named declarations resolved,
  so a cell carrying three stale names beside one live one read as verified.
* **Last-component matching.** `known_declarations()` reduced every declaration
  to its final segment, so `Wrong.Namespace.Realized` resolved because some
  unrelated `Realized` exists somewhere in the tree.

The name capture had the third defect already fixed in `check_print_axioms.py`
and pinned by `test_public_theorem_regex.py`: an ASCII character class truncates
subscripted names, putting `F` into the declared set in place of
`F₁_of_compatible`. A checker whose vocabulary is wrong fails open in both
directions -- it accepts a name no declaration has, and rejects one that exists.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from check_wolpert_status_table import (  # noqa: E402
    DECL_LINE_RE,
    EXAMPLES,
    known_declarations,
    resolves,
)

DECLARED = known_declarations()


def _name(line: str) -> str | None:
    match = DECL_LINE_RE.match(line)
    return match.group(1) if match else None


def test_declarations_are_fully_qualified() -> None:
    assert all(isinstance(entry, tuple) for entry in DECLARED)
    assert any(len(entry) > 1 for entry in DECLARED)


def test_bare_name_resolves() -> None:
    assert resolves("not_stronglyInfers_self", DECLARED)


def test_dotted_suffix_resolves() -> None:
    assert resolves("InferenceDevice.Realized", DECLARED)


def test_full_path_resolves() -> None:
    assert resolves("AISafetyAtlas.Inference.InferenceDevice.Realized", DECLARED)


def test_wrong_prefix_is_rejected() -> None:
    """The defect: last-component matching accepted this."""
    assert not resolves("Wrong.Namespace.Realized", DECLARED)
    assert not resolves("Bogus.not_stronglyInfers_self", DECLARED)


def test_absent_name_is_rejected() -> None:
    assert not resolves("no_such_declaration_anywhere", DECLARED)


def test_subscripted_name_is_captured() -> None:
    assert _name("public theorem F₁_of_compatible {x : Pair S A}") == "F₁_of_compatible"


def test_primed_name_is_captured() -> None:
    assert _name("public theorem inv_complexity' :") == "inv_complexity'"
    assert _name("public theorem inv_complexity :") != _name(
        "public theorem inv_complexity' :"
    )


def test_subscripted_declarations_reach_the_declared_set() -> None:
    """`F₁_of_compatible` exists; the ASCII-class form recorded `F` instead."""
    assert resolves("F₁_of_compatible", DECLARED)
    assert not resolves("F", DECLARED)


def test_declaration_keywords() -> None:
    assert _name("public noncomputable def rowSpinDevice (sp : I → J → Bool)") == (
        "rowSpinDevice"
    )
    assert _name("@[expose] public def StronglyInfersPair (C : X)") == (
        "StronglyInfersPair"
    )
    assert _name("public abbrev gridPurple : Fin 2 → Fin 2 → Bool") == "gridPurple"
    assert _name("public structure InferenceDevice (U : Type u) where") == (
        "InferenceDevice"
    )


def test_example_five_declarations_exist() -> None:
    """Example 5 is the one worked example graded as a claim, so it owns Lean."""
    assert EXAMPLES["5"] == "SOURCE-EXACT"
    for name in (
        "rowSpinDevice",
        "colSpinDevice",
        "rowSpinDevice_distinguishable_colSpinDevice",
        "rowSpinDevice_infersDevice_colSpinDevice",
        "not_colSpinDevice_infersDevice_rowSpinDevice",
    ):
        assert resolves(name, DECLARED), name


def test_other_examples_state_no_claim() -> None:
    assert {number for number, status in EXAMPLES.items() if status == "INTERPRETATION"} == {
        "1",
        "2",
        "3",
        "4",
        "6",
    }
