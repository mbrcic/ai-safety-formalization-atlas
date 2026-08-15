"""The public-theorem scanner must not silently drop declarations.

`check_print_axioms.py` derives the entire axiom-checked surface from one
regex. Two silent defects lived in its earlier `([A-Za-z0-9_'.]+)\\b` form, and
both were found only when a new declaration happened to collide:

* **Trailing prime.** `foo'` has no word boundary after the quote, so the match
  backtracked to `foo`. A file with both `foo` and `foo'` then produced a
  spurious "duplicate declarations" error, and on any other file one of the two
  was checked twice while the other was never checked at all.
* **Subscripts.** `F₁_of_compatible` could not be matched: the ASCII class stops
  at `F`, and `\\b` then fails because Python counts `₁` as a word character. Four
  such theorems in the Preference cluster were dropped from the scan entirely.

A scanner that drops declarations reports a clean axiom check over a surface
smaller than the one it claims to cover, which is the same failure mode as the
allowlist gate in `test_wolpert_2018_inventory.py`. These tests pin the shapes.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from check_print_axioms import PUBLIC_THEOREM_RE  # noqa: E402


def _name(line: str) -> str | None:
    match = PUBLIC_THEOREM_RE.match(line)
    return match.group(1) if match else None


def test_plain_name() -> None:
    assert _name("public theorem foo :") == "foo"


def test_trailing_prime_is_kept() -> None:
    assert _name("public theorem inv_complexity' :") == "inv_complexity'"


def test_prime_and_plain_name_stay_distinct() -> None:
    assert _name("public theorem inv_complexity :") != _name(
        "public theorem inv_complexity' :"
    )


def test_interior_prime() -> None:
    assert _name("public theorem fig6_mass_X'_true :") == "fig6_mass_X'_true"


def test_subscript_is_matched() -> None:
    assert _name("public theorem F₁_of_compatible {x : Pair S A}") == "F₁_of_compatible"


def test_subscripts_stay_distinct() -> None:
    names = {
        _name(f"public theorem F{sub}_of_compatible {{x : Pair S A}}")
        for sub in ("₁", "₂", "₃")
    }
    assert len(names) == 3


def test_stops_at_every_delimiter() -> None:
    assert _name("public theorem foo (x : Nat) :") == "foo"
    assert _name("public theorem foo {x : Nat} :") == "foo"
    assert _name("public theorem foo [Inst] :") == "foo"
    assert _name("public theorem foo :=") == "foo"
    assert _name("public lemma bar.baz :") == "bar.baz"


def test_greek_names_are_matched() -> None:
    assert _name("public theorem αβ_lemma :") == "αβ_lemma"


def test_non_public_is_not_matched() -> None:
    assert _name("private theorem foo :") is None
    assert _name("theorem foo :") is None
