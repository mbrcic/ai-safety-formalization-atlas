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

from check_print_axioms import PUBLIC_DEF_RE, PUBLIC_THEOREM_RE  # noqa: E402


def _name(line: str) -> str | None:
    match = PUBLIC_THEOREM_RE.match(line)
    return match.group(1) if match else None


def _def_name(line: str) -> str | None:
    match = PUBLIC_DEF_RE.match(line)
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


# --- Leading attributes -----------------------------------------------------
#
# The tests above pin the *name* grammar exhaustively and never once varied what
# precedes `public`. That is exactly the shape the scanner got wrong: without an
# `@[…]` prefix group, `@[simp] public theorem` matches nothing and every
# attributed theorem drops out of the axiom audit in silence. An example suite is
# only as good as the axes it varies.


def test_simp_attribute_does_not_hide_a_theorem() -> None:
    assert _name("@[simp] public theorem binaryState_true :") == "binaryState_true"


def test_fun_prop_attribute_does_not_hide_a_theorem() -> None:
    assert _name("@[fun_prop] public theorem measurable_setup :") == "measurable_setup"


def test_attribute_with_several_entries() -> None:
    assert _name("@[simp, norm_cast] public lemma foo :") == "foo"


def test_attribute_with_arguments() -> None:
    assert _name("@[deprecated (since := \"2026-01-01\")] public theorem foo :") == "foo"


def test_indented_attribute() -> None:
    assert _name("  @[simp] public theorem foo :") == "foo"


def test_attribute_alone_is_still_not_a_public_theorem() -> None:
    assert _name("@[simp] theorem foo :") is None
    assert _name("@[simp] private theorem foo :") is None


# --- The two patterns must agree on what may precede `public` ---------------


def test_both_patterns_accept_the_same_prefixes() -> None:
    """The invariant the bug violated, stated once instead of example by example.

    `PUBLIC_DEF_RE` always admitted a leading attribute and `PUBLIC_THEOREM_RE`
    did not. Nothing compared them, so the asymmetry survived every test in this
    file. Whatever prefix one pattern accepts, the other must accept too --
    they are collecting one surface, not two.
    """
    for prefix in ("", "@[simp] ", "@[simp, norm_cast] ", "  ", "  @[fun_prop] "):
        assert _name(f"{prefix}public theorem foo :") == "foo", prefix
        assert _def_name(f"{prefix}public def foo :") == "foo", prefix


# --- Keywords the definition scan collects ---------------------------------


def test_instance_and_inductive_are_collected() -> None:
    """Both belong in the definition scan; see `PUBLIC_DEF_RE` for why.

    A named `public instance` can carry a `Prop`-valued field and so can hide a
    `sorry` exactly as a `def` can.
    """
    assert _def_name("public instance decidableRealized {m n : ℕ}") == "decidableRealized"
    assert _def_name("public inductive Principal") == "Principal"
    assert _def_name("public structure PairModel where") == "PairModel"
    assert _def_name("public noncomputable def f :") == "f"
    assert _def_name("public scoped instance instFoo : Foo") == "instFoo"
    assert _def_name("public noncomputable scoped instance instBar : Bar") == "instBar"


def test_anonymous_instance_has_no_name_to_collect() -> None:
    """Deliberate, and the reason `check_audit_coverage.py` exempts instances.

    `public instance : Fintype X` names nothing, so no text pattern can collect
    it; Lean names it. Its axioms are checked from the environment instead.
    """
    assert _def_name("public instance : Fintype X where") is None
