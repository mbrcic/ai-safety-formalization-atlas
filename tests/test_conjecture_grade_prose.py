"""Regression tests for `scripts/check_conjecture_grade_prose.py`.

The check exists because two module docstrings
asserted a scope grade `conjectures.yaml` did not hold, and shipped green: every
other validator reads syntax, references, schema or generated views, and a
sentence disagreeing with a YAML field is well formed on both sides.

Its first two versions each passed the very sentence they were written for, so
both real sentences are pinned here verbatim:

* *"The axis that keeps the grade at `Mixed` is the estimator's output law"* —
  missed because a fixed-width guard window reached back into the previous
  sentence and found an unrelated *"rather than"*.
* *"Until then CONJ-003 and CONJ-006 stay `Mixed`"* — missed twice, first
  because the scan visited only the modules that declare conjectures and this
  one lives in `Causal.Query`, then because `until` was in the guard list. A
  deadline for when a grade will change is an assertion about what it is now.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"


def _load(name: str):
    if str(SCRIPTS) not in sys.path:
        sys.path.insert(0, str(SCRIPTS))
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


prose = _load("check_conjecture_grade_prose")


def _claims(text: str) -> list[str]:
    """Every grade a sentence asserts, after the retrospective guards."""
    found: list[str] = []
    for pattern in prose.ASSERTIONS:
        for match in pattern.finditer(text):
            window = text[max(0, match.start() - prose.GUARD_WINDOW) : match.start()]
            before = prose.SENTENCE_BREAK.split(window)[-1]
            if prose.GUARDS.search(before):
                continue
            found.append(match.group(1))
    return found


# --- the repository's own prose agrees with the ledger -------------------------


def test_check_passes_on_the_repository():
    assert prose.main() == 0


def test_the_ledger_is_read_as_both_axes():
    """Every live row yields a scope grade and at least one fidelity grade.

    This asserted a specific grade for a specific row until 2026-08-21, which
    coupled a checker test to ledger *data*: regrading CONJ-003 broke it, and
    the break said nothing about the checker. The invariant worth testing is
    that both axes are read for every row, whatever the grades happen to be.
    """
    ledger = prose.load_ledger()
    assert ledger
    for row_id, row in ledger.items():
        grades = prose.grades_of(row)
        assert grades & prose.SCOPE_VALUES, row_id
        assert grades & prose.FIDELITY_VALUES, row_id


def test_a_fidelity_list_is_read_element_by_element():
    grades = prose.grades_of(
        {"source_scope": "Same", "source_fidelity": ["Literal", "Bridged"]}
    )
    assert grades == {"Same", "Literal", "Bridged"}


# --- the two sentences that shipped stale --------------------------------------


def test_the_o25_sentence_is_caught():
    text = (
        "`binaryDim` replaces the old general `dim` with an `IsBinaryDimension` "
        "hypothesis, which is print's own restriction stated in the type rather "
        "than carried as an antecedent.\n\n"
        "**The axis that keeps the grade at `Mixed` is the estimator's output law.**"
    )
    assert _claims(text) == ["Mixed", "Mixed"]


def test_the_query_sentence_is_caught():
    text = "Until then CONJ-003 and CONJ-006 stay `Mixed`."
    assert _claims(text) == ["Mixed"]


# --- and the narration around them is not --------------------------------------


def test_retrospective_narration_is_left_alone():
    assert _claims("It had been graded `Mixed`, narrower on three axes.") == []
    assert _claims("The row is no longer `Narrower`.") == []
    assert _claims("A tighter reading would make the grade `Same`.") == []


def test_a_guard_does_not_reach_across_a_sentence_boundary():
    guarded = "The threshold is supplied rather than derived. It stays `Mixed`."
    assert _claims(guarded) == ["Mixed"]


# --- the ledger's own notes ----------------------------------------------------


def _note(cid: str, note: str, scope: str, fidelity) -> list[str]:
    ledger = {cid: {"source_scope": scope, "source_fidelity": fidelity,
                    "source_note": note, "lean": "X.Y"}}
    failures, _ = prose.check_notes(ledger)
    return failures


def test_a_note_denying_a_tag_the_row_holds_is_caught():
    """The sentence CONJ-006 shipped with on 2026-08-21, verbatim."""
    note = "Fidelity stays Selected and is no longer Bridged: prob:exact says ..."
    assert _note("CONJ-006", note, "Same", ["Selected", "Bridged"])


def test_a_note_asserting_a_grade_the_row_lacks_is_caught():
    assert _note("CONJ-006", "Fidelity stays Literal.", "Same", ["Selected"])


def test_a_note_agreeing_with_its_row_passes():
    note = "Fidelity carries Selected. SCOPE STAYS Same. Bridged is the eps0 reading."
    assert _note("CONJ-006", note, "Same", ["Selected", "Bridged"]) == []


def test_a_note_denying_a_tag_the_row_does_not_hold_passes():
    """Narrating a tag that was removed is a fact about the past, not a defect."""
    note = "This row is no longer Mixed."
    assert _note("CONJ-006", note, "Same", ["Selected"]) == []


def test_lowercase_same_is_ordinary_english():
    """"the same day" must not read as a grade claim."""
    note = "Regraded the same day, for the same reason. Fidelity stays Selected."
    assert _note("CONJ-006", note, "Same", ["Selected"]) == []


# --- graded Markdown tables ----------------------------------------------------

AUDIT = ROOT / "docs" / "provenance" / "source-coverage-audit.md"


def _audit(text: str) -> list[str]:
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "source-coverage-audit.md"
        path.write_text(text, encoding="utf-8")
        failures, _ = prose.check_audit(path)
    return failures


HEADER = "| # | printed statement | atlas | Cov. | Scope | note |\n|---|---|---|---|---|---|\n"


def test_the_repository_audit_is_consistent():
    failures, _ = prose.check_audit(AUDIT)
    assert failures == []


def test_a_note_describing_a_widening_under_a_Same_cell_is_caught():
    """Pearl's Property 2, which read `Same` for as long as the row existed."""
    text = "## 7. Pearl → `A.B`\n\n" + HEADER + (
        "| Property 2 | print's statement | `A.B.thm` | Yes | **Same** | "
        "the hypothesis is weaker than print's and the conclusion the same |\n"
    )
    assert _audit(text)


def test_the_same_note_under_a_Wider_cell_passes():
    text = "## 7. Pearl → `A.B`\n\n" + HEADER + (
        "| Property 2 | print's statement | `A.B.thm` | Yes | **Wider** | "
        "the hypothesis is weaker than print's and the conclusion the same |\n"
    )
    assert _audit(text) == []


def test_a_universal_claim_outliving_a_regrade_is_caught():
    """"every `Yes` row reads `Narrower`" after the policy row went `Mixed`."""
    text = "## 8. Everitt → `A.B`\n\nEvery `Yes` row below therefore reads `Narrower`.\n\n" + HEADER + (
        "| Def. 1 | x | `A.B.one` | Yes | **Narrower** | finite |\n"
        "| policy | x | `A.B.two` | Yes | **Mixed** | both directions |\n"
    )
    assert _audit(text)


def test_a_universal_claim_naming_its_exception_passes():
    text = (
        "## 8. Everitt → `A.B`\n\nEvery `Yes` row below therefore reads "
        "`Narrower`, except the policy row, which reads `Mixed`.\n\n" + HEADER + (
            "| Def. 1 | x | `A.B.one` | Yes | **Narrower** | finite |\n"
            "| policy | x | `A.B.two` | Yes | **Mixed** | both directions |\n"
        )
    )
    assert _audit(text) == []


def test_a_universal_claim_is_checked_against_its_own_coverage_column():
    """A `Beyond` row with no `Yes` coverage must not falsify a claim about `Yes` rows."""
    text = (
        "## 8. Everitt → `A.B`\n\nEvery `Yes` row below therefore reads `Narrower`.\n\n"
        + HEADER + (
            "| Def. 1 | x | `A.B.one` | Yes | **Narrower** | finite |\n"
            "| — | x | `A.B.extra` | — | **Beyond** | atlas original |\n"
        )
    )
    assert _audit(text) == []


def test_every_vocabulary_word_is_matched():
    for value in prose.GRADE_VALUES:
        assert _claims(f"The row stays `{value}`.") == [value]
