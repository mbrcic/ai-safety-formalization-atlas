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


# --- grade claims outside Lean -------------------------------------------------


def _markdown(text: str, ledger: dict[str, dict[str, object]]) -> list[str]:
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "current.md"
        path.write_text(text, encoding="utf-8")
        failures, _ = prose.check_markdown(ledger, [path])
    return failures


def test_markdown_claim_disagreeing_with_ledger_is_caught():
    ledger: dict[str, dict[str, object]] = {
        "CONJ-003": {
            "source_scope": "Same",
            "source_fidelity": "Literal",
        }
    }
    assert _markdown("CONJ-003 is graded `Narrower`.", ledger)


def test_markdown_historical_grade_is_not_a_current_claim():
    ledger: dict[str, dict[str, object]] = {
        "CONJ-003": {
            "source_scope": "Same",
            "source_fidelity": "Literal",
        }
    }
    assert _markdown("CONJ-003 had been graded `Narrower`.", ledger) == []


def test_superseded_markdown_archive_is_skipped():
    ledger: dict[str, dict[str, object]] = {
        "CONJ-003": {
            "source_scope": "Same",
            "source_fidelity": "Literal",
        }
    }
    text = (
        "> **Superseded.** Nothing here states a current grade.\n\n"
        "CONJ-003 is graded `Narrower`."
    )
    assert _markdown(text, ledger) == []


def test_every_vocabulary_word_is_matched():
    for value in prose.GRADE_VALUES:
        assert _claims(f"The row stays `{value}`.") == [value]


# --- the coverage table's own cells, and the counts quoted in public prose -----
#
# Three defects shipped green on 2026-08-23 that no pattern above could see,
# because none of them names a `CONJ-###` row anywhere near the claim:
#
#   * the coverage table's O26 row read *"graded `Same`"* while the ledger had
#     recorded `Narrower` for a day — the cell names `maisO26_exactRate`, not
#     the row;
#   * its Counts bullet read *"all four at `Same` scope"* and named no row at
#     all;
#   * `site/index.html` read *"five open, four resolved … one withdrawn"* after
#     the ledger had dropped to four and zero.
#
# The table now carries explicit `Ledger` and `Scope` columns so the first two
# are machine-comparable, and the counts are recomputed from the ledger.


def _ledger() -> dict:
    return prose.load_ledger()


def test_coverage_row_disagreeing_with_the_ledger_is_caught(tmp_path):
    table = tmp_path / "coverage.md"
    table.write_text(
        "| ID | Ledger | Scope | Lean statement status |\n"
        "|---|---|---|---|\n"
        "| O26 | `CONJ-003` | `Narrower` | **Statement only** |\n",
        encoding="utf-8",
    )
    failures, checked = prose.check_mais_coverage(_ledger(), table)
    assert checked
    assert any("CONJ-003" in f and "Narrower" in f for f in failures)


def test_coverage_row_prose_disagreeing_with_its_own_cell_is_caught(tmp_path):
    """The exact shape of the O26 defect: cell right, prose in the row stale."""
    table = tmp_path / "coverage.md"
    table.write_text(
        "| ID | Ledger | Scope | Lean statement status |\n"
        "|---|---|---|---|\n"
        "| O26 | `CONJ-003` | `Same` | **Statement only, graded `Narrower`** |\n",
        encoding="utf-8",
    )
    failures, _ = prose.check_mais_coverage(_ledger(), table)
    assert any("graded" in f and "Scope cell" in f for f in failures)


def test_universal_scope_claim_is_recomputed_from_the_rows(tmp_path):
    """*"all four at `Same` scope"* over a table one of whose rows is not."""
    table = tmp_path / "coverage.md"
    table.write_text(
        "| ID | Ledger | Scope | Lean statement status |\n"
        "|---|---|---|---|\n"
        "| O23 | `CONJ-004` | `Same` | **Resolved** |\n"
        "| O26 | `CONJ-003` | `Same` | **Statement only** |\n"
        "\n"
        "- Four source targets have complete propositions, all four at `Beyond` scope.\n",
        encoding="utf-8",
    )
    failures, _ = prose.check_mais_coverage(_ledger(), table)
    assert any("claims every graded row is `Beyond`" in f for f in failures)


def test_target_with_no_ledger_row_may_not_carry_a_grade(tmp_path):
    table = tmp_path / "coverage.md"
    table.write_text(
        "| ID | Ledger | Scope | Lean statement status |\n"
        "|---|---|---|---|\n"
        "| O27 | — | `Retired` | **Withdrawn encoding** |\n",
        encoding="utf-8",
    )
    failures, _ = prose.check_mais_coverage(_ledger(), table)
    assert any("no ledger row" in f for f in failures)


def test_stale_public_counts_are_caught(tmp_path):
    """The `site/index.html` sentence as it stood, against the live ledger."""
    page = tmp_path / "index.html"
    page.write_text(
        "<p>five open, four resolved by linked Lean theorems, one withdrawn.</p>",
        encoding="utf-8",
    )
    failures, checked, skipped = prose.check_counts(_ledger(), (page,))
    assert checked
    assert any("open" in f for f in failures)
    assert any("withdrawn" in f for f in failures)


def test_live_counts_pass(tmp_path):
    # The counts are over *conjecture* rows -- kind claim or answer -- because
    # that is what the prose these patterns match is about. Counting the target
    # and blocked rows the ledger gained on 2026-08-24 would make every sentence
    # in the guide fail at once while saying nothing truer about them.
    ledger = {
        cid: row
        for cid, row in _ledger().items()
        if row.get("kind", "claim") in {"claim", "answer"}
    }
    opened = sum(e["status"] == "OPEN" for e in ledger.values())
    resolved = sum(e["status"] == "RESOLVED" for e in ledger.values())
    page = tmp_path / "index.html"
    page.write_text(f"<p>{opened} open and {resolved} resolved.</p>", encoding="utf-8")
    failures, checked, skipped = prose.check_counts(ledger, (page,))
    assert checked and not failures


# --- a capitalised sentence start is still an assertion ------------------------


def test_capitalised_row_verdict_is_an_assertion():
    """*"This row is `Same`."* — the sentence that shipped stale in the audit.

    Every pattern was case-sensitive and written lowercase, so the one form a
    Markdown sentence actually takes was the one form none of them matched.
    """
    assert _claims("This row is `Same`.") == ["Same"]
    assert _claims("The row is `Narrower` on one axis.") == ["Narrower"]


def test_mais_scoped_counts_are_checked(tmp_path):
    """The `site/index.html` rewording of 2026-08-23 matched no count pattern.

    It replaced "four open and four resolved" with a MAIS-scoped sentence, so
    the page's numbers went unchecked again on the same day the previous stale
    one was fixed. Three independent numbers are now read from the ledger.
    """
    ledger = _ledger()
    page = tmp_path / "index.html"
    page.write_text(
        "<p>ninety-nine MAIS-linked records. One have linked Lean proofs; "
        "the other twelve remain open.</p>",
        encoding="utf-8",
    )
    failures, checked, skipped = prose.check_counts(ledger, (page,))
    assert checked == 3
    # `mais_all` since 2026-08-24: "MAIS-linked records" counts rows of every
    # kind, while `mais` counts the conjectures among them. The two were the
    # same number until the ledger gained target and blocked rows.
    assert any("mais_all" == f.split("for ")[1].split(",")[0] for f in failures)
    assert any("mais_resolved" in f for f in failures)
    assert any("mais_open" in f for f in failures)


def test_live_site_counts_pass():
    """The page as it actually stands agrees with the ledger."""
    site = ROOT / "site" / "index.html"
    failures, checked, skipped = prose.check_counts(_ledger(), (site,))
    # Five numbers since 2026-08-24: the all-kinds row count and the count of
    # distinct printed problems joined the three conjecture-scoped ones, as the
    # sentence was rewritten first to say what the ledger holds and then to stop
    # claiming one row per problem, which was false while every number in the
    # same sentence was right.
    assert checked == 5, "the live sentence must stay in a checked shape"
    assert not failures
    assert not skipped


def test_hyphenated_number_word_is_parsed(tmp_path):
    """`twenty-one-row file` used to match no pattern at all.

    A bare `\\w+` slot cannot capture a hyphenated compound, so the sentence was
    skipped rather than compared -- and a skipped sentence produces the same
    silent success as an agreeing one. This is the denominator failure the
    `checked` assertions above exist for, caught one layer earlier.
    """
    page = tmp_path / "guide.md"
    page.write_text("This is a twenty-one-row file.", encoding="utf-8")
    failures, checked, skipped = prose.check_counts(_ledger(), (page,))
    assert checked == 1
    assert any("21" in f and "rows" in f for f in failures)


def test_ordinary_prose_is_not_reported_as_an_unparsed_count(tmp_path):
    """The wide slot catches sentences that were never counting anything.

    Reporting those as unchecked count claims is a false positive that trains a
    reader to ignore the report, which costs more than the hole it closes. Only
    tokens built from number words or digits are reported.
    """
    page = tmp_path / "guide.md"
    page.write_text(
        "The rest are determine-problem specifications.", encoding="utf-8"
    )
    failures, checked, skipped = prose.check_counts(_ledger(), (page,))
    assert not failures and not skipped and checked == 0
