#!/usr/bin/env python3
"""Cross-check grade claims in Lean prose against ``conjectures.yaml``.

Twice a module docstring shipped green while
asserting a scope grade the ledger did not hold: once claiming a quantifier
convention was a widening when the neighbouring docstring called it print's own,
and once saying MAIS-O25 was ``Mixed`` after ``conjectures.yaml`` had recorded
``Same``.  Neither is visible to the other validators: they check syntax,
references, schema and generated views, and a prose sentence that contradicts a
YAML field is well formed on both sides.

This closes that class.  A conjecture's docstring may narrate its grading
history freely — *"had been graded ``Mixed``"* is a fact about the past — but a
sentence asserting what the grade **is** must agree with the ledger.  The
patterns below match present-tense assertions only; the guards drop the
retrospective and hypothetical forms that surround them.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = ROOT / "AISafetyAtlas"

SCOPE_VALUES = {"Same", "Narrower", "Mixed", "Retired", "Beyond"}
FIDELITY_VALUES = {
    "Literal",
    "Selected",
    "Bridged",
    "DetermineProblem",
    "AtlasOriginal",
}
GRADE_VALUES = SCOPE_VALUES | FIDELITY_VALUES
GRADE_RE = "|".join(sorted(GRADE_VALUES))

# Present-tense assertions of the grade a row currently carries.
ASSERTIONS = [
    re.compile(r"`conjectures\.yaml`[^.`]{0,80}?grades[^.`]{0,60}?`(" + GRADE_RE + r")`"),
    re.compile(r"\bthe grade (?:at|to|is) `(" + GRADE_RE + r")`"),
    re.compile(r"\bkeeps? the (?:grade|row) (?:at )?`(" + GRADE_RE + r")`"),
    re.compile(r"\bstays? `(" + GRADE_RE + r")`"),
    re.compile(r"\bremains? `(" + GRADE_RE + r")`"),
    re.compile(r"\bthis row is `(" + GRADE_RE + r")`"),
    re.compile(r"\bis graded `(" + GRADE_RE + r")`"),
    re.compile(r"\bgrades (?:it|this row|the row|this entry) `(" + GRADE_RE + r")`"),
    re.compile(r"\bthe row (?:is|carries) `(" + GRADE_RE + r")`"),
]

# A window before the match that makes it retrospective or hypothetical rather
# than an assertion about the current grade.
GUARDS = re.compile(
    r"had been|has been|was |were |previously|no longer|rather than|"
    r"instead of|would |could |cannot |is not |are not |not `|from `|"
    r"if it |so that |which would",
    re.IGNORECASE,
)
GUARD_WINDOW = 300

# "until" is deliberately absent from the guards. *"Until X lands, the row
# stays `Mixed`"* asserts what the grade **is** — the conditional is about when
# it will change, not about whether it holds now — and the sentence that
# shipped stale in `Causal.Query` had exactly that shape.

# The guards must read the *current* sentence only.  A window of fixed width
# crosses into the previous one, where an unrelated "rather than" silently
# excuses the claim that follows it — which is how the first version of this
# check passed the very docstring it was written for.
SENTENCE_BREAK = re.compile(r"(?<=[.!?])\s+|\n\n")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:public |private |protected )*"
    r"(?:noncomputable )?(?:def|theorem|abbrev|structure|inductive|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)",
    re.MULTILINE,
)


def load_ledger() -> dict[str, dict[str, object]]:
    data = yaml.safe_load((ROOT / "conjectures.yaml").read_text(encoding="utf-8"))
    return {c["id"]: c for c in data["conjectures"]}


def grades_of(entry: dict[str, object]) -> set[str]:
    fidelity = entry.get("source_fidelity")
    if isinstance(fidelity, str):
        fidelity_list: list[object] = [fidelity]
    elif isinstance(fidelity, list):
        fidelity_list = list(fidelity)
    else:
        fidelity_list = []
    scope = entry.get("source_scope")
    return {str(scope), *(str(f) for f in fidelity_list)}


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


# --- the ledger's own notes ------------------------------------------------
#
# `source_note` is prose sitting in the same YAML object as `source_scope` and
# `source_fidelity`, and it narrates grading history at length. That makes it
# the easiest place in the repository for a sentence to outlive the field it
# describes: on 2026-08-21 CONJ-006 gained `Bridged` and its note went on saying
# *"Fidelity stays Selected and is no longer Bridged"* in the same string.
#
# Positive claims must name a grade the row holds; negative claims must not.
# The vocabulary words are matched case-sensitively because "same" is ordinary
# English and `Same` is not.

NOTE_POSITIVE = [
    re.compile(r"\b(?:Fidelity|FIDELITY) (?:stays|is|carries|remains) (" + GRADE_RE + r")\b"),
    re.compile(r"\b(?:Scope|SCOPE) (?:stays|is|remains) (" + GRADE_RE + r")\b"),
    re.compile(r"\bThis row is (" + GRADE_RE + r")\b"),
    re.compile(r"\bthe row (?:is|stays|remains) (" + GRADE_RE + r")\b"),
]

NOTE_NEGATIVE = [
    re.compile(r"\bis no longer (" + GRADE_RE + r")\b"),
    re.compile(r"\bare no longer (" + GRADE_RE + r")\b"),
    re.compile(r"\bno longer (?:graded|carries) (" + GRADE_RE + r")\b"),
]


def check_notes(ledger: dict[str, dict[str, object]]) -> tuple[list[str], int]:
    """Claims a `source_note` makes about the grades of its own row."""
    failures: list[str] = []
    checked = 0
    for cid, entry in ledger.items():
        note = entry.get("source_note")
        if not isinstance(note, str):
            continue
        held = grades_of(entry)
        for pattern in NOTE_POSITIVE:
            for match in pattern.finditer(note):
                checked += 1
                if match.group(1) in held:
                    continue
                failures.append(
                    f"conjectures.yaml: {cid} source_note asserts "
                    f"`{match.group(1)}` for itself, but the row records "
                    f"scope={entry['source_scope']} "
                    f"fidelity={entry['source_fidelity']}\n"
                    f"    {match.group(0)}"
                )
        for pattern in NOTE_NEGATIVE:
            for match in pattern.finditer(note):
                checked += 1
                if match.group(1) not in held:
                    continue
                failures.append(
                    f"conjectures.yaml: {cid} source_note denies "
                    f"`{match.group(1)}`, which the row holds: "
                    f"scope={entry['source_scope']} "
                    f"fidelity={entry['source_fidelity']}\n"
                    f"    {match.group(0)}"
                )
    return failures, checked


# --- graded Markdown tables ------------------------------------------------
#
# `source-coverage-audit.md` grades a printed statement per row: a `Cov.` cell,
# a `Scope` cell, and a note cell that argues for them. Three of the five
# observed findings were a note and its own cell disagreeing, or
# a summary sentence quantifying over rows whose cells had since moved:
#
#   * Pearl's Property 2 read `Same` while its note said, in the same cell, that
#     the hypothesis is weaker than print's and the conclusion the same;
#   * the policy row read `Narrower` while its note described a widening;
#   * "every `Yes` row below therefore reads `Narrower`" outlived the policy row
#     going `Mixed`.
#
# The first two are a cell-versus-note diff. The third is a universal claim
# about a row set that can be recomputed. Both are checked here.

TABLE_ROW = re.compile(r"^\|(?P<cells>.+)\|\s*$")
SECTION_HEAD = re.compile(r"^## +\d+\. +(?P<name>.+?)\s*$")

AUDIT_SCOPES = {"Same", "Narrower", "Wider", "Mixed", "Beyond"}
AUDIT_SCOPE_RE = "|".join(sorted(AUDIT_SCOPES))

# What a note says the row *is*. Deliberately narrow: notes argue at length and
# most sentences are about print, not about the grade.
NOTE_VERDICT = [
    re.compile(r"\bis a widening\b", re.I),
    re.compile(r"\bthat is a widening\b", re.I),
    re.compile(r"\bweaker than print's\b", re.I),
    re.compile(r"\bwider than print\b", re.I),
]

# A universal claim about the rows below it.
UNIVERSAL = re.compile(
    r"[Ee]very `?(?P<cov>Yes|No|Partial)`? row[^.]{0,120}?"
    r"(?:reads|is|are) `?(?P<scope>" + AUDIT_SCOPE_RE + r")`?",
)

# "…, except the policy row, which reads `Mixed`" is a legitimate exception and
# names the grade it excepts, so the claim is checked against the union.
EXCEPTION = re.compile(r"except[^.]{0,160}?`(" + AUDIT_SCOPE_RE + r")`")


def split_cells(line: str) -> list[str]:
    r"""Markdown row cells, honouring an escaped pipe inside a cell."""
    body = line.strip()
    body = body[1:] if body.startswith("|") else body
    body = body[:-1] if body.endswith("|") else body
    out, cur, i = [], "", 0
    while i < len(body):
        if body[i] == "\\" and i + 1 < len(body) and body[i + 1] == "|":
            cur += "|"
            i += 2
            continue
        if body[i] == "|":
            out.append(cur.strip())
            cur = ""
            i += 1
            continue
        cur += body[i]
        i += 1
    out.append(cur.strip())
    return out


def audit_rows(text: str) -> list[tuple[int, str, str, str, str]]:
    """`(line, section, coverage, scope, note)` for each graded row."""
    rows: list[tuple[int, str, str, str, str]] = []
    section = "?"
    for num, line in enumerate(text.splitlines(), start=1):
        head = SECTION_HEAD.match(line)
        if head:
            section = head.group("name")
            continue
        if not TABLE_ROW.match(line):
            continue
        cells = split_cells(line)
        if len(cells) < 6:
            continue
        scope_cell = cells[4].strip().strip("*").strip()
        if scope_cell not in AUDIT_SCOPES:
            continue
        coverage = cells[3].strip().strip("*").strip()
        rows.append((num, section, coverage, scope_cell, cells[5]))
    return rows


def check_audit(audit_path: Path) -> tuple[list[str], int]:
    """A row's note against its own `Scope` cell, and universal claims."""
    if not audit_path.is_file():
        return [], 0
    text = audit_path.read_text(encoding="utf-8")
    rel = audit_path.name
    failures: list[str] = []
    checked = 0
    rows = audit_rows(text)

    for num, _section, _coverage, scope, note in rows:
        for pattern in NOTE_VERDICT:
            if not pattern.search(note):
                continue
            checked += 1
            if scope in {"Wider", "Mixed", "Beyond"}:
                continue
            failures.append(
                f"{rel}:{num}: the note says the atlas is wider than print "
                f"(\"{pattern.pattern}\"), but the Scope cell reads `{scope}`. "
                "A widening is `Wider`, or `Mixed` when the row narrows too."
            )

    # Universal claims are recomputed against the rows of their own section.
    section = "?"
    for num, line in enumerate(text.splitlines(), start=1):
        head = SECTION_HEAD.match(line)
        if head:
            section = head.group("name")
        for match in UNIVERSAL.finditer(line):
            checked += 1
            claimed = {match.group("scope")}
            tail = line[match.end():] + " " + "\n".join(
                text.splitlines()[num : num + 3]
            )
            claimed |= {m.group(1) for m in EXCEPTION.finditer(tail)}
            cov = match.group("cov")
            actual = {
                sc
                for n, sec, coverage, sc, _ in rows
                if sec == section and n > num and coverage == cov
            }
            if not actual or actual <= claimed:
                continue
            failures.append(
                f"{rel}:{num}: claims every `{cov}` row below reads "
                f"{sorted(claimed)}, but those rows read {sorted(actual)}.\n"
                f"    {match.group(0).strip()}"
            )
    return failures, checked


def main() -> int:
    ledger = load_ledger()

    # module -> {declaration basename -> conjecture id}
    by_module: dict[str, dict[str, str]] = {}
    for cid, entry in ledger.items():
        full = str(entry["lean"])
        module, _, basename = full.rpartition(".")
        by_module.setdefault(module, {})[basename] = cid

    failures: list[str] = []
    # Several patterns match the same sentence — "keeps the grade at `Mixed`"
    # is both a *keeps* claim and a *the grade at* claim — so a hit is keyed by
    # what it says about which row, not by which pattern found it.
    seen: set[tuple[str, int, str, str]] = set()
    checked = 0

    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        module = module_of(path)
        # Every module is scanned, not only the two that declare conjectures.
        # The stalest claim this check was written for lived in
        # `Causal.Query` — "CONJ-003 and CONJ-006 stay `Mixed`" — in a file
        # with no conjecture declaration in it, so a scan restricted to the
        # declaring modules would have walked straight past it. Elsewhere a
        # claim has to name its row explicitly to be actionable, which the
        # attribution below already requires.
        decls = by_module.get(module, {})
        text = path.read_text(encoding="utf-8")

        # Offset of each graded conjecture declaration, so a claim can be
        # attributed to the row whose declaration follows it.
        anchors = sorted(
            (m.start(), decls[m.group(1)])
            for m in DECL_RE.finditer(text)
            if m.group(1) in decls
        )

        for pattern in ASSERTIONS:
            for match in pattern.finditer(text):
                window = text[max(0, match.start() - GUARD_WINDOW) : match.start()]
                before = SENTENCE_BREAK.split(window)[-1]
                if GUARDS.search(before):
                    continue
                claimed = match.group(1)

                explicit = re.findall(
                    r"CONJ-\d+", text[max(0, match.start() - 400) : match.end() + 400]
                )
                if explicit:
                    targets = [c for c in dict.fromkeys(explicit) if c in ledger]
                else:
                    following = [cid for off, cid in anchors if off >= match.end()]
                    if not following:
                        continue
                    targets = [following[0]]

                line = text.count("\n", 0, match.start()) + 1
                for cid in targets:
                    key = (str(path.relative_to(ROOT)), line, cid, claimed)
                    if key in seen:
                        continue
                    seen.add(key)
                    checked += 1
                    held = grades_of(ledger[cid])
                    if claimed in held:
                        continue
                    # A claim naming a vocabulary the row's other axis owns is
                    # only a contradiction against that axis.
                    failures.append(
                        f"{path.relative_to(ROOT)}:{line}: prose asserts "
                        f"`{claimed}` for {cid}, but conjectures.yaml records "
                        f"scope={ledger[cid]['source_scope']} "
                        f"fidelity={ledger[cid]['source_fidelity']}\n"
                        f"    {match.group(0).strip()}"
                    )

    note_failures, note_checked = check_notes(ledger)
    failures.extend(note_failures)
    checked += note_checked

    audit_failures, audit_checked = check_audit(
        ROOT / "docs" / "provenance" / "source-coverage-audit.md"
    )
    failures.extend(audit_failures)
    checked += audit_checked

    if failures:
        print("conjecture grade prose contradicts the ledger:\n")
        for failure in failures:
            print(f"  {failure}")
        print(
            "\nEither the prose is stale or the ledger is. Fix the one that is "
            "wrong; do not delete the sentence to silence this."
        )
        return 1

    print(f"conjecture grade prose ok: {checked} claim(s) agree with the ledger")
    return 0


if __name__ == "__main__":
    sys.exit(main())
