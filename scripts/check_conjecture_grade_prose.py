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
MARKDOWN_ROOTS = (
    ROOT / "README.md",
    ROOT / "STATE.md",
    ROOT / "docs" / "guide",
    ROOT / "docs" / "provenance",
)

SCOPE_VALUES = {"Same", "Narrower", "Mixed", "Retired", "Beyond", "NotFormalized"}
FIDELITY_VALUES = {
    "Literal",
    "Selected",
    "Bridged",
    "DetermineProblem",
    "NotFormalized",
    "AtlasOriginal",
}
GRADE_VALUES = SCOPE_VALUES | FIDELITY_VALUES
GRADE_RE = "|".join(sorted(GRADE_VALUES))

# Present-tense assertions of the grade a row currently carries.
ASSERTIONS = [
    re.compile(r"`conjectures\.yaml`[^.`]{0,80}?grades[^.`]{0,60}?`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bthe grade (?:at|to|is) )`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bkeeps? the (?:grade|row) (?:at )?)`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bstays? )`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bremains? )`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bthis row is )`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bis graded )`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bgrades (?:it|this row|the row|this entry) )`(" + GRADE_RE + r")`"),
    re.compile(r"(?i:\bthe row (?:is|carries) )`(" + GRADE_RE + r")`"),
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

# A sentence that DENIES a grade the row actually holds. Every pattern above is
# an assertion, so all of them walk straight past `THE ROW IS NOT Same` sitting
# in a row graded `Same` -- which is exactly the sentence that survived in
# CONJ-006's `prior_art` through several passes and was quoted back by an
# external review as if it were the live grade.

# Fields read as the row's current rationale. `prior_art` is here because a
# retracted grade hid in it: `source_note` had carried a superseded-history
# marker for months and `prior_art` never did, so the field went unscanned while
# asserting the opposite of the row's own grade.
NOTE_FIELDS = ("source_note", "prior_art")

NOTE_NEGATIVE = [
    re.compile(r"\bis no longer (" + GRADE_RE + r")\b"),
    re.compile(r"\bare no longer (" + GRADE_RE + r")\b"),
    re.compile(r"\bno longer (?:graded|carries) (" + GRADE_RE + r")\b"),
    # A flat denial of a grade the row holds. The three above all read as a
    # *transition* -- "is no longer X" is true of a row that used to be X -- so
    # none of them fires on a sentence that simply says the row is not what it
    # is. That is the shape the defect took: `THE ROW IS NOT Same` sat in a row
    # graded `Same`, and an external review quoted it back as the live grade.
    re.compile(r"\b(?:THE ROW IS NOT|This row is not|the row is not) (" + GRADE_RE + r")\b"),
]


def check_notes(ledger: dict[str, dict[str, object]]) -> tuple[list[str], int]:
    """Claims a row's own rationale fields make about that row's grades."""
    failures: list[str] = []
    checked = 0
    for cid, entry in ledger.items():
      for field in NOTE_FIELDS:  # noqa: E111 -- narrow loop, body indent kept
        note = entry.get(field)
        if not isinstance(note, str):
            continue
        held = grades_of(entry)
        for pattern in NOTE_POSITIVE:
            for match in pattern.finditer(note):
                checked += 1
                if match.group(1) in held:
                    continue
                failures.append(
                    f"conjectures.yaml: {cid} {field} asserts "
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
                    f"conjectures.yaml: {cid} {field} denies "
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


def live_markdown_paths() -> list[Path]:
    """Current public/provenance prose, excluding explicit history archives."""
    paths: set[Path] = set()
    for root in MARKDOWN_ROOTS:
        if root.is_file():
            paths.add(root)
        elif root.is_dir():
            paths.update(root.rglob("*.md"))
    return sorted(paths)


def check_markdown(
    ledger: dict[str, dict[str, object]], paths: list[Path]
) -> tuple[list[str], int]:
    """Explicit current grade claims in Markdown against the live ledger.

    Markdown has no declaration anchor, so a claim is actionable only when its
    local context names a ``CONJ-###`` row. Files whose opening banner explicitly
    says they are superseded grade history are excluded; the live documents they
    point to remain checked.
    """
    failures: list[str] = []
    seen: set[tuple[str, int, str, str]] = set()
    checked = 0
    for path in paths:
        text = path.read_text(encoding="utf-8")
        try:
            rel = path.relative_to(ROOT)
        except ValueError:
            rel = path
        banner = text[:700]
        if "Superseded" in banner and "current grade" in banner:
            continue
        for pattern in ASSERTIONS:
            for match in pattern.finditer(text):
                window = text[max(0, match.start() - GUARD_WINDOW) : match.start()]
                before = SENTENCE_BREAK.split(window)[-1]
                if GUARDS.search(before):
                    continue
                explicit = re.findall(
                    r"CONJ-\d+", text[max(0, match.start() - 400) : match.end() + 400]
                )
                targets = [cid for cid in dict.fromkeys(explicit) if cid in ledger]
                if not targets:
                    continue
                claimed = match.group(1)
                line = text.count("\n", 0, match.start()) + 1
                for cid in targets:
                    key = (str(rel), line, cid, claimed)
                    if key in seen:
                        continue
                    seen.add(key)
                    checked += 1
                    if claimed in grades_of(ledger[cid]):
                        continue
                    failures.append(
                        f"{rel}:{line}: prose asserts "
                        f"`{claimed}` for {cid}, but conjectures.yaml records "
                        f"scope={ledger[cid]['source_scope']} "
                        f"fidelity={ledger[cid]['source_fidelity']}\n"
                        f"    {match.group(0).strip()}"
                    )
    return failures, checked


# --- the MAIS coverage table ------------------------------------------------
#
# `mais-a2-statement-coverage.md` grades one printed A2 target per row, and its
# rows carry ledger grades that the generic scan above cannot see: the claim
# sits in a cell that names the Lean declaration, not the `CONJ-###` row, so no
# attribution window reaches the ledger. That is how an `O26 | graded `Same``
# row and an "all four at `Same` scope" count both outlived the ledger's move to
# `Narrower` on 2026-08-22 and shipped green for a day.
#
# The table therefore carries an explicit `Ledger` and `Scope` column, and this
# reads them. A row with no ledger row writes `—` in both.

def _rel(path: Path) -> Path | str:
    """Repo-relative path where possible; tests pass throwaway files."""
    try:
        return path.relative_to(ROOT)
    except ValueError:
        return path


MAIS_COVERAGE = ROOT / "docs" / "provenance" / "mais-a2-statement-coverage.md"
MAIS_ROW = re.compile(r"^\| (O\d+) \|")
CELL_IDS = re.compile(r"CONJ-\d+")
CELL_GRADE = re.compile(r"`(" + GRADE_RE + r")`")
GRADED_IN_CELL = re.compile(r"graded `(" + GRADE_RE + r")`")
UNIVERSAL_SCOPE = re.compile(r"\ball\b[^.`]{0,40}?at `(" + GRADE_RE + r")` scope")


def check_mais_coverage(
    ledger: dict[str, dict[str, object]], path: Path = MAIS_COVERAGE
) -> tuple[list[str], int]:
    """The coverage table's own `Scope` cells, and universal claims over them."""
    if not path.is_file():
        return [], 0
    text = path.read_text(encoding="utf-8")
    rel = _rel(path)
    failures: list[str] = []
    checked = 0
    rows: list[tuple[int, str, list[str], str]] = []

    for num, line in enumerate(text.splitlines(), start=1):
        head = MAIS_ROW.match(line)
        if not head:
            continue
        cells = split_cells(line)
        if len(cells) < 3:
            failures.append(
                f"{rel}:{num}: row {head.group(1)} has fewer than three cells; "
                "the table needs `| ID | Ledger | Scope | …`"
            )
            continue
        target, ledger_cell, scope_cell = head.group(1), cells[1], cells[2]
        cids = CELL_IDS.findall(ledger_cell)
        scope_match = CELL_GRADE.search(scope_cell)
        rows.append((num, target, cids, scope_match.group(1) if scope_match else ""))

        if not cids:
            checked += 1
            if scope_match:
                failures.append(
                    f"{rel}:{num}: {target} names no ledger row but its Scope cell "
                    f"reads `{scope_match.group(1)}`; a target with no row has no "
                    "grade to carry"
                )
            continue
        if not scope_match:
            failures.append(
                f"{rel}:{num}: {target} names {cids} but its Scope cell carries no "
                "grade"
            )
            continue

        # A printed target may carry several rows with different grades -- a
        # resolved claim for one clause, an open target for another, a blocked
        # third. `prob:boltzmann` is exactly that. So the cell may list one
        # grade per row, positionally, in the Ledger cell's order; a single
        # grade still applies to every row, which is the common case. Reading
        # only the first grade and holding every row to it made a three-clause
        # problem inexpressible, and the checker reported the mismatch as a
        # stale document rather than as its own limit.
        graded = [match.group(1) for match in CELL_GRADE.finditer(scope_cell)]
        if len(graded) not in {1, len(cids)}:
            failures.append(
                f"{rel}:{num}: {target} names {len(cids)} ledger row(s) but its "
                f"Scope cell carries {len(graded)} grade(s); give one grade for "
                "all of them or one per row in the Ledger cell's order"
            )
            continue
        claimed_for = (
            dict(zip(cids, graded))
            if len(graded) == len(cids)
            else {cid: graded[0] for cid in cids}
        )
        claimed = graded[0]
        for cid in cids:
            checked += 1
            if cid not in ledger:
                failures.append(
                    f"{rel}:{num}: {target} names {cid}, which is not a ledger row"
                )
                continue
            held = ledger[cid]["source_scope"]
            if claimed_for[cid] != held:
                failures.append(
                    f"{rel}:{num}: {target}'s Scope cell reads "
                    f"`{claimed_for[cid]}` for {cid}, but conjectures.yaml "
                    f"records scope={held!r}"
                )
        # A grade asserted in the row's prose must match the row's own cell.
        for match in GRADED_IN_CELL.finditer(line):
            checked += 1
            if match.group(1) != claimed:
                failures.append(
                    f"{rel}:{num}: {target}'s prose says \"graded "
                    f"`{match.group(1)}`\" while its Scope cell reads `{claimed}`"
                )

    # Universal claims are recomputed against the rows that carry a ledger grade.
    graded = [(num, target, scope) for num, target, cids, scope in rows if cids]
    for num, line in enumerate(text.splitlines(), start=1):
        for match in UNIVERSAL_SCOPE.finditer(line):
            checked += 1
            claimed = match.group(1)
            off = [f"{t}=`{s}`" for _, t, s in graded if s != claimed]
            if off:
                failures.append(
                    f"{rel}:{num}: claims every graded row is `{claimed}`, but "
                    f"{sorted(off)} disagree.\n    {match.group(0).strip()}"
                )
    return failures, checked


# --- ledger counts quoted in prose ------------------------------------------
#
# "five open, four resolved, one withdrawn" is a grade-adjacent claim the scan
# above cannot see: it names no row and no grade. It went stale on the public
# site the same day the ledger dropped two rows, which is the failure this
# closes. `site/index.html` is included because it is public prose about the
# same ledger, and nothing else checks it.

COUNT_FILES = (
    ROOT / "README.md",
    ROOT / "STATE.md",
    ROOT / "docs" / "guide" / "conjectures.md",
    ROOT / "site" / "index.html",
)
NUMBER_WORDS = {
    "zero": 0, "no": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
    "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
    # The ledger outgrew this vocabulary on 2026-08-24. A number word the table
    # does not carry is silently *skipped* rather than reported, so the public
    # sentence saying "eighteen MAIS-linked records" was unchecked at the moment
    # it most needed checking -- the count had just changed. Prose about a
    # growing ledger should keep reaching words the checker knows.
    "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
    "twenty": 20, "twenty-one": 21, "twenty-two": 22, "twenty-three": 23,
    "twenty-four": 24, "twenty-five": 25,
}
COUNT_OPEN_RESOLVED = re.compile(
    r"\b(?P<open>\w+) open,?\s*(?:and\s*)?(?P<res>\w+) resolved", re.I
)
COUNT_WITHDRAWN = re.compile(r"\b(?P<n>\w+) withdrawn", re.I)

# Public prose does not always use the "N open, M resolved" shape. `site/index.html`
# was reworded on 2026-08-23 into a MAIS-scoped sentence that matched none of the
# patterns above, so its counts went unchecked again the same day the last stale
# one was fixed. These read the MAIS-scoped totals instead, so the sentence is
# checked on three independent numbers rather than on none.
COUNT_MAIS = [
    # Two different quantities wear similar words, and conflating them is how a
    # sentence can be true and fail. "MAIS-linked records" counts every row
    # against an agenda problem, of any kind; "conjectures" counts only the
    # claim and answer rows among them. Since 2026-08-24 those differ -- 18 and
    # 7 -- and before that date they were the same number, which is why one key
    # sufficed and then silently did not.
    (re.compile(r"\b(?P<n>\w+) MAIS-linked records?\b", re.I), "mais_all"),
    (re.compile(r"\b(?P<n>\w+)\s+MAIS-linked ledger rows?\b", re.I), "mais_all"),
    (re.compile(r"\b(?P<n>\w+) are conjectures\b", re.I), "mais"),
    (re.compile(r"\b(?P<n>\w+) have linked Lean proofs\b", re.I), "mais_resolved"),
    (re.compile(r"\bthe other (?P<n>\w+) remain open\b", re.I), "mais_open"),
    # Kind totals. The ledger stopped being all-conjectures on 2026-08-24 and the
    # narrative paragraph that described its shape was hand-counted, so it went
    # stale the first time a row changed kind -- twice within the same day, once
    # in each direction. Anything that quotes the shape is now checked on it.
    # `\s+` rather than a literal space, because a paragraph in `STATE.md` wraps
    # between "are" and "determine-problem" and between "a" and "printed". Both
    # of these patterns matched nothing on their first run for exactly that
    # reason -- the failure this file's own header describes, reproduced by the
    # check written to prevent it.
    (re.compile(r"\b(?P<n>\w+)\s+(?:are\s+)?determine-problem specifications?\b",
                re.I), "target"),
    (re.compile(r"\b(?P<n>\w+)\s+record\s+a\s+printed\s+problem\s+the\s+atlas"
                r"\s+cannot\s+state\b", re.I), "blocked"),
    # The lookbehind matters: without it `twenty-one-row` matches on `one`,
    # because a hyphenated compound is several `\w+` runs and the pattern
    # happily takes the last of them. `[\w-]+` is what makes the compound
    # *captured* rather than merely not-mismatched: with a bare `\w+` the whole
    # pattern failed on `twenty-one-row file` and the sentence went unchecked,
    # which reads exactly like a sentence that agreed with the ledger.
    (re.compile(r"(?<![-\w])(?P<n>[\w-]+)[- ]row file\b", re.I), "rows"),
    # Was `problems of agenda A2`, which stopped being the whole set when
    # MAIS-O38 arrived from agenda A3. A pattern naming one agenda would have
    # gone on matching a sentence that had become false about the ledger,
    # or -- once the sentence was rewritten -- matched nothing at all and
    # read exactly like agreement.
    (
        re.compile(
            r"\b(?:all|covering) (?P<n>[\w-]+) printed problems of the MAIS agendas\b", re.I
        ),
        "mais_problems",
    ),
]


def is_count_word(word: str) -> bool:
    """Whether a captured token was *trying* to state a number.

    The count patterns have to leave the slot wide, because a number word can
    be a hyphenated compound and the compound has to be captured whole. A wide
    slot also catches ordinary prose -- *the rest are determine-problem
    specifications* -- and those tokens are not unchecked count claims, they are
    sentences that were never counting. A token is reported as an unparsed count
    only when it is built out of number words or digits, which is the case the
    vocabulary can actually be short for.
    """
    parts = word.lower().split("-")
    return any(part.isdigit() or part in NUMBER_WORDS for part in parts)


def as_count(word: str) -> int | None:
    if word.isdigit():
        return int(word)
    return NUMBER_WORDS.get(word.lower())


def check_counts(
    ledger: dict[str, dict[str, object]], paths: tuple[Path, ...] = COUNT_FILES
) -> tuple[list[str], int, set[str]]:
    """Ledger totals quoted in public prose, against the ledger itself.

    Returns the failures, how many count claims were compared, and the count
    words that could not be parsed -- the denominator matters, because a
    sentence no pattern matched produces exactly the output of a sentence that
    agreed.
    """
    def is_mais(entry: dict[str, object]) -> bool:
        refs = entry.get("source_ref")
        return isinstance(refs, list) and any(
            isinstance(r, str) and r.startswith("mais-") for r in refs
        )

    # Counts are over *conjectures* -- rows of kind claim or answer -- because
    # that is what the prose these patterns match is about. A target row records
    # a determine-problem's specification and a blocked row records an absence;
    # neither is an open conjecture, and folding them in would make every
    # sentence in the guide wrong at once while saying nothing truer. The
    # breakdown by kind is printed by `validate_conjectures.py`, which is where
    # a reader asking "what does the atlas cover" should be sent.
    conjecture_rows = [
        e for e in ledger.values() if e.get("kind", "claim") in {"claim", "answer"}
    ]
    mais = [e for e in conjecture_rows if is_mais(e)]
    actual = {
        "open": sum(e["status"] == "OPEN" for e in conjecture_rows),
        "resolved": sum(e["status"] == "RESOLVED" for e in conjecture_rows),
        "withdrawn": sum(e["status"] == "WITHDRAWN" for e in conjecture_rows),
        "mais": len(mais),
        "mais_all": sum(is_mais(e) for e in ledger.values()),
        "rows": len(ledger),
        "target": sum(e.get("kind") == "target" for e in ledger.values()),
        "blocked": sum(e.get("kind") == "blocked" for e in ledger.values()),
        # Distinct printed problems the MAIS rows reach, which is not the row
        # count: O29 has three rows and O31 and O34 two each, so prose saying
        # "one per problem" was structurally false while every number in the
        # same sentence was right.
        "mais_problems": len(
            {
                str(e.get("problem", "")).split("(")[0]
                for e in ledger.values()
                if is_mais(e) and e.get("problem")
            }
        ),
        "mais_open": sum(e["status"] == "OPEN" for e in mais),
        "mais_resolved": sum(e["status"] == "RESOLVED" for e in mais),
    }
    failures: list[str] = []
    checked = 0
    # A token that reaches `as_count` and comes back `None` was written in a
    # sentence shaped like a count claim, and skipping it silently is the
    # failure this script exists to prevent: the output of a check that found
    # nothing is indistinguishable from the output of a check that ran on
    # nothing. These are surfaced instead, and `tests/` asserts the live files
    # produce none -- so an unrecognised number word breaks the suite without
    # this script guessing that arbitrary prose meant to state a number.
    skipped: set[str] = set()
    for path in paths:
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        rel = _rel(path)
        for match in COUNT_OPEN_RESOLVED.finditer(text):
            opened, resolved = as_count(match["open"]), as_count(match["res"])
            if opened is None or resolved is None:
                skipped.update(
                    w for w, c in ((match["open"], opened), (match["res"], resolved))
                    if c is None and is_count_word(w)
                )
                continue
            checked += 1
            if (opened, resolved) != (actual["open"], actual["resolved"]):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{rel}:{line}: prose says {opened} open / {resolved} "
                    f"resolved, but conjectures.yaml holds {actual['open']} open "
                    f"/ {actual['resolved']} resolved.\n    {match.group(0)}"
                )
            tail = text[match.end() : match.end() + 120]
            drawn = COUNT_WITHDRAWN.search(tail)
            if drawn is None:
                continue
            count = as_count(drawn["n"])
            if count is None:
                if is_count_word(drawn["n"]):
                    skipped.add(drawn["n"])
                continue
            checked += 1
            if count != actual["withdrawn"]:
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{rel}:{line}: prose says {count} withdrawn, but "
                    f"conjectures.yaml holds {actual['withdrawn']}.\n"
                    f"    {match.group(0)}{tail[: drawn.end()]}"
                )
        for pattern, key in COUNT_MAIS:
            for match in pattern.finditer(text):
                stated = as_count(match["n"])
                if stated is None:
                    if is_count_word(match["n"]):
                        skipped.add(match["n"])
                    continue
                checked += 1
                if stated != actual[key]:
                    line = text.count("\n", 0, match.start()) + 1
                    failures.append(
                        f"{rel}:{line}: prose says {stated} for {key}, but "
                        f"conjectures.yaml holds {actual[key]}.\n"
                        f"    {match.group(0)}"
                    )
    return failures, checked, skipped


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

    markdown_failures, markdown_checked = check_markdown(
        ledger, live_markdown_paths()
    )
    failures.extend(markdown_failures)
    checked += markdown_checked

    coverage_failures, coverage_checked = check_mais_coverage(ledger)
    failures.extend(coverage_failures)
    checked += coverage_checked

    count_failures, count_checked, count_skipped = check_counts(ledger)
    failures.extend(count_failures)
    checked += count_checked
    if count_skipped:
        failures.append(
            "count words this script cannot parse, so the sentences holding "
            f"them went unchecked: {', '.join(sorted(count_skipped))}. Add them "
            "to NUMBER_WORDS or write the number as digits."
        )

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
