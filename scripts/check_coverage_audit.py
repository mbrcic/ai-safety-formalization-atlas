"""Check the source-coverage audit's tables against its own totals.

The audit grades every printed statement of each source it covers on two axes. Its numbers
are quoted in commit messages and in a published artifact, so they have to be
mechanically checkable rather than hand-counted — an earlier revision published a
grand total no consistent counting of its own rows could reach.

Counting convention (also stated in the document):
  * a row is counted in exactly one column;
  * `Beyond` rows are those whose Coverage cell is a dash — they record something
    the atlas proves that the source does not state, so there is no printed
    statement to grade;
  * a row covering a printed statement is counted under Yes/Partial/No even when
    its Scope verdict is `Beyond`.

Also verifies that every backticked Lean declaration named in the Atlas column
exists in the pinned public API or in an Examples module.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "docs" / "provenance" / "source-coverage-audit.md"
PUBLIC_API = ROOT / "docs" / "status" / "public-api.txt"

SECTION_RE = re.compile(r"^## (\d+)\. (.+)$")
# The bold per-section tallies a reader actually sees, e.g. "**9 Yes, 0 Partial, 0 No.**"
SUMMARY_RE = re.compile(
    r"\*\*(\d+) Yes\s*[,/]\s*(\d+) Partial\s*[,/]\s*(\d+) No"
    r"(?:\s*[,/]\s*(\d+) Beyond)?"
)
# Backticked names whose head component belongs to a dependency, not the atlas.
CAMEL_CASE = re.compile(r"^[A-Z][A-Za-z0-9']*[a-z][A-Z][A-Za-z0-9']*$")
# Backticked names whose head component belongs to a dependency, not the atlas.
EXTERNAL_ROOTS = {
    "Set", "Finset", "Nat", "Real", "Function", "Equiv", "PMF", "ZMod", "Measure",
    "Fin", "Prod", "Bool", "Classical", "ENNReal", "Filter", "Fintype", "Mathlib",
    "MeasureTheory", "ProbabilityTheory", "PFR", "GaloisField", "IsUniform",
    "CondIndepFun", "IndepFun", "SimpleGraph", "FiniteRange",
    "IsProbabilityMeasure", "IsZeroOrProbabilityMeasure", "LinearOrder",
}
# Mathlib names that are lowercase-initial, so the "looks like an atlas
# declaration" heuristic below would otherwise flag them.
EXTERNAL_LOWERCASE = {"sInf", "sSup", "iInf", "iSup", "uniformOn", "binEntropy"}
# A backticked token is treated as a declaration name only if it looks like one:
# an identifier with an underscore or an internal capital, and not a known piece
# of notation or a Mathlib/PFR name the atlas does not own.
_UNUSED_LOOKS_LIKE_DECL = re.compile(r"^(?:[A-Za-z][A-Za-z0-9']*\.)*[A-Za-z][A-Za-z0-9']*(?:_[A-Za-z0-9_']+|[a-z][A-Z][A-Za-z0-9_']*)$")
TOTALS_ROW_RE = re.compile(r"^\| ([^|]+?) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \|$")
GRAND_RE = re.compile(r"^\| \*\*total\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \|$")


def strip_markup(cell: str) -> str:
    return cell.replace("**", "").strip()


class Unclassifiable(Exception):
    """A six-cell data row that falls in no column — silently uncounted."""


def classify(coverage: str, scope: str) -> str:
    """Which column a data row is counted in.

    Raises rather than returning None: a row that lands in no column would be
    dropped from every total while the arithmetic still balanced, which is the
    failure mode this whole script exists to prevent.
    """
    cov = strip_markup(coverage)
    if cov in {"Yes", "Partial", "No"}:
        return cov
    if cov in {"—", "-", ""}:
        if strip_markup(scope) == "Beyond":
            return "Beyond"
        raise Unclassifiable(
            f"row with dash coverage and scope {strip_markup(scope)!r} is counted nowhere"
        )
    raise Unclassifiable(f"unrecognised coverage cell {cov!r}")


def parse_sections(
    text: str,
) -> tuple[
    dict[str, dict[str, int]],
    dict[str, list[tuple[int, ...]]],
    dict[str, list[str]],
    list[tuple[str, str]],
]:
    """Row counts, printed tallies, row keys and Atlas-column cells, per section."""
    counts: dict[str, dict[str, int]] = {}
    summaries: dict[str, list[tuple[int, ...]]] = {}
    rows: dict[str, list[str]] = {}
    atlas_cells: list[tuple[str, str]] = []
    current: str | None = None
    for line in text.splitlines():
        if line.startswith("## "):
            m = SECTION_RE.match(line)
            # any other `## ` heading closes the current section, so a stray
            # six-cell table below the last source is not attributed to it
            current = m.group(2).strip() if m else None
            if current is not None:
                counts.setdefault(current, {"Yes": 0, "Partial": 0, "No": 0, "Beyond": 0})
                rows.setdefault(current, [])
            continue
        if current is not None and not line.startswith("|"):
            # every tally in the section is checked, not only the first: a
            # second, contradicting one further down is exactly as misleading
            for m in SUMMARY_RE.finditer(line):
                g = m.groups()
                summaries.setdefault(current, []).append(
                    tuple(int(x) for x in g[:3])
                    + (int(g[3]) if g[3] is not None else -1,)
                )
        if not line.startswith("|"):
            continue
        if current is None:
            # a six-cell grading table outside any numbered section would be
            # counted nowhere; refuse rather than skip
            masked = line.replace(r"\|", "\x00")
            if len(masked.split("|")) - 2 == 6 and strip_markup(masked.split("|")[4]) in {
                "Yes", "Partial", "No", "—", "-"
            }:
                raise Unclassifiable("grading row found outside any numbered source section")
            continue
        # cells may contain escaped pipes (`\|`) inside inline maths
        masked = line.replace(r"\|", "\x00")
        cells = masked.split("|")[1:-1]
        if len(cells) != 6:
            # a grading table's rows are six cells; a row of any other width in a
            # numbered section is dropped by every counter but read by a human
            probe = [strip_markup(c.replace("\x00", "|")) for c in cells]
            if any(v in {"Yes", "Partial", "No"} for v in probe):
                raise Unclassifiable(
                    f"section {current!r} has a {len(cells)}-cell row carrying a verdict: "
                    f"{' | '.join(probe)[:90]}"
                )
            continue
        cells = [c.replace("\x00", "|") for c in cells]
        if strip_markup(cells[0]) in {"#", "§", "source"} or set(strip_markup(cells[0])) <= {"-"}:
            continue  # header or separator row
        counts[current][classify(cells[3], cells[4])] += 1
        rows[current].append(strip_markup(cells[0]) + "||" + strip_markup(cells[2]))
        atlas_cells.append((current, cells[2]))
    return counts, summaries, rows, atlas_cells


def parse_totals(text: str) -> tuple[list[tuple[str, tuple[int, ...]]], tuple[int, ...]]:
    rows: list[tuple[str, tuple[int, ...]]] = []
    grand: tuple[int, ...] | None = None
    in_totals = False
    for line in text.splitlines():
        if line.strip() == "## Totals":
            in_totals = True
            continue
        if in_totals and line.startswith("## "):
            break
        if not in_totals:
            continue
        g = GRAND_RE.match(line)
        if g:
            grand = tuple(int(x) for x in g.groups())
            continue
        m = TOTALS_ROW_RE.match(line)
        if m:
            rows.append((m.group(1).strip(), tuple(int(x) for x in m.groups()[1:])))
    if grand is None:
        raise SystemExit("check_coverage_audit: no grand-total row found")
    return rows, grand


def label_matches(label: str, section: str) -> bool:
    """Does a totals-table label name the section it is aligned with?

    Compared on alphanumeric words, so "Cover & Thomas §2.8" matches
    "Cover & Thomas, §2.8 → `AISafetyAtlas...`" but not "§2.10".
    """
    def words(s: str) -> set[str]:
        drop = {"and", "the", "of", "et", "al", "ch", "book"}
        return {
            w.strip(".,")
            for w in re.findall(r"[A-Za-z0-9.§]+", s.lower())
            if len(w) > 1 and w not in drop
        }
    lw, sw = words(label), words(section)
    if not lw:
        return False
    # every token carrying a number must match: those are what distinguish
    # "§2.8" from "§2.10" and "ch. 11" from "ch. 12"
    numeric = {w for w in lw if any(c.isdigit() for c in w)}
    if not numeric <= sw:
        return False
    # and at least one word must match, so a wholesale rename is caught
    return bool((lw - numeric) & sw) or bool(numeric)


def check_name(raw: str, known: set[str], modules: set[str]) -> list[str]:
    """Flag `raw` if it looks like an atlas declaration and resolves to none.

    Fully-qualified `AISafetyAtlas.…` names are resolved *in full*: a real tail
    under a fictional namespace is not a resolution.
    """
    parts = raw.split(".")
    if raw.startswith("AISafetyAtlas."):
        if raw in known or raw in modules:
            return []
        return [f"audit names `{raw}`, which is neither a declaration nor a module"]
    if {".".join(parts[i:]) for i in range(len(parts))} & known or raw in modules:
        return []
    # A repo script may be cited by name, but only if it is really there — an
    # audit that promises a check no file performs is the failure this guards.
    # Checked before the shape heuristics below, which a name like `nosuch.py`
    # slips through entirely (no underscore, no internal capital).
    if raw.endswith(".py"):
        if (ROOT / "scripts" / raw).is_file():
            return []
        return [f"audit names the script `{raw}`, which is not in scripts/"]
    if raw in EXTERNAL_LOWERCASE:
        return []
    if parts[0][0].islower() and ("_" in raw or re.search(r"[a-z][A-Z]", raw)):
        return [f"audit names `{raw}`, which is not a declaration in the atlas"]
    if (
        parts[0] not in EXTERNAL_ROOTS
        and not raw.endswith(".lean")
        and CAMEL_CASE.match(parts[0])
    ):
        return [
            f"audit names `{raw}`, which is not a declaration in the atlas "
            f"(add {parts[0]!r} to EXTERNAL_ROOTS if it belongs to a dependency)"
        ]
    return []


def known_modules() -> set[str]:
    """Module paths under `AISafetyAtlas/`, as the audit writes them."""
    names = {"AISafetyAtlas"}
    for path in (ROOT / "AISafetyAtlas").rglob("*.lean"):
        rel = path.relative_to(ROOT).with_suffix("")
        names.add(".".join(rel.parts))
    return names


def known_declarations() -> set[str]:
    names: set[str] = set()
    for line in PUBLIC_API.read_text().splitlines():
        if "::" in line:
            names.add(line.split("::", 1)[1].strip())
    for path in (ROOT / "AISafetyAtlas").rglob("*.lean"):
        for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?public (?:noncomputable )?(?:theorem|def|abbrev|instance|structure|inductive) ([A-Za-z_][A-Za-z0-9_'.]*)", path.read_text(), re.M):
            names.add(m.group(1))
    return names


def registry_modules() -> set[str]:
    """Every in-tree Lean module some registry row hosts.

    A module this audit grades but no row hosts is invisible to every generated
    status page, so a reader of `formalization-status.md` cannot see that the
    work exists. That was true of all three information-theory modules until
    2026-08-16; nothing but this check stops it recurring.
    """
    registry = json.loads((ROOT / "registry.yaml").read_text())
    modules: set[str] = set()
    for row in registry.get("results", []):
        for record in row.get("formalizations", []):
            if record.get("version") == "IN_TREE" and record.get("module"):
                modules.add(record["module"])
    return modules


def audit_target_modules(text: str) -> list[tuple[str, str]]:
    """`(source name, module)` for each `## N. source → `Module`` heading.

    The first component drops the arrow, so it is *not* the key `parse_sections`
    uses; `audit_declared_headings` gives that.
    """
    targets: list[tuple[str, str]] = []
    for line in text.splitlines():
        m = re.match(r"^## \d+\. (.+?) *(?:→|->) *`([A-Za-z0-9_.]+)`\s*$", line)
        if m:
            targets.append((m.group(1).strip(), m.group(2)))
    return targets


def audit_declared_headings(text: str) -> set[str]:
    """The `parse_sections` keys of sections that declare a target module."""
    declared: set[str] = set()
    for line in text.splitlines():
        m = re.match(r"^## \d+\. (.+?) *(?:→|->) *`[A-Za-z0-9_.]+`\s*$", line)
        if m:
            declared.add(re.sub(r"^## \d+\. ", "", line).strip())
    return declared


def main() -> int:
    text = AUDIT.read_text()
    try:
        per_section, summaries, section_rows, atlas_cells = parse_sections(text)
    except Unclassifiable as exc:
        print(f"check_coverage_audit: {exc}", file=sys.stderr)
        return 1
    totals_rows, grand = parse_totals(text)

    problems: list[str] = []

    counted = [c for c in per_section.values() if any(c.values())]
    if len(counted) != len(totals_rows):
        problems.append(
            f"totals table has {len(totals_rows)} source rows but {len(counted)} sections carry graded rows"
        )

    for (label, quoted), (name, actual) in zip(
        totals_rows, [(k, v) for k, v in per_section.items() if any(v.values())]
    ):
        want = (actual["Yes"], actual["Partial"], actual["No"], actual["Beyond"])
        if quoted != want:
            problems.append(
                f"{label!r}: totals table says {quoted}, section {name!r} rows count {want}"
            )
        # the totals label has to name the section it is aligned with, or the
        # table can be silently reordered or relabelled
        if not label_matches(label, name):
            problems.append(
                f"totals row {label!r} does not name section {name!r} — "
                "the table is reordered or relabelled"
            )

    for name, entries in section_rows.items():
        seen: dict[str, int] = {}
        for e in entries:
            seen[e] = seen.get(e, 0) + 1
        for e, n in seen.items():
            if n > 1 and e.split("||")[1]:
                problems.append(f"section {name!r} repeats a row for {e.split('||')[1]!r}")

    for name, actual in per_section.items():
        if not any(actual.values()):
            continue
        quoted_list = summaries.get(name)
        if not quoted_list:
            problems.append(f"section {name!r} prints no tally, so nothing cross-checks its rows")
            continue
        want = (actual["Yes"], actual["Partial"], actual["No"])
        for quoted in quoted_list:
            if quoted[:3] != want:
                problems.append(
                    f"section {name!r} prints the tally {quoted[:3]} but its rows count {want}"
                )
            if quoted[3] < 0:
                # an omitted "N Beyond" clause reads as a complete tally
                if actual["Beyond"]:
                    problems.append(
                        f"section {name!r} has {actual['Beyond']} Beyond row(s) but its tally "
                        "omits the Beyond clause, so it reads as a complete count"
                    )
            elif quoted[3] != actual["Beyond"]:
                problems.append(
                    f"section {name!r} prints {quoted[3]} Beyond but its rows count {actual['Beyond']}"
                )

    summed = tuple(sum(r[1][i] for r in totals_rows) for i in range(4))
    if summed != grand:
        problems.append(f"grand total {grand} does not equal the column sums {summed}")

    hosted = registry_modules()
    targets = audit_target_modules(text)
    if not targets:
        problems.append(
            "no section heading names a target module — the "
            "'## N. source → `Module`' form changed and the registry-row check is dead"
        )
    for heading, module in targets:
        if module not in hosted:
            problems.append(
                f"section {heading!r} grades `{module}`, which no registry row hosts "
                "as an IN_TREE formalization — every status page will omit it"
            )
    # The loop above only reaches sections that *declare* a target. A graded
    # section whose heading drops the `→ `Module`` suffix would be counted into
    # the totals and never checked, which is the whole point of the check.
    declared = audit_declared_headings(text)
    for name, counts in per_section.items():
        if any(counts.values()) and name not in declared:
            problems.append(
                f"section {name!r} carries graded rows but its heading names no target "
                "module, so no registry row is required of it — restore the "
                "'## N. source → `Module`' form"
            )

    known = known_declarations()
    modules = known_modules()

    # The Atlas column is unambiguous: every backticked name in it is a claim
    # that a declaration of that name exists. Resolve those strictly, which
    # catches the all-lowercase names the general heuristic cannot.
    for section, cell in atlas_cells:
        for m in re.finditer(r"`([^`]+)`", cell):
            for nm in re.finditer(r"[A-Za-z][A-Za-z0-9_.'\u2032\u2081-\u2089]*", m.group(1)):
                raw = nm.group(0)
                if raw in {"Examples", "and", "via", "from", "the"}:
                    continue
                parts = raw.split(".")
                if {".".join(parts[i:]) for i in range(len(parts))} & known:
                    continue
                problems.append(
                    f"section {section!r}: the Atlas column names `{raw}`, "
                    "which is not a declaration in the atlas"
                )
    for span in re.finditer(r"`([^`\n]+)`", text):
        # a backtick span may hold several names, or prose around one
        for m in re.finditer(r"[A-Za-z][A-Za-z0-9_.']*", span.group(1)):
            problems.extend(check_name(m.group(0), known, modules))

    if problems:
        for p in sorted(set(problems)):
            print(f"check_coverage_audit: {p}", file=sys.stderr)
        return 1

    print(
        f"coverage audit ok: {len(totals_rows)} sources, "
        f"{grand[0]} Yes / {grand[1]} Partial / {grand[2]} No / {grand[3]} Beyond, "
        f"row counts and declaration names consistent"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
