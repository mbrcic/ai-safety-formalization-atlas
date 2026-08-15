#!/usr/bin/env python3
"""Keep the Wolpert 2008 status tally honest.

Four review rounds in a row shipped a coverage figure that did not match the table
it described: ``34/5`` in the facade against ``29/10`` in the provenance and the
registry, none of them equal to the table's own contents. Prose that describes a
table must be derived from it, not written beside it.

This script recomputes the tally from the one authoritative table -- the
transcription table in ``docs/provenance/wolpert-inference-devices.md`` -- and
fails when any surface disagrees:

* the provenance's own summary table and prose,
* the ``AISafetyAtlas.Inference`` facade docstring,
* ``BY-024``'s ``scope_delta`` and ``notes`` in ``registry.yaml``.

It also rejects rows whose Lean column does not name a real declaration. That is
the shape defect that let ``Theorem 7(ii)`` ship with a parenthesised prose entry
where a declaration name belongs, and ``prop6_half`` ship as ``Proposition 6``.

Three later hardenings, each closing a way this gate could pass while the thing
it certifies is wrong:

* **Every name, not one of them.** A row used to pass when a single named
  declaration resolved, so a cell could carry three stale names beside one live
  one and read as verified.
* **Qualified resolution.** ``known_declarations`` used to reduce declarations
  to a last component, so ``Wrong.Namespace.foo`` resolved against any unrelated
  ``foo``. Names are now matched as a suffix of a real qualified path.
* **The worked examples.** The numbered inventory reaches Definitions,
  Theorems, Propositions, Corollaries and Lemma 1 -- not the paper's six
  examples, which were tracked nowhere. ``EXAMPLES`` closes that set. The
  prompt was the 2018 map: its Example 6 is *refuted*, so "it is only an
  example" is not a reason to leave one unread.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
PROVENANCE = ROOT / "docs" / "provenance" / "wolpert-inference-devices.md"
FACADE = ROOT / "AISafetyAtlas" / "Inference.lean"
REGISTRY = ROOT / "registry.yaml"
LEAN_ROOT = ROOT / "AISafetyAtlas"

STATUSES = ("SOURCE-EXACT", "SPECIALIZED", "REPAIRED", "ASSUMED-STEP", "REFUTED")

# Worked examples are graded on the 2018 map's narrower vocabulary: either the
# example makes a claim that is transcribed, or it makes none.
EXAMPLE_STATUSES = ("SOURCE-EXACT", "INTERPRETATION")
ALL_STATUSES = tuple(dict.fromkeys(STATUSES + EXAMPLE_STATUSES))

# The paper's six worked examples, which the numbered inventory does not reach.
#
# They were untracked entirely until an adversarial review of the coverage tables
# noticed that the 2018 map inventories its examples and this one does not -- and
# that the only example ever actually checked, 2018's Example 6, turned out to be
# REFUTED. Examples 1-4 are the motivating physical scenarios and Example 6 is
# the RAM-and-prefix-strings scaffolding for Definition 6; none states a claim.
# Example 5 does: it asserts distinguishability, a conditional weak inference,
# and the impossibility that follows.
#
# This tally is kept SEPARATE from the 46 numbered statements on purpose. That
# figure is pinned in four surfaces and means what it says.
EXAMPLES = {
    "1": "INTERPRETATION",
    "2": "INTERPRETATION",
    "3": "INTERPRETATION",
    "4": "INTERPRETATION",
    "5": "SOURCE-EXACT",
    "6": "INTERPRETATION",
}

# The paper's numbered inventory, split exactly as the paper splits it.
INVENTORY: list[tuple[str, str, str]] = (
    [("Def", str(i), "") for i in range(1, 15)]
    + [
        ("Thm", "1", ""), ("Thm", "2", "i"), ("Thm", "2", "ii"), ("Thm", "3", ""),
        ("Thm", "4", ""), ("Thm", "5", ""), ("Thm", "6", "i"), ("Thm", "6", "ii"),
        ("Thm", "7", "i"), ("Thm", "7", "ii"),
    ]
    + [
        ("Prop", "1", "i"), ("Prop", "1", "ii"), ("Prop", "2", "i"), ("Prop", "2", "ii"),
        ("Prop", "3", "i"), ("Prop", "3", "ii"), ("Prop", "3", "iii"), ("Prop", "4", ""),
        ("Prop", "5", "i"), ("Prop", "5", "ii"), ("Prop", "6", ""), ("Prop", "7", ""),
    ]
    + [
        ("Cor", "1", "i"), ("Cor", "1", "ii"), ("Cor", "2", ""), ("Cor", "3", "i"),
        ("Cor", "3", "ii"), ("Cor", "3", "iii"), ("Cor", "4", ""), ("Cor", "5", ""),
    ]
    + [("Lemma", "1", "")]
)

ITEM_RE = re.compile(r"^(Def|Thm|Prop|Cor|Lemma)\s+(\d+)(?:\(([ivx]+)\))?")
EXAMPLE_RE = re.compile(r"^Example\s+(\d+)")
DECL_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']*)`")


def split_row(line: str) -> list[str]:
    """Split a markdown row on unescaped pipes."""
    return [c.strip() for c in re.split(r"(?<!\\)\|", line.strip().strip("|"))]


def parse_table(
    text: str,
) -> tuple[dict[tuple[str, str, str], str], list[str], list[str], dict[str, tuple[str, str]]]:
    """Return numbered-item statuses, prose statuses, Lean cells, and examples."""
    items: dict[tuple[str, str, str], str] = {}
    prose: list[str] = []
    lean_cells: list[str] = []
    examples: dict[str, tuple[str, str]] = {}
    for line in text.splitlines():
        if not line.startswith("| ") or line.startswith("|---"):
            continue
        cells = split_row(line)
        if len(cells) < 4:
            continue
        # Read the status from the **status cell** only, never from any cell.
        #
        # Scanning `cells[1:]` matched the vocabulary wherever it appeared,
        # including inside a note. A row graded `CORE-ONLY` whose note read
        # "`CORE-ONLY`, not `SOURCE-EXACT`" was therefore counted as
        # SOURCE-EXACT -- a silent misread of a row that was explaining why it
        # was *not* that grade.
        status = next((s for s in ALL_STATUSES if s in cells[-1]), None)
        if status is None:
            continue
        label = cells[0].replace("**", "")
        match = ITEM_RE.match(label)
        example = EXAMPLE_RE.match(label)
        if match:
            key = (match.group(1), match.group(2), match.group(3) or "")
            items[key] = status
            lean_cells.append(cells[2])
        elif example:
            examples.setdefault(example.group(1), (status, cells[2]))
        else:
            prose.append(status)
    return items, prose, lean_cells, examples


DECL_LINE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|public\s+)?(?:noncomputable\s+)?"
    r"(?:def|theorem|abbrev|structure|class|instance|inductive|lemma)\s+"
    r"([^\s:({\[]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s]+)")
END_RE = re.compile(r"^\s*end\s+([^\s]+)\s*$")


def known_declarations() -> set[tuple[str, ...]]:
    """Every declaration under AISafetyAtlas, as its fully-qualified segments.

    Two things here are deliberate, and both are repairs of defects this repo
    has actually shipped.

    The name capture is ``[^\\s:({\\[]+`` rather than an ASCII character class.
    The class form silently truncated subscripted and primed names -- it read
    ``F`` out of ``F₁_of_compatible`` -- which put names into the "declared" set
    that no declaration has. A checker whose vocabulary is wrong fails open.

    Names are qualified by their enclosing ``namespace`` rather than reduced to
    a last component. Last-component matching lets a table cell write
    ``Wrong.Namespace.foo`` and pass because some unrelated ``foo`` exists
    elsewhere in the tree.
    """
    names: set[tuple[str, ...]] = set()
    for path in LEAN_ROOT.rglob("*.lean"):
        stack: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            if opened := NAMESPACE_RE.match(line):
                stack.append(opened.group(1))
                continue
            if closed := END_RE.match(line):
                if stack and stack[-1] == closed.group(1):
                    stack.pop()
                continue
            if found := DECL_LINE_RE.match(line):
                prefix = ".".join(stack)
                qualified = f"{prefix}.{found.group(1)}" if prefix else found.group(1)
                names.add(tuple(qualified.split(".")))
    return names


def resolves(name: str, declared: set[tuple[str, ...]]) -> bool:
    """Does a table's declaration name identify a declaration that exists?

    A cell may abbreviate: ``Realized`` for ``InferenceDevice.Realized``. So the
    written segments must be a *suffix* of some real qualified name -- which
    still rejects a wrong prefix, unlike last-component matching.
    """
    segments = tuple(name.split("."))
    return any(
        qualified[-len(segments):] == segments
        for qualified in declared
        if len(qualified) >= len(segments)
    )


def main() -> int:
    errors: list[str] = []

    provenance = PROVENANCE.read_text(encoding="utf-8")
    items, prose, lean_cells, examples = parse_table(provenance)

    missing = [i for i in INVENTORY if i not in items]
    if missing:
        errors.append(f"inventory items with no status row: {missing}")

    unexpected = [
        k for k in items
        if k not in INVENTORY and k != ("Thm", "2", "")
    ]
    if unexpected:
        errors.append(f"status rows outside the numbered inventory: {unexpected}")

    counts = {s: sum(1 for v in items.values() if v == s) for s in STATUSES}
    tracked = len(items)

    # The worked examples are a closed inventory of their own.
    missing_examples = sorted(set(EXAMPLES) - set(examples), key=int)
    extra_examples = sorted(set(examples) - set(EXAMPLES), key=int)
    if missing_examples:
        errors.append(f"worked examples with no row: {missing_examples}")
    if extra_examples:
        errors.append(f"example rows outside the paper's six: {extra_examples}")
    for number, expected in EXAMPLES.items():
        if number not in examples:
            continue
        status, lean = examples[number]
        if status != expected:
            errors.append(f"Example {number}: expected {expected}, found {status}")
        if status == "INTERPRETATION":
            # Same rule the 2018 gate enforces: an item that states no claim owns
            # no Lean, and the cell says so rather than being merely declaration-free.
            if DECL_RE.findall(lean) or lean not in {"—", "-", ""}:
                errors.append(
                    f"Example {number}: INTERPRETATION states no claim, so its Lean "
                    f"cell must be an em dash, found {lean!r}"
                )
        elif not DECL_RE.findall(lean):
            errors.append(f"Example {number}: status {status} names no declaration")

    # Rows must name declarations that exist, not prose in a declaration column.
    #
    # Every name, not merely one of them: the earlier rule passed a row as long
    # as a single name resolved, so a row could carry three stale names beside
    # one live one and read as verified.
    declared = known_declarations()
    lean_cells += [
        lean for status, lean in examples.values() if status in EXAMPLE_STATUSES
        and status != "INTERPRETATION"
    ]
    for cell in lean_cells:
        names = DECL_RE.findall(cell)
        if not names:
            errors.append(f"table row has no declaration in its Lean column: {cell!r}")
            continue
        unknown = [n for n in names if not resolves(n, declared)]
        if unknown:
            errors.append(f"table row names unknown declarations {unknown}: {cell!r}")

    # The facade's own per-item table must agree with the provenance, row by row.
    #
    # Only the facade's aggregate *sentence* was checked before, so its table
    # could drift silently -- and it had. Definition 9 read SPECIALIZED there
    # against SOURCE-EXACT here, and Theorem 7(i) advertised the finite
    # `thm7_card` where the provenance names `thm7_mk`, which drops that
    # finiteness. A reader who opens the library sees the facade first.
    facade_text = FACADE.read_text(encoding="utf-8")
    facade_items, _facade_prose, _facade_lean, _facade_examples = parse_table(facade_text)
    for key, status in facade_items.items():
        if key not in items:
            errors.append(f"facade table has a row the provenance does not: {key}")
        elif items[key] != status:
            errors.append(
                f"facade says {key} is {status}, provenance says {items[key]}"
            )

    # Every surface that repeats the tally must agree with it.
    exact, spec = counts["SOURCE-EXACT"], counts["SPECIALIZED"]
    rep, assumed, ref = counts["REPAIRED"], counts["ASSUMED-STEP"], counts["REFUTED"]

    surfaces = {
        "provenance summary table": (
            provenance,
            [rf"\|\s*`SOURCE-EXACT`\s*\|\s*{exact}\s*\|", rf"\|\s*`SPECIALIZED`\s*\|\s*{spec}\s*\|"],
        ),
        "provenance prose": (
            provenance,
            [rf"{exact} `SOURCE-EXACT`, {spec} `SPECIALIZED`"],
        ),
        "facade docstring": (
            FACADE.read_text(encoding="utf-8"),
            [rf"`SOURCE-EXACT` for\s*\n?\s*{exact},\s*`SPECIALIZED` for {spec}"],
        ),
        "registry": (
            REGISTRY.read_text(encoding="utf-8"),
            [rf"{exact} SOURCE-EXACT, {spec} SPECIALIZED"],
        ),
    }
    for name, (text, patterns) in surfaces.items():
        for pattern in patterns:
            if not re.search(pattern, text):
                errors.append(
                    f"{name} does not state the computed tally "
                    f"({exact} SOURCE-EXACT / {spec} SPECIALIZED); expected /{pattern}/"
                )

    # The grade and the prose about it must not contradict each other.
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))

    # JSON is dynamically shaped; Any is the honest annotation here.
    def find_row(node: Any) -> Any:
        if isinstance(node, dict):
            if node.get("id") == "BY-024":
                return node
            for value in node.values():
                found = find_row(value)
                if found is not None:
                    return found
        elif isinstance(node, list):
            for value in node:
                found = find_row(value)
                if found is not None:
                    return found
        return None

    row = find_row(registry)
    if row is None:
        errors.append("BY-024 not found in registry.yaml")
    else:
        relationship = str(row["formalizations"][0]["relationship"])
        notes = str(row.get("notes", ""))
        for other in ("EXACT", "EQUIVALENT", "RELATED", "NEW_PROOF"):
            if other != relationship and re.search(rf"\bat {other}\b|graded {other}\b", notes):
                errors.append(
                    f"BY-024 notes say {other} while the formalization record says {relationship}"
                )

    if errors:
        for error in errors:
            print(f"wolpert status error: {error}", file=sys.stderr)
        return 1

    print(
        f"wolpert status table ok: {tracked} tracked statements "
        f"({len(INVENTORY)} numbered inventory + Theorem 2's unnumbered sentence), "
        f"{exact} SOURCE-EXACT, {spec} SPECIALIZED, {rep} REPAIRED, "
        f"{assumed} ASSUMED-STEP, {ref} REFUTED; {len(prose)} prose rows and "
        f"{len(EXAMPLES)} worked examples counted separately"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
