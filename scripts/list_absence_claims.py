#!/usr/bin/env python3
"""Inventory every sentence asserting that something is *not* formalized.

**This is a worklist, not a check.** It cannot fail, and it is not in the gate.
Read the next paragraph before adding it to one.

Four of the stale records this repository has paid for were absence claims that a
later commit falsified: `BayesianNetwork.lean` saying Pearl's (1.38) and (1.39)
"are not here" after they landed in `Model.lean`; `Query.lean` saying the
reverse inequality "is not here" four hundred lines above its proof; the
coverage audit saying Everitt had "no structural layer" after `Causal.SCM`
existed; and three separate records saying a gap "needs a CID layer" after
`Causal.CID` was built.

The obvious mechanization does not work, and it is worth saying why rather than
shipping something that looks like it does. Those four sentences name
**concepts** — "the reverse inequality", "a structural layer", "a CID layer" —
not identifiers. A check that resolved backticked names against the declaration
index would have caught none of them, because none of them contains a backticked
name. Deciding whether "no structural layer" is still true requires knowing what
would count as one, which is the reviewer's job and not a regex's.

So this prints the claims and leaves the judgement alone. Run it after landing
anything that closes a gap; every line is a sentence to re-read, and most will
be fine. `scripts/where_is_graded.py` is the same idea for grades.

    scripts/list_absence_claims.py                 # every claim
    scripts/list_absence_claims.py --module Causal # claims in one subtree
    scripts/list_absence_claims.py --count         # just the totals
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "AISafetyAtlas"
PROSE = ["README.md", "STATE.md", "docs/guide", "docs/provenance", "docs/bridges"]

# Phrases that assert an absence. Kept literal and few: a wider net turns this
# from a worklist into a wall of text, and a worklist nobody reads is worse than
# no worklist.
CLAIMS = [
    (r"\b(?:is|are) not here\b", "not here"),
    (r"\b(?:is|are) not formalized\b", "not formalized"),
    (r"\bnothing (?:here )?formalizes\b", "nothing formalizes"),
    (r"\bno claim here\b", "no claim here"),
    (r"\bhas no (?:atlas )?counterpart\b", "no counterpart"),
    (r"\bdoes not exist\b", "does not exist"),
    (r"\bneeds? an? [a-z][\w-]* layer\b", "needs a layer"),
    (r"\bno [a-z][\w-]* layer\b", "no layer"),
    (r"\bis absent\b", "absent"),
    (r"\bare absent\b", "absent"),
    (r"\bnot built\b", "not built"),
    (r"\bis unavailable\b", "unavailable"),
    (r"\bout of reach\b", "out of reach"),
    (r"\bis missing\b", "missing"),
    (r"\bare missing\b", "missing"),
]
PATTERNS = [(re.compile(p, re.I), label) for p, label in CLAIMS]

DATED = re.compile(r"^(?:Date|HEAD):\s*\S", re.MULTILINE)


def is_frozen(path: Path) -> bool:
    """A dated snapshot records what was true when written; leave it alone."""
    return bool(DATED.search(path.read_text(encoding="utf-8", errors="replace")[:600]))


def targets(module_filter: str | None) -> list[Path]:
    found = [p for p in sorted(SRC.rglob("*.lean"))]
    for entry in PROSE:
        target = ROOT / entry
        if target.is_file():
            found.append(target)
        elif target.is_dir():
            found.extend(sorted(target.rglob("*.md")))
    if module_filter:
        found = [p for p in found if module_filter in str(p)]
    return found


def sentences(text: str) -> list[tuple[int, str]]:
    """`(line, sentence)`, with wrapped lines rejoined.

    Sentence-level rather than line-level on purpose: these claims wrap, and a
    line grep splits *"the reverse inequality … is not here"* across two
    matches or misses it entirely.
    """
    out: list[tuple[int, str]] = []
    line_of: list[int] = []
    flat: list[str] = []
    for num, raw in enumerate(text.splitlines(), start=1):
        flat.append(raw.strip())
        line_of.append(num)
    joined = " ".join(flat)
    # map character offset back to a line number
    offsets: list[tuple[int, int]] = []
    pos = 0
    for num, chunk in zip(line_of, flat):
        offsets.append((pos, num))
        pos += len(chunk) + 1
    for match in re.finditer(r"[^.!?]+[.!?]", joined):
        start = match.start()
        line = 1
        for off, num in offsets:
            if off > start:
                break
            line = num
        out.append((line, match.group(0).strip()))
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", help="only paths containing this string")
    parser.add_argument("--count", action="store_true", help="totals only")
    args = parser.parse_args()

    from collections import Counter

    tally: Counter[str] = Counter()
    total = 0
    frozen = 0
    for path in targets(args.module):
        text = path.read_text(encoding="utf-8", errors="replace")
        if is_frozen(path):
            continue
        rel = path.relative_to(ROOT)
        hits: list[tuple[int, str, str]] = []
        for line, sentence in sentences(text):
            for pattern, label in PATTERNS:
                if pattern.search(sentence):
                    hits.append((line, label, sentence))
                    tally[label] += 1
                    break
        total += len(hits)
        if hits and not args.count:
            print(f"{rel}")
            for line, label, sentence in hits:
                body = sentence if len(sentence) <= 200 else sentence[:197] + "..."
                print(f"  {line:>5}  [{label}]  {body}")
            print()

    for path in targets(args.module):
        if is_frozen(path):
            frozen += 1

    print(f"{total} absence claim(s) across the hand-written corpus.")
    for label, n in tally.most_common():
        print(f"   {n:>4}  {label}")
    if frozen:
        print(f"   ({frozen} dated snapshot(s) skipped — they record the past.)")
    print()
    print("Each line is a sentence to re-read after a gap closes, not a finding.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
