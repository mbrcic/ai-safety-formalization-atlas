#!/usr/bin/env python3
"""Report facade primary-surface entries that the ledger does not record.

Each facade module docstring publishes a small table of the results a reader
should start from — rows marked **Law**, **Bridge**, **Boundary**, **Model**, or
**Core**. Those tables are curated by whoever wrote the module. The ledger is a
separate list, and the two drift: an entire module of compositional boundary
results sat on the public root import with no registry row at all, and the weak
Rashomon attribution theorem was published in `Explainability`'s own table while
appearing in no index.

This is a **work queue, not a gate**, and deliberately feeds no generated view —
the same footing as `report_consumers.py`. Not every primary-surface entry
should become a registry declaration: a model structure is not a result, and a
row that already records its headline theorem does not need every variant. What
the queue is for is making the decision explicit instead of leaving the gap
where nobody looks.

Usage:
    python3 scripts/report_surface_gaps.py
    python3 scripts/report_surface_gaps.py --module Compositional
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from typing import NamedTuple

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "registry.yaml"
LEAN_DIR = ROOT / "AISafetyAtlas"

# `| **Law** | `name` | description |` in a facade docstring.
SURFACE_ROW = re.compile(
    r"^\|\s*\*\*(Law|Bridge|Boundary|Model|Core)\*\*\s*\|\s*`([^`]+)`\s*\|([^|]*)\|",
    re.M,
)


class Entry(NamedTuple):
    module: str
    kind: str
    name: str
    description: str


def ledger_leaves() -> set[str]:
    """Leaf names of every declaration the registry records.

    Matching on the leaf, because a facade table writes `Networks.runFor_eq…`
    while the ledger writes the fully qualified name. Leaf matching can collide
    (two declarations sharing a leaf), and that bias hides gaps rather than
    inventing them — the right direction for a queue.
    """
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    return {
        declaration["atlas_declaration"].rsplit(".", 1)[-1]
        for result in registry["results"]
        if result["lean_artifact"] is not None
        for declaration in result["lean_artifact"]["declarations"]
    }


def surface_entries() -> list[Entry]:
    """Every primary-surface row published by a facade docstring."""
    entries: list[Entry] = []
    for path in sorted(LEAN_DIR.rglob("*.lean")):
        if "Upstream" in path.parts or "Examples" in path.parts:
            continue
        module = str(path.relative_to(LEAN_DIR))
        for kind, name, description in SURFACE_ROW.findall(
            path.read_text(encoding="utf-8")
        ):
            entries.append(
                Entry(module, kind, name.strip(), " ".join(description.split()))
            )
    return entries


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--module", help="restrict to facades matching this substring")
    args = parser.parse_args()

    recorded = ledger_leaves()
    entries = surface_entries()
    if args.module:
        entries = [e for e in entries if args.module in e.module]

    gaps = [e for e in entries if e.name.rsplit(".", 1)[-1] not in recorded]
    print(f"facade primary-surface entries: {len(entries)}")
    print(f"  recorded in the ledger : {len(entries) - len(gaps)}")
    print(f"  not recorded           : {len(gaps)}")
    if not gaps:
        return
    print()
    print("Queue — record it as a declaration, or decide it is supporting:")
    current = ""
    for entry in gaps:
        if entry.module != current:
            current = entry.module
            print(f"\n  {current}")
        print(f"    [{entry.kind}] {entry.name}")
        if entry.description:
            print(f"        {entry.description[:88]}")


if __name__ == "__main__":
    sys.exit(main())
