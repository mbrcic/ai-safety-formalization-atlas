#!/usr/bin/env python3
"""Validate the conjecture ledger.

A conjecture is an open question with a compiling Lean statement and no proof.
The rules exist to keep two things true at once: the ledger stays open to
strangers, and nothing in it can ever be mistaken for a result.

Containment is structural rather than editorial. Conjecture modules live under
`AISafetyAtlas.Conjectures.*` and are never reachable from the atlas root
import, so a badly judged conjecture cannot reach the public API no matter who
merged it. `sorry` stays banned repo-wide: a conjecture is a `Prop`-valued
definition, which asserts nothing, plus a generated `example : Prop := <name>`
requiring it to be a closed proposition. A string that looks like a declaration
is not a declaration, and `#check` would be too weak — it prints whatever type a
declaration happens to have rather than demanding one.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from validate_current_state import (  # noqa: E402
    dependency_closure,
    lean_code_without_comments_or_strings,
    lean_module_name,
    local_imports,
)


ROOT = Path(__file__).resolve().parents[1]
CONJECTURES = ROOT / "conjectures.yaml"
REGISTRY = ROOT / "registry.yaml"
LEAN_ROOT = ROOT / "AISafetyAtlas.lean"
LEAN_BUILD_TARGETS = ROOT / "scripts/lean_build_targets.txt"
CONJECTURE_NAMESPACE = "AISafetyAtlas.Conjectures."
STATUS_VALUES = {"OPEN", "RESOLVED", "WITHDRAWN"}
TERMINAL_STATUS_VALUES = {"RESOLVED", "WITHDRAWN"}
CONJECTURE_ID = re.compile(r"CONJ-\d{3}")
REQUIRED_FIELDS = {
    "id",
    "statement",
    "refutation",
    "prior_art",
    "lean",
    "tags",
    "proposed_by",
    "status",
    "resolution",
}


def fail(message: str) -> None:
    print(f"conjectures error: {message}", file=sys.stderr)
    raise SystemExit(1)


def nonempty_text(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def main() -> None:
    try:
        data = json.loads(CONJECTURES.read_text(encoding="utf-8"))
        registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))

    if data.get("schema_version") != 1:
        fail("conjectures.yaml must use schema_version 1")
    entries = data.get("conjectures")
    if not isinstance(entries, list):
        fail("conjectures must be a list")

    tag_values = set(registry.get("vocabulary", {}).get("tag") or [])
    if not tag_values:
        fail("registry vocabulary.tag must be populated before conjecture tags validate")

    # Containment must hold for the namespace, not merely for the conjectures
    # that happen to be recorded: an unrecorded module under
    # AISafetyAtlas.Conjectures.* reaching the root would put an unproved
    # statement on the public surface with nothing objecting.
    sources = {}
    for path in [ROOT / "AISafetyAtlas.lean", *sorted((ROOT / "AISafetyAtlas").rglob("*.lean"))]:
        sources[lean_module_name(path)] = lean_code_without_comments_or_strings(
            path.read_text(encoding="utf-8")
        )
    graph = {
        module: local_imports(code, set(sources)) for module, code in sources.items()
    }
    reachable = dependency_closure("AISafetyAtlas", graph)
    leaked = sorted(m for m in reachable if m.startswith(CONJECTURE_NAMESPACE))
    if leaked:
        fail(
            "the atlas root import reaches conjecture modules, which would put "
            f"unproved statements on the public surface: {leaked}"
        )

    root_source = LEAN_ROOT.read_text(encoding="utf-8")
    build_targets = {
        line.strip()
        for line in LEAN_BUILD_TARGETS.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }

    seen: set[str] = set()
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            fail(f"conjecture {index} must be an object")
        missing = REQUIRED_FIELDS - entry.keys()
        if missing:
            fail(f"conjecture {index} missing fields: {sorted(missing)}")
        extra = entry.keys() - REQUIRED_FIELDS
        if extra:
            fail(f"conjecture {index} has unknown fields: {sorted(extra)}")

        cid = entry["id"]
        if not isinstance(cid, str) or not CONJECTURE_ID.fullmatch(cid):
            fail(f"conjecture id must match CONJ-###: {cid!r}")
        if cid in seen:
            fail(f"duplicate conjecture id {cid}")
        seen.add(cid)

        # A conjecture nobody can attack is a slogan. Requiring the refutation
        # condition up front is the cheapest filter there is: it costs a
        # serious proposer one sentence and stops the rest.
        for field in ("statement", "refutation", "prior_art", "proposed_by"):
            if not nonempty_text(entry[field]):
                fail(f"{cid} must record a non-empty {field}")

        if entry["status"] not in STATUS_VALUES:
            fail(f"{cid} has unknown status {entry['status']!r}")
        # Every terminal status carries its reason, withdrawal included. A
        # conjecture that leaves the queue without a recorded argument is an
        # undocumented decision, and the next person re-proposes it.
        terminal = entry["status"] in TERMINAL_STATUS_VALUES
        if terminal != nonempty_text(entry["resolution"]):
            fail(
                f"{cid} must record a resolution exactly when its status is "
                f"terminal ({sorted(TERMINAL_STATUS_VALUES)}); status is "
                f"{entry['status']!r}"
            )

        tags = entry["tags"]
        if not isinstance(tags, list) or not tags:
            fail(f"{cid} must carry at least one tag")
        unknown_tags = [tag for tag in tags if tag not in tag_values]
        if unknown_tags:
            fail(f"{cid} has tags outside the vocabulary: {sorted(unknown_tags)}")

        lean = entry["lean"]
        if not nonempty_text(lean) or not lean.startswith(CONJECTURE_NAMESPACE):
            fail(f"{cid} Lean statement must live under {CONJECTURE_NAMESPACE}*: {lean!r}")
        module = lean.rsplit(".", 1)[0]
        if module not in build_targets:
            fail(
                f"{cid} names module {module} which is not an explicit Lean build "
                "target; an unbuilt statement is not a checked statement"
            )
        if re.search(rf"(?m)^\s*(?:public\s+)?import\s+.*\b{re.escape(module)}\b", root_source):
            fail(
                f"{cid} module {module} is reachable from the atlas root import; "
                "conjectures must stay off the public surface"
            )

    open_count = sum(entry["status"] == "OPEN" for entry in entries)
    print(f"conjectures ok: {len(entries)} recorded, {open_count} open")


if __name__ == "__main__":
    main()
