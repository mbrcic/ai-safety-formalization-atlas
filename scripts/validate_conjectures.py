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
from typing import Any, NoReturn, cast

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
    "source_ref",
    "context_source_ref",
    "source_scope",
    "source_fidelity",
    "source_note",
}

# A conjecture is what gets doubted and proved, so its `Prop` must be the
# printed statement, not a version of it the atlas finds convenient. Definitions
# are held to the same bar for the same reason — they are the objects under
# discussion. Theorems are exempt and preferred *wider*: a proved lemma that
# reaches further only increases what the tooling can be used for.
# `Retired` is reserved for WITHDRAWN entries, where there is no live claim to
# be `Same` as; it is required there and forbidden everywhere else.
# `Beyond` is for a conjecture the atlas originated: there is no printed
# statement to be `Same` as, because the source never asks the question. It is
# not a licence to drift — the entry must say which printed result the question
# is *about*, and why the source does not settle it.
SOURCE_SCOPE_VALUES = {"Same", "Narrower", "Mixed", "Retired", "Beyond"}

# How the `Prop` relates to the printed sentence, as a kind rather than a grade.
#   Literal          — the `Prop` transcribes the printed statement.
#   Selected         — print says "decide whether X"; the atlas states one
#                      branch, which is a truth-valued statement print asked for.
#   Bridged          — an atlas-supplied object stands in for something print
#                      leaves implicit or defers to an unsolved problem.
#   DetermineProblem — print asks to *determine* a quantity or a set. No
#                      truth-valued `Prop` can be the same statement; this is a
#                      category, not a defect, and the entry must say what shape
#                      replaces it.
#   AtlasOriginal    — the source contains no counterpart sentence at all. The
#                      question is the atlas's, usually asked *about* a printed
#                      result rather than transcribed from one.
# A `Prop` can relate to print in more than one way at once — one branch of a
# decide-clause, stated over an atlas stand-in — so the field accepts a list.
# A bare string is read as a one-element list.
SOURCE_FIDELITY_VALUES = {
    "Literal",
    "Selected",
    "Bridged",
    "DetermineProblem",
    "AtlasOriginal",
}

# Language that declares a narrowing inside the statement itself. Harmless when
# the entry admits a narrowing; a contradiction when it claims `Same`.
SPECIALIZATION_PHRASES = (
    "specialization",
    "specialisation",
    "in the atlas's",
    "subfamily",
    "restricted to the atlas",
)

# A narrowing has to be argued, not labelled. Short enough that one honest
# sentence clears it, long enough that a bare word does not.
MIN_SOURCE_NOTE = 80


def fail(message: str) -> NoReturn:
    print(f"conjectures error: {message}", file=sys.stderr)
    raise SystemExit(1)


def require_mapping(value: object, message: str) -> dict[str, Any]:
    """Return `value` as a JSON object, or fail with an actionable reason.

    `isinstance(value, dict)` narrows only to `dict[Unknown, Unknown]`, whose
    key type is `Never`, so every subsequent subscript reads as an error. One
    spelling for "this must be an object" keeps the narrowing honest and the
    message uniform.
    """
    if not isinstance(value, dict):
        fail(message)
    return cast("dict[str, Any]", value)



def nonempty_text(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def main() -> None:
    try:
        data = json.loads(CONJECTURES.read_text(encoding="utf-8"))
        registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(str(error))

    data = require_mapping(data, "conjectures.yaml must contain an object")
    registry = require_mapping(registry, "registry.yaml must contain an object")
    if data.get("schema_version") != 1:
        fail("conjectures.yaml must use schema_version 1")
    entries = data.get("conjectures")
    if not isinstance(entries, list):
        fail("conjectures must be a list")

    vocabulary = require_mapping(
        registry.get("vocabulary", {}), "registry vocabulary must be an object"
    )
    raw_tags = vocabulary.get("tag")
    if not isinstance(raw_tags, list) or any(
        not isinstance(tag, str) or not tag.strip() for tag in raw_tags
    ):
        fail("registry vocabulary.tag must be a list of non-empty strings")
    tag_values = set(raw_tags)
    if not tag_values:
        fail("registry vocabulary.tag must be populated before conjecture tags validate")

    source_catalog = require_mapping(
        registry.get("source_catalog", {}), "registry source_catalog must be an object"
    )

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
        entry = require_mapping(entry, f"conjecture {index} must be an object")
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

        if not isinstance(entry["status"], str) or entry["status"] not in STATUS_VALUES:
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

        # The scope grade is a claim about a specific artifact, so it must name
        # one. Without a pinned source there is nothing to be `Same` as, which
        # is exactly the state MAIS was in until 2026-08-20.
        refs = entry["source_ref"]
        if not isinstance(refs, list) or not refs:
            fail(f"{cid} must name at least one registry source in source_ref")
        unknown_refs = [r for r in refs if r not in source_catalog]
        if unknown_refs:
            fail(f"{cid} source_ref names sources absent from registry.yaml: {sorted(unknown_refs)}")

        # `source_ref` names the artifact whose *statement* is transcribed;
        # `context_source_ref` names what the work draws on without being
        # graded against — a definition it reuses, an issue that supplied a
        # witness. Keeping them in one field made a single `Same` cell answer to
        # artifacts of different genre at once: CONJ-009 was graded against both
        # a GitHub issue's criterion and a MAIS-A2 clause that says "Determine
        # …", which no truth-valued `Prop` can be `Same` as.
        context_refs = entry["context_source_ref"]
        if not isinstance(context_refs, list):
            fail(f"{cid} context_source_ref must be a list (empty is fine)")
        unknown_context = [r for r in context_refs if r not in source_catalog]
        if unknown_context:
            fail(
                f"{cid} context_source_ref names sources absent from registry.yaml: "
                f"{sorted(unknown_context)}"
            )
        overlap = set(refs) & set(context_refs)
        if overlap:
            fail(
                f"{cid} lists {sorted(overlap)} as both a graded source and a "
                "context source; an artifact is either the one the statement is "
                "transcribed from or one the work draws on, not both"
            )
        # A DOI-fixed publication does not move, so its locator *is* the pin.
        # Anything else — a repository file, an issue body, a living page — is
        # rewritten without notice and needs a hash of the bytes that were read.
        missing_pin = [
            r
            for r in refs
            if not nonempty_text(source_catalog[r].get("content_sha256"))
            and "doi.org" not in str(source_catalog[r].get("locator", ""))
        ]
        if missing_pin:
            fail(
                f"{cid} is graded against unpinned sources {sorted(missing_pin)}; "
                "a Same/Narrower verdict about a moving artifact is unfalsifiable, "
                "so a graded source needs either a DOI locator or a content_sha256"
            )

        scope = entry["source_scope"]
        if scope not in SOURCE_SCOPE_VALUES:
            fail(
                f"{cid} has unknown source_scope {scope!r}; expected one of "
                f"{sorted(SOURCE_SCOPE_VALUES)}"
            )
        raw_fidelity = entry["source_fidelity"]
        # One `Prop` can stand in more than one relation to print at once, so a
        # list is allowed; a bare string is the one-element case.
        fidelity = (
            [raw_fidelity] if isinstance(raw_fidelity, str) else raw_fidelity
        )
        if not isinstance(fidelity, list) or not fidelity:
            fail(
                f"{cid} source_fidelity must be a value or a non-empty list of them"
            )
        if any(not isinstance(f, str) for f in fidelity):
            fail(f"{cid} source_fidelity entries must be strings")
        if len(set(fidelity)) != len(fidelity):
            fail(f"{cid} source_fidelity repeats a value: {fidelity}")
        unknown_fidelity = [f for f in fidelity if f not in SOURCE_FIDELITY_VALUES]
        if unknown_fidelity:
            fail(
                f"{cid} has unknown source_fidelity {sorted(unknown_fidelity)}; "
                f"expected values from {sorted(SOURCE_FIDELITY_VALUES)}"
            )
        # `AtlasOriginal` says there is no printed sentence behind the `Prop`.
        # Pairing it with a kind that describes how a printed sentence was read
        # asserts both that print says something and that it does not.
        if "AtlasOriginal" in fidelity and len(fidelity) > 1:
            fail(
                f"{cid} pairs AtlasOriginal with {sorted(set(fidelity) - {'AtlasOriginal'})}; "
                "AtlasOriginal means the source has no counterpart statement, so "
                "there is nothing for another kind to describe"
            )
        if ("AtlasOriginal" in fidelity) != (scope == "Beyond"):
            fail(
                f"{cid} is {scope}/{sorted(fidelity)}; scope 'Beyond' and fidelity "
                "'AtlasOriginal' are the same fact seen from two sides and must "
                "be used together"
            )

        note = entry["source_note"]
        if not isinstance(note, str):
            fail(f"{cid} source_note must be a string")
        # A withdrawn conjecture has no live claim, so there is nothing left to
        # be `Same` as. Its grade records the statement that was retired and
        # usually *is* the reason for the retirement, so the note is required
        # rather than forbidden, whatever the scope cell says.
        withdrawn = entry["status"] == "WITHDRAWN"
        if withdrawn and scope != "Retired":
            fail(
                f"{cid} is WITHDRAWN, so its source_scope must be 'Retired': "
                "a retired statement is not graded against a printed one"
            )
        if not withdrawn and scope == "Retired":
            fail(f"{cid} is not WITHDRAWN, so its source_scope cannot be 'Retired'")
        # Grading one cell against several artifacts hides which of them the
        # verdict is about. Provenance beyond the single graded artifact belongs
        # in `context_source_ref`, where nothing claims to be `Same` as it.
        if len(refs) > 1 and scope in {"Same", "Beyond"}:
            fail(
                f"{cid} is scope {scope} against {len(refs)} sources {sorted(refs)}; "
                "one grade cannot answer to several artifacts at once — name the "
                "one whose statement is transcribed and move the rest to "
                "context_source_ref"
            )
        needs_note = withdrawn or scope != "Same" or fidelity != ["Literal"]
        if needs_note and len(note.strip()) < MIN_SOURCE_NOTE:
            fail(
                f"{cid} is {scope}/{sorted(fidelity)} and must argue it in "
                f"source_note; a narrowing or a bridge is a debt, and a label is "
                f"not the argument (need {MIN_SOURCE_NOTE}+ characters)"
            )
        # A Same/Literal entry *may* carry a note, and the earlier rule that it
        # must not was this schema's worst defect: the rows claiming perfect
        # fidelity were the only ones structurally barred from disclosing how a
        # printed sentence was read, so every such disclosure migrated into Lean
        # docstrings where no validator and no reader of the ledger sees it. The
        # discipline that rule was reaching for is kept, and aimed at the right
        # target: a note here must be an argument, not a hedge.
        if not needs_note and note.strip() and len(note.strip()) < MIN_SOURCE_NOTE:
            fail(
                f"{cid} is Same/Literal with a short source_note; a note here is "
                f"welcome and should record what was read from the source rather "
                f"than supplied, but a fragment is a hedge (need "
                f"{MIN_SOURCE_NOTE}+ characters, or leave it empty)"
            )

        # Claiming `Same` while the statement announces a specialization is a
        # contradiction the reader should never have to catch by hand.
        if scope == "Same":
            statement_text = cast("str", entry["statement"]).lower()
            found = [p for p in SPECIALIZATION_PHRASES if p in statement_text]
            if found:
                fail(
                    f"{cid} claims source_scope Same but its statement declares a "
                    f"specialization: {sorted(found)}. Either the statement is at "
                    "the printed quantifier and the words should go, or the scope "
                    "is not Same"
                )

        tags = entry["tags"]
        if not isinstance(tags, list) or not tags:
            fail(f"{cid} must carry at least one tag")
        if any(not isinstance(tag, str) or not tag.strip() for tag in tags):
            fail(f"{cid} tags must be non-empty strings")
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
