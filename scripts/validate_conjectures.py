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
# `MAIS-O29` or `MAIS-O29(b)`: the printed target a row is about, so several
# rows can share one problem and the table reads per-problem. O34 already had
# two rows before this field existed and nothing said they were one problem.
PROBLEM_ID = re.compile(r"MAIS-O\d{1,2}(?:\([a-c]\))?")
RETIRED_CONJECTURE_HEADING = re.compile(r"(?m)^## (CONJ-\d{3})\b")
# What a row *is*. The ledger was built for one shape -- a truth-valued `Prop`
# somebody doubts -- and MAIS-A2 contains exactly one printed `conjecture`
# against eleven `problem`s and two `question`s. A problem reading "determine
# the asymptotics" is resolved by determining them; what it cannot have is a
# `Prop` that is `Same` as the instruction, which is a fact about transcription
# and not about solvability. Keeping such problems out of the ledger left the
# atlas with no single index of what it covers, and a reader who opened
# `conjectures.yaml` concluded the formalization stopped where the rows did.
#
#   claim   -- print states something true-or-false; `lean` is that `Prop`.
#   answer  -- somebody proposed an answer to a determine-problem and `lean`
#              grades "this answer is correct". CONJ-009 and CONJ-010 were
#              already this and the field only names it.
#   target  -- print says determine/exhibit and no answer is proposed. `lean`
#              points at the *specification*, never at a record a solver fills:
#              inhabiting a bare structure proves nothing, which is the failure
#              the answer-construction literature names first.
#   blocked -- the atlas cannot state it at all; no Lean object exists.
KIND_VALUES = {"claim", "answer", "target", "blocked"}
CONJECTURE_KINDS = {"claim", "answer"}

# Whether a *circular* answer is excluded. `{x | P x}` satisfies any find-all
# specification, and no Lean check rejects it; Formal Conjectures says as much
# and declines to police it, and ECP adds a separate admissible-vocabulary
# layer instead. So the ledger records which of two very different situations
# holds, because a single "none" would collapse them:
#   NotApplicable -- the row is not an answer-construction row.
#   NoneRequired  -- the source asks for no explicit/computable/closed form.
#   Unformalized  -- the source does ask, and the atlas has not encoded it.
#                    That is an open formalization gap, not a clean state.
#   Formalized    -- an admissibility predicate exists and is named.
#   Partial       -- a multi-clause row where some clauses have one and some
#                    do not. Without this value such a row has to round to
#                    `Formalized`, which claims a clause that is open, or to
#                    `Unformalized`, which hides a predicate that exists; the
#                    positional `answer_admissible` list says which clauses are
#                    which, and the rule below makes the value checkable rather
#                    than a matter of the author's mood.
ADMISSIBILITY_VALUES = {
    "NotApplicable",
    "NoneRequired",
    "Unformalized",
    "Formalized",
    "Partial",
}

REQUIRED_FIELDS = {
    "id",
    "kind",
    "problem",
    # A Lean *type expression* -- `ℝ`, `Set (ℝ × ℝ)`, `AISafetyAtlas.Causal.
    # O24Solution` -- and never a prose description of one. `answer_admissible`
    # and `answer_correct` are declaration names or empty.
    "answer_candidate",
    "answer_admissible",
    "answer_correct",
    "admissibility_status",
    "blocked_on",
    "absent_declarations",
    "statement",
    "refutation",
    "prior_art",
    "lean",
    # The module a reader must import to see `lean`. Not derivable: a
    # declaration's namespace is not its module, and `O24Solution` lives in the
    # `AISafetyAtlas.Causal` namespace and the
    # `AISafetyAtlas.Causal.EffectiveGenericity` module. Deriving it worked only
    # while every row's namespace happened to coincide with its file.
    "lean_module",
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
# `NotFormalized` is the sentinel for a `blocked` row: there is no Lean object,
# so there is nothing to be `Same` as. It is a value rather than an empty cell
# because eight rules below read this field, and a blank would need eight
# carve-outs -- of which the one somebody forgets fails open.
SOURCE_SCOPE_VALUES = {
    "Same", "Narrower", "Mixed", "Retired", "Beyond", "NotFormalized",
}

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
    "NotFormalized",
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
    next_id = data.get("next_id")
    if not isinstance(next_id, int) or isinstance(next_id, bool) or next_id < 1:
        fail("conjectures.yaml next_id must be a positive integer")
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

        kind = entry["kind"]
        if kind not in KIND_VALUES:
            fail(
                f"{cid} has unknown kind {kind!r}; expected one of "
                f"{sorted(KIND_VALUES)}"
            )
        blocked = kind == "blocked"

        # A conjecture nobody can attack is a slogan. Requiring the refutation
        # condition up front is the cheapest filter there is: it costs a
        # serious proposer one sentence and stops the rest. A `blocked` row has
        # no statement to attack, so it owes `blocked_on` instead, below.
        fields = ["statement", "prior_art", "proposed_by"]
        if not blocked:
            fields.append("refutation")
        for field in fields:
            if not nonempty_text(entry[field]):
                fail(f"{cid} must record a non-empty {field}")
        if blocked and nonempty_text(entry["refutation"]):
            fail(
                f"{cid} is blocked and records a refutation; there is no stated "
                "claim to refute until the substrate exists"
            )

        for field in ("problem", "blocked_on"):
            if not isinstance(entry[field], str):
                fail(f"{cid} {field} must be a string (empty is fine)")
        # One entry per printed clause, in print's order. A printed problem gets
        # ONE row -- `prob:floor` is a single problem environment with three
        # clauses, and splitting it into three rows on 2026-08-24 was the schema
        # driving the data rather than the source, since these fields were
        # single strings. The lists are positional, so a row with two of them
        # populated must populate them to the same length or the correspondence
        # is guesswork.
        lengths = {}
        for field in ("answer_candidate", "answer_admissible", "answer_correct"):
            value = entry[field]
            if not isinstance(value, list) or any(
                not isinstance(item, str) for item in value
            ):
                fail(f"{cid} {field} must be a list of strings (empty is fine)")
            if value:
                lengths[field] = len(value)
        if len(set(lengths.values())) > 1:
            fail(
                f"{cid} answer fields disagree on clause count {lengths}; the "
                "lists are positional, one entry per printed clause in print's "
                "order, so a shorter one makes the correspondence guesswork"
            )
        if entry["problem"] and not PROBLEM_ID.fullmatch(entry["problem"]):
            fail(
                f"{cid} problem {entry['problem']!r} must look like MAIS-O31 or "
                "MAIS-O29(b); leave it empty for a row with no printed problem"
            )

        admissibility = entry["admissibility_status"]
        if admissibility not in ADMISSIBILITY_VALUES:
            fail(
                f"{cid} has unknown admissibility_status {admissibility!r}; "
                f"expected one of {sorted(ADMISSIBILITY_VALUES)}"
            )
        # Only a row that carries an answer can say anything about whether a
        # circular one is excluded.
        answer_shaped = kind in {"answer", "target"}
        if answer_shaped and admissibility == "NotApplicable":
            fail(
                f"{cid} is kind {kind!r} and records admissibility_status "
                "'NotApplicable'; an answer-construction row must say whether a "
                "circular answer is excluded, and 'Unformalized' is the honest "
                "value when the source asks for an explicit form and the atlas "
                "has not encoded one"
            )
        # `Partial` is a claim about the shape of `answer_admissible`, so it is
        # checked against it. A row that names a predicate for every clause is
        # `Formalized` and one that names none is `Unformalized`; `Partial` is
        # only honest in between, and saying it elsewhere would let a row look
        # more open, or more closed, than its own fields.
        if admissibility == "Partial":
            named = [a for a in entry["answer_admissible"] if a]
            missing = [a for a in entry["answer_admissible"] if not a]
            if not named or not missing:
                fail(
                    f"{cid} records admissibility_status 'Partial', but its "
                    f"answer_admissible list names {len(named)} predicate(s) "
                    f"and leaves {len(missing)} clause(s) empty; 'Partial' "
                    "means some clauses have an admissibility predicate and "
                    "some do not, so both counts must be nonzero"
                )
        if admissibility == "Formalized" and entry["answer_admissible"] and not all(
            entry["answer_admissible"]
        ):
            fail(
                f"{cid} records admissibility_status 'Formalized' while "
                "leaving a clause of answer_admissible empty; use 'Partial', "
                "which says which clauses are covered"
            )
        if not answer_shaped and admissibility != "NotApplicable":
            fail(
                f"{cid} is kind {kind!r} and records admissibility_status "
                f"{admissibility!r}; admissibility is a property of an answer, "
                "and this row does not carry one"
            )
        if admissibility == "Formalized" and not any(entry["answer_admissible"]):
            fail(
                f"{cid} records admissibility_status 'Formalized' but names no "
                "answer_admissible predicate; the label is not the artifact"
            )

        # A target row points at the specification, and the specification is a
        # predicate over a candidate answer. Naming only a type would let a row
        # advertise a fillable record, which is the shape that proves nothing.
        if kind == "target" and not entry["answer_candidate"]:
            fail(
                f"{cid} is a target row and names no answer_candidate; a "
                "determine-problem's row must say what type an answer has"
            )
        # And what makes an answer *right*. A candidate type alone is the
        # fillable-record shape: a solver could inhabit it and prove nothing.
        # CONJ-013 carried three clauses with two specifications for a day, and
        # nothing said so; the empty entry sat in a list the eye reads as full.
        if kind == "target" and (
            not entry["answer_correct"] or not all(entry["answer_correct"])
        ):
            fail(
                f"{cid} is a target row whose answer_correct is "
                f"{entry['answer_correct']}; every printed clause needs the "
                "predicate that decides whether a proposed answer to it is right, "
                "or the row advertises a type a solver can inhabit for free. For "
                "an exhibit-problem whose candidate type carries the obligations "
                "in its own fields, name that type in both -- `O24Solution` is "
                "the case, and the two fields agreeing is the shape rather than "
                "an omission"
            )
        # `all([])` is `True`, so the emptiness test above has to be written
        # separately from the entry test. Without it the rule passed over
        # precisely the row that registered no correctness predicate at all,
        # while the guide said the validator enforced one -- a check that reads
        # as enforcing and does not is worse than no check, because the
        # documentation is then wrong on its own authority.

        absent = entry["absent_declarations"]
        if not isinstance(absent, list) or any(
            not isinstance(name, str) or not name.strip() for name in absent
        ):
            fail(f"{cid} absent_declarations must be a list of non-empty strings")
        if blocked:
            if not nonempty_text(entry["blocked_on"]):
                fail(f"{cid} is blocked and must record what blocks it")
            if len(cast("str", entry["blocked_on"]).strip()) < MIN_SOURCE_NOTE:
                fail(
                    f"{cid} blocked_on is too short; naming the missing "
                    f"substrate is the whole content of a blocked row (need "
                    f"{MIN_SOURCE_NOTE}+ characters)"
                )
            if not absent:
                fail(
                    f"{cid} is blocked and names no absent_declarations; a "
                    "blocked row that lists nothing is a note that rots, and "
                    "check_cited_declarations.py fails when a named absence "
                    "turns out to exist"
                )
            if entry["status"] != "OPEN":
                fail(f"{cid} is blocked, so its status must be OPEN")
        else:
            if nonempty_text(entry["blocked_on"]):
                fail(f"{cid} is not blocked but records blocked_on")
            if absent:
                fail(
                    f"{cid} is not blocked but names absent_declarations; the "
                    "tripwire belongs to rows that claim something is missing"
                )

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
        # `NotFormalized` says the same thing from three sides: no Lean object,
        # so no scope grade and no reading of print. Requiring all three to
        # agree keeps a blocked row from carrying a grade it cannot have earned.
        not_formalized = {
            scope == "NotFormalized",
            "NotFormalized" in fidelity,
            blocked,
        }
        if len(not_formalized) != 1:
            fail(
                f"{cid} is kind {kind!r} with scope {scope!r} and fidelity "
                f"{sorted(fidelity)}; 'blocked', scope 'NotFormalized' and "
                "fidelity 'NotFormalized' are one fact and must be used together"
            )
        if "NotFormalized" in fidelity and len(fidelity) > 1:
            fail(
                f"{cid} pairs NotFormalized with "
                f"{sorted(set(fidelity) - {'NotFormalized'})}; there is no Lean "
                "statement for another kind to describe"
            )
        if ("AtlasOriginal" in fidelity) != (scope == "Beyond"):
            fail(
                f"{cid} is {scope}/{sorted(fidelity)}; scope 'Beyond' and fidelity "
                "'AtlasOriginal' are the same fact seen from two sides and must "
                "be used together"
            )

        # MAIS rows are source-first by project policy. A flaw in the printed
        # statement is a finding about MAIS, not permission for the atlas to
        # repair the conjecture by narrowing it or supplying a bridge. Useful
        # repaired variants may remain in Lean, but they do not belong in the
        # live MAIS ledger. `Selected` is still source-faithful when MAIS itself
        # asks the reader to decide a truth-valued branch.
        mais_refs = [ref for ref in refs if ref.startswith("mais-")]
        if mais_refs and not blocked and scope != "Same":
            fail(
                f"{cid} is graded against MAIS source(s) {mais_refs} but has "
                f"source_scope {scope!r}; every MAIS ledger row must be 'Same'. "
                "Record source defects literally and keep atlas-only or retired "
                "variants outside the live MAIS ledger"
            )
        if mais_refs and "Bridged" in fidelity:
            fail(
                f"{cid} is graded against MAIS source(s) {mais_refs} but uses "
                "source_fidelity 'Bridged'; a MAIS row may not substitute an "
                "atlas-supplied object for the source statement"
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
        needs_note = not blocked and (
            withdrawn or scope != "Same" or fidelity != ["Literal"]
        )
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
        if blocked:
            if nonempty_text(entry["lean_module"]):
                fail(f"{cid} is blocked and names a lean_module")
            if nonempty_text(lean):
                fail(
                    f"{cid} is blocked and names a Lean declaration {lean!r}; a "
                    "blocked row is the record that none exists"
                )
            continue
        # A `claim` or an `answer` is a doubted `Prop` and must stay off the
        # public surface. A `target` points at a *specification*, which is an
        # ordinary definition other code may legitimately use -- `O24Solution`
        # lives in `AISafetyAtlas.Causal` and is imported by the O26 statement.
        # Holding it to the conjecture namespace would force a real definition
        # off the surface to satisfy a rule written for unproved claims.
        if not nonempty_text(lean):
            fail(f"{cid} must name a Lean declaration")
        if kind in CONJECTURE_KINDS and not lean.startswith(CONJECTURE_NAMESPACE):
            fail(f"{cid} Lean statement must live under {CONJECTURE_NAMESPACE}*: {lean!r}")
        if not lean.startswith("AISafetyAtlas."):
            fail(f"{cid} Lean declaration must live under AISafetyAtlas.*: {lean!r}")
        module = entry["lean_module"]
        if not nonempty_text(module):
            fail(f"{cid} must name the lean_module that carries {lean!r}")
        if not (ROOT / (module.replace(".", "/") + ".lean")).is_file():
            fail(f"{cid} lean_module {module!r} is not a Lean file")
        if not lean.startswith(module.rsplit(".", 1)[0]):
            fail(
                f"{cid} lean_module {module!r} does not plausibly carry {lean!r}"
            )
        root_reachable = bool(
            re.search(
                rf"(?m)^\s*(?:public\s+)?import\s+.*\b{re.escape(module)}\b",
                root_source,
            )
        )
        if module not in build_targets and not root_reachable:
            fail(
                f"{cid} names module {module} which is neither an explicit Lean "
                "build target nor reachable from the atlas root import; an "
                "unbuilt statement is not a checked statement"
            )
        # Containment is about *doubt*, not about determine-problems. An
        # unproved `Prop` on the public surface would let a conjecture be
        # mistaken for a result, which is what this rule exists to stop. A
        # specification asserts nothing to be mistaken for anything, and forcing
        # one off the surface would mean `O24Solution` -- which the MAIS-O26
        # statement imports -- could not be the object its own row names.
        if kind in CONJECTURE_KINDS and root_reachable:
            fail(
                f"{cid} module {module} is reachable from the atlas root import; "
                "a doubted Prop must stay off the public surface"
            )

    # A row may leave the ledger — a withdrawn encoding, or an atlas-original
    # variant the source-first rule keeps out. Parse archive headings rather
    # than searching for an id anywhere in the prose: a cross-reference is not
    # a retirement record. Include archived ids above the current live maximum,
    # and reject live/archive overlap so a retired number cannot be reused.
    retired_path = ROOT / "docs" / "provenance" / "retired-conjecture-rows.md"
    retired_text = retired_path.read_text(encoding="utf-8") if retired_path.is_file() else ""
    retired_list = RETIRED_CONJECTURE_HEADING.findall(retired_text)
    retired_seen = set(retired_list)
    duplicate_retired = sorted(cid for cid in retired_seen if retired_list.count(cid) > 1)
    if duplicate_retired:
        fail(f"retired conjecture archive repeats headings for {duplicate_retired}")

    reused = sorted(seen & retired_seen)
    if reused:
        fail(
            f"conjecture ids {reused} appear in both the live ledger and the retired "
            "archive; retired numbers must not be reused"
        )

    recorded = seen | retired_seen
    assigned = {f"CONJ-{n:03d}" for n in range(1, next_id)}
    missing = sorted(assigned - recorded)
    unexpected = sorted(recorded - assigned)
    if missing:
        fail(
            f"conjecture numbering skips assigned ids {missing}; every number below "
            "conjectures.yaml next_id must be recorded exactly once, live or retired"
        )
    if unexpected:
        fail(
            f"conjecture ids {unexpected} are not below next_id {next_id}; assign the "
            "next id monotonically and advance next_id"
        )

    # Report the breakdown, not a single count. "8 recorded, 4 open" over a
    # file that also holds targets and blocked rows is how a reader concludes
    # the formalization stops where the conjectures do -- which is the reading
    # this schema exists to prevent, and printing one number would reintroduce
    # it at the point of highest trust.
    by_kind = {kind: 0 for kind in sorted(KIND_VALUES)}
    for entry in entries:
        by_kind[entry["kind"]] += 1
    conjectures = [e for e in entries if e["kind"] in CONJECTURE_KINDS]
    open_conjectures = sum(entry["status"] == "OPEN" for entry in conjectures)
    print(
        f"conjectures ok: {len(entries)} rows -- "
        f"{len(conjectures)} conjectures ({open_conjectures} open), "
        f"{by_kind['target']} targets, {by_kind['blocked']} blocked"
    )


if __name__ == "__main__":
    main()
