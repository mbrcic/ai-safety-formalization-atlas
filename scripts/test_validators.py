#!/usr/bin/env python3
"""Regression tests: the ledger validators must reject what they claim to reject.

A validator that has never been shown to fail is a validator nobody has tested.
`validate_current_state.validate_scanner_examples` already applies this to the
forbidden-token scanner; this extends it to the registry, conjecture, and task
ledgers, so the rules stay enforced when someone refactors them later.

Each case copies the repository's data files and the validator scripts into a
temporary tree, mutates one field, and asserts the validator exits non-zero with
the expected reason. The real repository is never modified: `ROOT` in each
validator resolves from its own path, so a copy under a temp directory validates
that copy.
"""

from __future__ import annotations

import json
import os
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
DATA = [
    "registry.yaml",
    "conjectures.yaml",
    "tasks.yaml",
    "docs/provenance/formalization-search.json",
]
EXTRA = ["AISafetyAtlas.lean"]
SCRIPTS = [
    "validate_registry.py",
    "validate_conjectures.py",
    "validate_tasks.py",
    # validate_conjectures imports it for the Lean import-graph helpers.
    "validate_current_state.py",
    "lean_build_targets.txt",
]


def build_tree(tmp: Path) -> Path:
    (tmp / "scripts").mkdir(parents=True, exist_ok=True)
    (tmp / "docs/provenance").mkdir(parents=True, exist_ok=True)
    for name in DATA + EXTRA:
        (tmp / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, tmp / name)
    for name in SCRIPTS:
        shutil.copy2(ROOT / "scripts" / name, tmp / "scripts" / name)
    # Registry validation checks that every recorded reproduction command
    # names an executable script, so the copies must carry them too.
    for script in sorted(ROOT.glob("scripts/reproduce_*.sh")):
        shutil.copy2(script, tmp / "scripts" / script.name)
    # Registry validation resolves every in-repository formalization module, so
    # the Lean sources must be present as files (they are never built here).
    shutil.copytree(ROOT / "AISafetyAtlas", tmp / "AISafetyAtlas", dirs_exist_ok=True)
    # ...and every scope_delta names an evidence document that must resolve.
    for docs in ("docs/provenance", "docs/guide", "docs/bridges"):
        shutil.copytree(ROOT / docs, tmp / docs, dirs_exist_ok=True)
    return tmp


def run(tmp: Path, script: str) -> tuple[int, str]:
    done = subprocess.run(
        [sys.executable, str(tmp / "scripts" / script)],
        capture_output=True,
        text=True,
    )
    return done.returncode, (done.stderr + done.stdout).strip()


def mutate(tmp: Path, name: str, change) -> None:
    path = tmp / name
    data = json.loads(path.read_text(encoding="utf-8"))
    change(data)
    path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def first(items, **match):
    return next(i for i in items if all(i[k] == v for k, v in match.items()))


def synthetic_conjecture(data: dict) -> dict:
    """A schema-clean conjecture record to mutate, independent of the ledger.

    The ledger is legitimately empty most of the time — a recorded conjecture is
    a research event, not a fixture. Mutating `conjectures[0]` therefore tests
    whichever entry happens to exist, and raises `IndexError` when none does.
    Seeding a record instead keeps every rule below exercised at all times, and
    keeps the harness from quietly shrinking when the last conjecture resolves.

    Schema-clean, not real: `validate_conjectures.py` checks the namespace
    prefix, the module against `lean_build_targets.txt`, and root-import
    containment — all string-level. It never elaborates, so
    `AISafetyAtlas.Conjectures.Checks.synthetic` satisfies it while naming no
    declaration that exists. That is the right scope for a schema mutation
    harness and the wrong thing to copy into `conjectures.yaml`: a real record
    must name a declaration the generated `Checks.lean` can elaborate, which is
    what CI checks and this file deliberately does not.
    """
    data["next_id"] = 26
    data["conjectures"].insert(
        0,
        {
            "id": "CONJ-025",
            "kind": "claim",
            "problem": "",
            "statement": "Synthetic harness record. Never written to the ledger.",
            "refutation": "Not applicable; this record exists only under test.",
            "prior_art": "Not applicable; this record exists only under test.",
            "lean": "AISafetyAtlas.Conjectures.Checks.synthetic",
            "lean_module": "AISafetyAtlas.Conjectures.Checks",
            "answer_candidate": [],
            "answer_admissible": [],
            "answer_correct": [],
            "admissibility_status": "NotApplicable",
            "blocked_on": "",
            "absent_declarations": [],
            "tags": ["learning-theory"],
            "proposed_by": "test_validators",
            "status": "OPEN",
            "resolution": None,
            "source_ref": ["survey-ref-005"],
            "context_source_ref": [],
            "source_scope": "Same",
            "source_fidelity": "Literal",
            "source_note": "",
        },
    )
    return data["conjectures"][0]


CASES = [
    (
        "registry: graded row citing only a directory source",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="BY-043").__setitem__(
            "original_source_refs", ["brcic-yampolskiy-2023"]
        ),
        "cites only directory sources",
    ),
    (
        "registry: living directory with no retrieved date",
        "validate_registry.py",
        "registry.yaml",
        lambda d: d["source_catalog"]["mathforaisafety-2026"].pop("retrieved"),
        "must record a `retrieved` ISO date",
    ),
    (
        "registry: graded row citing no source at all",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-NFL-001").__setitem__(
            "original_source_refs", []
        ),
        "names no work source; a grade relates two statements",
    ),
    (
        "registry: public RELATED with no sources skipping its scope delta",
        "validate_registry.py",
        "registry.yaml",
        lambda d: [
            first(d["results"], id="LAND-GOAL-001").__setitem__(
                "original_source_refs", ["mathforaisafety-2026"]
            ),
            next(
                f
                for f in first(d["results"], id="LAND-GOAL-001")["formalizations"]
                if f.get("relationship") == "RELATED"
            ).pop("scope_delta"),
        ],
        "must carry a scope_delta",
    ),
    (
        "registry: claim row using the artifact namespace",
        "validate_registry.py",
        "registry.yaml",
        lambda d: d["results"].append(
            dict(first(d["results"], id="BY-001"), id="LAND-NOT-A-CLAIM")
        ),
        "its id must be BY-### (the closed survey block) or CLM-*",
    ),
    (
        "registry: non-survey claim carrying survey-only fields",
        "validate_registry.py",
        "registry.yaml",
        lambda d: d["results"].append(
            dict(first(d["results"], id="BY-001"), id="CLM-BORROWED-001")
        ),
        "carries survey-only fields",
    ),
    (
        "registry: reproduction claimed with a command that reproduces nothing",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-NFL-001")["formalizations"][0].__setitem__(
            "build_command", "echo pretend"
        ),
        "neither a scripts/reproduce_*.sh entry point nor a `lake build`",
    ),
    (
        "registry: reproduction claimed with a non-reproduction script",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-NFL-001")["formalizations"][0].__setitem__(
            "build_command", "scripts/validate_registry.py"
        ),
        "neither a scripts/reproduce_*.sh entry point nor a `lake build`",
    ),
    (
        "registry: reproduction lake-building a module that does not exist",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["formalizations"][0].__setitem__(
            "build_command", "lake build AISafetyAtlas.NoSuchModule"
        ),
        "builds no module that exists in this tree",
    ),
    (
        "registry: BRIDGE declaration with no application line",
        "validate_registry.py",
        "registry.yaml",
        lambda d: next(
            x
            for x in first(d["results"], id="BY-012")["lean_artifact"]["declarations"]
            if x["type"] == "BRIDGE"
        ).pop("application"),
        "must record an `application` line",
    ),
    (
        "registry: result tagged outside the vocabulary",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="BY-001").__setitem__("tags", ["o-minimality"]),
        "tags outside the vocabulary",
    ),
    (
        "search evidence: profile not declared",
        "validate_registry.py",
        "docs/provenance/formalization-search.json",
        lambda d: d.__setitem__("profile", "novelty-check"),
        "must declare profile 'baseline-catalogue'",
    ),
    (
        "search evidence: novelty check missing its scope limits",
        "validate_registry.py",
        "docs/provenance/formalization-search.json",
        lambda d: d["novelty_checks"][0].__setitem__("scope_limits", "  "),
        "must record a non-empty scope_limits",
    ),
    (
        "search evidence: novelty check naming an unpinned corpus",
        "validate_registry.py",
        "docs/provenance/formalization-search.json",
        lambda d: d["novelty_checks"][0].__setitem__("corpora", ["google"]),
        "corpora with no pinned revision on record",
    ),
    (
        "search evidence: novelty follow-up using an unpinned revision",
        "validate_registry.py",
        "docs/provenance/formalization-search.json",
        lambda d: next(
            check for check in d["novelty_checks"] if check["id"] == "NC-009"
        )["followup_searches"][0].__setitem__("version", "main"),
        "must pin a 40-character Git revision",
    ),
    (
        "registry: public RELATED record with no scope delta",
        "validate_registry.py",
        "registry.yaml",
        lambda d: next(
            f
            for f in first(d["results"], id="BY-020")["formalizations"]
            if f["relationship"] == "RELATED"
        ).pop("scope_delta"),
        "must carry a scope_delta",
    ),
    (
        "registry: scope delta citing evidence that does not exist",
        "validate_registry.py",
        "registry.yaml",
        lambda d: next(
            f
            for f in first(d["results"], id="BY-033")["formalizations"]
            if f["relationship"] == "RELATED"
        )["scope_delta"].__setitem__("evidence", "docs/provenance/nope.md"),
        "scope_delta evidence does not exist",
    ),
    (
        "registry: scope delta evidence escaping the repository",
        "validate_registry.py",
        "registry.yaml",
        lambda d: next(
            f
            for f in first(d["results"], id="BY-039")["formalizations"]
            if f["relationship"] == "RELATED"
        )["scope_delta"].__setitem__("evidence", "../../../etc/passwd"),
        "must be a repository-relative path inside the tree",
    ),
    (
        "registry: artifact formalization with invalid relationship",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"][0].__setitem__(
            "relationship", "NOT-A-RELATIONSHIP"
        ),
        "has unknown relationship",
    ),
    (
        "registry: artifact formalization with no schema",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001").__setitem__(
            "formalizations", [{"garbage": "no"}]
        ),
        "formalization missing fields",
    ),
    (
        "registry: artifact formalization with invalid repository",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"][0].__setitem__(
            "repository", "not a url"
        ),
        "has an invalid repository URL",
    ),
    (
        "registry: artifact formalization with invalid license",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["formalizations"][0].__setitem__(
            "license", "NOT-SPDX"
        ),
        "has an unknown SPDX license identifier",
    ),
    (
        "registry: artifact formalization with invalid reproduced flag",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"][0].__setitem__(
            "reproduced", "yes"
        ),
        "reproduced flag must be boolean",
    ),
    (
        "registry: artifact formalization with incomplete provenance",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"][0].pop(
            "version"
        ),
        "formalization missing fields",
    ),
    (
        "registry: artifact declaration without source",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["lean_artifact"]["declarations"][0].update(
            type="WRAPPER", source_declarations=[]
        ),
        "Lean artifact declaration lacks sources",
    ),
    (
        "registry: duplicate artifact declaration within a row",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-ATTR-001")["lean_artifact"]["declarations"].append(
            dict(first(d["results"], id="LAND-ATTR-001")["lean_artifact"]["declarations"][0])
        ),
        "duplicate Lean artifact declaration within LAND-ATTR-001",
    ),
    (
        "registry: artifact with unknown related result",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-001")["related_result_ids"].append(
            "LAND-GHOST-001"
        ),
        "related_result_ids names unknown result",
    ),
    # Typed relations. The point of the schema is that an edge cannot assert
    # structure nobody checked, so each guard gets a case.
    (
        "registry: relation kind outside the vocabulary",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-AMBIG-001")["relations"][0].__setitem__(
            "kind", "IMPLIES"
        ),
        "relation kind 'IMPLIES' is outside the vocabulary",
    ),
    (
        "registry: typed relation not backed by untyped adjacency",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-AMBIG-001")["relations"].append(
            {"target": "LAND-ACCUM-001", "kind": "BUILDS_ON"}
        ),
        "is not in related_result_ids",
    ),
    (
        "registry: boundary partner without a model delta",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-CL-001")["relations"][0].pop("note"),
        "must carry a note stating the model delta",
    ),
    (
        "registry: builds-on edge to a row with no Lean",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-TEMPORAL-001")["relations"].append(
            {"target": "LAND-CL-001", "kind": "BUILDS_ON"}
        ),
        "needs a Lean artifact on both rows",
    ),
    (
        "registry: relation pointing at its own row",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-AMBIG-001")["relations"][0].__setitem__(
            "target", "LAND-AMBIG-001"
        ),
        "relation points at itself",
    ),
    (
        "registry: repeated typed edge",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-AMBIG-001")["relations"].append(
            dict(first(d["results"], id="LAND-AMBIG-001")["relations"][0])
        ),
        "repeats relation",
    ),
    (
        "registry: result shape outside the vocabulary",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-ACCUM-001").__setitem__(
            "result_shape", "NO_GO"
        ),
        "result_shape 'NO_GO' is outside the vocabulary",
    ),
    (
        "registry: relation with an unknown field",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-AMBIG-001")["relations"][0].__setitem__(
            "strength", "high"
        ),
        "relation has unknown fields",
    ),
    (
        "registry: artifact with no formalization",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001").__setitem__(
            "formalizations", []
        ),
        "records no claim, so it must record at least one formalization",
    ),
    (
        "registry: artifact formalizations with wrong container type",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001").__setitem__(
            "formalizations", {}
        ),
        "formalizations must be a list",
    ),
    (
        "registry: artifact with malformed lean artifact",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002").__setitem__(
            "lean_artifact", []
        ),
        "lean_artifact must be an object or null",
    ),
    (
        "registry: artifact declaration with wrong container type",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["lean_artifact"].__setitem__(
            "declarations", [{}]
        ),
        "Lean artifact declaration missing fields",
    ),
    (
        "registry: artifact declarations with wrong container type",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["lean_artifact"].__setitem__(
            "declarations", None
        ),
        "Lean artifact lacks atlas declarations",
    ),
    (
        "registry: artifact declaration with non-list sources",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["lean_artifact"]["declarations"][0].__setitem__(
            "source_declarations", "not-a-list"
        ),
        "source_declarations must be a list",
    ),
    (
        "registry: reproduced artifact without build evidence",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"][0].pop(
            "build_environment"
        ),
        "build_environment must be a non-empty string",
    ),
    (
        "registry: reproduced artifact with malformed environment",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"][0].__setitem__(
            "build_environment", []
        ),
        "build_environment must be a non-empty string",
    ),
    (
        "registry: artifact with malformed relationship type",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GOAL-001")["formalizations"][0].__setitem__(
            "relationship", []
        ),
        "relationship must be a string",
    ),
    (
        "registry: artifact declaration with malformed type",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["lean_artifact"]["declarations"][0].__setitem__(
            "type", []
        ),
        "has unknown Lean artifact type",
    ),
    (
        "registry: artifact declaration with malformed source entry",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["lean_artifact"]["declarations"][0].__setitem__(
            "source_declarations", [[]]
        ),
        "source_declarations must contain non-empty names",
    ),
    (
        "registry: artifact declaration packs multiple source names",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-HYPER-002")["lean_artifact"][
            "declarations"
        ][0]["source_declarations"].__setitem__(0, "first; second"),
        "must be one identifier per list entry",
    ),
    (
        "registry: formalization packs multiple declaration names",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-HYPER-002")["formalizations"][
            0
        ]["declarations"].__setitem__(0, "first; second"),
        "declaration names must be one identifier per list entry",
    ),
    (
        "registry: formalization packs names with a comma",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-HYPER-002")["formalizations"][
            0
        ]["declarations"].__setitem__(0, "first, second"),
        "declaration names must be one identifier per list entry",
    ),
    (
        "registry: Lean row without a public summary",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-KNOW-001").pop("public"),
        "has no public summary",
    ),
    (
        "registry: public group outside the vocabulary",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-KNOW-001")["public"].__setitem__(
            "group", "Miscellaneous"
        ),
        "is outside the vocabulary",
    ),
    (
        "registry: public summary empty",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-KNOW-001")["public"].__setitem__(
            "summary", "   "
        ),
        "public summary must be a non-empty string",
    ),
    (
        "registry: public missing a required field",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-KNOW-001")["public"].pop("use"),
        "public is missing",
    ),
    (
        "registry: public carries an unknown field",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-KNOW-001")["public"].__setitem__(
            "tagline", "catchy"
        ),
        "public has unknown fields",
    ),
    (
        "registry: reproduced row without a public summary",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-CL-001").pop("public"),
        "has no public summary",
    ),
    (
        "registry: artifact with non-boolean root import",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002").__setitem__(
            "root_import", "yes"
        ),
        "root_import must be boolean",
    ),
    (
        "registry: artifact with incorrect root import claim",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-JOINTOBS-001").__setitem__(
            "root_import", False
        ),
        "disagrees with the public root import closure",
    ),
    (
        "registry: one declaration owned by two rows",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["lean_artifact"][
            "declarations"
        ].__setitem__(
            0,
            dict(
                first(d["results"], id="LAND-GS-002")["lean_artifact"]["declarations"][
                    0
                ],
                atlas_declaration="AISafetyAtlas.SocialChoice.arrow",
            ),
        ),
        "is owned by BY-007 and claimed again by LAND-GS-002",
    ),
    (
        "registry: result with empty notes",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001").__setitem__("notes", " "),
        "must have non-empty notes",
    ),
    (
        "registry: external artifact without local atlas module",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["formalizations"][0].pop(
            "atlas_module"
        ),
        "external Lean artifact must record atlas_module",
    ),
    (
        "registry: artifact with malformed tag",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001").__setitem__(
            "tags", [[]]
        ),
        "tags must be non-empty strings",
    ),
    (
        "registry: in-repository artifact without declaration provenance",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-HYPER-002")["formalizations"][0].pop(
            "module"
        ),
        "in-repository formalization must record module and declaration",
    ),
    (
        "registry: external artifact using in-tree version",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"][0].__setitem__(
            "version", "IN_TREE"
        ),
        "external formalization cannot use IN_TREE",
    ),
    (
        "registry: duplicate artifact formalization",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-VNM-001")["formalizations"].append(
            dict(first(d["results"], id="LAND-VNM-001")["formalizations"][0])
        ),
        "contains a duplicate formalization record",
    ),
    (
        "conjectures: no refutation condition",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("refutation", "   "),
        "non-empty refutation",
    ),
    (
        "conjectures: statement outside the Conjectures namespace",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "lean", "AISafetyAtlas.Learning.no_free_lunch"
        ),
        "must live under AISafetyAtlas.Conjectures",
    ),
    # A conjecture is what gets doubted and proved, so the scope grade against
    # its printed source is part of the schema rather than commentary. Each
    # rule below is the one a tired author would otherwise walk past.
    (
        "conjectures: unknown source_scope",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("source_scope", "Wider"),
        "unknown source_scope",
    ),
    (
        "conjectures: unknown source_fidelity",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("source_fidelity", "High"),
        "unknown source_fidelity",
    ),
    (
        "conjectures: MAIS row not at the source scope",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "source_ref": ["mais-a2-2026"],
                "source_scope": "Narrower",
                "source_note": (
                    "The synthetic row adds a premise that MAIS does not state; "
                    "the validator must keep this repaired variant out of the ledger."
                ),
            }
        ),
        "every MAIS ledger row must be 'Same'",
    ),
    (
        # A row may leave the ledger, but not silently: the withdrawn encoding
        # and the atlas-original variant that left on 2026-08-23 took their
        # `CONJ-` numbers with them, and only a record keeps that from being an
        # undocumented decision.
        "conjectures: a removed row leaves no record",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: d["conjectures"].__delitem__(
            next(i for i, e in enumerate(d["conjectures"]) if e["id"] == "CONJ-004")
        ),
        "conjecture numbering skips assigned ids",
    ),
    (
        "conjectures: a retired id is reused",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-010").__setitem__(
            "id", "CONJ-011"
        ),
        "appear in both the live ledger and the retired archive",
    ),
    (
        # This case names the *next* free id, so it moves every time a row
        # lands. Left alone it turns into a no-op that passes for the wrong
        # reason -- the mutation stops changing anything -- which is the one
        # failure shape a regression suite cannot report on itself.
        "conjectures: next_id skips an unrecorded assignment",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: d.__setitem__("next_id", 27),
        "conjecture numbering skips assigned ids ['CONJ-026']",
    ),
    (
        "conjectures: MAIS row using an atlas bridge",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "source_ref": ["mais-a2-2026"],
                "source_fidelity": ["Literal", "Bridged"],
                "source_note": (
                    "The synthetic row supplies an atlas object where MAIS did "
                    "not; the validator must keep that bridge out of the ledger."
                ),
            }
        ),
        "may not substitute an atlas-supplied object",
    ),
    (
        "conjectures: source_ref names no registry source",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("source_ref", []),
        "at least one registry source",
    ),
    (
        "conjectures: source_ref names a source the registry does not have",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("source_ref", ["not-a-source"]),
        "absent from registry.yaml",
    ),
    (
        "conjectures: graded against an unpinned source",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "source_ref", ["mathforaisafety-2026"]
        ),
        "unpinned sources",
    ),
    (
        "conjectures: a narrowing labelled but not argued",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {"source_scope": "Narrower", "source_note": "binary only"}
        ),
        "a label is not the",
    ),
    (
        # A Same/Literal row *may* explain what it read from the source; the
        # rule that it must not was this schema's worst defect, because the rows
        # claiming perfect fidelity were then the only ones barred from
        # disclosing a reading choice. What is still rejected is a fragment: a
        # note here is an argument or it is absent.
        "conjectures: Same and Literal hedging in a fragment instead of arguing",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "source_note", "Roughly the same, give or take."
        ),
        "a fragment is a hedge",
    ),
    (
        "conjectures: Beyond scope without the AtlasOriginal fidelity",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "source_scope": "Beyond",
                "source_note": (
                    "An atlas-original question still has to say which printed "
                    "result it is about and why the source does not settle it."
                ),
            }
        ),
        "same fact seen from two sides",
    ),
    (
        "conjectures: AtlasOriginal fidelity without the Beyond scope",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "source_fidelity": "AtlasOriginal",
                "source_note": (
                    "Claiming the Prop is at the printed quantifier while saying "
                    "there is no printed statement is a contradiction in one row."
                ),
            }
        ),
        "same fact seen from two sides",
    ),
    (
        "conjectures: AtlasOriginal paired with a kind that reads a printed sentence",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "source_scope": "Beyond",
                "source_fidelity": ["AtlasOriginal", "Selected"],
                "source_note": (
                    "There is no printed sentence for Selected to have selected a "
                    "branch of, so the two kinds cannot both hold of one Prop."
                ),
            }
        ),
        "nothing for another kind to describe",
    ),
    (
        "conjectures: source_fidelity list repeating a value",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "source_fidelity": ["Selected", "Selected"],
                "source_note": (
                    "A repeated kind says nothing twice and hides whether a second "
                    "distinct relation to print was meant to be recorded."
                ),
            }
        ),
        "repeats a value",
    ),
    (
        # One Same cell answering to two artifacts hides which of them the
        # verdict is about, and the two are rarely the same genre: CONJ-009 was
        # graded against both a GitHub issue's criterion and an agenda clause
        # that says "Determine ...", which no truth-valued Prop can be Same as.
        "conjectures: one Same grade answering to several sources at once",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "source_ref", ["survey-ref-005", "mais-a2-2026"]
        ),
        "one grade cannot answer to several artifacts",
    ),
    (
        "conjectures: a source listed as both graded and context",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "context_source_ref", ["survey-ref-005"]
        ),
        "not both",
    ),
    (
        "conjectures: context_source_ref naming a source the registry lacks",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "context_source_ref", ["no-such-source-9999"]
        ),
        "context_source_ref names sources absent",
    ),
    (
        "conjectures: withdrawn without the Retired scope",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "status": "WITHDRAWN",
                "resolution": "Retired under test.",
                "source_scope": "Narrower",
                "source_note": (
                    "A withdrawn entry still has to say what it retired and why, "
                    "at enough length that the next proposer does not repeat it."
                ),
            }
        ),
        "source_scope must be 'Retired'",
    ),
    (
        "conjectures: Retired scope on a live conjecture",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "source_scope": "Retired",
                "source_note": (
                    "A live conjecture graded as retired would hide an ungraded "
                    "claim behind a status it does not have."
                ),
            }
        ),
        "cannot be 'Retired'",
    ),
    (
        "conjectures: claims Same while the statement declares a specialization",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "statement",
            "In the atlas's finite binary rational specialization, the thing holds.",
        ),
        "declares a specialization",
    ),
    (
        "conjectures: terminal status with no resolution",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(status="RESOLVED", resolution=None),
        "resolution exactly when its status is terminal",
    ),
    (
        "conjectures: status has the wrong scalar type",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("status", []),
        "unknown status",
    ),
    (
        "conjectures: tag has the wrong scalar type",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("tags", [[]]),
        "tags must be non-empty strings",
    ),
    (
        "conjectures: statement module carrying no declaration prefix",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "lean_module", "AISafetyAtlas.Causal.EffectiveGenericity"
        ),
        "does not plausibly carry",
    ),
    (
        "conjectures: answer fields disagreeing on clause count",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-013").__setitem__(
            "answer_correct", ["AISafetyAtlas.Conjectures.MAIS.IsO27EdgeSurvivalRegion"]
        ),
        "disagree on clause count",
    ),
    (
        "conjectures: blocked row naming a Lean declaration",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-018").__setitem__(
            "lean", "AISafetyAtlas.Conjectures.Checks.synthetic"
        ),
        "blocked row is the record that none exists",
    ),
    (
        "conjectures: blocked row with no absence to trip on",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-019").__setitem__(
            "absent_declarations", []
        ),
        "a note that rots",
    ),
    (
        "conjectures: blocked row carrying a scope grade",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-020").__setitem__(
            "source_scope", "Same"
        ),
        "are one fact and must be used together",
    ),
    (
        "conjectures: target row silent about circular answers",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-013").__setitem__(
            "admissibility_status", "NotApplicable"
        ),
        "must say whether a circular answer is excluded",
    ),
    (
        "conjectures: target row naming no candidate type",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-013").__setitem__(
            "answer_candidate", []
        ),
        "must say what type an answer has",
    ),
    (
        "conjectures: claim row grading admissibility it does not carry",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__(
            "admissibility_status", "Unformalized"
        ),
        "admissibility is a property of an answer",
    ),
    (
        "conjectures: admissibility claimed Formalized with no predicate",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-009").__setitem__(
            "admissibility_status", "Formalized"
        ),
        "the label is not the artifact",
    ),
    (
        "conjectures: Partial admissibility with every clause covered",
        "validate_conjectures.py",
        "conjectures.yaml",
        # `Partial` on a row whose clauses are all covered would let a fully
        # closed row read as open, which is the mirror of the `Formalized`
        # overclaim below and just as invisible to a reader.
        lambda d: first(d["conjectures"], id="CONJ-017").__setitem__(
            "admissibility_status", "Partial"
        ),
        "both counts must be nonzero",
    ),
    (
        "conjectures: Partial admissibility with no clause covered",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: first(d["conjectures"], id="CONJ-016").__setitem__(
            "admissibility_status", "Partial"
        ),
        "both counts must be nonzero",
    ),
    (
        "conjectures: Formalized while a clause has no predicate",
        "validate_conjectures.py",
        "conjectures.yaml",
        # CONJ-013 covers clause (c) and leaves (a) and (b) open. Rounding that
        # up to `Formalized` claims an admissibility condition for two clauses
        # that have none, which is exactly the drift `Partial` exists to stop.
        lambda d: first(d["conjectures"], id="CONJ-013").__setitem__(
            "admissibility_status", "Formalized"
        ),
        "use 'Partial'",
    ),
    (
        "conjectures: unknown kind",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).__setitem__("kind", "problem"),
        "has unknown kind",
    ),
    (
        "conjectures: lean_module naming no Lean file",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: synthetic_conjecture(d).update(
            {
                "lean": "AISafetyAtlas.Conjectures.Ghost.statement",
                "lean_module": "AISafetyAtlas.Conjectures.Ghost",
            }
        ),
        "is not a Lean file",
    ),
    (
        "tasks: done badge disagreeing with status",
        "validate_tasks.py",
        "tasks.yaml",
        lambda d: first(d["tasks"], id="CT-7").__setitem__("status", "OPEN"),
        "disagrees with status",
    ),
    (
        "tasks: citing a registry row that does not exist",
        "validate_tasks.py",
        "tasks.yaml",
        lambda d: first(d["tasks"], id="CT-15").__setitem__(
            "body", first(d["tasks"], id="CT-15")["body"] + " See BY-099."
        ),
        "result ids that do not exist",
    ),
    (
        "tasks: citing a claim row that does not exist",
        "validate_tasks.py",
        "tasks.yaml",
        lambda d: first(d["tasks"], id="CT-15").__setitem__(
            "body", first(d["tasks"], id="CT-15")["body"] + " See CLM-GHOST-001."
        ),
        "result ids that do not exist",
    ),
    (
        "tasks: citing a landscape entry that does not exist",
        "validate_tasks.py",
        "tasks.yaml",
        lambda d: first(d["tasks"], id="CT-16").__setitem__(
            "body", first(d["tasks"], id="CT-16")["body"] + " See LAND-GHOST-001."
        ),
        "landscape ids that do not exist",
    ),
    (
        "tasks: size has the wrong scalar type",
        "validate_tasks.py",
        "tasks.yaml",
        lambda d: d["tasks"][0].__setitem__("size", []),
        "unknown size",
    ),
    (
        "tasks: status has the wrong scalar type",
        "validate_tasks.py",
        "tasks.yaml",
        lambda d: d["tasks"][0].__setitem__("status", []),
        "unknown status",
    ),
]


def run_cases(cases: list[tuple]) -> list[str]:
    """Run a slice of the case list against a private copy of the tree.

    Each worker gets its own tree because a case mutates a ledger file and
    restores it afterwards; sharing one tree would make the cases race. The copy
    costs about 10 ms, which is nothing next to the validator runs it enables to
    proceed in parallel.
    """
    failures: list[str] = []
    with tempfile.TemporaryDirectory() as raw:
        tmp = build_tree(Path(raw))
        for label, script, target, change, expected in cases:
            original = (tmp / target).read_text(encoding="utf-8")
            try:
                mutate(tmp, target, change)
                code, output = run(tmp, script)
                if code == 0:
                    failures.append(f"{label}: accepted, expected rejection")
                elif expected not in output:
                    failures.append(
                        f"{label}: rejected for the wrong reason\n    got: {output}"
                    )
            finally:
                (tmp / target).write_text(original, encoding="utf-8")
    return failures


def run_control() -> list[str]:
    """The unmutated copy must pass, or every rejection below proves nothing."""
    failures: list[str] = []
    with tempfile.TemporaryDirectory() as raw:
        tmp = build_tree(Path(raw))
        for script in (
            "validate_registry.py",
            "validate_conjectures.py",
            "validate_tasks.py",
        ):
            code, output = run(tmp, script)
            if code != 0:
                failures.append(f"control: {script} rejected valid data: {output}")
    return failures


def main() -> None:
    # The work is a subprocess per case, so threads are enough — the GIL is
    # released while each validator runs. Capped because the win flattens once
    # workers outnumber the cases each would carry.
    workers = max(1, min(os.cpu_count() or 1, 8, len(CASES)))
    chunks: list[list[tuple]] = [CASES[index::workers] for index in range(workers)]

    failures: list[str] = []
    with ThreadPoolExecutor(max_workers=workers + 1) as pool:
        pending = [pool.submit(run_control)]
        pending += [pool.submit(run_cases, chunk) for chunk in chunks if chunk]
        for future in pending:
            failures.extend(future.result())

    for failure in sorted(failures):
        print(f"validator regression FAILED — {failure}", file=sys.stderr)
    if failures:
        raise SystemExit(1)
    print(
        f"validator regressions ok: {len(CASES)} invalid ledgers rejected, "
        f"valid ledgers accepted ({workers} workers)"
    )


if __name__ == "__main__":
    main()
