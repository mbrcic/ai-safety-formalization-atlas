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
        "registry: reproduction lake-building a module that does not exist",
        "validate_registry.py",
        "registry.yaml",
        lambda d: first(d["results"], id="LAND-GS-002")["formalizations"][0].__setitem__(
            "build_command", "lake build AISafetyAtlas.NoSuchModule"
        ),
        "builds no module that exists in this tree",
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
        "source_declarations must contain non-empty strings",
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
        lambda d: d["conjectures"][0].__setitem__("refutation", "   "),
        "non-empty refutation",
    ),
    (
        "conjectures: statement outside the Conjectures namespace",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: d["conjectures"][0].__setitem__(
            "lean", "AISafetyAtlas.Learning.no_free_lunch"
        ),
        "must live under AISafetyAtlas.Conjectures",
    ),
    (
        "conjectures: terminal status with no resolution",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: d["conjectures"][0].update(status="RESOLVED", resolution=None),
        "resolution exactly when its status is terminal",
    ),
    (
        "conjectures: module that is not a Lean build target",
        "validate_conjectures.py",
        "conjectures.yaml",
        lambda d: d["conjectures"][0].__setitem__(
            "lean", "AISafetyAtlas.Conjectures.Ghost.statement"
        ),
        "not an explicit Lean build target",
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
        "tasks: citing a landscape entry that does not exist",
        "validate_tasks.py",
        "tasks.yaml",
        lambda d: first(d["tasks"], id="CT-16").__setitem__(
            "body", first(d["tasks"], id="CT-16")["body"] + " See LAND-GHOST-001."
        ),
        "landscape ids that do not exist",
    ),
]


def main() -> None:
    failures: list[str] = []

    with tempfile.TemporaryDirectory() as raw:
        tmp = build_tree(Path(raw))

        # Control: the unmutated copy must pass, otherwise a rejection below
        # proves nothing about the rule it claims to exercise.
        for script in (
            "validate_registry.py",
            "validate_conjectures.py",
            "validate_tasks.py",
        ):
            code, output = run(tmp, script)
            if code != 0:
                failures.append(f"control: {script} rejected valid data: {output}")

        for label, script, target, change, expected in CASES:
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

    for failure in failures:
        print(f"validator regression FAILED — {failure}", file=sys.stderr)
    if failures:
        raise SystemExit(1)
    print(
        f"validator regressions ok: {len(CASES)} invalid ledgers rejected, "
        "valid ledgers accepted"
    )


if __name__ == "__main__":
    main()
