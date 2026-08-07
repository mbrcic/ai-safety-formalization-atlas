"""The validators must reject malformed shapes with a reason, not a traceback.

`scripts/test_validators.py` covers *semantic* ledger rules — a grade with no
work source, a bridge graduated without evidence. This file covers the layer
below: what happens when a hand-edited ledger is the wrong shape entirely.

The distinction matters because the two failure modes look different in CI. A
semantic rule prints one line naming the row and the rule. A wrong shape used to
print a Python traceback, which tells a contributor that the validator broke —
not that their edit did, and not which field. Every case here asserts a non-zero
exit *and* the absence of a traceback, because passing only the first check is
how these regressions hid.

Run: `python3 -m pytest tests/ -q`
"""

from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any, Callable, Iterator

import pytest

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = "registry.yaml"
SEARCH = "docs/provenance/formalization-search.json"

Mutation = Callable[[dict[str, Any]], object]


def _first(items: list[dict[str, Any]], **match: object) -> dict[str, Any]:
    return next(i for i in items if all(i[k] == v for k, v in match.items()))


@pytest.fixture(scope="module")
def tree(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """One pristine copy of the repository, reused across cases.

    Each case restores the file it mutated, so the copy stays valid. Copying the
    tree per case would be correct too and roughly forty times slower.
    """
    target = tmp_path_factory.mktemp("atlas") / "repo"
    shutil.copytree(
        ROOT,
        target,
        symlinks=True,
        ignore=shutil.ignore_patterns(".lake", ".git", "vendor", "tests"),
    )
    return target


@pytest.fixture
def mutated(tree: Path) -> Iterator[Callable[[str, Mutation], subprocess.CompletedProcess[str]]]:
    """Apply one mutation to one ledger file and run the registry validator."""
    touched: list[tuple[Path, str]] = []

    def run(target: str, mutation: Mutation) -> subprocess.CompletedProcess[str]:
        path = tree / target
        original = path.read_text(encoding="utf-8")
        touched.append((path, original))
        data = json.loads(original)
        mutation(data)
        path.write_text(
            json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        return subprocess.run(
            [sys.executable, "scripts/validate_registry.py"],
            cwd=tree,
            capture_output=True,
            text=True,
        )

    yield run
    for path, original in touched:
        path.write_text(original, encoding="utf-8")


def _assert_clean_rejection(done: subprocess.CompletedProcess[str], expected: str) -> None:
    output = done.stderr + done.stdout
    assert "Traceback" not in output, f"validator crashed instead of reporting:\n{output}"
    assert done.returncode != 0, f"malformed ledger accepted:\n{output}"
    assert expected in output, f"rejected for the wrong reason:\n{output}"


CONTAINER_CASES: list[tuple[str, str, Mutation, str]] = [
    (
        "survey block is null",
        REGISTRY,
        lambda d: d.__setitem__("survey", None),
        "survey must be an object",
    ),
    (
        "vocabulary block is null",
        REGISTRY,
        lambda d: d.__setitem__("vocabulary", None),
        "vocabulary must be an object",
    ),
    (
        "results block is null",
        REGISTRY,
        lambda d: d.__setitem__("results", None),
        "results must be a list",
    ),
    (
        "source catalog is null",
        REGISTRY,
        lambda d: d.__setitem__("source_catalog", None),
        "source_catalog must be an object",
    ),
    (
        "a result is not an object",
        REGISTRY,
        lambda d: d["results"].append("not a result"),
        "every result must be an object",
    ),
    (
        "a source is not an object",
        REGISTRY,
        lambda d: d["source_catalog"].__setitem__("bogus", "not a source"),
        "must be an object",
    ),
    (
        "tag vocabulary mixes types",
        REGISTRY,
        lambda d: d["vocabulary"].__setitem__("tag", ["arrow", 7]),
        "tag vocabulary must contain only non-empty strings",
    ),
    (
        "formalizations block is null",
        REGISTRY,
        lambda d: _first(d["results"], id="LAND-RECT-001").__setitem__(
            "formalizations", None
        ),
        "formalizations must be a list",
    ),
    (
        "lean artifact declarations are null",
        REGISTRY,
        lambda d: _first(d["results"], id="LAND-RECT-001")["lean_artifact"].__setitem__(
            "declarations", None
        ),
        "Lean artifact lacks atlas declarations",
    ),
    (
        "search corpora block is null",
        SEARCH,
        lambda d: d.__setitem__("corpora", None),
        "corpora must be an object",
    ),
    (
        "one corpus hit record is null",
        SEARCH,
        lambda d: d["results"]["BY-020"]["candidate_hits"].__setitem__("mathlib", None),
        "hit evidence must be an object",
    ),
]


METADATA_CASES: list[tuple[str, str, Mutation, str]] = [
    (
        "candidate revision is a list",
        REGISTRY,
        lambda d: _first(d["results"], id="BY-021")["candidate_formalizations"][
            0
        ].__setitem__("revision", ["abc123"]),
        "must record revision as a non-empty string",
    ),
    (
        "candidate declaration is a list",
        REGISTRY,
        lambda d: _first(d["results"], id="BY-021")["candidate_formalizations"][
            0
        ].__setitem__("declaration", ["a", "b"]),
        "must record declaration as a non-empty string",
    ),
    (
        "candidate notes are a list",
        REGISTRY,
        lambda d: _first(d["results"], id="BY-021")["candidate_formalizations"][
            0
        ].__setitem__("notes", ["see the paper"]),
        "must record notes as a non-empty string",
    ),
    (
        "bridge review date is a list",
        REGISTRY,
        lambda d: _first(d["results"], id="BY-012")["bridge_review"].__setitem__(
            "date", ["2026-07-19"]
        ),
        "bridge_review must record date as a non-empty string",
    ),
    (
        "bridge review date is not an ISO date",
        REGISTRY,
        lambda d: _first(d["results"], id="BY-012")["bridge_review"].__setitem__(
            "date", "last July"
        ),
        "bridge_review date must be an ISO date",
    ),
    (
        "source citation is a list",
        REGISTRY,
        lambda d: d["source_catalog"]["survey-ref-018"].__setitem__(
            "citation", ["Wolpert", "1996"]
        ),
        "must contain a citation",
    ),
    (
        "source citation is whitespace",
        REGISTRY,
        lambda d: d["source_catalog"]["survey-ref-018"].__setitem__("citation", "   "),
        "must contain a citation",
    ),
]


@pytest.mark.parametrize(
    "target,mutation,expected",
    [case[1:] for case in CONTAINER_CASES],
    ids=[case[0] for case in CONTAINER_CASES],
)
def test_malformed_container_is_reported_not_raised(
    mutated: Callable[[str, Mutation], subprocess.CompletedProcess[str]],
    target: str,
    mutation: Mutation,
    expected: str,
) -> None:
    _assert_clean_rejection(mutated(target, mutation), expected)


@pytest.mark.parametrize(
    "target,mutation,expected",
    [case[1:] for case in METADATA_CASES],
    ids=[case[0] for case in METADATA_CASES],
)
def test_metadata_field_of_the_wrong_type_is_rejected(
    mutated: Callable[[str, Mutation], subprocess.CompletedProcess[str]],
    target: str,
    mutation: Mutation,
    expected: str,
) -> None:
    _assert_clean_rejection(mutated(target, mutation), expected)


def test_generator_points_at_the_validator_instead_of_crashing(tree: Path) -> None:
    """The documented workflow regenerates before it gates.

    So the generator, not the validator, is what a malformed ledger meets first.
    It must say where the real diagnosis lives rather than print a traceback.
    """
    path = tree / REGISTRY
    original = path.read_text(encoding="utf-8")
    try:
        data = json.loads(original)
        data["vocabulary"] = None
        path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        done = subprocess.run(
            [sys.executable, "scripts/generate_registry_views.py", "--check"],
            cwd=tree,
            capture_output=True,
            text=True,
        )
        output = done.stderr + done.stdout
        assert done.returncode != 0
        assert "Traceback" not in output, output
        assert "validate_registry.py" in output, output
    finally:
        path.write_text(original, encoding="utf-8")


def test_the_unmutated_copy_still_validates(tree: Path) -> None:
    """Control. Without it, every rejection above proves nothing."""
    done = subprocess.run(
        [sys.executable, "scripts/validate_registry.py"],
        cwd=tree,
        capture_output=True,
        text=True,
    )
    assert done.returncode == 0, done.stderr + done.stdout


def test_every_published_declaration_is_inside_the_axiom_audit() -> None:
    """The kernel audit must cover what the ledger publishes, by rule.

    This held by coincidence before: the audit finds names by scanning for
    keywords, and every published result happened to use one it scanned for.
    Imported directly rather than run as a subprocess — the coverage check is
    pure, so it needs no Lean toolchain.
    """
    sys.path.insert(0, str(ROOT / "scripts"))
    import check_print_axioms

    audited = set(check_print_axioms.DECLARATIONS)
    published = set(check_print_axioms.ledger_declarations())
    assert published, "registry publishes no declarations; the check is vacuous"
    assert published <= audited, sorted(published - audited)


def test_a_claim_from_another_source_is_admissible(tree: Path) -> None:
    """The ledger must accept a non-survey claim without survey vocabulary.

    Every negative test in the suite shows what is rejected. This one shows the
    thing the design is *for* is possible at all: before the CLM- namespace, a
    claim from AISI or MAIS had to borrow the artifact prefix and invent a
    `survey_proof_assessment` to pass, so "source-neutral ledger" was a property
    of the generated views and not of the schema.
    """
    path = tree / REGISTRY
    original = path.read_text(encoding="utf-8")
    try:
        data = json.loads(original)
        row = json.loads(json.dumps(_first(data["results"], id="BY-001")))
        row["id"] = "CLM-AISI-001"
        row["name"] = "Admissibility probe: a claim catalogued from another source"
        row["original_source_refs"] = ["aisi-alignment-project-2026"]
        for survey_only in (
            "paper_reference",
            "survey_proof_assessment",
            "formal_library_search",
        ):
            row.pop(survey_only, None)
        data["results"].append(row)
        path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        done = subprocess.run(
            [sys.executable, "scripts/validate_registry.py"],
            cwd=tree,
            capture_output=True,
            text=True,
        )
        assert done.returncode == 0, done.stderr + done.stdout
        assert "45 claims" in done.stdout, done.stdout
    finally:
        path.write_text(original, encoding="utf-8")
