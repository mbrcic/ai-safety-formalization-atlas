"""Regression tests for `report_predicate_duplicates.py`.

The script exists because the ontology work's structural matcher fingerprints
elaborated *signatures* and therefore could not see that `Knowable` and
`Determines` are one proposition — a duplicate shipped through it. The first
test is that exact pair: if the script stops finding it, the script has stopped
doing the one thing it was written for.

The third test pins that literal *values* survive the rendering: an earlier
version kept only a literal's type, so `n = 1` and `n = 2` were one shape and
the report would have grouped two different propositions.

The second test pins the normalization that makes the first possible. The two
declarations bind their type parameters in a different order, so abstracting in
declaration order renders them differently; ordering by first use in the body
does not. The first version of this script reported nothing for that reason.
"""

from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parent.parent


def _prelude(source: str) -> str:
    """The renderer, lifted out of the script rather than restated here.

    Kept as a helper because the two probes below both need it and because the
    script's harness is assembled at runtime from an import list plus this
    prelude — a test that pasted a copy would pass against an implementation it
    no longer matches.
    """
    body = source.split('HARNESS_PRELUDE = r"""', 1)[1].split('"""', 1)[0]
    return "import AISafetyAtlas\n" + body.split("def report : MetaM Unit")[0]

pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(
        shutil.which("lake") is None, reason="lake is not on PATH"
    ),
]


@pytest.fixture(scope="module")
def output() -> str:
    result = subprocess.run(
        [sys.executable, "scripts/report_predicate_duplicates.py"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    )
    return result.stdout


def test_finds_the_knowable_determines_collapse(output: str) -> None:
    groups = _groups(output)
    pair = {
        "AISafetyAtlas.Knowledge.Knowable",
        "AISafetyAtlas.Knowledge.Determines",
    }
    assert any(pair <= group for group in groups), output


def test_reordering_is_not_equivalence(tmp_path: Path) -> None:
    """`∀ n, f n = g n` and `∀ n, g n = f n` render the same, and are not equal.

    Ordering parameters by first use is what makes the `Knowable`/`Determines`
    group findable, and it is also why a group is a candidate rather than a
    verdict: it is invariant under swapping two parameters' roles, which `Eq` is
    not. This test pins the overreach so that the word "candidate" in the
    report's output cannot quietly become "identical" again.
    """
    source = (ROOT / "scripts/report_predicate_duplicates.py").read_text(
        encoding="utf-8"
    )
    prelude = _prelude(source)
    probe = tmp_path / "OrientationProbe.lean"
    probe.write_text(
        prelude
        + """
def shapeOf (n : Name) : MetaM String := do
  let some ci := (← getEnv).find? n | return "?"
  let some value := ci.value? | return "?"
  lambdaTelescope value fun xs body => render (body.abstract (canonicalOrder xs body))

def Q1 (f g : Nat → Nat) : Prop := ∀ n, f n = g n
def Q2 (f g : Nat → Nat) : Prop := ∀ n, g n = f n

#eval show MetaM Unit from do
  IO.println s!"q1\t{← shapeOf ``Q1}"
  IO.println s!"q2\t{← shapeOf ``Q2}"
""",
        encoding="utf-8",
    )
    result = subprocess.run(
        ["lake", "env", "lean", str(probe)],
        cwd=ROOT, capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    shapes = dict(
        line.split("\t", 1) for line in result.stdout.splitlines() if "\t" in line
    )
    assert shapes["q1"] == shapes["q2"], (
        "the renderer stopped being reorder-invariant; if that is deliberate, "
        "the Knowable/Determines group may no longer be found — check that first"
    )


def test_output_calls_groups_candidates(output: str) -> None:
    """The report must not claim more than a shape match establishes."""
    assert "candidate group(s)" in output, output
    assert "definitionally identical" not in output, output


def test_scans_beyond_the_root_import(output: str) -> None:
    """The scan must cover the build targets, not just the root closure.

    `import AISafetyAtlas` alone reaches 253 predicates. Adding
    `scripts/lean_build_targets.txt` — the MAIS conjecture layer, which the root
    does not import, and `Examples/` — reaches 432. The threshold sits between
    the two on purpose: a revert to a root-only harness drops the count back to
    253 and fails here, rather than silently shrinking a scan whose header
    claims to cover the atlas.
    """
    line = next(l for l in output.splitlines() if l.startswith("predicates scanned:"))
    scanned = int(line.split(":")[1])
    assert scanned > 300, (
        f"{line} — this is close to the root-only figure of 253; check that "
        "the harness still imports scripts/lean_build_targets.txt"
    )


def test_literals_are_not_erased(tmp_path: Path) -> None:
    """`n = 1` and `n = 2` are different propositions.

    An earlier version rendered a literal's *type*, so every natural collapsed
    to one token and the two shapes below were identical — the report would have
    grouped two different propositions and called them one. The renderer is
    lifted out of the script itself rather than restated here, so this cannot
    pass against a copy that has drifted from the implementation.
    """
    source = (ROOT / "scripts/report_predicate_duplicates.py").read_text(
        encoding="utf-8"
    )
    prelude = _prelude(source)
    probe = tmp_path / "LiteralProbe.lean"
    probe.write_text(
        prelude
        + """
def shapeOf (n : Name) : MetaM String := do
  let some ci := (← getEnv).find? n | return "?"
  let some value := ci.value? | return "?"
  lambdaTelescope value fun xs body => render (body.abstract (canonicalOrder xs body))

def eqOne : Prop := (1 : Nat) = 1
def eqTwo : Prop := (1 : Nat) = 2

#eval show MetaM Unit from do
  IO.println s!"one\t{← shapeOf ``eqOne}"
  IO.println s!"two\t{← shapeOf ``eqTwo}"
""",
        encoding="utf-8",
    )
    result = subprocess.run(
        ["lake", "env", "lean", str(probe)],
        cwd=ROOT, capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    shapes = dict(
        line.split("\t", 1) for line in result.stdout.splitlines() if "\t" in line
    )
    assert set(shapes) == {"one", "two"}, result.stdout
    assert shapes["one"] != shapes["two"], shapes["one"]


def _groups(output: str) -> list[set[str]]:
    groups: list[set[str]] = []
    for line in output.splitlines():
        if line.startswith("  shape "):
            groups.append(set())
        elif line.startswith("      ") and groups:
            groups[-1].add(line.strip())
    return groups
