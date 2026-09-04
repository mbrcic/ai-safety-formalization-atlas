#!/usr/bin/env python3
"""Require every frontier proposition to carry explicit stress evidence.

A frontier proposition can be **false** -- not unproved, false, with an explicit
counterexample. Everything conditional on it is then *unapplicable* rather than
conditional: `P -> Q` with `P` false elaborates, kernel-checks, freezes, audits
clean and can never be instantiated by anything. No other gate here sees it, and
each is blind for a different reason: the freeze faithfully freezes a false
statement; the axiom audit sees no axiom footprint, because nobody proved it;
the scope grading reads the extra width as a pass; the worked examples pin the
reading of the definitions, which can be right while the proposition about them
is false. `docs/provenance/o70-frontier-manifest.md` records the case this
repository ran into, under `O70-ZETA-BRIDGE`.

The obligation that follows: before a frontier proposition may be
stated, put an unconditional artifact beside it that exercises a known failure
mode or checks the setting in which it is asserted. This is that obligation,
mechanized as far as it goes.

What it enforces, per frontier:

* the proposition resolves at the file the registry below names;
* a frozen `..._iff` specification surface exists, is one of the surfaces
  `check_statement_freeze.py` watches, and is recorded in the statement lock --
  so the body behind the `def` cannot be weakened unnoticed;
* at least one consumer takes it as a hypothesis, found by scanning signatures
  rather than trusted from a table -- a frontier nothing stands on is not a
  frontier;
* it has a section in `docs/provenance/o70-frontier-manifest.md`, the
  human-maintained record of what the atlas assumes and does not prove;
* **and at least one stress artifact that does not itself assume the frontier.**

That last clause carries the whole point, and the distinction it draws is the
one the defect turned on. A theorem of the form `frontier -> X` cannot stress a
frontier independently: if the frontier is false the theorem is vacuous, and it
looks exactly as strong either way. An artifact that stands outside the frontier can instead probe a
formula, rule out a cheap branch, check that the asserted family has the needed
properties, or show that a conclusion is meaningful on a representative model.
`hasLocalVolumeOrder_residualGerm_one` in `ResidualScalar.lean` says this in its
own docstring: "a witness proved under `EigenvalueLawStatement` -- a hypothesis
with no known inhabitant -- could not show that".

Conditional consequences are still worth recording, so the registry keeps them
with `unconditional=False`. They are reported and they do not count. The script
checks the declared conditionality against the source: a row claiming a
declaration is frontier-free when its signature takes the frontier fails, which
is the mistake this check exists to make expensive.

**A registry, not an inference.** The three frontiers are named literally below,
the way `check_statement_freeze.SPECIFICATION_SURFACES` names the surfaces it
watches, and for the same reason: inferring "a `Prop` nobody proves that
something else assumes" from the declaration index would be a guess with false
positives, and a diff to this table is exactly the review event that should
accompany adding or retiring a frontier. Adding a frontier here with no
unconditional stress artifact fails the gate, which is the intended cost of
stating one.

**What this cannot do.** It checks that named evidence exists, resolves, and is
independent of the frontier. It does not establish that the proposition is
satisfiable, likely, or sourced correctly, and it does not check that the
evidence is *strong*. The eigenvalue-law probe covers `k <= 2`; the exact-local
artifact only rules out the neutral branch; and the zeta artifact is outside the
O70 family. A frontier can pass here and still be false. The check buys a visible
stress package, not a truth verdict.

Blocking: exits 1 when any frontier is short of evidence.

Usage:
    python3 scripts/check_frontier_evidence.py
    python3 scripts/check_frontier_evidence.py --notes   # why each one counts
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_statement_freeze import SPECIFICATION_SURFACES  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "docs/provenance/o70-frontier-manifest.md"
LOCK = "docs/status/statement-lock.json"
LEAN_ROOT = "AISafetyAtlas"
EXAMPLES_PREFIX = "AISafetyAtlas/Examples/"

# `example` is absent on purpose: it declares nothing anything else can stand
# on, and `Examples/` is excluded from the scan by path anyway.
DECLARATION_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
    "inductive", "opaque", "axiom",
)
LINE_COMMENT = re.compile(r"--.*$")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
MODIFIERS = (
    "public", "private", "protected", "noncomputable", "partial", "unsafe",
    "nonrec", "scoped", "local",
)
DECLARATION_START = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    rf"(?:(?:{'|'.join(MODIFIERS)})\s+)*"
    rf"(?:{'|'.join(DECLARATION_KEYWORDS)})\s+"
    r"([A-Za-z_À-￿][^\s:({\[]*)"
)


@dataclass(frozen=True)
class Artifact:
    """One named piece of evidence about a frontier.

    `unconditional` is a claim about the artifact, checked against the source:
    True means it does not take the frontier as a hypothesis, and only those
    count towards the stress-evidence requirement. A `script` artifact is
    unconditional by construction -- Python cannot assume a Lean hypothesis --
    and declaring one conditional is rejected as a registry error.
    """

    kind: str            # "lean" | "script"
    name: str            # fully qualified Lean name, or repo-relative path
    file: str            # repo-relative file it lives in
    unconditional: bool
    note: str


@dataclass(frozen=True)
class Frontier:
    """A `Prop` the atlas assumes, does not prove, and states theorems over."""

    identifier: str      # the manifest's section name, e.g. O70-EIGEN-LAW
    proposition: str     # fully qualified Lean name
    file: str            # repo-relative file it is defined in
    surface: str         # fully qualified `..._iff` specification surface
    artifacts: tuple[Artifact, ...]

    # The debt fields. An assumed proposition is a debt the atlas owes, and
    # these three record what is owed to whom and what has been decided about
    # paying it. Nothing checks them -- they are a maintainer's judgement, and
    # the point of writing them beside the machine-checked fields is that the
    # gate prints both together, so the decision cannot quietly go missing.
    #
    # `owed_to` is the one distinction that must never be collapsed:
    #   "candidate"  the candidate solution cites it rather than deriving it.
    #                Assuming it leaves the candidate's own derivation intact,
    #                so verifying the candidate does not require paying it.
    #   "source"     the printed problem statement asserts it. Ours to carry.
    #   "atlas"      the atlas chose a formulation the source did not. The
    #                expensive kind: the gap is of our own making.
    # `decision` is "hold" or "discharge"; a hold is a decision, not a silence.
    owed_to: str
    decision: str
    reason: str


# The frontier registry. Three entries, hand-chosen; see the module docstring
# for why this is a literal and not an inference over the declaration index.
FRONTIERS: tuple[Frontier, ...] = (
    Frontier(
        identifier="O70-EIGEN-LAW",
        proposition="AISafetyAtlas.SingularLearning.EigenvalueLawStatement",
        file="AISafetyAtlas/SingularLearning/EigenvalueLaw.lean",
        surface="AISafetyAtlas.SingularLearning.eigenvalueLawStatement_iff",
        owed_to="candidate",
        decision="hold",
        reason=("Muirhead 3.2.1/3.2.17 after James 1954, which the candidate "
                "cites and does not derive. Discharging it means real Wishart "
                "theory, absent from the pinned Mathlib in every form: a "
                "campaign, not a task. The source is a copyrighted monograph "
                "and is unpinned. No maintainer has ruled."),
        artifacts=(
            Artifact(
                kind="script",
                name="scripts/reproduce_eigenvalue_law_probe.py",
                file="scripts/reproduce_eigenvalue_law_probe.py",
                unconditional=True,
                note="numerical falsification probe of the Z-free ratio; "
                     "exact at k=1, Monte-Carlo at k=2, did not break it",
            ),
            Artifact(
                kind="lean",
                name="AISafetyAtlas.SingularLearning."
                     "hasLocalVolumeOrder_residualGerm_one",
                file="AISafetyAtlas/SingularLearning/ResidualScalar.lean",
                unconditional=True,
                note="frontier-free local pair of x^2 y^2; `volumeOrder_unique` "
                     "forces the conditional chain to agree, so a wrong "
                     "eigenvalue law would show up as a contradiction here",
            ),
            Artifact(
                kind="lean",
                name="AISafetyAtlas.SingularLearning.eigenvalueLaw_ratio",
                file="AISafetyAtlas/SingularLearning/EigenvalueLaw.lean",
                unconditional=False,
                note="the Z-free cross-multiplied identity the probe tests; "
                     "proved under the frontier, so it is the shape of the "
                     "evidence and not the evidence",
            ),
        ),
    ),
    Frontier(
        identifier="O70-EXACT-LOCAL",
        proposition="AISafetyAtlas.Conjectures.MAIS.O70ExactLocalPairsExist",
        file="AISafetyAtlas/Conjectures/MAIS/O70.lean",
        surface="AISafetyAtlas.Conjectures.MAIS.o70ExactLocalPairsExist_iff",
        owed_to="candidate",
        decision="hold",
        reason=("the candidate's section 13 names this the single "
                "non-elementary citation in its derivation and sources it to "
                "Lin's thesis, not to Greenblatt, which the candidate never "
                "cites. Lin Cor 2.6 is the route and is pinned. No maintainer "
                "has ruled."),
        artifacts=(
            Artifact(
                kind="lean",
                name="AISafetyAtlas.Conjectures.MAIS."
                     "not_eventually_rrrLossCoords_eq_zero_of_pos",
                file="AISafetyAtlas/Conjectures/MAIS/O70.lean",
                unconditional=True,
                note="closes off the neutral branch at every instance the "
                     "frontier quantifies over, with no frontier and no "
                     "factorization hypothesis: it cannot be satisfied cheaply",
            ),
            Artifact(
                kind="lean",
                name="AISafetyAtlas.Conjectures.MAIS."
                     "exactLocalPair_nondegenerate_of_frontier",
                file="AISafetyAtlas/Conjectures/MAIS/O70.lean",
                unconditional=False,
                note="reads nondegeneracy off whatever witnesses the frontier "
                     "supplies; says nothing if the frontier is false",
            ),
        ),
    ),
    Frontier(
        identifier="O70-ZETA-BRIDGE",
        proposition="AISafetyAtlas.Conjectures.MAIS.O70ZetaPoleBridge",
        file="AISafetyAtlas/Conjectures/MAIS/O70.lean",
        surface="AISafetyAtlas.Conjectures.MAIS.o70ZetaPoleBridge_iff",
        owed_to="source",
        decision="hold",
        reason=("MAIS-A6 def:local asserts this equivalence itself, citing "
                "[lau2023] = arXiv:2308.12108, which is pinned but states no "
                "theorem, runs zeta to volume where this assumes the reverse, "
                "and carries hypotheses this does not. So the route is open, "
                "not merely long, and a wider form of this proposition is "
                "false. No maintainer has ruled."),
        # A wider form of this frontier is false, and without this slot nothing
        # would exhibit a germ satisfying its conclusion at all -- which is the
        # case the check exists for. `hasZetaPoleOrder_sqGerm` closes it. It
        # computes the zeta function of `x0^2` exactly, reads a simple pole at
        # -1/2 off it, and assumes nothing; the same germ's ball-volume pair is
        # `(1/2, 1)` by `hasExactLocalPair_sq`, so the two normalizations
        # demonstrably agree somewhere. It is not an instance of the frontier --
        # `x0^2` is not a reduced-rank loss -- and must not be recorded as one.
        artifacts=(
            Artifact(
                kind="lean",
                name="AISafetyAtlas.SingularLearning.hasZetaPoleOrder_sqGerm",
                file="AISafetyAtlas/SingularLearning/ZetaMonomial.lean",
                unconditional=True,
                note=("the quadratic germ x0^2 has zeta pair (1/2, 1), computed "
                      "exactly and assuming nothing; hasExactLocalPair_sq gives "
                      "the same germ the same ball-volume pair, so the two "
                      "normalizations agree at a germ the atlas can check"),
            ),
        ),
    ),
)


@dataclass
class Report:
    """What backs one frontier, and what it is short of."""

    frontier: Frontier
    consumers: list[tuple[str, str, int]] = field(default_factory=list)
    counted: list[Artifact] = field(default_factory=list)
    conditional: list[Artifact] = field(default_factory=list)
    failures: list[str] = field(default_factory=list)


def declarations(text: str) -> list[tuple[str, int, str]]:
    """Every declaration in a Lean source, as `(leaf name, line, signature)`.

    The signature runs from the declaration keyword to the `:=` that starts the
    proof, stopping at `where` or a blank line -- the same slice
    `check_statement_freeze.signature` freezes, so "takes it as a hypothesis"
    here means what it means there: the name occurs in a binder, not in a proof
    body and not in a docstring.
    """
    blocks_masked = BLOCK_COMMENT.sub(
        lambda match: "\n" * match.group().count("\n"), text)
    lines = blocks_masked.split("\n")
    found: list[tuple[str, int, str]] = []
    for index, raw in enumerate(lines):
        match = DECLARATION_START.match(LINE_COMMENT.sub("", raw))
        if not match:
            continue
        collected: list[str] = []
        for candidate in lines[index:index + 80]:
            stripped = LINE_COMMENT.sub("", candidate)
            if ":=" in stripped:
                collected.append(stripped.split(":=")[0])
                break
            if re.match(r"\s*where\b", stripped):
                break
            if collected and not stripped.strip():
                break
            collected.append(stripped)
        signature = re.sub(r"\s+", " ", " ".join(collected)).strip()
        found.append((match.group(1), index + 1, signature))
    return found


def lean_sources(root: Path) -> list[Path]:
    """Every atlas Lean module outside `Examples/`.

    Examples are excluded on purpose: an example is a *use* of a frontier, so it
    can neither be stood on nor stand as evidence. The manifest counts them
    separately for the same reason.
    """
    return [
        path
        for path in sorted(root.glob(f"{LEAN_ROOT}/**/*.lean"))
        if not path.relative_to(root).as_posix().startswith(EXAMPLES_PREFIX)
    ]


def find_declaration(
    root: Path, name: str, file: str
) -> tuple[int, str] | None:
    """Locate a declaration by leaf name in the file that should define it."""
    source = root / file
    if not source.is_file():
        return None
    leaf = name.rsplit(".", 1)[-1]
    hits = [
        (line, signature)
        for found, line, signature in declarations(
            source.read_text(encoding="utf-8"))
        if found == leaf
    ]
    return hits[0] if len(hits) == 1 else None


def mentions(signature: str, name: str) -> bool:
    """Does this signature name the declaration, however it is qualified?

    All three ways Lean lets a consumer write it count -- `foo`,
    `Namespace.foo`, `AISafetyAtlas.Namespace.foo` -- which is the rule
    `report_consumers.py` uses and has the same known limit: a different
    declaration sharing the leaf name would match. The bias is towards finding a
    consumer, and both places this is called want it that way. A false consumer
    at worst counts a frontier as stood-on; a false *absence* would let an
    artifact that quietly assumes the frontier pass as evidence.
    """
    parts = name.split(".")
    suffixes = [".".join(parts[index:]) for index in range(len(parts))]
    alternatives = "|".join(re.escape(suffix) for suffix in suffixes)
    return re.search(rf"(?<![\w.])(?:{alternatives})\b", signature) is not None


def scan_consumers(root: Path, frontier: Frontier) -> list[tuple[str, str, int]]:
    """Declarations outside `Examples/` that take the frontier as a hypothesis.

    Measured from the sources rather than read off the manifest's table, so a
    consumer that is added, renamed or deleted needs no second edit to stay
    counted. The frontier's own definition and its frozen `..._iff` surface both
    mention it and neither stands on it, so both are excluded.
    """
    excluded = {
        frontier.proposition.rsplit(".", 1)[-1],
        frontier.surface.rsplit(".", 1)[-1],
    }
    consumers: list[tuple[str, str, int]] = []
    for path in lean_sources(root):
        relative = path.relative_to(root).as_posix()
        for name, line, signature in declarations(
                path.read_text(encoding="utf-8")):
            if name in excluded:
                continue
            if mentions(signature, frontier.proposition):
                consumers.append((name, relative, line))
    return consumers


def locked_statements(root: Path) -> set[str]:
    lock = root / LOCK
    if not lock.is_file():
        return set()
    recorded = json.loads(lock.read_text(encoding="utf-8"))
    return set(recorded.get("declarations", {}))


def evaluate(
    frontier: Frontier,
    root: Path,
    frozen_surfaces: dict[str, str],
    locked: set[str],
    manifest: str | None,
) -> Report:
    """Every obligation on one frontier, checked. Failures are strings."""
    report = Report(frontier=frontier)

    if find_declaration(root, frontier.proposition, frontier.file) is None:
        report.failures.append(
            f"proposition {frontier.proposition} does not resolve in "
            f"{frontier.file}")

    if frontier.surface not in frozen_surfaces:
        report.failures.append(
            f"specification surface {frontier.surface} is not one of the "
            "surfaces check_statement_freeze.py watches "
            "(add it to SPECIFICATION_SURFACES)")
    elif find_declaration(
            root, frontier.surface, frozen_surfaces[frontier.surface]) is None:
        report.failures.append(
            f"specification surface {frontier.surface} does not resolve in "
            f"{frozen_surfaces[frontier.surface]}")
    if frontier.surface not in locked:
        report.failures.append(
            f"specification surface {frontier.surface} is not recorded in "
            f"{LOCK} (run check_statement_freeze.py --write)")

    report.consumers = scan_consumers(root, frontier)
    if not report.consumers:
        report.failures.append(
            "no declaration outside Examples/ takes it as a hypothesis: "
            "a frontier nothing stands on is not a frontier")

    if manifest is None:
        report.failures.append(f"missing frontier manifest {MANIFEST}")
    else:
        if not re.search(rf"^##+\s+{re.escape(frontier.identifier)}\s*$",
                         manifest, re.MULTILINE):
            report.failures.append(
                f"no '## {frontier.identifier}' section in {MANIFEST}")
        if frontier.proposition not in manifest:
            report.failures.append(
                f"{MANIFEST} never names {frontier.proposition}")

    for artifact in frontier.artifacts:
        problem = check_artifact(root, frontier, artifact)
        if problem is not None:
            report.failures.append(problem)
        elif artifact.unconditional:
            report.counted.append(artifact)
        else:
            report.conditional.append(artifact)

    if not report.counted:
        report.failures.append(
            "no unconditional stress artifact: a theorem proved *under* the "
            "frontier is vacuous if the frontier is false and does not count. "
            "Name an independent probe, witness, failure-mode check, or "
            "setting check, and document exactly what it does and does not show")
    return report


def check_artifact(
    root: Path, frontier: Frontier, artifact: Artifact
) -> str | None:
    """Does this artifact exist, and is it the kind of thing it claims to be?"""
    where = f"{frontier.identifier} artifact {artifact.name}"
    if artifact.kind == "script":
        if not artifact.unconditional:
            return f"{where}: a script cannot assume a Lean hypothesis; " \
                   "declaring it conditional is a registry error"
        if not (root / artifact.file).is_file():
            return f"{where}: missing file {artifact.file}"
        return None
    if artifact.kind != "lean":
        return f"{where}: unknown artifact kind {artifact.kind!r}"

    located = find_declaration(root, artifact.name, artifact.file)
    if located is None:
        return f"{where}: does not resolve in {artifact.file}"
    _, signature = located
    assumes = mentions(signature, frontier.proposition)
    if assumes and artifact.unconditional:
        return (f"{where}: recorded as unconditional, but its signature takes "
                f"{frontier.proposition.rsplit('.', 1)[-1]} as a hypothesis. A "
                "theorem proved under the frontier is vacuous if the frontier "
                "is false, so it cannot be evidence that the frontier holds")
    if not assumes and not artifact.unconditional:
        return (f"{where}: recorded as conditional, but its signature does not "
                "take the frontier -- it counts, so say so")
    return None


def short(artifact: Artifact) -> str:
    """The artifact's own last name: a Lean leaf, or a script's basename."""
    if artifact.kind == "script":
        return PurePosixPath(artifact.name).name
    return artifact.name.rsplit(".", 1)[-1]


def describe(report: Report) -> str:
    """One line naming what backs this frontier. The gate output is the record."""
    frontier = report.frontier
    counted = ", ".join(
        f"{artifact.kind}:{short(artifact)}"
        for artifact in report.counted) or "none"
    conditional = (
        f", conditional={len(report.conditional)}"
        if report.conditional else "")
    status = "FAIL" if report.failures else "ok  "
    return (f"{status} {frontier.identifier}: "
            f"surface {frontier.surface.rsplit('.', 1)[-1]} frozen, "
            f"{len(report.consumers)} consumer(s), "
            f"manifest {frontier.identifier}, "
            f"stress [{counted}]{conditional}\n"
            f"     debt: owed to the {frontier.owed_to}; "
            f"{frontier.decision} -- {frontier.reason}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--notes", action="store_true",
        help="print the registry's note on every artifact, counted or not")
    arguments = parser.parse_args()

    manifest_path = ROOT / MANIFEST
    manifest = (
        manifest_path.read_text(encoding="utf-8")
        if manifest_path.is_file() else None)
    locked = locked_statements(ROOT)

    failed = 0
    for frontier in FRONTIERS:
        report = evaluate(
            frontier, ROOT, SPECIFICATION_SURFACES, locked, manifest)
        print(describe(report))
        if arguments.notes:
            for artifact in (*report.counted, *report.conditional):
                counts = "counts" if artifact.unconditional else "does not count"
                print(f"     · {short(artifact)} ({counts}): {artifact.note}")
        for failure in report.failures:
            print(f"     - {failure}")
        failed += bool(report.failures)

    if failed:
        print(
            f"check_frontier_evidence: {failed} of {len(FRONTIERS)} frontier(s) "
            "short of unconditional stress evidence. This check does not "
            "establish satisfiability; a false frontier still makes every "
            "theorem standing on it unapplicable rather than conditional -- see "
            "docs/provenance/o70-frontier-manifest.md.")
        return 1
    print(
        f"check_frontier_evidence: {len(FRONTIERS)} frontier(s), each with a "
        "frozen surface, a consumer, a manifest entry and an unconditional "
        "stress artifact (not a satisfiability proof)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
