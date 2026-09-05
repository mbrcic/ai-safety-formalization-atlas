#!/usr/bin/env python3
"""How many lines of a verification a human has to read.

A machine-checked answer to a printed problem moves work rather than removing
it. The kernel settles whether the proof follows; it cannot settle whether the
*statement* is the printed question, nor whether an assumed proposition is the
classical result it is named after. Those two are what a reader is left with,
and this script measures them, so a claim like "22,627 lines of Lean, of which
a reader has to audit 338" is reproducible rather than asserted.

Two numbers per surface:

* the **conclusion** — the definitional closure of the graded statement inside
  the surface's own statement modules. Read it to answer *is this print's
  question?*
* the **hypotheses** — the assumed propositions and their frozen `..._iff`
  bodies. Read them to answer *are these the results they are named after?*

Statement lines, and the docstring attached to each: for a theorem the count
stops at the proof's `:=`, and a `def` is counted whole, because for a
`Prop`-valued definition the body *is* the statement. The docstring counts
because it is where a transcription is defended -- a reader deciding whether a
statement is the printed question reads the argument for it, not only the
binders. Section headers (`/-! ... -/`) belong to no declaration and are not
counted.

The closure is restricted to each surface's statement modules. That is a
deliberate under-count of everything a referee could read -- the machinery
underneath is not counted -- and it is the right cut for the question the
number answers, which is how much *transcription* stands between print and the
kernel.

    python3 scripts/audit_surface.py                # every surface
    python3 scripts/audit_surface.py --key MAIS-O70 # one
    python3 scripts/audit_surface.py --json         # for a generator

Exit code is 1 if a listed declaration is missing, which is what makes a
published figure fail loudly after a rename instead of quietly going stale.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

DECL_KEYWORDS = ("theorem", "lemma", "def", "abbrev", "structure", "class", "instance")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    rf"(?P<kw>{'|'.join(DECL_KEYWORDS)})\s+(?P<name>[A-Za-z_][A-Za-z0-9_.'!?]*)"
)
LINE_COMMENT = re.compile(r"--.*$")


@dataclass(frozen=True)
class Surface:
    """One published verification, and the reading it asks of a human."""

    key: str
    issue: int
    problem: str
    layer: tuple[str, ...]              # modules the verification consists of
    statement_modules: tuple[str, ...]  # modules the transcription lives in
    conclusion_roots: tuple[str, ...]
    hypothesis_roots: tuple[str, ...] = ()
    note: str = ""


# The registry. A surface is added when a verification is published somewhere a
# reader can act on it -- an issue thread, a release note -- because that is
# when the figures become a claim rather than a measurement.
SURFACES: tuple[Surface, ...] = (
    Surface(
        key="MAIS-O70",
        issue=3,
        problem="prob:calibration",
        layer=(
            "AISafetyAtlas/SingularLearning.lean",
            "AISafetyAtlas/SingularLearning/",
            "AISafetyAtlas/Examples/SingularLearning.lean",
            "AISafetyAtlas/Examples/SingularLearning/",
            "AISafetyAtlas/Conjectures/MAIS/O70.lean",
            "AISafetyAtlas/Conjectures/MAIS/O70Proof.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O70.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O70Proof.lean",
        ),
        statement_modules=(
            "AISafetyAtlas/Conjectures/MAIS/O70.lean",
            "AISafetyAtlas/SingularLearning/LocalPair.lean",
            "AISafetyAtlas/SingularLearning/ZetaPair.lean",
            "AISafetyAtlas/SingularLearning/Loss.lean",
            "AISafetyAtlas/SingularLearning/AoyagiWatanabe.lean",
            "AISafetyAtlas/SingularLearning/EigenvalueLaw.lean",
        ),
        conclusion_roots=(
            "IsO70RankTable",
            "O70DependsOnRanksOnly",
            "IsO70MinimizerCharacterization",
            "IsO70FiberMinimumTable",
            "IsO70AWValueStratumTable",
            "o70Pair",
            "o70Minimizers",
        ),
        hypothesis_roots=(
            "EigenvalueLawStatement",
            "eigenvalueLawStatement_iff",
            "O70ExactLocalPairsExist",
            "o70ExactLocalPairsExist_iff",
            "O70ZetaPoleBridge",
            "o70ZetaPoleBridge_iff",
        ),
        note="conditional: the three frontiers are assumed, not proved",
    ),
    Surface(
        key="MAIS-O38",
        issue=30,
        problem="prob:samples",
        layer=(
            "AISafetyAtlas/Conjectures/MAIS/O38.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O38.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O38Candidate.lean",
        ),
        statement_modules=("AISafetyAtlas/Conjectures/MAIS/O38.lean",),
        conclusion_roots=(
            "maisO38_polynomialSamplesSuffice",
            "o38PolynomialSampleCandidate",
        ),
        note="unconditional",
    ),
    Surface(
        key="MAIS-O33",
        issue=9,
        problem="prob:corruption",
        layer=(
            "AISafetyAtlas/Conjectures/MAIS/O33.lean",
            "AISafetyAtlas/Causal/Corruption.lean",
            "AISafetyAtlas/Causal/Goal.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O33.lean",
            "AISafetyAtlas/Examples/Causal/O33Corruption.lean",
            "AISafetyAtlas/Examples/Causal/Goal.lean",
        ),
        statement_modules=(
            "AISafetyAtlas/Conjectures/MAIS/O33.lean",
            "AISafetyAtlas/Causal/Goal.lean",
            "AISafetyAtlas/Causal/Corruption.lean",
        ),
        conclusion_roots=(
            "maisO33_etaStarPos",
            "maisO33_etaStarIsZero",
            "maisO33_etaStarIsZeroGivenBaseline",
        ),
        hypothesis_roots=("maisO33_baselineTolerable",),
        note="the negative half is unconditional; the value needs thm:rabe",
    ),
    Surface(
        key="MAIS-O24",
        issue=7,
        problem="prob:effective",
        layer=(
            "AISafetyAtlas/Causal/EffectiveGenericity.lean",
            "AISafetyAtlas/Causal/MarginClass.lean",
            "AISafetyAtlas/Examples/Causal/O24Refutation.lean",
            "AISafetyAtlas/Examples/Causal/EffectiveGenericity.lean",
        ),
        statement_modules=(
            "AISafetyAtlas/Causal/EffectiveGenericity.lean",
            "AISafetyAtlas/Causal/MarginClass.lean",
        ),
        conclusion_roots=("O24Solution",),
        note="unconditional",
    ),
    Surface(
        key="MAIS-O23",
        issue=6,
        problem="q:ident",
        layer=(
            "AISafetyAtlas/Conjectures/MAIS/O23.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O23.lean",
            "AISafetyAtlas/Causal/MarginClass.lean",
            "AISafetyAtlas/Examples/Causal/BehavioralCollision.lean",
            "AISafetyAtlas/Examples/Causal/OneNodeClass.lean",
        ),
        statement_modules=(
            "AISafetyAtlas/Conjectures/MAIS/O23.lean",
            "AISafetyAtlas/Causal/MarginClass.lean",
        ),
        conclusion_roots=("maisO23_marginsDoNotSuffice",),
        note="unconditional",
    ),
    Surface(
        key="MAIS-O31",
        issue=8,
        problem="q:chain",
        layer=(
            "AISafetyAtlas/Conjectures/MAIS/O31.lean",
            "AISafetyAtlas/Conjectures/MAIS/O31Chart.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O31.lean",
            "AISafetyAtlas/Examples/Conjectures/MAIS/O31Measure.lean",
        ),
        statement_modules=(
            "AISafetyAtlas/Conjectures/MAIS/O31.lean",
            "AISafetyAtlas/Conjectures/MAIS/O31Chart.lean",
        ),
        conclusion_roots=(
            "maisO31_chainClassificationCandidate",
            "O31IdentifiesCoordinate",
            "O31SameSideChamber",
        ),
        note="partial: one chamber and one refuted heuristic, not the classification",
    ),
    Surface(
        key="MAIS-O34",
        issue=4,
        problem="prob:fiber",
        layer=(
            "AISafetyAtlas/Conjectures/MAIS/O34.lean",
            "AISafetyAtlas/Conjectures/BinaryPair.lean",
            "AISafetyAtlas/Examples/Conjectures/O34Fiber.lean",
        ),
        statement_modules=(
            "AISafetyAtlas/Conjectures/MAIS/O34.lean",
            "AISafetyAtlas/Conjectures/BinaryPair.lean",
        ),
        conclusion_roots=("maisO34_exactFiberCandidate",),
        note="part (a) only; part (b) untouched",
    ),
)


@dataclass
class Declaration:
    name: str
    module: str
    keyword: str
    start: int
    end: int
    doc: int
    text: str = field(repr=False)

    @property
    def lines(self) -> int:
        return self.end - self.start + 1 + self.doc


def declarations(path: Path, module: str) -> dict[str, Declaration]:
    """Every declaration in one module, with its statement extent."""
    lines = path.read_text(encoding="utf-8").split("\n")
    starts: list[tuple[int, str, str]] = []
    in_block = False
    for number, raw in enumerate(lines, start=1):
        opens, closes = raw.count("/-"), raw.count("-/")
        was_in_block = in_block
        if opens > closes:
            in_block = True
        elif closes > opens:
            in_block = False
        if was_in_block:
            continue
        match = DECL_RE.match(raw)
        if match:
            starts.append((number, match.group("kw"), match.group("name")))

    found: dict[str, Declaration] = {}
    for index, (number, keyword, name) in enumerate(starts):
        limit = starts[index + 1][0] - 1 if index + 1 < len(starts) else len(lines)
        end = statement_end(lines, number, limit, keyword)
        found[name] = Declaration(
            name=name,
            module=module,
            keyword=keyword,
            start=number,
            end=end,
            doc=docstring_lines(lines, number),
            text="\n".join(lines[number - 1:end]),
        )
    return found


def docstring_lines(lines: list[str], start: int) -> int:
    """Length of the `/-- ... -/` docstring attached to the declaration, if any."""
    index = start - 2  # 0-based line above the declaration
    while index >= 0 and (lines[index].strip().startswith("@[")
                          or not lines[index].strip()):
        if not lines[index].strip():
            break
        index -= 1
    if index < 0 or not lines[index].rstrip().endswith("-/"):
        return 0
    if lines[index].lstrip().startswith("/--"):
        return 1
    for first in range(index, -1, -1):
        if lines[first].lstrip().startswith("/--"):
            return index - first + 1
        if lines[first].lstrip().startswith("/-!"):
            return 0
    return 0


def statement_end(lines: list[str], start: int, limit: int, keyword: str) -> int:
    """Where the statement stops.

    For a theorem that is the proof's `:=`; for a definition it is the end of
    the block, since a `Prop`-valued definition's body is its statement.
    """
    if keyword in ("theorem", "lemma"):
        for number in range(start, min(limit, start + 80) + 1):
            stripped = LINE_COMMENT.sub("", lines[number - 1])
            if ":=" in stripped or re.search(r"\bby\s*$", stripped):
                return number
        return min(limit, start + 80)
    for number in range(start, limit + 1):
        if not lines[number - 1].strip():
            return number - 1
    return limit


def closure(roots: tuple[str, ...], table: dict[str, Declaration]) -> list[Declaration]:
    """Declarations reachable from `roots` by name, inside the statement modules."""
    seen: dict[str, Declaration] = {}
    pending = [name for name in roots]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        declaration = table.get(name)
        if declaration is None:
            raise LookupError(name)
        seen[name] = declaration
        for other, candidate in table.items():
            if other in seen or other == name:
                continue
            if re.search(rf"(?<![A-Za-z0-9_.'])" + re.escape(other) + r"(?![A-Za-z0-9_'])",
                         declaration.text):
                pending.append(other)
    return sorted(seen.values(), key=lambda d: (d.module, d.start))


def layer_lines(surface: Surface) -> tuple[int, int]:
    """Lines and module count of the layer this verification consists of."""
    modules: set[Path] = set()
    for entry in surface.layer:
        path = ROOT / entry
        if entry.endswith("/"):
            modules.update(sorted(path.rglob("*.lean")))
        else:
            modules.add(path)
    total = 0
    for path in sorted(modules):
        if not path.is_file():
            raise FileNotFoundError(path)
        total += len(path.read_text(encoding="utf-8").split("\n")) - 1
    return total, len(modules)


def measure(surface: Surface) -> dict:
    table: dict[str, Declaration] = {}
    for module in surface.statement_modules:
        path = ROOT / module
        if not path.is_file():
            raise FileNotFoundError(path)
        for name, declaration in declarations(path, module).items():
            table.setdefault(name, declaration)

    # Hypotheses first: an assumed proposition stays on the hypothesis side even
    # when the conclusion's own statement names it, because the question it
    # raises for a reader is the other one -- *is this the cited result?*
    hypothesis = closure(surface.hypothesis_roots, table) if surface.hypothesis_roots else []
    assumed = set(surface.hypothesis_roots)
    conclusion = [d for d in closure(surface.conclusion_roots, table)
                  if d.name not in assumed]
    # A definition both sides reach is read once, and it is read as vocabulary
    # of the conclusion.
    shared = {d.name for d in conclusion}
    hypothesis = [d for d in hypothesis if d.name not in shared]
    total, modules = layer_lines(surface)
    conclusion_lines = sum(d.lines for d in conclusion)
    hypothesis_lines = sum(d.lines for d in hypothesis)
    audit = conclusion_lines + hypothesis_lines
    return {
        "key": surface.key,
        "issue": surface.issue,
        "problem": surface.problem,
        "note": surface.note,
        "layer_lines": total,
        "layer_modules": modules,
        "conclusion_lines": conclusion_lines,
        "conclusion_declarations": [f"{d.module}:{d.start} {d.name}" for d in conclusion],
        "hypothesis_lines": hypothesis_lines,
        "hypothesis_declarations": [f"{d.module}:{d.start} {d.name}" for d in hypothesis],
        "audit_lines": audit,
        "audit_fraction": audit / total if total else 0.0,
    }


def report(result: dict, verbose: bool) -> None:
    print(f"{result['key']} (MAIS issue #{result['issue']}, {result['problem']}) "
          f"-- {result['note']}")
    print(f"  layer            {result['layer_lines']:>7,} lines "
          f"across {result['layer_modules']} modules")
    print(f"  conclusion       {result['conclusion_lines']:>7,} lines "
          f"({len(result['conclusion_declarations'])} declarations)")
    print(f"  hypotheses       {result['hypothesis_lines']:>7,} lines "
          f"({len(result['hypothesis_declarations'])} declarations)")
    print(f"  human audit      {result['audit_lines']:>7,} lines "
          f"= {result['audit_fraction'] * 100:.1f}% of the layer")
    if verbose:
        for label in ("conclusion_declarations", "hypothesis_declarations"):
            for entry in result[label]:
                print(f"    {label[0]} {entry}")
    print()


def main() -> int:
    parser = argparse.ArgumentParser(
        description="How many lines of a verification a human has to read.")
    parser.add_argument("--key", help="one surface, e.g. MAIS-O70")
    parser.add_argument("--json", action="store_true", help="machine-readable")
    parser.add_argument("--list", action="store_true",
                        help="print every declaration counted")
    args = parser.parse_args()

    selected = [s for s in SURFACES if args.key in (None, s.key)]
    if not selected:
        print(f"audit_surface: no surface named {args.key}", file=sys.stderr)
        return 1

    results = []
    failures = []
    for surface in selected:
        try:
            results.append(measure(surface))
        except LookupError as missing:
            failures.append(f"{surface.key}: no declaration {missing.args[0]} "
                            f"in its statement modules")
        except FileNotFoundError as missing:
            failures.append(f"{surface.key}: missing module {missing.args[0]}")

    if args.json:
        print(json.dumps(results, indent=2))
    else:
        for result in results:
            report(result, args.list)

    for failure in failures:
        print(f"audit_surface: {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
