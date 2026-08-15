#!/usr/bin/env python3
"""Fail when a library module has no worked model anywhere in ``Examples/``.

This gate exists because one defect kept recurring and nothing caught it.  Six
times a layer was added, compiled, passed the axiom scan and the status tables,
and was still a statement about nothing: ``Prop6Law``, section 9's
``Infallible``, the general section-8 measure layer, section 5's inference
complexity, Proposition 3(ii)'s mutual distinguishability, and the
general-measure section-5 layer.  Each was found by a human re-reading the tree,
and each had been sitting there for at least one review round.  Two of the six
arrived with a *generalisation* — the special case had a model, the general
restatement did not.

The reason it kept escaping is that the existing tooling checks *proofs*.  A
theorem whose hypotheses nothing satisfies is a valid proof.  A definition no
model ever evaluates is a valid definition.  ``lake build`` is happy, the axiom
scan is happy, and the provenance tables are happy because the declaration
exists and matches the source.  Nothing anywhere asked whether a reader could
see the thing run.

So this checks the one property none of those do: every module that declares
public API must be referenced by at least one example.  It is deliberately weak
— one reference to one declaration clears a whole module — because a strict
per-declaration rule would need an allowlist of about eighty internal
construction helpers, and an allowlist that large is not read.  A weak check
that is trusted beats a strong one that is bypassed.

Exemptions carry a reason and are themselves checked: a module that gains
coverage must be removed from the list, or the gate fails.  Otherwise the
exemptions rot into a list of things nobody remembers excusing.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Modules that declare public API but are not expected to appear in any example,
# with the reason. Each entry is re-checked: gaining coverage is an error here,
# so the list cannot silently outlive its justification.
EXEMPT: dict[str, str] = {
    "AISafetyAtlas/Inference/Stochastic/Gibbs.lean": (
        "pure real arithmetic (Gibbs' inequality and its equality case), consumed "
        "only through Stochastic.lean and Stochastic/Measure.lean, both of which "
        "carry worked models"
    ),
    "AISafetyAtlas/Upstream/KolmogorovMathlib/Foundation/NatEncoding.lean": (
        "staged for upstreaming to Mathlib, which carries its own test discipline"
    ),
    "AISafetyAtlas/Upstream/KolmogorovMathlib/Foundation/RecursivelyEnumerable.lean": (
        "staged for upstreaming to Mathlib, which carries its own test discipline"
    ),
    "AISafetyAtlas/Upstream/KolmogorovMathlib/Complexity/Properties.lean": (
        "staged for upstreaming to Mathlib, which carries its own test discipline"
    ),
    "AISafetyAtlas/Upstream/KolmogorovMathlib/Complexity/Incompressibility.lean": (
        "staged for upstreaming to Mathlib, which carries its own test discipline"
    ),
    "AISafetyAtlas/Upstream/KolmogorovMathlib/Complexity/Uncomputability.lean": (
        "staged for upstreaming to Mathlib, which carries its own test discipline"
    ),
}

DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?public\s+(?:noncomputable\s+)?"
    r"(?:def|abbrev|structure|class|inductive|theorem|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)"
)

IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def public_names(path: Path) -> set[str]:
    """The public declarations a module introduces, by last name component."""
    names: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        if match := DECLARATION.match(line):
            names.add(match.group(1).split(".")[-1])
    return names


def check(root: Path, exempt: dict[str, str]) -> tuple[list[str], int, int]:
    """Return the errors, the covered module count, and the checked count."""
    lean_root = root / "AISafetyAtlas"
    examples = lean_root / "Examples"

    example_text = "\n".join(
        path.read_text(encoding="utf-8") for path in sorted(examples.rglob("*.lean"))
    )
    referenced = set(IDENTIFIER.findall(example_text))
    # Qualified occurrences count for the declaration they end in, so
    # `Inference.massOn` covers `massOn`.
    referenced |= {name.split(".")[-1] for name in referenced}

    conjectures = lean_root / "Conjectures"

    errors: list[str] = []
    checked = 0
    covered = 0
    for path in sorted(lean_root.rglob("*.lean")):
        if examples == path or examples in path.parents:
            continue
        # Conjectures are `Prop`-valued definitions that assert nothing and are
        # never on the root import. Requiring a worked model of an open question
        # is a category error: the model would be a proof. `conjectures.yaml`
        # and `Conjectures/Checks.lean` already require each one to be a closed
        # proposition, which is the check that applies here.
        if conjectures == path or conjectures in path.parents:
            continue
        names = public_names(path)
        if not names:
            # Facades and rule-set declarations introduce nothing to exercise.
            continue
        relative = path.relative_to(root).as_posix()
        checked += 1
        hits = names & referenced
        if hits:
            covered += 1
            if relative in exempt:
                errors.append(
                    f"{relative} is exempt but now has coverage "
                    f"({len(hits)} declaration(s) referenced); drop its EXEMPT entry"
                )
        elif relative not in exempt:
            errors.append(
                f"{relative} declares {len(names)} public declaration(s) and no "
                "example references any of them; add a worked model under "
                "AISafetyAtlas/Examples/ or an EXEMPT entry with a reason"
            )

    for name, reason in sorted(exempt.items()):
        if not (root / name).exists():
            errors.append(f"EXEMPT names {name}, which does not exist")
        elif not reason.strip():
            errors.append(f"EXEMPT entry {name} carries no reason")

    return errors, covered, checked


def main() -> int:
    errors, covered, checked = check(ROOT, EXEMPT)
    if errors:
        for error in errors:
            print(f"example coverage error: {error}", file=sys.stderr)
        return 1
    print(
        f"example coverage ok: {covered}/{checked} library modules referenced by "
        f"an example, {len(EXEMPT)} exempt"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
