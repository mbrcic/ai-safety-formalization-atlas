#!/usr/bin/env python3
"""Group the atlas's predicates by the proposition they actually are.

The structural matcher in the ontology work fingerprints *elaborated
signatures*. That is why it could not find the largest structural collapse in
this tree: `Knowledge.Knowable`, `Knowledge.Determines`,
`Oversight.JointObservation.Covers` and `Oversight.JointObservation.Refines` all
unfold to `∃ f, ∀ x, B x = f (A x)` while carrying four different signatures —
different arity, different implicit structure, one of them taking a bundled
structure. Signatures differ, bodies are identical, and the matcher only looks
at signatures. A duplicate shipped through it: `Determines.trans` was added as
"an elementary law the relation lacked" and is `Knowable.mono`.

`docs/status/elab-baseline-*.json` cannot fix that either. Its `fp` field is a
fingerprint of the declaration's *type*; it records no definition bodies, by the
same design decision that keeps `declaration-index.json` type-free. So this asks
Lean directly.

**What it does.** For every `AISafetyAtlas` definition whose type telescopes to
`Prop`, it takes the definition's value, telescopes the binders, and prints a
name-erased de Bruijn rendering of the body. The scan covers the root import
*plus* `scripts/lean_build_targets.txt`, which is the same domain
`generate_declaration_index.py` walks and is reused from it: the root alone
misses the MAIS conjecture layer, which `AISafetyAtlas.lean` does not import,
and everything under `Examples/`. An earlier version scanned the root only while
claiming to cover the atlas. Two predicates with
the same rendering are the same proposition with different parameter names.
A group is a **candidate**: two vocabularies that may have been built for one
idea. It is not a proof that they were, and the output says `candidate` rather
than `identical` for a reason given below.

Parameters are ordered by **first use in the body**, not by declaration, and
that is load-bearing rather than tidy. `Knowable` binds `{Ω} {I} {Y}
(observation : Ω → I) (property : Ω → Y)` while `Determines` binds `{Ω} {I} {J}
(finer : Ω → J) (coarser : Ω → I)`: the same proposition with the second and
third type parameters playing swapped roles. Abstracting in declaration order
gives them different renderings, and the first version of this script reported
no group for exactly that reason.

Constants keep their names and literals keep their values, so two predicates
that differ only in a number are two shapes. That is not a refinement: an
earlier version rendered a literal's *type*, which made `n = 1` and `n = 2`
identical and would have reported them as one proposition.

**What a group does and does not establish.** The rendering is invariant under
parameter renaming *and reordering*, and reordering is where it overreaches:

    def Q1 (f g : Nat → Nat) : Prop := ∀ n, f n = g n
    def Q2 (f g : Nat → Nat) : Prop := ∀ n, g n = f n

render identically, because ordering parameters by first use swaps `f` and `g`.
Those are not the same proposition — `Eq` is not definitionally symmetric — so a
group is a place to look, not a verdict. Both live groups were confirmed
separately, by writing the term that proves one from the other
(`Determines.trans := Knowable.mono`) and by the two `Compatible` definitions
being character-identical with identical types.

**Confirming a group automatically is harder than it looks, and one obvious
route is a dead end.** Applying both constants to fresh metavariables and asking
`isDefEq` does not test whether they agree for *all* arguments; it tests whether
some assignment makes them agree, so it unifies almost anything of the same
result type. Run on this tree it reported `Analysis.ClosedBox` as
`Examples.Analysis.Semialgebraic.unitSquare`, `SelfAwareness.Model.available` as
`Verification.Holds`, and `Causal.Model.HasRegretAtMost` as
`Preference.OverrideModel.Overrides`, before exhausting `maxHeartbeats`. It is a
unifier, not an equivalence test. Do not rebuild it.

**What it does not do, and the case that proves it.** The rendering is
syntactic after name erasure, so a predicate that reaches its arguments through
a projection does not match one that takes them directly: `Covers q h` mentions
`q.observe` where `Knowable observation property` mentions a bare variable, and
the two render differently even though `Covers q h ↔ Knowable q.observe h` holds
by `Iff.rfl`. Catching that needs definitional unification at instantiated
arguments, which is quadratic and is not what this script is for. So a group
here is evidence of duplication; the absence of a group is not evidence of its
absence.

Usage:
    python3 scripts/report_predicate_duplicates.py                  # every group
    python3 scripts/report_predicate_duplicates.py --cross-domain   # only across domains

Both live groups are *within* one domain, which is why cross-domain is a flag
rather than the default: duplication is at least as likely between two files a
person wrote a month apart as between two domains.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "AISafetyAtlas"

sys.path.insert(0, str(Path(__file__).resolve().parent))

from generate_declaration_index import consumer_modules  # noqa: E402

HARNESS_PRELUDE = r"""
open Lean Meta

/-- A name-erased de Bruijn rendering: structure only, no identifiers from the
binders. Constants keep their names, because two predicates built from
different constants are different predicates. -/
partial def render : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .fvar f => do return s!"@{(← f.getUserName)}"
  | .mvar _ => return "?"
  | .sort _ => return "S"
  | .const n _ => return s!"c:{n}"
  | .app f a => do return s!"({← render f} {← render a})"
  | .lam _ t b _ => do return s!"(L {← render t} {← render b})"
  | .forallE _ t b _ => do return s!"(P {← render t} {← render b})"
  | .letE _ t v b _ => do return s!"(E {← render t} {← render v} {← render b})"
  -- The literal's *value*, not its type. Rendering `l.type` collapsed every
  -- natural to `lit:Nat`, so `n = 1` and `n = 2` were one shape and the report
  -- would have grouped two different propositions as the same one.
  | .lit (.natVal v) => return s!"nat:{v}"
  | .lit (.strVal v) => return s!"str:{v}"
  | .mdata _ e => render e
  | .proj s i e => do return s!"(proj {s} {i} {← render e})"

/-- The free variables of `e`, in order of first appearance. -/
partial def occurrences : Expr → Array FVarId → Array FVarId
  | .fvar f, acc => if acc.contains f then acc else acc.push f
  | .app g a, acc => occurrences a (occurrences g acc)
  | .lam _ t b _, acc => occurrences b (occurrences t acc)
  | .forallE _ t b _, acc => occurrences b (occurrences t acc)
  | .letE _ t v b _, acc => occurrences b (occurrences v (occurrences t acc))
  | .mdata _ e, acc => occurrences e acc
  | .proj _ _ e, acc => occurrences e acc
  | _, acc => acc

/-- Parameters ordered by first use in the body, not by declaration.

Two predicates can be the same proposition and declare their type parameters in
a different order. `Knowable` binds `{Ω} {I} {Y} (observation : Ω → I)
(property : Ω → Y)`; `Determines` binds `{Ω} {I} {J} (finer : Ω → J)
(coarser : Ω → I)`, so the second and third type parameters play swapped roles.
Abstracting positionally gives them different de Bruijn renderings for one
proposition, which is the whole failure this report exists to avoid. Ordering by
first use in the body is invariant under that permutation. Parameters the body
never mentions keep their declared order at the end. -/
def canonicalOrder (xs : Array Expr) (body : Expr) : Array Expr :=
  let used := occurrences body #[]
  let rank := fun (e : Expr) =>
    match e with
    | .fvar f => match used.findIdx? (· == f) with
                 | some i => i
                 | none => used.size + 1
    | _ => used.size + 1
  xs.qsort (fun a b => rank a < rank b)

def report : MetaM Unit := do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless n.toString.startsWith "AISafetyAtlas" do continue
    unless ci.isDef do continue
    let isPred ← forallTelescopeReducing ci.type fun _ b => return (← whnf b).isProp
    unless isPred do continue
    let some value := ci.value? | continue
    -- Telescope the parameters so that only the proposition's shape remains,
    -- with the parameters themselves as de Bruijn references into it.
    let shape ← lambdaTelescope value fun xs body => do
      let abstracted := body.abstract (canonicalOrder xs body)
      render abstracted
    IO.println s!"{n}\t{shape}"

#eval report
"""


def harness_source() -> str:
    """The same import set `generate_declaration_index.py` walks.

    `import AISafetyAtlas` alone reaches only the root closure. The MAIS
    conjecture layer is not root-imported — `AISafetyAtlas.lean` names no
    `Conjectures` module — so 562 declarations, plus everything under
    `Examples/`, were outside a scan whose header claimed to cover every atlas
    definition. Reusing `consumer_modules()` rather than restating the list
    keeps the two scans from drifting to different domains.
    """
    imports = ["import AISafetyAtlas", *(f"import {m}" for m in consumer_modules())]
    return "\n".join(imports) + "\n" + HARNESS_PRELUDE


def domain(name: str) -> str:
    parts = name.split(".")
    return parts[1] if len(parts) > 1 else "?"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cross-domain", action="store_true",
        help="print only groups spanning more than one top-level domain",
    )
    args = parser.parse_args()

    with tempfile.TemporaryDirectory(prefix="atlas-preddup-") as tmp:
        path = Path(tmp) / "PredicateShapes.lean"
        path.write_text(harness_source(), encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT, capture_output=True, text=True,
        )
    if proc.returncode != 0:
        print(proc.stdout + proc.stderr, file=sys.stderr)
        print("report_predicate_duplicates: the harness did not run", file=sys.stderr)
        return 1

    groups: dict[str, list[str]] = defaultdict(list)
    for line in proc.stdout.splitlines():
        if "\t" not in line:
            continue
        name, shape = line.split("\t", 1)
        if not name.startswith(PREFIX):
            continue
        groups[shape].append(name)

    interesting = []
    for shape, names in groups.items():
        if len(names) < 2:
            continue
        if args.cross_domain and len({domain(n) for n in names}) < 2:
            continue
        interesting.append((sorted(names), shape))
    interesting.sort()

    print(f"predicates scanned: {sum(len(v) for v in groups.values())}")
    label = "cross-domain candidate group(s)" if args.cross_domain else "candidate group(s)"
    print(
        f"{len(interesting)} {label} — same body up to parameter renaming and "
        "reordering; confirm each by proving one from the other:"
    )
    for names, shape in interesting:
        print(f"  shape {shape[:90]}{'…' if len(shape) > 90 else ''}")
        for name in names:
            print(f"      {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
