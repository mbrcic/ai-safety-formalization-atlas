# Compositional boundaries — provenance and statement cards

Native atlas module (landscape entries `LAND-COMP-001`, `LAND-OBS-001`; never
survey headline coverage). Lean surface:
`AISafetyAtlas/Composition/Rectangularity.lean`,
`AISafetyAtlas/Composition/Observability.lean`, witnesses under
`AISafetyAtlas/Examples/Composition/`.

## Prior-art position

The mathematics is established; the claim is **mechanization + safety-facing
interface**, not mathematical priority.

- **Rectangularity** (`independent_iff_rectangular`): the "combinatorial
  rectangle closed under mix-and-match" folklore of communication complexity
  (Kushilevitz & Nisan, *Communication Complexity*, CUP 1997, Ch. 1) and the
  degenerate empty-antecedent case of Fagin's multivalued-dependency
  decomposition (Fagin, *ACM TODS* 2(3):262–278, 1977, DOI
  10.1145/320557.320571).
- **Observation factorization**
  (`factors_through_iff_fiber_invariant`): set-level packaging of
  factorization through a map. The pointwise form is Mathlib's
  `Function.FactorsThrough`; the equivalence parallels
  `Function.factorsThrough_iff` and `Function.DependsOn`
  (`Mathlib/Logic/Function/DependsOn.lean`). Reused, not redefined.
- **Mechanization gap at triage time (2026-07-24):** no formalization of the
  rectangle ⟺ exchange characterization, nor of MVD/join-dependency
  decomposition, located in Mathlib, Isabelle AFP, or Coq. Local sweep of
  the pinned Mathlib tree: only `Set.pi` building blocks
  (`Set.eval_image_pi`, `Set.subset_pi_eval_image`, `Set.update_mem_pi_iff`)
  and `BoxIntegral.Box` (real interval boxes, unrelated). "None found" ≠
  "does not exist"; a Zulip/AFP/opam sweep remains open before any
  publication claim.

## Mathlib reuse map

| This module | Reuses |
| --- | --- |
| `IndependentlyExpressible` | `Set.pi Set.univ` |
| projections | `Function.eval i '' P` (no new definition) |
| `independent_iff_eq_pi_projections` | `Set.subset_pi_eval_image` |
| `CoordinateSpliceClosed` | `Function.update` (predicate is new) |
| fiber invariance | `Function.FactorsThrough (· ∈ hazard) observe` (not redefined) |
| monitors | flagged set `Set Observation`; soundness/completeness are preimage inclusions |

## Statement cards

### `independent_iff_rectangular` (T2)

- Mathematical: for `[Fintype Agent] [DecidableEq Agent] [Nonempty Agent]`,
  a set `P : Set (∀ i, LocalState i)` is a `Set.pi` of per-agent sets iff it
  is closed under one-coordinate splices.
- Engineering: independent local predicates are complete exactly for
  recombination-closed properties.
- AI-safety: individually approved agent states need not compose safely.
- Non-claim: nothing about learning, strategic behavior, temporal
  evolution, hidden channels, computability of projections, or
  hyperproperties.
- Edge cases: `[Nonempty Agent]` excludes only the empty-agent corner
  (empty product is a singleton; `∅` is splice-closed but not a product).
  Empty `P` is handled inside the theorem, not assumed away.

### `independent_iff_eq_pi_projections` (T1)

- The strongest independent local contracts are exactly the coordinate
  projections; if rebuilding from projections adds states, independence
  lost global information. Non-claim: projections need not be tractable or
  observable.

### `not_independent_of_failed_splice` (T3)

- One certified failed recombination refutes every independent per-agent
  contract family. Needs only `[DecidableEq Agent]` — no finiteness, no
  nonemptiness.

### `factors_through_iff_fiber_invariant` (T4)

- A hazard is a preimage of a flagged observation set iff membership never
  separates two executions with equal observations. General observability
  statement; not LLM-specific.

### `exists_perfect_monitor_iff` / `no_perfect_monitor_of_collision` (T5)

- A sound and complete monitor exists iff the hazard is
  observation-determined; a single safe/hazardous observational collision
  rules out every such monitor. Non-claim: imperfect (sound-but-incomplete
  or statistical) monitoring is not claimed useless; no statement about
  detection power, timing, or probability.

## Certified witnesses

| Witness | File | Axes (scope, arity) | Content |
| --- | --- | --- | --- |
| W1 shared budget | `Examples/SharedBudget.lean` | (2, 1) | `![1,0]`, `![0,1]` safe; splice `![1,1]` busts cap |
| W3 fragment trap | `Examples/FragmentTrap.lean` | (2, 1) | **same theorem shape as W1** — one theorem, two instantiations; value is the bridge to the compositional-fragment-trap literature (bridge claim documented, not formalized) |
| W2 two-trace agreement | `Examples/TraceAgreement.lean` | (1, 2) | product indexed by *execution*, local state is a whole one-agent trace; the 2-safety/hyperproperty boundary in minimal form. Axes are distinct; no "scope arity = k-safety" claim |
| W4 observation collision | `Examples/LocalObservationCollision.lean` | — | agent-0-scoped view cannot host a sound-and-complete monitor for a joint hazard |

## Scope boundary

All positive results concern trace/state safety properties over a product of
per-agent (or per-execution) states. Hyperproperties (noninterference,
collusion-as-information-flow, privacy-by-composition) are **not** claimed
expressible by independent per-agent contracts — W2 certifies exactly this
boundary along the execution axis. The k-safety/self-composition lifting
(Clarkson–Schneider, *J. Comput. Secur.* 18(6), 2010, Thm 2) is the known
escape hatch and a candidate follow-up target.

## Verification

- `lake build AISafetyAtlas` — module on the public root import.
- `xargs lake build < scripts/lean_build_targets.txt` — witnesses build.
- `python3 scripts/check_print_axioms.py` — all six public declarations
  kernel-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no
  `native_decide`.
