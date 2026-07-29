# Source audit: compositional A1–A3 and wireheading B1–B3

Date: 2026-07-28; retraction 2026-07-29; narrative refresh 2026-07-29 after
Phase 1–3 packages. This note records statement-level checks, representation
deltas, failed reproduction evidence, and one primary-source retraction. It does
not graduate any AI bridge.

Per-item source-notation to Lean tables (live, preferred):
[`a1-a3-b1-b3-b7-statement-maps.md`](a1-a3-b1-b3-b7-statement-maps.md).

Consolidated adversarial re-verification:
[`a1-a3-b1-b3-b7-reverification.md`](a1-a3-b1-b3-b7-reverification.md).

---

## A1 — hyperproperties

Primary mathematical source: Clarkson and Schneider, “Hyperproperties,”
*Journal of Computer Security* 18(6), 2010,
<https://www.cs.cornell.edu/fbs/publications/Hyperproperties.pdf>.

Two Lean presentations of Theorem 2 exist:

- **Batch form**
  `AISafetyAtlas.Compositional.Hyperproperties.k_safety_iff_finite_self_composition`
  — unordered batches of at most `k` complete traces.
- **Product form**
  `AISafetyAtlas.Compositional.Hyperproperties.k_safety_iff_product_self_composition`
  — synchronized `Fin k → Trace` tuples (`productSelfComposition`), with
  `toBatch` / `padBatch` translations and proved empty-batch boundaries. The
  product satisfaction theorem carries a **nonempty system** hypothesis, which
  the empty-system lemmas show is necessary for `k > 0`.

Operational topology:

- `prefixTopology` in
  `AISafetyAtlas.Compositional.Hyperproperties.PrefixTopology` is a **def**, not
  a global instance (it depends on `prefixOf`).
- `isClosed_iff_hyperSafety` and `dense_iff_hyperLiveness` identify closed/dense
  with operational hypersafety/hyperliveness.
- `hyperSafety_of_isKSafety` joins the k-safety reduction to that reading.
- `hyperSafety_hyperLiveness_decomposition` specializes the classical
  decomposition through this topology.

The parent module still exposes a **generic** topology theorem
(`hypersafety_hyperliveness_decomposition` under an arbitrary
`TopologicalSpace`); that is not the operational claim. Cite `PrefixTopology`
for operational meaning.

### Exact Rocq reproduction attempt

Upstream artifact:
<https://github.com/secure-compilation/exploring-robust-property-preservation>,
revision `c68187cbaba763d88cbb3509df4ca9cf49cc6338`.

Unmodified `make -j4` was attempted in:

- `coqorg/coq:8.9.1`, digest
  `sha256:8e26609c5450aa795af6917cf169a65ab3952ba666d1b0c90e6b0179314a1149`;
- `coqorg/coq:8.20`, digest
  `sha256:e50d77c4c5a9aa0d76ae1b343d79c5f922da3a75054b79c5dc635895438e4674`.

Both builds compiled `Properties.v`, `Topology.v`, `TopologyTrace.v`, and most
of the tree, then failed at `InternalNondet.v:8`:

```text
From Stdlib Require Import List.
Error: Cannot find a physical path bound to logical path List with prefix Stdlib.
```

Exact repository-wide reproduction is **failed**, not reproduced. No source
patch was used to relabel the result. `Topology.v:11` declares
`Axiom prop_ext : prop_extensionality`. The independent Lean result does not
import that axiom.

---

## A2 — rectangularity

Sources:

- Kushilevitz and Nisan, *Communication Complexity*, 1997;
- Fagin, *ACM TODS* 2(3), 1977 (empty-determinant lossless-join case).

Headline results:

- `rectangle_iff_exchange_closed` — binary folklore.
- `coordinate_product_iff_spliceClosed` — finite index, nonempty `P`: full
  product of unary projections iff single-coordinate splice closure.
- Machine-checked necessity: `FinitelySupported` is splice-closed with full
  projections but not a product (`not_isCoordinateProduct_finitelySupported`).

`coordinate_product_iff_recombination_closed` is retained as a **helper** (near
definitional); it is not the module headline.

---

## A3 — deterministic symmetry and networks

Primary source: Angluin, STOC 1980.

Two layers:

1. `AISafetyAtlas.Compositional.Symmetry` — inductive core with
   `symmetric_observation` as a structure field (consequence of anonymity).
2. `AISafetyAtlas.Compositional.Networks` — port-labelled networks, shared
   algorithms, depth-`n` views, automorphisms;
   `runFor_eq_of_view_eq` **derives** equal states from equal views;
   `no_unique_leader_of_fixedPointFree` uses a fixed-point-free automorphism.

Landscape: `LAND-ANGLUIN-001`. **RELATED** only for BY-043: not the survey’s
self-interest / embodiment / mutual-control model. Non-claims: simplified
message routing (no reverse-port involution), no covering theory, no randomness.

---

## B1 — objective factorization and agent equations

Primary source: Ring and Orseau, AGI 2011, §2 (statements/arguments; **no
numbered factorization theorem**).

- `Objective.value_congr` / `optimal_decisions_congr` — record congruence only
  (honest names; do not call them factorization theorems).
- `value_eq_of_agree_on_window`, `value_scaleUtility`,
  `optimal_decisions_eq_of_pos_scaleUtility` — unfold the finite sum.
- `AgentEquations` — finite-horizon form of displayed equations (1)–(3), with
  `truncation_exact` when the horizon vanishes past the window;
  `value_eq_of_agree_on_window` uses the recursion.

`ρ` is an arbitrary real conditional weight (not a probability measure or
Solomonoff prior). Utilities are unbounded real values rather than the source's
`[0,1]` range. Delusion box / Statements 1–7 not formalized.

---

## B2 — goal preservation

Primary source: Everitt, Filan, Daswani, Hutter (2016), Theorem 16.

Two layers:

1. `GoalPreservation` — deterministic specialization; still uses
   `names_surjective` (stronger than the source); retained as the simpler model.
2. `GoalPreservationSource` — induction step of Theorem 16 **without**
   surjectivity: compares only against the named initial policy under a
   normalized full-support finite distribution (`prob_sum_one`, `prob_pos`) and
   `initial_dominates`. Theorem 20 / modification-independence not derived.

Landscape headline: `GoalPreservationSource.Model.selected_matches_initial`.

---

## B3 — corrupted-reward regret

Primary source: Everitt et al., IJCAI 2017 / arXiv:1705.08417, Theorem 11.

Two levels:

1. `Corruption.ComplementedClass` — algebraic core (complement closure +
   extrema witnesses) → `everitt_theorem_eleven`.
2. `CRMDP` — states, actions, one fixed deterministic transition,
   unit-interval true and observed rewards, corruption, policies on
   action-and-observation histories; proves
   `observed_complement`, history agreement, equation (3)
   `return_add_complement`; packages as `ComplementedClass`; canonical
   declaration `CRMDP.Model.everitt_theorem_eleven`.

Still RELATED: one Lean `Model` fixes a deterministic transition while the
source's complete class may range over stochastic kernels; extrema are
structure fields not derived from finiteness; rewards use the continuous
interval `[0,1]`, not a finite uniform grid. The bound is load-bearing: the
superseded unrestricted-real interface forced every inhabited model to have
zero regret. `SixTargets.nonzeroCRMDPModel` now proves worst-case regret `1` in
a concrete model.

### Retraction, 2026-07-29

An earlier version of this note claimed the source's displayed proof states
`max_π Reg(ℳ, π) = M - m` for global maximum and minimum returns, and that this
intermediate step does not follow without stronger assumptions.
**That claim is withdrawn. It was based on a misreading, and the source proof is
correct as published.**

The IJCAI conference version contains no proof (points to the long version).
The arXiv version’s equation (4) uses `M_µ` and `m_µ` as max/min cumulative
reward **in a single fixed environment `µ`**, not over the class. Pulling the
maximum through is valid. The earlier note transcribed environment-level
quantities as class-level ones.

The Lean contribution is **abstraction and a CRMDP-level construction**, not
repair of a broken source proof.

---

## B7 (pointer)

Preference-deduction detail lives in the statement maps and registry
`source_coverage` for BY-011 (6/8; Conjecture 9 predicate-only; Proposition 10
blocked on resource-bounded complexity). Canonical source Prop 7/8:
`Preference.Source.ReasonableForF`. Lean reward functions are unrestricted
real-valued functions rather than the source's `[-1,1]`-valued functions.
