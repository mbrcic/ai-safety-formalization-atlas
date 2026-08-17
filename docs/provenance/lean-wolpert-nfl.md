# Lean formalization — Wolpert finite-domain No Free Lunch

In-tree Lean proofs of the **finite discrete uniform-averaging** cores associated
with:

- Wolpert–Macready *No free lunch theorems for optimization* (IEEE TEC 1997;
  survey-ref-019 / **BY-021**);
- Wolpert *The **Lack** of A Priori Distinctions Between Learning Algorithms*
  (Neural Computation 8(7):1341–1390, 1996, doi `10.1162/neco.1996.8.7.1341`) —
  the actual source of the formalized supervised NFL (uniform target average,
  off-training-set error learner-independence, homogeneous loss).
  **Citation note:** survey ref [18] and registry `survey-ref-018` cite the
  companion paper *The Existence of A Priori Distinctions Between Learning
  Algorithms* (same issue, pp. 1391–1420, doi `10.1162/neco.1996.8.7.1391`),
  which proves the *converse* — distinctions exist for non-homogeneous loss
  (e.g. quadratic). The registry deliberately mirrors the survey's own citation;
  the content formalized in this module is from the *Lack* paper, not *Existence*.
  (survey-ref-018 / **BY-020**).

## Public surface

| Item | Optimization (BY-021) | Supervised (BY-020) |
|------|------------------------|---------------------|
| Module | `AISafetyAtlas.Learning` | same |
| Headline theorem | `no_free_lunch` | `no_free_lunch_supervised` |
| Supporting identities | `sum_performance_eq_scaled_sum`, `aggregatePerformance_eq_scaled_sum` | `sum_pointLoss_off_training`, `aggregateOffTrainingLoss_eq` |
| Artifact type | `NEW_PROOF` | `NEW_PROOF` |
| Relationship | **RELATED** | **RELATED** |
| Root import | `AISafetyAtlas` → Learning | same |
| Consumer examples | `Examples.PublicAPI`, `Examples.NFLConcrete` | same |
| Build | `lake build AISafetyAtlas.Learning AISafetyAtlas.Examples.PublicAPI AISafetyAtlas.Examples.NFLConcrete` | same |
| Axiom check | `python3 scripts/check_print_axioms.py` | lists both headlines |

## Optimization statement (BY-021)

Finite types `X` (search domain) and `Y` (cost codomain). A
**non-adaptive schedule** is an injective sample `sample : Fin m → X` (no
revisits). A **cost-sequence performance** is any `Φ : (Fin m → Y) → ℝ`.
**Aggregate performance** is the sum of `Φ(f ∘ sample)` over all objectives
`f : X → Y`.

**Theorem (`no_free_lunch`):** for any `Φ` and any two non-adaptive schedules
of length `m`,

```text
aggregatePerformance Φ s₁ = aggregatePerformance Φ s₂
```

**Closed form:**

```text
∑_f Φ(f ∘ σ) = |Y|^{|X| − m} · ∑_c Φ(c)
```

Proof: decompose `X ≃ range(σ) ⊕ complement` and reindex
(`Equiv.Set.sumCompl`, `Equiv.sumArrowEquivProdArrow`).

## Supervised statement (BY-020)

Finite types `X`, `Y`. Fixed training domain `S ⊆ X`. A **supervised learner**
is `A : (S → Y) → (X → Y)`. **Off-training-set loss** is the sum of pointwise
0-1 losses on `X \ S`. **Aggregate OTS loss** sums that quantity over all
targets `f : X → Y`.

**Theorem (`no_free_lunch_supervised`):** for any `S` and learners `A`, `B`,

```text
aggregateOffTrainingLoss S A = aggregateOffTrainingLoss S B
```

**Pointwise engine (`sum_pointLoss_off_training`):** for any `x ∉ S`,

```text
∑_f pointLoss f (predict A f) x = (|Y| − 1) · |Y|^{|X| − 1}
```

**Closed form:**

```text
aggregateOffTrainingLoss S A = |Sᶜ| · (|Y| − 1) · |Y|^{|X| − 1}
```

Proof: `Equiv.funSplitAt` at the test point — training labels (and thus the
learner’s prediction at `x`) depend only on values off `x`, while `f(x)` is
free under the uniform sum.

## Supervised distributional / homogeneous-loss strengthening (2026-07-20)

The mean-only closed form above is the first moment. Two Wolpert-1996
strengthenings are now proven, both still finite / uniform-averaging and
kernel-clean:

- **Homogeneous loss.** `HomogeneousLoss ℓ` := for any two predictions there is a
  relabeling `π : Y ≃ Y` of truth values matching their loss profiles. 0-1 loss
  qualifies (`homogeneous_zeroOne`, via the transposition `Equiv.swap`). Replaces
  the hard-coded 0-1 loss.
- **The condition is tight (iff).** `homogeneous_iff_learner_indep`: given at least
  one off-training point, homogeneity is **necessary and sufficient** for the OTS
  loss *vector* distribution — every functional `Ψ` of the loss vector — to be
  learner-independent. Scalar vs vector: the scalar total-loss distribution
  (`ots_error_distribution_learner_indep`) is a weaker consequence of the vector
  form; sufficiency covers it, but necessity is proven only from vector-level
  independence — that scalar independence *alone* forces homogeneity is not
  claimed. Sufficiency is
  `lossConfig_sum_learner_indep`; necessity (`homogeneous_of_learner_indep`) probes
  learner-independence with two constant learners and a value-indicator functional,
  reducing (`sum_ite_pointval_eq`) to equal loss-value fibers, then glues a
  permutation of the truth space (`exists_perm_comp_of_fiber_card_eq`,
  `Equiv.sigmaFiberEquiv` + `Fintype.equivOfCardEq`). This iff is a **NEW_PROOF**:
  Wolpert never stated it as a biconditional (his *Existence* companion only
  *demonstrates* distinctions for non-homogeneous loss). It is the loss-axis analog
  of the Schumacher–Vose–Whitley (GECCO 2001) / Igel–Toussaint (2004,
  doi `10.1023/B:JMMA.0000049381.24625.f7`) "closed under permutation"
  necessary-and-sufficient NFL characterization, which lives on the prior axis
  and is now formalized in its own right — see [CT-10](#ct-10--the-sharp-closed-under-permutation-characterization) below.
- **Full distribution, not just the mean.** For homogeneous `ℓ` and *any*
  functional `Ψ` of the off-training-set loss vector,

  ```text
  ∑_f Ψ(lossConfig ℓ S A f) = ∑_f Ψ(lossConfig ℓ S B f)
  ```

  (`lossConfig_sum_learner_indep`). `Ψ = sum` recovers the mean; an indicator of
  a value recovers the entire generalization-error distribution
  (`ots_error_distribution_learner_indep`, i.e. every learner attains any given
  total OTS loss on the *same number* of targets); `Ψ = (sum)^k` recovers every
  moment.

Proof: group targets by the training restriction `d` (`Equiv.Set.sumCompl`);
within a fixed block the free OTS values are relabeled coordinate-wise by the
homogeneity `π` (`Equiv.piCongrRight`), a bijection on the target space that turns
`A`'s loss vector into `B`'s. So the OTS-error *distribution* — not just its mean
— is learner-independent.

## Adaptive optimization strengthening (BY-021, 2026-07-20)

The optimization core (`no_free_lunch`) restricts to **non-adaptive** schedules —
a fixed point sequence that ignores observed costs. The genuinely adaptive case
is now proven:

- `AdaptiveRule X Y m := ∀ k : Fin m, (Fin k → Y) → X` — a deterministic rule that
  picks each next query from the costs already observed.
- `observed r f` — the cost sequence rule `r` produces on objective `f`, built
  prefix by prefix (`Fin.snoc`).
- `no_free_lunch_adaptive` — for `m ≤ |X|` and any two **no-revisit** adaptive
  rules and any functional `Ψ` of the observed cost sequence,

  ```text
  ∑_f Ψ(observed r₁ f) = ∑_f Ψ(observed r₂ f)  ( = |Y|^{|X|−m} · ∑_c Ψ(c) )
  ```

Proof: the "backward" fiber inclusion `(∀k, f(ruleVisit r c k) = c k) → observed r f = c`
by prefix induction; each fiber then has real cardinality `|Y|^{|X|−m}` by a
**pigeonhole** — each fiber is at least the constrained set (via the non-adaptive
reindexing `sum_performance_eq_scaled_sum` on the injective trajectory), the fibers
partition `X → Y`, and the totals `∑ = |Y|^{|X|}` match, forcing equality
(`Finset.sum_eq_sum_iff_of_le`). No forward fixpoint lemma needed.

## Why RELATED (not EXACT / EQUIVALENT)

Both results match the classical **finite-domain, uniform-over-all-targets,
equal aggregate performance** NFL identities in the standard deterministic
special cases used in expositions.

The honesty cuts both ways: the two strengthenings (`no_free_lunch_adaptive`,
`lossConfig_sum_learner_indep` / `ots_error_distribution_learner_indep`)
reproduce their papers' deterministic finite-case claims **exactly** — the
adaptive one is Wolpert–Macready Theorem 1 (full cost-sequence histogram, not a
scalar), the supervised one is Wolpert 1996's OTS error *distribution* under
homogeneous loss. The taxonomy classification stays `RELATED` (not `EXACT`) at
the **row** level, taken against the full papers, which also cover the deferred
tail below.

Not claimed EXACT/EQUIVALENT to the full papers:

- **1997:** the deterministic **adaptive** no-revisit case is now covered (see
  the adaptive strengthening above); *stochastic* algorithms and time-varying
  objectives remain out of scope (open collaboration work);
- **1996:** *stochastic* learners and non-uniform prior `P(f)` averaging remain
  out of scope (open collaboration work — needs Mathlib probability). The
  deterministic homogeneous-loss **full-distribution** core is now covered (see
  strengthening above); general (non-homogeneous) loss is genuinely
  learner-dependent and correctly excluded.

## CT-10 — the sharp closed-under-permutation characterization

Landed 2026-08-16 in
[`AISafetyAtlas/Learning/Sharp.lean`](../../AISafetyAtlas/Learning/Sharp.lean),
with worked readings in
[`AISafetyAtlas/Examples/Learning/Sharp.lean`](../../AISafetyAtlas/Examples/Learning/Sharp.lean).
This closes the prior axis, as the loss axis was closed by
`homogeneous_iff_learner_indep`.

**Sources.** Schumacher, Vose and Whitley, *The No Free Lunch and Problem
Description Length* (GECCO 2001) — the first closure-under-permutation
characterization, stated for a *set* of objectives. Igel and Toussaint, *A
No-Free-Lunch Theorem for Non-Uniform Distributions of Target Functions*
(J. Math. Modelling and Algorithms 3(4), 2004,
doi `10.1023/B:JMMA.0000049381.24625.f7`) — both directions, for a
*distribution*. Catalogued as `schumacher-vose-whitley-2001` and
`igel-toussaint-2004`.

**Which texts were read.** All three, in their published form. The 2004 JMMA
statement was additionally checked against arXiv:`cs/0303032` (Theorem 6,
"non-uniform sharpened NFL") and Igel's later survey chapter, which agree with
it:

* **Igel–Toussaint 2004, Theorem 5** (*non-uniform sharpened NFL*): the
  condition is `f, g ∈ B_h ⇒ p(f) = p(g)`, and their Lemma 1(2) identifies the
  basis class `B_h` with the permutation orbit `⋃_π {f ∘ π}` — so it is exactly
  `PermInvariant`. The conclusion is quantified over any two algorithms, any
  `k ∈ ℝ`, any performance measure, **and any `m ∈ {1, …, |X|}`**. The algorithms
  are *non-repeating black-box search algorithms*, which are adaptive: they
  choose each next point from the history of prior explorations.
* **Schumacher–Vose–Whitley 2001**: the sharpened NFL is *"a No Free Lunch
  result holds over the set of functions `F` if and only if `F` is closed under
  permutation"*, over the same adaptive algorithm class. Their **NFL4** is
  worth noting for the weight axis: they observe that a *weighted* overall
  measure "is not generally subject to the No Free Lunch theorem except in the
  case where the functions are equally weighted", and stop there. The extension
  to non-uniform weights is Igel–Toussaint's, and the extension to arbitrary
  signed weights is this module's.

The printed
condition in every version is that the weight is constant on each basis class,
which by their Lemma 1 is the same condition as `PermInvariant`.

**The statement.** `nfl_iff_permInvariant`: aggregate performance is
schedule-independent, for every cost-sequence performance measure and every
sample length, **iff** the weighting of objectives satisfies
`P (f ∘ π) = P f` for every permutation `π` of the search domain.

**Grading: `RELATED`, and the difference cuts both ways.** This was corrected on
2026-08-16, having first been recorded as `EQUIVALENT` on a misreading; the
correction is kept visible here rather than quietly overwritten, and reading the
published papers the same day confirmed the corrected reading.

| axis | printed | atlas | effect |
|---|---|---|---|
| weight | a probability distribution over objectives | **any** real weight — no nonnegativity, no normalization | atlas is more general |
| condition | constant on each basis class | `P (f ∘ π) = P f` | the same condition, by their Lemma 1 |
| sample length | every `m ∈ {1, …, |X|}` | every `m` | the same |
| algorithms | non-repeating black-box search algorithms, **adaptive** | `AdaptiveRule` with `∀ c, Injective (ruleVisit r c)` — the same class | the same, since `nfl_adaptive_of_permInvariant` |

The two halves are no longer separated by the algorithm axis, and what remains
separates them in one direction only:

| declaration | relative to the source |
|---|---|
| `permInvariant_of_nfl` | **stronger**: it assumes schedule-independence only at the single length `m = card X`, only over non-adaptive schedules, and only at indicator measures. A weaker hypothesis for the same conclusion. |
| `nfl_adaptive_of_permInvariant` | **the printed class**: it concludes schedule-independence for adaptive non-repeating rules, quantified over every `m` and every cost-sequence measure, exactly as the source does. It exceeds print only on the weight axis. |
| `nfl_of_permInvariant` | the fixed-schedule special case, kept because it is the form the rest of the atlas consumes — not a scope claim. |

Two corrections are kept visible here rather than quietly overwritten.

* The sufficiency half does **not** sharpen the source by quantifying over every
  sample length: Theorem 5 quantifies over `m` as well.
* The algorithm axis is met. `nfl_adaptive_of_permInvariant` proves sufficiency
  over `AdaptiveRule` with the no-revisit hypothesis, which is the printed
  non-repeating black-box class; the proof is a fibre reindexing that builds the
  matching permutation from the cost sequence alone.

**Consequence for scope.** `CT-10` widens the **prior** axis and now meets the
source's algorithm class. **The stochastic axis is closed for both `CT-10`
sources**: Igel-Toussaint's cited randomized class is Droste-Jansen-Wegener's,
and `mixtureTrace` is their definition of it, while Schumacher-Vose-Whitley open
their §2 with *"deterministic non-repeating blackbox search algorithms"*, which
is `AdaptiveRule` and never carried a gap. What remains out of scope is
time-varying objectives, and Wolpert-Macready 1997's own stochastic algorithms,
which are a different paper and a different row.

**Which row these records live on.** `BY-021` (No Free Lunch — optimization),
not `BY-020` (supervised learning). Both `CT-10` sources quantify over
non-repeating black-box *search* algorithms — Igel–Toussaint's Figure 1 is
captioned "the optimization scenario considered in NFL-theorems" — so the
characterization is about the optimization row. The records sat on `BY-020`
until 2026-08-16 and were refiled then; `BY-020` keeps `no_free_lunch_supervised`
and the loss-axis `iff`, which are Wolpert 1996.

**The characterization is not vacuous in either direction.** Both cases are
inhabited, which is what makes it a characterization rather than a restatement:

* `Examples.Learning.nfl_fails_off_permInvariant` — a two-point domain, a weight
  concentrated on the identity objective, and two one-query schedules scoring
  `0` and `1`. Drop the hypothesis and NFL genuinely fails.
* `Examples.Learning.nfl_over_constants` — the constant objectives form a
  *proper* permutation-closed subset, so NFL holds over a non-uniform prior.
  This is Schumacher–Vose–Whitley's set form instantiated, via
  `permInvariant_of_closedUnderPermutation`.

**Subsumption.** The uniform cores are the constant-weight case;
`no_free_lunch_embedding_of_sharp` derives `no_free_lunch_embedding` from the
sharp theorem. The original proofs are independent and are retained — the
derivation is recorded to show the relationship, not to replace them.

**Axioms.** Every declaration is within `{propext, Classical.choice,
Quot.sound}`; `closedUnderPermutation_constants` needs only `{Quot.sound}`. No
`sorry`, no `native_decide`.

## Explicit non-coverage

| Target | Status |
|--------|--------|
| LAND-NFL-001 / AFP `No_Free_Lunch_ML` / SSBD Thm 5.1 | **DISTINCT** (PAC adversarial lower bound) |
| BY-022 continuous / coevolutionary free lunches | **Not** formalized (symmetry *fails* there) |

## AI-safety bridge

None graduated. `ai_bridge_status` remains `HUMAN_REVIEW` on both rows.

## Reproduction

```console
lake build AISafetyAtlas.Learning AISafetyAtlas.Examples.PublicAPI AISafetyAtlas.Examples.NFLConcrete
python3 scripts/check_print_axioms.py
rg sorry AISafetyAtlas/Learning.lean   # expect empty
```
