# Lean formalization — Wolpert finite-domain No Free Lunch

In-tree Lean proofs of the **finite discrete uniform-averaging** cores associated
with:

- Wolpert–Macready *No free lunch theorems for optimization* (IEEE TEC 1997;
  survey-ref-019 / **BY-021**);
- Wolpert *The Existence of A Priori Distinctions Between Learning Algorithms*
  (Neural Computation 1996; survey-ref-018 / **BY-020**).

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

## Why RELATED (not EXACT / EQUIVALENT)

Both results match the classical **finite-domain, uniform-over-all-targets,
equal aggregate performance** NFL identities in the standard deterministic
special cases used in expositions.

Not claimed EXACT/EQUIVALENT to the full papers:

- **1997:** adaptive query trees, stochastic algorithms, time-varying objectives;
- **1996:** general loss, stochastic learners, cross-validation-as-meta-algorithm
  arguments beyond the OTS core.

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
