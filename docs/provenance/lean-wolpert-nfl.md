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

## Supervised distributional / homogeneous-loss strengthening (2026-07-20)

The mean-only closed form above is the first moment. Two Wolpert-1996
strengthenings are now proven, both still finite / uniform-averaging and
kernel-clean:

- **Homogeneous loss.** `HomogeneousLoss ℓ` := for any two predictions there is a
  relabeling `π : Y ≃ Y` of truth values matching their loss profiles. 0-1 loss
  qualifies (`homogeneous_zeroOne`, via the transposition `Equiv.swap`). Replaces
  the hard-coded 0-1 loss.
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

Not claimed EXACT/EQUIVALENT to the full papers:

- **1997:** the deterministic **adaptive** no-revisit case is now covered (see
  the adaptive strengthening above); *stochastic* algorithms and time-varying
  objectives remain out of scope (open collaboration work);
- **1996:** *stochastic* learners and non-uniform prior `P(f)` averaging remain
  out of scope (open collaboration work — needs Mathlib probability). The
  deterministic homogeneous-loss **full-distribution** core is now covered (see
  strengthening above); general (non-homogeneous) loss is genuinely
  learner-dependent and correctly excluded.

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
