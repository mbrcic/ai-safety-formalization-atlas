# Lean formalization — Wolpert finite-domain No Free Lunch (BY-021)

In-tree Lean proof of the **finite discrete uniform-averaging** core associated
with Wolpert–Macready *No free lunch theorems for optimization* (IEEE TEC 1997;
survey-ref-019 / **BY-021**).

## Public surface

| Item | Value |
|------|--------|
| Module | `AISafetyAtlas.Learning` |
| Headline theorem | `AISafetyAtlas.Learning.no_free_lunch` |
| Supporting identity | `AISafetyAtlas.Learning.sum_performance_eq_scaled_sum` |
| Artifact type | `NEW_PROOF` |
| Relationship to BY-021 | **RELATED** |
| Root import | `AISafetyAtlas` → Learning |
| Consumer example | `AISafetyAtlas.Examples.PublicAPI` |
| Build | `lake build AISafetyAtlas.Learning AISafetyAtlas.Examples.PublicAPI` |
| Axiom check | `python3 scripts/check_print_axioms.py` (lists `no_free_lunch`) |

## Statement formalized

Finite types `X` (search domain) and `Y` (cost codomain). A
**non-adaptive schedule** is an injective sample `sample : Fin m → X` (no
revisits). A **cost-sequence performance** is any `Φ : (Fin m → Y) → ℝ`.
**Aggregate performance** is the sum of `Φ(f ∘ sample)` over all objectives
`f : X → Y` (uniform sum; averages are proportional).

**Theorem (`no_free_lunch`):** for any `Φ` and any two non-adaptive schedules
of length `m`,

```text
aggregatePerformance Φ s₁ = aggregatePerformance Φ s₂
```

**Closed form (`sum_performance_eq_scaled_sum` / `aggregatePerformance_eq_scaled_sum`):**

```text
∑_f Φ(f ∘ σ) = |Y|^{|X| − m} · ∑_c Φ(c)
```

independent of the injective sample `σ`. Proof: decompose `X ≃ range(σ) ⊕ complement`
and reindex the product of function spaces (`Equiv.Set.sumCompl`,
`Equiv.sumArrowEquivProdArrow`).

## Why RELATED (not EXACT / EQUIVALENT)

Matches the **finite-domain, uniform-over-all-objectives, equal aggregate
performance** claim that is the classical NFL identity for optimization, in the
**non-adaptive / non-revisiting** special case with performance a function of
the ordered cost sequence only.

Not claimed EXACT/EQUIVALENT to the full 1997 development:

- adaptive next-query maps (history-dependent algorithms);
- fully stochastic algorithms as probability kernels;
- time-varying objective functions (paper Theorem 2).

Those are natural extensions of the same reindexing idea; they are out of scope
for this cycle.

## Explicit non-coverage

| Target | Status |
|--------|--------|
| BY-020 Wolpert 1996 supervised (off-training-set) NFL | **Not** this formalization (different statement) |
| LAND-NFL-001 / AFP `No_Free_Lunch_ML` / SSBD Thm 5.1 | **DISTINCT** (PAC adversarial lower bound) |
| BY-022 continuous / coevolutionary free lunches | **Not** formalized (symmetry *fails* there) |

## AI-safety bridge

None graduated. `ai_bridge_status` remains `HUMAN_REVIEW`. The theorem is
classical finite combinatorics packaged under the Learning facade; any reading
about real AI optimizers or “no universal optimizer for deep learning” requires
separate human review.

## Reproduction

```console
lake build AISafetyAtlas.Learning AISafetyAtlas.Examples.PublicAPI
python3 scripts/check_print_axioms.py
rg sorry AISafetyAtlas/Learning.lean   # expect empty
```
