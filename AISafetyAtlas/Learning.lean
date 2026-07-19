module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Equiv.Set

/-!
# Learning limits — finite-domain No Free Lunch (Wolpert)

## Statement intent

- **Domain:** finite discrete search space `X` and finite cost codomain `Y`.
- **Objects:** non-adaptive black-box query schedules — injective samples of
  `m` distinct points in `X` (no revisits).
- **Performance:** any real-valued score `Φ` that depends only on the ordered
  cost sequence observed at the sample points (not on the point identities).
- **Averaging measure:** the uniform sum / average over **all** objective maps
  `f : X → Y`.
- **Conclusion:** every non-adaptive schedule of length `m` has the **same**
  aggregate performance; equivalently, the sum factors as
  `|Y|^{|X|-m} · ∑_c Φ(c)` and is independent of the schedule.

This is the classical **finite uniform-averaging** core associated with
Wolpert–Macready *No free lunch theorems for optimization* (1997): when
objectives are drawn uniformly from all maps on a finite domain, no
non-adaptive algorithm has an a priori advantage under a cost-sequence
performance measure.

## Explicit non-claims

- **Not** the Shalev-Shwartz–Ben-David PAC / sample-complexity NFL
  (Understanding ML Thm 5.1; AFP `No_Free_Lunch_ML`; landscape
  `LAND-NFL-001`). That result is an adversarial lower bound under a domain-size
  hypothesis `2m < |X|`, not a uniform average over all target functions.
- **Not** continuous free lunches or coevolutionary free lunches (survey
  BY-022 / Auger–Teytaud): those are settings where the finite NFL symmetry
  **fails**.
- **Not** a full paper-syntax port of Wolpert 1996 (supervised off-training-set
  error) or every lemma of Wolpert–Macready 1997 (adaptive trees, stochastic
  algorithms, time-varying objectives). Adaptive schedules and supervised
  off-training-set forms are left as related extensions.

No AI-system bridge is asserted; `ai_bridge_status` remains human review.
-/

open Classical
open Fintype Function

namespace AISafetyAtlas.Learning

/-! ## Definitions -/

/--
A non-adaptive black-box query schedule: `m` distinct points of the finite
search domain `X` (no revisits). This is the deterministic non-revisiting
special case of a Wolpert–Macready search algorithm that does not use observed
costs to choose the next query.
-/
public structure NonadaptiveSchedule (X : Type*) (m : ℕ) where
  /-- The ordered sample of query points. -/
  sample : Fin m → X
  /-- Distinctness / no-revisit condition. -/
  injective : Injective sample

/-- The embedding associated to a non-adaptive schedule. -/
@[expose] public noncomputable def NonadaptiveSchedule.embedding
    {X : Type*} {m : ℕ} (s : NonadaptiveSchedule X m) : Fin m ↪ X :=
  ⟨s.sample, s.injective⟩

/--
Cost-sequence performance measure: a real score of the ordered values of the
objective on the `m` queried points. (Wall-clock time and other
representation-dependent costs are outside this model.)
-/
public abbrev CostPerformance (m : ℕ) (Y : Type*) := (Fin m → Y) → ℝ

/--
Aggregate (uniform-sum) performance of a non-adaptive schedule: sum of the
cost-sequence score over **every** objective `f : X → Y`.

Dividing by `|Y|^{|X|}` recovers the uniform average; equality of sums is
equivalent to equality of averages.
-/
@[expose] public noncomputable def aggregatePerformance
    {X Y : Type*} [Fintype X] [Fintype Y] {m : ℕ}
    (Φ : CostPerformance m Y) (s : NonadaptiveSchedule X m) : ℝ :=
  ∑ f : X → Y, Φ (fun i => f (s.sample i))

/-! ## Core finite reindexing identity -/

/--
For any injective sample of `m` points, the sum of a cost-sequence score over
all objectives equals `|Y|^{|X|-m}` times the unrestricted sum of the score
over all cost sequences of length `m`.

This is the combinatorial engine of finite-domain NFL: once performance
depends only on observed costs, the sample locations drop out of the
uniform sum.
-/
public theorem sum_performance_eq_scaled_sum
    {X Y : Type*} [Fintype X] [Fintype Y]
    {m : ℕ} (σ : Fin m ↪ X) (Φ : CostPerformance m Y) :
    ∑ f : X → Y, Φ (fun i => f (σ i)) =
      (card Y : ℝ) ^ (card X - m) * ∑ c : Fin m → Y, Φ c := by
  classical
  -- Classical decidable equality on `X` for range/complement subtypes.
  letI : DecidableEq X := Classical.decEq X
  let R : Set X := Set.range (σ : Fin m → X)
  let eRange : Fin m ≃ R := σ.toEquivRange
  let eSum : R ⊕ (Rᶜ : Set X) ≃ X := Equiv.Set.sumCompl R
  let eFun : (X → Y) ≃ (R → Y) × ((Rᶜ : Set X) → Y) :=
    (eSum.symm.arrowCongr (Equiv.refl Y)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  let eSample : (R → Y) ≃ (Fin m → Y) :=
    Equiv.arrowCongr eRange.symm (Equiv.refl Y)
  let eAll : (X → Y) ≃ (Fin m → Y) × ((Rᶜ : Set X) → Y) :=
    eFun.trans (Equiv.prodCongr eSample (Equiv.refl _))
  have hcard_range : card R = m := by
    rw [card_congr eRange.symm, card_fin]
  have hcard_compl : card (Rᶜ : Set X) = card X - m := by
    have hsum : card (R ⊕ (Rᶜ : Set X)) = card X := card_congr eSum
    rw [card_sum] at hsum
    have : m + card (Rᶜ : Set X) = card X := by
      simpa [hcard_range] using hsum
    omega
  have hrestrict (f : X → Y) : (fun i => f (σ i)) = (eAll f).1 := by
    ext i
    dsimp [eAll, eFun, eSample]
    change f (eSum (Sum.inl (eRange i))) = f (σ i)
    have heq : eSum (Sum.inl (eRange i)) = σ i := by
      have hr : eRange i = ⟨σ i, Set.mem_range_self i⟩ := by
        simp [eRange, Embedding.toEquivRange]
      show eSum (Sum.inl (eRange i)) = σ i
      rw [hr]
      exact Equiv.Set.sumCompl_apply_inl (s := R) ⟨σ i, Set.mem_range_self i⟩
    rw [heq]
  calc
    ∑ f : X → Y, Φ (fun i => f (σ i))
        = ∑ f : X → Y, Φ (eAll f).1 := by
          refine Fintype.sum_congr _ _ fun f => ?_
          rw [hrestrict]
    _ = ∑ p : (Fin m → Y) × ((Rᶜ : Set X) → Y), Φ p.1 :=
          Fintype.sum_equiv eAll _ _ (fun _ => rfl)
    _ = ∑ c : Fin m → Y, ∑ _g : (Rᶜ : Set X) → Y, Φ c := by
          simpa using
            (Fintype.sum_prod_type
              (fun p : (Fin m → Y) × ((Rᶜ : Set X) → Y) => Φ p.1))
    _ = ∑ c : Fin m → Y, (card ((Rᶜ : Set X) → Y) : ℝ) * Φ c := by
          refine Fintype.sum_congr _ _ fun c => ?_
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_comm]
    _ = ∑ c : Fin m → Y, ((card Y : ℝ) ^ card (Rᶜ : Set X)) * Φ c := by
          refine Fintype.sum_congr _ _ fun c => ?_
          rw [card_fun, Nat.cast_pow]
    _ = ∑ c : Fin m → Y, ((card Y : ℝ) ^ (card X - m)) * Φ c := by
          simp [hcard_compl]
    _ = (card Y : ℝ) ^ (card X - m) * ∑ c : Fin m → Y, Φ c := by
          simp [Finset.mul_sum]

/--
Closed form for aggregate performance of any non-adaptive schedule: it equals
the schedule-independent quantity `|Y|^{|X|-m} · ∑_c Φ(c)`.
-/
public theorem aggregatePerformance_eq_scaled_sum
    {X Y : Type*} [Fintype X] [Fintype Y]
    {m : ℕ} (Φ : CostPerformance m Y) (s : NonadaptiveSchedule X m) :
    aggregatePerformance Φ s =
      (card Y : ℝ) ^ (card X - m) * ∑ c : Fin m → Y, Φ c := by
  simpa [aggregatePerformance, NonadaptiveSchedule.embedding] using
    sum_performance_eq_scaled_sum (σ := s.embedding) Φ

/-! ## No Free Lunch (finite, non-adaptive, uniform average) -/

/--
**No Free Lunch (finite-domain, non-adaptive optimization form).**

On a finite search domain `X` and finite cost codomain `Y`, for any cost-sequence
performance measure `Φ` and any two non-adaptive no-revisit schedules of the
same length, the uniform sum of performance over all objectives
`f : X → Y` is equal.

Hence no non-adaptive algorithm has an a priori advantage when objectives are
aggregated uniformly over the entire finite function space.

Survey row: **BY-021** (Wolpert–Macready 1997 optimization NFL) — formalized
here as the non-adaptive finite uniform-averaging core (`RELATED`, not full
paper adaptive/stochastic coverage). Distinct from BY-020 supervised Wolpert
1996, from SSBD PAC NFL (`LAND-NFL-001`), and from continuous free lunches
(BY-022).
-/
public theorem no_free_lunch
    {X Y : Type*} [Fintype X] [Fintype Y]
    {m : ℕ} (Φ : CostPerformance m Y)
    (s₁ s₂ : NonadaptiveSchedule X m) :
    aggregatePerformance Φ s₁ = aggregatePerformance Φ s₂ := by
  rw [aggregatePerformance_eq_scaled_sum Φ s₁,
    aggregatePerformance_eq_scaled_sum Φ s₂]

/--
Same identity for raw embeddings (schedules without the structure wrapper).
Useful for consumers that work directly with injections.
-/
public theorem no_free_lunch_embedding
    {X Y : Type*} [Fintype X] [Fintype Y]
    {m : ℕ} (Φ : CostPerformance m Y) (σ τ : Fin m ↪ X) :
    ∑ f : X → Y, Φ (fun i => f (σ i)) =
      ∑ f : X → Y, Φ (fun i => f (τ i)) := by
  rw [sum_performance_eq_scaled_sum σ Φ, sum_performance_eq_scaled_sum τ Φ]

end AISafetyAtlas.Learning
