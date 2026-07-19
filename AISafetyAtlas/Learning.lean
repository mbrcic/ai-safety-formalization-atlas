module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Set

/-!
# Learning limits — finite-domain No Free Lunch (Wolpert)

Two classical **finite uniform-averaging** NFL cores live in this module:

1. **Optimization (BY-021 / Wolpert–Macready 1997)** —
   `no_free_lunch`: non-adaptive injective query schedules; performance a
   function of the ordered cost sequence; equal aggregate sum over all
   objectives `f : X → Y`.
2. **Supervised learning (BY-020 / Wolpert 1996)** —
   `no_free_lunch_supervised`: learners map training labels on a fixed domain
   `S ⊆ X` to full hypotheses; **off-training-set** 0-1 loss, averaged
   uniformly over all targets, is independent of the learner.

## Explicit non-claims

- **Not** the Shalev-Shwartz–Ben-David PAC / sample-complexity NFL
  (Understanding ML Thm 5.1; AFP `No_Free_Lunch_ML`; landscape
  `LAND-NFL-001`). That result is an adversarial lower bound under a domain-size
  hypothesis `2m < |X|`, not a uniform average over all target functions.
- **Not** continuous free lunches or coevolutionary free lunches (survey
  BY-022 / Auger–Teytaud): those are settings where the finite NFL symmetry
  **fails**.
- **Not** a full paper-syntax port of every lemma in Wolpert 1996 / 1997
  (stochastic algorithms, adaptive optimization trees, time-varying
  objectives, cross-validation meta-algorithms, etc.).

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
paper adaptive/stochastic coverage). The supervised OTS form is
`no_free_lunch_supervised` (BY-020). Distinct from SSBD PAC NFL
(`LAND-NFL-001`) and continuous free lunches (BY-022).
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

/-! ## Supervised learning NFL (Wolpert 1996, finite OTS form) -/

/--
A supervised learner for a fixed training domain `S`: given labels on `S`,
produce a hypothesis on all of `X`.
-/
public abbrev SupervisedLearner (X Y : Type*) (S : Set X) :=
  (S → Y) → (X → Y)

/-- Pointwise 0-1 loss of hypothesis `h` against target `f` at `x`. -/
@[expose] public noncomputable def pointLoss {X Y : Type*} [DecidableEq Y]
    (f h : X → Y) (x : X) : ℝ :=
  if h x = f x then 0 else 1

/--
Off-training-set total 0-1 loss: sum of point losses on `X \ S`
(un-normalized; averages are proportional to this sum).
-/
@[expose] public noncomputable def offTrainingLoss
    {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (S : Set X) (f h : X → Y) : ℝ :=
  ∑ x : X, if x ∈ S then (0 : ℝ) else pointLoss f h x

/-- Restrict a target to the training domain. -/
@[expose] public def restrictTo
    {X Y : Type*} (S : Set X) (f : X → Y) : S → Y :=
  fun s => f (s : X)

/-- Hypothesis produced by learner `A` on target `f`. -/
@[expose] public def predict
    {X Y : Type*} {S : Set X} (A : SupervisedLearner X Y S) (f : X → Y) :
    X → Y :=
  A (restrictTo S f)

/-- Aggregate off-training-set loss of a learner, summed over all targets. -/
@[expose] public noncomputable def aggregateOffTrainingLoss
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (S : Set X) (A : SupervisedLearner X Y S) : ℝ :=
  ∑ f : X → Y, offTrainingLoss S f (predict A f)

/-- ∑_y (0 if y = c else 1) = |Y| − 1. -/
private theorem sum_neq_indicator {Y : Type*} [Fintype Y] [DecidableEq Y]
    (c : Y) :
    (∑ y : Y, if y = c then (0 : ℝ) else 1) = (card Y : ℝ) - 1 := by
  calc
    (∑ y : Y, if y = c then (0 : ℝ) else 1)
        = ∑ y : Y, ((1 : ℝ) - if y = c then 1 else 0) := by
          refine Fintype.sum_congr _ _ fun y => ?_
          split_ifs <;> norm_num
    _ = (∑ y : Y, (1 : ℝ)) - ∑ y : Y, if y = c then (1 : ℝ) else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = (card Y : ℝ) - 1 := by
          simp [Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_eq']

private theorem card_ne_eq {X : Type*} [Fintype X] [DecidableEq X] (x : X) :
    card { j : X // j ≠ x } = card X - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun j : X => j = x)]
  simp [Fintype.card_unique]

/--
For any learner and any off-training point `x ∉ S`, the uniform sum of
pointwise 0-1 loss equals `(|Y|−1) · |Y|^{|X|−1}` — independent of the learner.

Combinatorial content of supervised NFL at a single test point: given training
labels on `S`, the target value at `x` is free under the uniform average.
-/
public theorem sum_pointLoss_off_training
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (S : Set X) (A : SupervisedLearner X Y S) (x : X) (hx : x ∉ S) :
    ∑ f : X → Y, pointLoss f (predict A f) x =
      ((card Y : ℝ) - 1) * (card Y : ℝ) ^ (card X - 1) := by
  classical
  let e : (X → Y) ≃ Y × ({ j : X // j ≠ x } → Y) := Equiv.funSplitAt x Y
  let pred : ({ j : X // j ≠ x } → Y) → Y := fun g =>
    A (fun s : S => g ⟨(s : X), fun h => hx (by simpa [h] using s.property)⟩) x
  have hpoint (f : X → Y) :
      pointLoss f (predict A f) x =
        (if pred (e f).2 = (e f).1 then (0 : ℝ) else 1) := by
    dsimp [pointLoss, predict, restrictTo, pred, e]
    -- `pred (e f).2` unfolds to `A (fun s => f s) x` via `funSplitAt`.
    simp [Equiv.funSplitAt_apply]
    rfl
  calc
    ∑ f : X → Y, pointLoss f (predict A f) x
        = ∑ f : X → Y, (if pred (e f).2 = (e f).1 then (0 : ℝ) else 1) := by
          refine Fintype.sum_congr _ _ fun f => hpoint f
    _ = ∑ p : Y × ({ j : X // j ≠ x } → Y),
          (if pred p.2 = p.1 then (0 : ℝ) else 1) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ g : { j : X // j ≠ x } → Y, ∑ y : Y,
          (if pred g = y then (0 : ℝ) else 1) := by
        simpa using
          (Fintype.sum_prod_type_right fun p : Y × ({ j : X // j ≠ x } → Y) =>
            (if pred p.2 = p.1 then (0 : ℝ) else 1))
    _ = ∑ g : { j : X // j ≠ x } → Y, ∑ y : Y,
          (if y = pred g then (0 : ℝ) else 1) := by
        refine Fintype.sum_congr _ _ fun g => ?_
        refine Fintype.sum_congr _ _ fun y => ?_
        simp [eq_comm]
    _ = ∑ g : { j : X // j ≠ x } → Y, ((card Y : ℝ) - 1) := by
        refine Fintype.sum_congr _ _ fun g => sum_neq_indicator (pred g)
    _ = ((card Y : ℝ) - 1) * (card ({ j : X // j ≠ x } → Y) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm, Finset.card_univ]
    _ = ((card Y : ℝ) - 1) * (card Y : ℝ) ^ (card X - 1) := by
        rw [card_fun, card_ne_eq x, Nat.cast_pow]

/--
Closed form for aggregate OTS loss of any supervised learner:
`|Sᶜ| · (|Y|−1) · |Y|^{|X|−1}`.
-/
public theorem aggregateOffTrainingLoss_eq
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (S : Set X) (A : SupervisedLearner X Y S) :
    aggregateOffTrainingLoss S A =
      (card { x : X // x ∉ S } : ℝ) *
        (((card Y : ℝ) - 1) * (card Y : ℝ) ^ (card X - 1)) := by
  classical
  let C : ℝ := ((card Y : ℝ) - 1) * (card Y : ℝ) ^ (card X - 1)
  calc
    aggregateOffTrainingLoss S A
        = ∑ f : X → Y, ∑ x : X,
            if x ∈ S then (0 : ℝ) else pointLoss f (predict A f) x := by
          simp [aggregateOffTrainingLoss, offTrainingLoss]
    _ = ∑ x : X, ∑ f : X → Y,
            if x ∈ S then (0 : ℝ) else pointLoss f (predict A f) x := by
          rw [Finset.sum_comm]
    _ = ∑ x : X,
          (if x ∈ S then (0 : ℝ)
            else ∑ f : X → Y, pointLoss f (predict A f) x) := by
          refine Fintype.sum_congr _ _ fun x => ?_
          split_ifs with hx
          · simp
          · simp
    _ = ∑ x : X, (if x ∈ S then (0 : ℝ) else C) := by
          refine Fintype.sum_congr _ _ fun x => ?_
          split_ifs with hx
          · rfl
          · exact sum_pointLoss_off_training S A x hx
    _ = ∑ x ∈ Finset.univ.filter (fun x : X => x ∉ S), C := by
          rw [Finset.sum_filter]
          refine Fintype.sum_congr _ _ fun x => ?_
          by_cases hx : x ∈ S <;> simp [hx]
    _ = ((Finset.univ.filter (fun x : X => x ∉ S)).card : ℝ) * C := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (card { x : X // x ∉ S } : ℝ) * C := by
          have : (Finset.univ.filter (fun x : X => x ∉ S)).card =
              card { x : X // x ∉ S } := by
            rw [Fintype.card_subtype]
          rw [this]

/--
**No Free Lunch (finite-domain, supervised off-training-set form).**

On finite `X`, `Y`, for any fixed training domain `S ⊆ X` and any two
supervised learners, the uniform sum of off-training-set 0-1 loss over all
target functions is equal.

Hence no learner has an a priori OTS advantage when targets are aggregated
uniformly over the entire finite function space.

Survey row: **BY-020** (Wolpert 1996 supervised NFL) — finite OTS core
(`RELATED`). Distinct from BY-021 optimization `no_free_lunch`, from SSBD PAC
NFL (`LAND-NFL-001`), and from continuous free lunches (BY-022).
-/
public theorem no_free_lunch_supervised
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (S : Set X) (A B : SupervisedLearner X Y S) :
    aggregateOffTrainingLoss S A = aggregateOffTrainingLoss S B := by
  rw [aggregateOffTrainingLoss_eq S A, aggregateOffTrainingLoss_eq S B]

end AISafetyAtlas.Learning
