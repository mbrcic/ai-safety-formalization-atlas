module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Set
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Learning limits — finite-domain No Free Lunch (Wolpert)

Two classical **finite uniform-averaging** NFL cores live in this module:

1. **Optimization (BY-021 / Wolpert–Macready 1997)** —
   `no_free_lunch`: non-adaptive injective query schedules; performance a
   function of the ordered cost sequence; equal aggregate sum over all
   objectives `f : X → Y`.
2. **Supervised learning (BY-020 / Wolpert 1996 — *The Lack of A Priori
   Distinctions Between Learning Algorithms*, Neural Comput. 8(7):1341–1390; the
   survey and registry `survey-ref-018` instead cite the companion *Existence*
   paper, pp. 1391–1420 — see the provenance doc)** —
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

/-! ## Supervised NFL — full distribution and homogeneous loss (Wolpert 1996)

The mean-only form above (`no_free_lunch_supervised`) is the first-moment core.
Wolpert's actual claim is stronger: for a **homogeneous** loss the entire
off-training-set error *distribution* — hence every moment — is learner-
independent, and the loss need not be 0-1. Both strengthenings are captured here
by a single functional identity, proven by a per-point relabeling bijection on the
target space. Still finite / uniform-averaging; stochastic learners and non-uniform
priors remain out of scope (open collaboration work). -/

/--
A loss `ℓ prediction truth` is **homogeneous** (Wolpert's condition): for any two
predictions there is a relabeling of the truth values matching their loss
profiles. Given at least one off-training point this is **exactly** the condition
under which the off-training-set loss *vector* distribution — every functional `Ψ`
of the loss vector — is learner-independent: sufficiency is
`lossConfig_sum_learner_indep`, necessity is `homogeneous_of_learner_indep`, and
the two are packaged as the tight `iff` `homogeneous_iff_learner_indep`. The
scalar total-loss distribution (`ots_error_distribution_learner_indep`) is a
weaker consequence; necessity from scalar independence alone is *not* claimed.
0-1 loss qualifies (`homogeneous_zeroOne`).
-/
public def HomogeneousLoss {Y : Type*} (ℓ : Y → Y → ℝ) : Prop :=
  ∀ a₁ a₂ : Y, ∃ π : Y ≃ Y, ∀ y, ℓ a₂ y = ℓ a₁ (π y)

/-- 0-1 loss is homogeneous: relabel truths by the transposition of the two
predictions. -/
public theorem homogeneous_zeroOne {Y : Type*} [DecidableEq Y] :
    HomogeneousLoss (fun a y : Y => if a = y then (0 : ℝ) else 1) := by
  intro a₁ a₂
  refine ⟨Equiv.swap a₁ a₂, fun y => ?_⟩
  by_cases hy : y = a₂
  · subst hy; simp [Equiv.swap_apply_right]
  · by_cases hy2 : y = a₁
    · subst hy2; simp [Equiv.swap_apply_left, eq_comm]
    · rw [Equiv.swap_apply_of_ne_of_ne hy2 hy]
      simp [Ne.symm hy, Ne.symm hy2]

/--
Off-training-set loss configuration of learner `A` on target `f` under loss `ℓ`:
the vector of losses `ℓ (predict A f x) (f x)` at each off-training point
`x ∉ S`. Its pushforward under the uniform target measure is the object Wolpert's
supervised NFL fixes a priori.
-/
@[expose] public noncomputable def lossConfig
    {X Y : Type*} (ℓ : Y → Y → ℝ) (S : Set X)
    (A : SupervisedLearner X Y S) (f : X → Y) : (Sᶜ : Set X) → ℝ :=
  fun x => ℓ (predict A f (x : X)) (f (x : X))

/--
**Supervised NFL, distributional / homogeneous-loss form (Wolpert 1996).**

For a homogeneous loss `ℓ` and *any* functional `Ψ` of the off-training-set loss
vector, the uniform sum over all target functions is learner-independent.

Taking `Ψ` a sum recovers the mean (`no_free_lunch_supervised`); an indicator of a
value recovers the full generalization-error distribution
(`ots_error_distribution_learner_indep`); a power recovers every moment. Proven by
a per-point relabeling bijection on the target space, fiber-wise over the training
restriction. Survey row **BY-020** (`RELATED`), strengthening the mean core. It reproduces
Wolpert 1996's deterministic finite-case claim exactly (the OTS error
*distribution*, not just its mean, is a priori learner-independent for homogeneous
loss). The artifact is still classified `RELATED`, not `EXACT`: that classification
is taken against the *full paper*, whose stochastic learners, label noise, and
non-uniform target priors `P(f)` remain out of scope.
-/
public theorem lossConfig_sum_learner_indep
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {ℓ : Y → Y → ℝ} (hℓ : HomogeneousLoss ℓ) (S : Set X)
    (A B : SupervisedLearner X Y S)
    (Ψ : ((Sᶜ : Set X) → ℝ) → ℝ) :
    ∑ f : X → Y, Ψ (lossConfig ℓ S A f) = ∑ f : X → Y, Ψ (lossConfig ℓ S B f) := by
  classical
  let eSum : S ⊕ (Sᶜ : Set X) ≃ X := Equiv.Set.sumCompl S
  let eFun : (X → Y) ≃ (S → Y) × ((Sᶜ : Set X) → Y) :=
    (eSum.symm.arrowCongr (Equiv.refl Y)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)
  -- Group the sum over targets by the training restriction `d` and free OTS part `g`.
  have hred : ∀ C : SupervisedLearner X Y S,
      ∑ f : X → Y, Ψ (lossConfig ℓ S C f)
        = ∑ d : S → Y, ∑ g : (Sᶜ : Set X) → Y,
            Ψ (fun x => ℓ (C d (x : X)) (g x)) := by
    intro C
    rw [← Fintype.sum_prod_type
      (fun p : (S → Y) × ((Sᶜ : Set X) → Y) =>
        Ψ (fun x => ℓ (C p.1 (x : X)) (p.2 x)))]
    refine Fintype.sum_equiv eFun _ _ (fun f => ?_)
    have h1 : (eFun f).1 = restrictTo S f := by
      funext s
      simp [eFun, eSum, restrictTo, Equiv.sumArrowEquivProdArrow_apply_fst,
        Equiv.arrowCongr_apply, Equiv.Set.sumCompl_apply_inl]
    have h2 : ∀ x : (Sᶜ : Set X), (eFun f).2 x = f (x : X) := by
      intro x
      simp [eFun, eSum, Equiv.sumArrowEquivProdArrow_apply_snd,
        Equiv.arrowCongr_apply, Equiv.Set.sumCompl_apply_inr]
    have h3 : (fun x : (Sᶜ : Set X) => ℓ (C (eFun f).1 (x : X)) ((eFun f).2 x))
        = lossConfig ℓ S C f := by
      funext x
      rw [h1, h2 x]
      rfl
    rw [h3]
  rw [hred A, hred B]
  refine Fintype.sum_congr _ _ (fun d => ?_)
  -- Fixed training block: relabel the free OTS values to turn `A`'s losses into `B`'s.
  refine Fintype.sum_equiv
    (Equiv.piCongrRight (fun x : (Sᶜ : Set X) =>
      (hℓ (B d (x : X)) (A d (x : X))).choose)) _ _ (fun g => ?_)
  have : (fun x : (Sᶜ : Set X) => ℓ (A d (x : X)) (g x))
      = fun x : (Sᶜ : Set X) =>
          ℓ (B d (x : X)) ((hℓ (B d (x : X)) (A d (x : X))).choose (g x)) := by
    funext x
    exact (hℓ (B d (x : X)) (A d (x : X))).choose_spec (g x)
  rw [this]
  rfl

/--
**Off-training-set error distribution is learner-independent (Wolpert 1996).**

For a homogeneous loss, the number of target functions on which a learner attains
any given total off-training-set loss `v` is the same for every learner. The full
generalization-error distribution — not merely its mean — is fixed a priori.
-/
public theorem ots_error_distribution_learner_indep
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {ℓ : Y → Y → ℝ} (hℓ : HomogeneousLoss ℓ) (S : Set X)
    (A B : SupervisedLearner X Y S) (v : ℝ) :
    (∑ f : X → Y,
        if (∑ x : (Sᶜ : Set X), ℓ (predict A f (x : X)) (f (x : X))) = v
          then (1 : ℝ) else 0)
      = ∑ f : X → Y,
        if (∑ x : (Sᶜ : Set X), ℓ (predict B f (x : X)) (f (x : X))) = v
          then (1 : ℝ) else 0 := by
  simpa [lossConfig] using
    lossConfig_sum_learner_indep hℓ S A B
      (fun w => if (∑ x : (Sᶜ : Set X), w x) = v then (1 : ℝ) else 0)

/-! ## Adaptive optimization NFL (Wolpert–Macready 1997, deterministic no-revisit)

The optimization core above (`no_free_lunch`) restricts to **non-adaptive**
schedules — a fixed sequence of points, ignoring observed costs. Wolpert–Macready's
actual content is that even a genuinely **adaptive** deterministic algorithm — one
that chooses each next query from the costs it has already seen — has no a priori
advantage once objectives are averaged uniformly. That is proven here, still
finite / combinatorial. Stochastic algorithms and time-varying objectives remain
out of scope. -/

/--
A deterministic **adaptive** query rule: given the `k` costs observed so far,
choose the next query point. The point genuinely depends on the observed cost
history, not on a fixed schedule.
-/
public abbrev AdaptiveRule (X Y : Type*) (m : ℕ) : Type _ :=
  ∀ k : Fin m, (Fin k → Y) → X

/--
The point rule `r` picks at step `k` when the observed cost sequence is `c`.
Depends on `c` only through its first `k` entries — the causal unrolling of the
rule.
-/
@[expose] public def ruleVisit {X Y : Type*} {m : ℕ}
    (r : AdaptiveRule X Y m) (c : Fin m → Y) (k : Fin m) : X :=
  r k (fun i : Fin k => c (i.castLE k.isLt.le))

/--
Cost sequence observed by rule `r` on objective `f`, built prefix by prefix: the
cost at step `n` is `f` of the point the rule picks from the earlier costs.
-/
@[expose] public noncomputable def obsPrefix {X Y : Type*} {m : ℕ}
    (r : AdaptiveRule X Y m) (f : X → Y) : (n : ℕ) → n ≤ m → (Fin n → Y)
  | 0, _ => fun i => i.elim0
  | n + 1, h =>
    Fin.snoc (obsPrefix r f n (Nat.le_of_succ_le h))
      (f (r ⟨n, h⟩ (obsPrefix r f n (Nat.le_of_succ_le h))))

/-- The full cost sequence rule `r` observes on objective `f`. -/
@[expose] public noncomputable def observed {X Y : Type*} {m : ℕ}
    (r : AdaptiveRule X Y m) (f : X → Y) : Fin m → Y :=
  obsPrefix r f m le_rfl

/--
If objective `f` reproduces cost sequence `c` along the trajectory `r` unrolls
from `c`, then `c` is exactly what `r` observes on `f`. (The "backward" half of the
fiber characterization; the forward half comes free by counting.)
-/
public theorem observed_of_consistent {X Y : Type*} {m : ℕ}
    (r : AdaptiveRule X Y m) (f : X → Y) (c : Fin m → Y)
    (hc : ∀ k, f (ruleVisit r c k) = c k) : observed r f = c := by
  have hpre : ∀ n (h : n ≤ m),
      obsPrefix r f n h = fun i : Fin n => c (i.castLE h) := by
    intro n
    induction n with
    | zero => intro h; funext i; exact i.elim0
    | succ n ih =>
      intro h
      have hn := ih (Nat.le_of_succ_le h)
      funext j
      have hstep : obsPrefix r f (n + 1) h
          = Fin.snoc (obsPrefix r f n (Nat.le_of_succ_le h))
              (f (r ⟨n, h⟩ (obsPrefix r f n (Nat.le_of_succ_le h)))) := rfl
      rw [hstep, hn]
      refine Fin.lastCases ?_ ?_ j
      · have hru : ruleVisit r c ⟨n, h⟩
            = r ⟨n, h⟩ (fun i : Fin n => c (i.castLE (Nat.le_of_succ_le h))) := rfl
        rw [Fin.snoc_last, ← hru, hc ⟨n, h⟩]
        congr 1
      · intro i
        rw [Fin.snoc_castSucc]
        congr 1
  have hmpre := hpre m le_rfl
  rw [observed, hmpre]
  simp

/--
For a no-revisit rule, the number of objectives that observe a *fixed* cost
sequence `c` is `|Y|^{|X|−m}` — independent of the rule. (Uses the non-adaptive
reindexing identity on the injective trajectory of `c`.)
-/
public theorem adaptive_constraint_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    {m : ℕ} (r : AdaptiveRule X Y m) (c : Fin m → Y)
    (hinj : Injective (ruleVisit r c)) :
    (∑ f : X → Y, if (fun i => f (ruleVisit r c i)) = c then (1 : ℝ) else 0)
      = (card Y : ℝ) ^ (card X - m) := by
  have hkey := sum_performance_eq_scaled_sum (σ := ⟨ruleVisit r c, hinj⟩)
    (Φ := fun cs : Fin m → Y => if cs = c then (1 : ℝ) else 0)
  simp only [Function.Embedding.coeFn_mk, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_one] at hkey
  exact hkey

/--
**No Free Lunch (finite-domain, adaptive optimization form; Wolpert–Macready 1997).**

For a finite search domain `X` and finite cost codomain `Y`, any two deterministic
adaptive no-revisit rules of length `m ≤ |X|` produce the same uniform sum, over
all objectives `f : X → Y`, of any functional `Ψ` of the observed cost sequence.
So no adaptive algorithm has an a priori advantage under uniform averaging — the
genuinely adaptive strengthening of `no_free_lunch`.

Survey row **BY-021** (`RELATED`). It reproduces Wolpert–Macready Theorem 1 for
the deterministic finite case exactly (taking `Ψ` an indicator of a cost sequence
gives that the number of objectives yielding it is rule-independent, the full
histogram). The artifact is still classified `RELATED`, not `EXACT`: that
classification is taken against the *full paper*, whose stochastic algorithms and
time-varying objectives remain out of scope.
-/
public theorem no_free_lunch_adaptive
    {X Y : Type*} [Fintype X] [Fintype Y]
    {m : ℕ} (hm : m ≤ card X)
    (r₁ r₂ : AdaptiveRule X Y m)
    (h₁ : ∀ c, Injective (ruleVisit r₁ c))
    (h₂ : ∀ c, Injective (ruleVisit r₂ c))
    (Ψ : (Fin m → Y) → ℝ) :
    ∑ f : X → Y, Ψ (observed r₁ f) = ∑ f : X → Y, Ψ (observed r₂ f) := by
  suffices h : ∀ (r : AdaptiveRule X Y m), (∀ c, Injective (ruleVisit r c)) →
      ∑ f : X → Y, Ψ (observed r f)
        = (card Y : ℝ) ^ (card X - m) * ∑ c : Fin m → Y, Ψ c by
    rw [h r₁ h₁, h r₂ h₂]
  intro r hr
  set K : ℝ := (card Y : ℝ) ^ (card X - m) with hK
  -- Each fiber `{f : observed r f = c}` has real cardinality `K`.
  have hfiber : ∀ c : Fin m → Y,
      (∑ f : X → Y, if observed r f = c then (1 : ℝ) else 0) = K := by
    -- Lower bound `K ≤ fiber c` from the constraint set (backward direction).
    have hle : ∀ c : Fin m → Y,
        K ≤ ∑ f : X → Y, if observed r f = c then (1 : ℝ) else 0 := by
      intro c
      rw [hK, ← adaptive_constraint_card r c (hr c)]
      refine Finset.sum_le_sum (fun f _ => ?_)
      by_cases hcons : (fun i => f (ruleVisit r c i)) = c
      · have hobs : observed r f = c :=
          observed_of_consistent r f c (fun k => congrFun hcons k)
        simp [hcons, hobs]
      · simp only [hcons, if_false]
        split_ifs <;> norm_num
    -- Totals agree: both sum to `|Y|^{|X|}`.
    have htot : (∑ c : Fin m → Y, ∑ f : X → Y,
        if observed r f = c then (1 : ℝ) else 0)
          = ∑ _c : Fin m → Y, K := by
      rw [Finset.sum_comm]
      have hone : ∀ f : X → Y,
          (∑ c : Fin m → Y, if observed r f = c then (1 : ℝ) else 0) = 1 := by
        intro f; simp
      rw [Finset.sum_congr rfl (fun f _ => hone f), Finset.sum_const, Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul, mul_one, hK]
      rw [card_fun, card_fun, card_fin]
      push_cast
      rw [← pow_add, Nat.add_sub_cancel' hm]
    -- `K ≤ fiber c` pointwise with equal totals forces equality.
    intro c
    have hpt := (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset (Fin m → Y)))
      (f := fun _ => K) (g := fun c => ∑ f : X → Y,
        if observed r f = c then (1 : ℝ) else 0)
      (fun c _ => hle c)).1 htot.symm
    exact (hpt c (Finset.mem_univ c)).symm
  -- Assemble: expand `Ψ (observed r f)` over the fibers.
  calc ∑ f : X → Y, Ψ (observed r f)
      = ∑ f : X → Y, ∑ c : Fin m → Y, (if observed r f = c then Ψ c else 0) := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        simp
    _ = ∑ c : Fin m → Y, ∑ f : X → Y, (if observed r f = c then Ψ c else 0) :=
        Finset.sum_comm
    _ = ∑ c : Fin m → Y, Ψ c * K := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [← hfiber c, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        by_cases hf : observed r f = c <;> simp [hf]
    _ = K * ∑ c : Fin m → Y, Ψ c := by
        rw [← Finset.sum_mul, mul_comm]

/-! ## Supervised NFL — necessity of homogeneity (converse; iff characterization)

`lossConfig_sum_learner_indep` shows homogeneity is **sufficient** for every
functional of the off-training-set loss vector to be learner-independent. The
converse holds too, given at least one off-training point: if every functional of
the OTS loss vector has the same uniform-over-targets sum for all learners, the
loss must be homogeneous. Together this is a tight `iff` at the loss-*vector*
level; necessity from the weaker scalar total-loss distribution alone is not
claimed.

This is a NEW_PROOF (folklore-tight, not stated as an iff by Wolpert): the loss-axis
analog of the Schumacher–Vose–Whitley / Igel–Toussaint "closed under permutation"
necessary-and-sufficient characterization, which is on the prior axis. -/

/--
Reduction: summing a value-indicator of the loss at a fixed test point `x` over all
targets factors as `|Y|^{|X|-1}` times the size of the loss fiber at that value.
-/
private theorem sum_ite_pointval_eq
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (x : X) (a : Y) (ℓ : Y → Y → ℝ) (v : ℝ) :
    (∑ f : X → Y, if ℓ a (f x) = v then (1 : ℝ) else 0)
      = (card Y : ℝ) ^ (card X - 1) * (Nat.card {y : Y // ℓ a y = v} : ℝ) := by
  classical
  let e : (X → Y) ≃ Y × ({ j : X // j ≠ x } → Y) := Equiv.funSplitAt x Y
  calc
    (∑ f : X → Y, if ℓ a (f x) = v then (1 : ℝ) else 0)
        = ∑ p : Y × ({ j : X // j ≠ x } → Y), if ℓ a p.1 = v then (1 : ℝ) else 0 := by
          refine Fintype.sum_equiv e _ _ (fun f => ?_)
          simp [e, Equiv.funSplitAt_apply]
    _ = ∑ _y : Y, ∑ _r : ({ j : X // j ≠ x } → Y), (if ℓ a _y = v then (1 : ℝ) else 0) :=
          Fintype.sum_prod_type _
    _ = ∑ y : Y, (card ({ j : X // j ≠ x } → Y) : ℝ) * (if ℓ a y = v then (1 : ℝ) else 0) := by
          refine Fintype.sum_congr _ _ fun y => ?_
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_comm]
    _ = (card ({ j : X // j ≠ x } → Y) : ℝ) * ∑ y : Y, if ℓ a y = v then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]
    _ = (card Y : ℝ) ^ (card X - 1) * (Nat.card {y : Y // ℓ a y = v} : ℝ) := by
          rw [card_fun, card_ne_eq x, Nat.cast_pow]
          congr 1
          rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/--
Equal loss-value fibers ⇒ a permutation of the truth space carrying one prediction's
loss row onto the other's. The combinatorial heart of the necessity direction.
-/
private theorem exists_perm_comp_of_fiber_card_eq
    {Y Z : Type*} [Finite Y] (g₁ g₂ : Y → Z)
    (h : ∀ v : Z, Nat.card {y : Y // g₂ y = v} = Nat.card {y : Y // g₁ y = v}) :
    ∃ π : Y ≃ Y, ∀ y, g₂ y = g₁ (π y) := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  have hcardEq : ∀ v : Z,
      Fintype.card {y : Y // g₂ y = v} = Fintype.card {y : Y // g₁ y = v} := by
    intro v
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact h v
  let e₁ : (Σ v : Z, {y : Y // g₁ y = v}) ≃ Y := Equiv.sigmaFiberEquiv g₁
  let e₂ : (Σ v : Z, {y : Y // g₂ y = v}) ≃ Y := Equiv.sigmaFiberEquiv g₂
  let F : ∀ v : Z, {y : Y // g₂ y = v} ≃ {y : Y // g₁ y = v} :=
    fun v => Fintype.equivOfCardEq (hcardEq v)
  let ϕ : (Σ v : Z, {y : Y // g₂ y = v}) ≃ (Σ v : Z, {y : Y // g₁ y = v}) :=
    Equiv.sigmaCongrRight F
  refine ⟨e₂.symm.trans (ϕ.trans e₁), fun y => ?_⟩
  have h2 : e₂.symm y = ⟨g₂ y, ⟨y, rfl⟩⟩ := (Equiv.symm_apply_eq e₂).2 rfl
  have hpi : (e₂.symm.trans (ϕ.trans e₁)) y = ↑(F (g₂ y) ⟨y, rfl⟩) := by
    rw [Equiv.trans_apply, Equiv.trans_apply, h2]
    rfl
  rw [hpi]
  exact (F (g₂ y) ⟨y, rfl⟩).2.symm

/--
**Necessity of homogeneity for learner-independence (Wolpert, converse direction).**

If, for a fixed training domain `S` with at least one off-training point `x ∉ S`,
every functional `Ψ` of the off-training-set loss vector has the same
uniform-over-targets sum for all learners, then the loss `ℓ` is homogeneous.

Proof: instantiate learner-independence with two constant learners and a
value-indicator functional at `x`; the reduction `sum_ite_pointval_eq` turns the
hypothesis into equal loss-value fibers for every pair of predictions, and
`exists_perm_comp_of_fiber_card_eq` produces the relabeling `π`.
-/
public theorem homogeneous_of_learner_indep
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {ℓ : Y → Y → ℝ} (S : Set X) (x : X) (hx : x ∉ S)
    (hLI : ∀ (A B : SupervisedLearner X Y S) (Ψ : ((Sᶜ : Set X) → ℝ) → ℝ),
      ∑ f : X → Y, Ψ (lossConfig ℓ S A f) = ∑ f : X → Y, Ψ (lossConfig ℓ S B f)) :
    HomogeneousLoss ℓ := by
  classical
  intro a₁ a₂
  have hxc : x ∈ (Sᶜ : Set X) := hx
  have key : ∀ v : ℝ,
      (∑ f : X → Y, if ℓ a₁ (f x) = v then (1 : ℝ) else 0)
        = ∑ f : X → Y, if ℓ a₂ (f x) = v then (1 : ℝ) else 0 := by
    intro v
    have hred : ∀ a : Y,
        (∑ f : X → Y, (fun w : (Sᶜ : Set X) → ℝ => if w ⟨x, hxc⟩ = v then (1 : ℝ) else 0)
            (lossConfig ℓ S (fun _ => fun _ => a) f))
          = ∑ f : X → Y, if ℓ a (f x) = v then (1 : ℝ) else 0 := by
      intro a
      refine Fintype.sum_congr _ _ (fun f => ?_)
      show (if (lossConfig ℓ S (fun _ => fun _ => a) f) ⟨x, hxc⟩ = v then (1 : ℝ) else 0) = _
      have hpt : (lossConfig ℓ S (fun _ => fun _ => a) f) ⟨x, hxc⟩ = ℓ a (f x) := rfl
      rw [hpt]
    have h := hLI (fun _ => fun _ => a₁) (fun _ => fun _ => a₂)
      (fun w => if w ⟨x, hxc⟩ = v then (1 : ℝ) else 0)
    rw [hred a₁, hred a₂] at h
    exact h
  have hcard : ∀ v : ℝ,
      Nat.card {y : Y // ℓ a₂ y = v} = Nat.card {y : Y // ℓ a₁ y = v} := by
    intro v
    have hk := key v
    rw [sum_ite_pointval_eq x a₁ ℓ v, sum_ite_pointval_eq x a₂ ℓ v] at hk
    have hpos : 0 < card Y := Fintype.card_pos_iff.2 ⟨a₁⟩
    have hbase : (0 : ℝ) < (card Y : ℝ) := by exact_mod_cast hpos
    have hYpos : (0 : ℝ) < (card Y : ℝ) ^ (card X - 1) := pow_pos hbase _
    have hc := mul_left_cancel₀ (ne_of_gt hYpos) hk
    exact_mod_cast hc.symm
  obtain ⟨π, hπ⟩ := exists_perm_comp_of_fiber_card_eq (ℓ a₁) (ℓ a₂) hcard
  exact ⟨π, hπ⟩

/--
**Homogeneous loss ⟺ learner-independent OTS loss-vector distribution (iff).**

For a fixed training domain `S` with at least one off-training point `x ∉ S`, the
loss `ℓ` is homogeneous **iff** every functional of the off-training-set loss vector
has the same uniform-over-targets sum for all learners. Forward is
`lossConfig_sum_learner_indep`; the converse is `homogeneous_of_learner_indep`.
-/
public theorem homogeneous_iff_learner_indep
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ℓ : Y → Y → ℝ) (S : Set X) (x : X) (hx : x ∉ S) :
    HomogeneousLoss ℓ ↔
      ∀ (A B : SupervisedLearner X Y S) (Ψ : ((Sᶜ : Set X) → ℝ) → ℝ),
        ∑ f : X → Y, Ψ (lossConfig ℓ S A f) = ∑ f : X → Y, Ψ (lossConfig ℓ S B f) := by
  constructor
  · intro hℓ A B Ψ
    exact lossConfig_sum_learner_indep hℓ S A B Ψ
  · intro hLI
    exact homogeneous_of_learner_indep S x hx hLI

end AISafetyAtlas.Learning
