module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

/-!
# Objective factorization

Ring and Orseau, *Delusion, Survival, and Intelligent Agents* (AGI 2011),
Section 2, describe their universal agents by shared environment dynamics plus
two objective components: a history utility and a horizon weighting.  Their
four agents differ only in those components.  This module isolates that
factorization at finite horizon.

## What is proved here

Two kinds of statement, kept apart deliberately.

* **Well-definedness.** `value_congr` and `optimal_decisions_congr` say that
  objectives with equal components induce equal values and equal optimal
  decisions.  These are record congruence: their proofs never unfold `value`.
  They are named accordingly and are *not* results about objectives.
* **Locality and scaling.** `value_eq_of_agree_on_window`,
  `value_scaleUtility`, and `optimal_decisions_eq_of_pos_scaleUtility` do unfold
  `value` and use the finite-horizon sum.  Locality is the truncation content:
  the value on a window depends only on the horizon weights and the utilities
  *inside* that window, so two objectives may disagree arbitrarily outside it.

The result does not formalize AIXI, Solomonoff induction, convergence, or the
paper's informal delusion-box arguments.  The paper states its results as
arguments rather than numbered theorems, so nothing here reproduces a numbered
source result. The source bounds utility in `[0,1]`; `Objective.utility` is
real-valued without a range invariant, a harmless generalization for these
algebraic locality and scaling lemmas but not an exact model match.
-/

namespace AISafetyAtlas.Wireheading

/-- The two objective components in Ring--Orseau's value equations. -/
public structure Objective (History : Type*) where
  utility : History → ℝ
  horizon : ℕ → ℕ → ℝ

namespace Objective

/-- Finite-horizon weighted utility of a trajectory. -/
@[expose] public def value {History : Type*} (O : Objective History)
    (start duration : ℕ) (trajectory : ℕ → History) : ℝ :=
  ∑ i ∈ Finset.range duration,
    O.horizon start (start + i) * O.utility (trajectory i)

/-!
### Well-definedness

These two are record congruence.  Their proofs conclude `O₁ = O₂` from
componentwise equality and never unfold `value`.  They are recorded under
honest names so that no reading of them as a result about objectives survives.
-/

/--
**Well-definedness of `value`.**  Objectives with equal components induce equal
values.

This is congruence for a two-field record, not a statement about the horizon
sum: the proof does not unfold `value`.
-/
public theorem value_congr {History : Type*}
    (O₁ O₂ : Objective History)
    (utility_eq : O₁.utility = O₂.utility)
    (horizon_eq : O₁.horizon = O₂.horizon)
    (start duration : ℕ) (trajectory : ℕ → History) :
    O₁.value start duration trajectory =
      O₂.value start duration trajectory := by
  have hO : O₁ = O₂ := by
    cases O₁
    cases O₂
    simp_all
  subst O₂
  rfl

/-!
### Locality of finite-horizon value

The substantive statements.  Each unfolds `value` and uses the sum over
`Finset.range duration`.
-/

/--
**Finite-horizon locality.**  Value on the window `[start, start + duration)`
depends only on the horizon weights and utilities *inside* that window.

The hypotheses are indexed by `i < duration`, so the two objectives may disagree
arbitrarily outside the window and still agree on it.  This is the truncation
content of the finite-horizon form, and unlike `value_congr` it is not
congruence: no equality of the objectives is available or derivable.
-/
public theorem value_eq_of_agree_on_window {History : Type*}
    (O₁ O₂ : Objective History) (start duration : ℕ)
    (trajectory : ℕ → History)
    (horizon_agree :
      ∀ i < duration, O₁.horizon start (start + i) = O₂.horizon start (start + i))
    (utility_agree :
      ∀ i < duration, O₁.utility (trajectory i) = O₂.utility (trajectory i)) :
    O₁.value start duration trajectory =
      O₂.value start duration trajectory := by
  unfold value
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hlt : i < duration := Finset.mem_range.mp hi
  rw [horizon_agree i hlt, utility_agree i hlt]

/-- Rescale an objective's utility, keeping its horizon weighting. -/
@[expose] public def scaleUtility {History : Type*}
    (c : ℝ) (O : Objective History) : Objective History where
  utility := fun h => c * O.utility h
  horizon := O.horizon

/--
**Value is homogeneous in utility.**  Scaling the utility component scales the
finite-horizon value by the same factor.

The proof distributes the scalar across the horizon sum, so it genuinely uses
the structure of `value`.
-/
public theorem value_scaleUtility {History : Type*}
    (c : ℝ) (O : Objective History) (start duration : ℕ)
    (trajectory : ℕ → History) :
    (scaleUtility c O).value start duration trajectory =
      c * O.value start duration trajectory := by
  unfold value scaleUtility
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  show O.horizon start (start + i) * (c * O.utility (trajectory i)) =
    c * (O.horizon start (start + i) * O.utility (trajectory i))
  rw [mul_left_comm]

/-- Value of a decision when fixed dynamics map it to a trajectory. -/
@[expose] public def decisionValue {History Decision : Type*}
    (O : Objective History)
    (dynamics : Decision → ℕ → History)
    (start duration : ℕ) (decision : Decision) : ℝ :=
  O.value start duration (dynamics decision)

/-- A decision is optimal within a specified feasible set. -/
@[expose] public def IsOptimal {History Decision : Type*}
    (O : Objective History)
    (dynamics : Decision → ℕ → History)
    (feasible : Set Decision)
    (start duration : ℕ) (decision : Decision) : Prop :=
  decision ∈ feasible ∧
    ∀ other ∈ feasible,
      O.decisionValue dynamics start duration other ≤
        O.decisionValue dynamics start duration decision

/--
**Well-definedness of `IsOptimal`.**  Objectives with equal components induce
the same optimal decisions.

Record congruence again; the proof does not unfold `value`.
-/
public theorem optimal_decisions_congr {History Decision : Type*}
    (O₁ O₂ : Objective History)
    (utility_eq : O₁.utility = O₂.utility)
    (horizon_eq : O₁.horizon = O₂.horizon)
    (dynamics : Decision → ℕ → History)
    (feasible : Set Decision) (start duration : ℕ) :
    {d | O₁.IsOptimal dynamics feasible start duration d} =
      {d | O₂.IsOptimal dynamics feasible start duration d} := by
  have hO : O₁ = O₂ := by
    cases O₁
    cases O₂
    simp_all
  subst O₂
  rfl

/--
**Positive utility rescaling preserves optimal decisions.**

Unlike `optimal_decisions_congr`, the two objectives here are genuinely
different whenever `c ≠ 1` and the utility is not identically zero. The proof
goes through `value_scaleUtility` and cancels the positive factor, so it depends
on the horizon sum rather than on record equality.
-/
public theorem optimal_decisions_eq_of_pos_scaleUtility
    {History Decision : Type*}
    (O : Objective History) {c : ℝ} (hc : 0 < c)
    (dynamics : Decision → ℕ → History)
    (feasible : Set Decision) (start duration : ℕ) :
    {d | (scaleUtility c O).IsOptimal dynamics feasible start duration d} =
      {d | O.IsOptimal dynamics feasible start duration d} := by
  have hval : ∀ d : Decision,
      (scaleUtility c O).decisionValue dynamics start duration d =
        c * O.decisionValue dynamics start duration d := by
    intro d
    exact value_scaleUtility c O start duration (dynamics d)
  ext d
  simp only [Set.mem_ofPred_eq, IsOptimal, hval]
  constructor
  · rintro ⟨hmem, hle⟩
    refine ⟨hmem, fun other hother => ?_⟩
    exact le_of_mul_le_mul_left (hle other hother) hc
  · rintro ⟨hmem, hle⟩
    refine ⟨hmem, fun other hother => ?_⟩
    exact mul_le_mul_of_nonneg_left (hle other hother) hc.le

end Objective
end AISafetyAtlas.Wireheading
