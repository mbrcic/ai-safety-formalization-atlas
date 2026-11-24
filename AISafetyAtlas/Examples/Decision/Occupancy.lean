module

public import AISafetyAtlas.Decision.Occupancy
public import AISafetyAtlas.Decision.OccupancyHistory
public import AISafetyAtlas.Examples.Decision.DiscountedValue

/-!
# Visit counts on a one-state environment

The smallest environment in which print's picture is visible: one state, two
actions, so a policy *is* a point of the interval and its visit counts are that
point scaled by the discounted horizon. Skalse et al.'s standing assumptions
hold — `S` and `A` finite, `|A| > 1`, every state reachable.

`stateOcc_unit` is the whole model: on one state the discounted occupancy is
`(1 - γ)⁻¹` whatever the policy and whatever the environment does, because the
environment cannot do anything. It follows from `sum_stateOcc_eq` rather than
from an induction on `stateDist`, which is the point of proving the total mass
in the library.
-/

namespace AISafetyAtlas.Examples.Decision

open AISafetyAtlas.Decision

open scoped NNReal

/-- The one-state environment: nothing an action does changes where you are. -/
@[expose] public noncomputable def oneState : MDP Unit Bool where
  transition := fun _ _ => PMF.pure ()

/-- And the only initial distribution there is. -/
@[expose] public noncomputable def startHere : PMF Unit := PMF.pure ()

/-! The discount is `AISafetyAtlas.Examples.Decision.half`, already defined for
the fixed-point examples: one half, so the horizon is `2`. Reusing it keeps the
two value computations on the same number. -/

/-- The policy that always takes `false`. -/
@[expose] public noncomputable def pickFalse : Unit → PMF Bool := fun _ => PMF.pure false

/-- The policy that always takes `true`. -/
@[expose] public noncomputable def pickTrue : Unit → PMF Bool := fun _ => PMF.pure true

/-! ## Occupancy on one state -/

/--
**On one state the discounted occupancy is the whole horizon**, at every policy,
every initial distribution and every environment.

This is `sum_stateOcc_eq` with the sum over a single state, and it is why the
one-state model is enough to exhibit everything in `Goodhart.Hackability`: the
visit counts of a policy are its action distribution, scaled.
-/
public theorem stateOcc_unit (M : MDP Unit Bool) (π : Unit → PMF Bool) (I : PMF Unit)
    {γ : ℝ≥0} (hγ : γ < 1) : stateOcc M π I γ () = (1 - (γ : ℝ))⁻¹ := by
  simpa using sum_stateOcc_eq M π I hγ

/-- **So the visit counts are the action probabilities, scaled by the horizon.** -/
public theorem visitCount_unit (M : MDP Unit Bool) (π : Unit → PMF Bool) (I : PMF Unit)
    {γ : ℝ≥0} (hγ : γ < 1) (a : Bool) :
    visitCount M π I γ () a = (1 - (γ : ℝ))⁻¹ * (π () a).toReal := by
  rw [visitCount, stateOcc_unit M π I hγ]

/-- **And the value is the horizon times the reward the policy expects.** Print's
`⟨ℛ, F^π⟩` with the geometry of one state written out. -/
public theorem J_unit (M : MDP Unit Bool) (π : Unit → PMF Bool) (I : PMF Unit)
    {γ : ℝ≥0} (hγ : γ < 1) (R : Unit → Bool → ℝ) :
    J M I γ R π = (1 - (γ : ℝ))⁻¹ * ∑ a, R () a * (π () a).toReal := by
  simp only [J, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [visitCount_unit M π I hγ a]
  ring

/-! ## The library facts, instantiated -/

/-- Summability of the discounted series, at the model. -/
public theorem summable_here (π : Unit → PMF Bool) :
    Summable fun n : ℕ => (half : ℝ) ^ n * (stateDist oneState π startHere n ()).toReal :=
  summable_stateOcc oneState π startHere half_lt_one ()

/-- Occupancy is non-negative, at the model. -/
public theorem stateOcc_nonneg_here (π : Unit → PMF Bool) :
    0 ≤ stateOcc oneState π startHere half () :=
  stateOcc_nonneg oneState π startHere half ()

/-- Occupancy is bounded by the horizon, at the model — and here with equality,
which `stateOcc_unit` shows is the extreme case rather than a slack bound. -/
public theorem stateOcc_le_here (π : Unit → PMF Bool) :
    stateOcc oneState π startHere half () ≤ (1 - (half : ℝ))⁻¹ :=
  stateOcc_le oneState π startHere half_lt_one ()

/-- Visit counts are non-negative, at the model. -/
public theorem visitCount_nonneg_here (π : Unit → PMF Bool) (a : Bool) :
    0 ≤ visitCount oneState π startHere half () a :=
  visitCount_nonneg oneState π startHere half () a

/-- The two-step unfolding of `stateDist`, so neither equation is unapplied. -/
public theorem stateDist_here (π : Unit → PMF Bool) :
    stateDist oneState π startHere 1 = startHere.bind (stepKernel oneState π) := by
  rw [stateDist_succ, stateDist_zero]

/-- The horizon at a half discount is `2`. -/
public theorem horizon_half : (1 - (half : ℝ))⁻¹ = 2 := by
  unfold half
  norm_num

/-! ## Value is a linear functional of the reward, on the model -/

/-- Additivity, at the model. -/
public theorem J_add_here (R₁ R₂ : Unit → Bool → ℝ) (π : Unit → PMF Bool) :
    J oneState startHere half (fun s a => R₁ s a + R₂ s a) π
      = J oneState startHere half R₁ π + J oneState startHere half R₂ π :=
  J_add oneState startHere half R₁ R₂ π

/-- Homogeneity, at the model. -/
public theorem J_smul_here (c : ℝ) (R : Unit → Bool → ℝ) (π : Unit → PMF Bool) :
    J oneState startHere half (fun s a => c * R s a) π
      = c * J oneState startHere half R π :=
  J_smul oneState startHere half c R π

/-- Linearity, at the model. -/
public theorem J_linear_here (c₁ c₂ : ℝ) (R₁ R₂ : Unit → Bool → ℝ)
    (π : Unit → PMF Bool) :
    J oneState startHere half (fun s a => c₁ * R₁ s a + c₂ * R₂ s a) π
      = c₁ * J oneState startHere half R₁ π + c₂ * J oneState startHere half R₂ π :=
  J_linear oneState startHere half c₁ c₂ R₁ R₂ π

/-- A constant reward, unfolded through the occupancy. -/
public theorem J_const_here (c : ℝ) (π : Unit → PMF Bool) :
    J oneState startHere half (fun _ _ => c) π
      = c * ∑ s, stateOcc oneState π startHere half s :=
  J_const oneState startHere half c π

/-- **A constant reward pays every policy `2c`**, which is what makes it print's
*trivial* reward function on this model. -/
public theorem J_const_eq_here (c : ℝ) (π : Unit → PMF Bool) :
    J oneState startHere half (fun _ _ => c) π = c * 2 := by
  rw [J_const_eq oneState startHere half_lt_one c π, horizon_half]

/-! ## Non-stationary policies -/

/-- A policy that reads the whole history: take `true` exactly when the history has
even length. Not stationary: on the one-state model the state never changes, so a
stationary policy would take the same action at every step. -/
@[expose] public noncomputable def alternate : Policy Unit Bool :=
  fun h => PMF.pure (decide (Even h.2.length))

/-- **The whole discounted horizon is spent somewhere** at a non-stationary policy. -/
public theorem sum_histVisitCount_alternate :
    ∑ s, ∑ a, histVisitCount oneState alternate startHere half s a = 2 := by
  rw [sum_histVisitCount_eq oneState alternate startHere half_lt_one, horizon_half]

/-- Linearity of print's `J_ℛ` at the non-stationary policy. -/
public theorem histJ_linear_alternate (c₁ c₂ : ℝ) (R₁ R₂ : Unit → Bool → ℝ) :
    histJ oneState startHere half (fun s a => c₁ * R₁ s a + c₂ * R₂ s a) alternate
      = c₁ * histJ oneState startHere half R₁ alternate
        + c₂ * histJ oneState startHere half R₂ alternate :=
  histJ_linear oneState startHere half c₁ c₂ R₁ R₂ alternate

/-- Print's "Note that `J(π) = ⟨ℛ, F^π⟩`" at the non-stationary policy: value is the
discounted sum of the expected rewards along the run. -/
public theorem histJ_alternate_eq_tsum (R : Unit → Bool → ℝ) :
    histJ oneState startHere half R alternate
      = ∑' n : ℕ, (half : ℝ) ^ n * expectedReward oneState alternate startHere R n :=
  histJ_eq_tsum_expectedReward oneState startHere half_lt_one R alternate

/-- Visit counts at the non-stationary policy are non-negative, and the run's
starting point, which is in its support, has the state as its history's current
state. -/
public theorem alternate_nonneg_and_lastObs (a : Bool) :
    0 ≤ histVisitCount oneState alternate startHere half () a ∧
      (((), ((), [])) : Unit × History Unit Bool).2.lastObs = () :=
  ⟨histVisitCount_nonneg oneState alternate startHere half () a,
    lastObs_of_mem_support_run oneState alternate () 0 ((), ((), []))
      (by simp [MDP.run])⟩

/-- At a stationary policy the non-stationary visit counts are the stationary ones. -/
public theorem histVisitCount_ofStationary_here (π : Unit → PMF Bool) (a : Bool) :
    histVisitCount oneState (Policy.ofStationary π) startHere half () a
      = visitCount oneState π startHere half () a :=
  histVisitCount_ofStationary oneState π startHere half () a

/-- And so are the values. -/
public theorem histJ_ofStationary_here (R : Unit → Bool → ℝ) (π : Unit → PMF Bool) :
    histJ oneState startHere half R (Policy.ofStationary π) = J oneState startHere half R π :=
  histJ_ofStationary oneState startHere half R π

end AISafetyAtlas.Examples.Decision
