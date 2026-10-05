module

public import AISafetyAtlas.Wireheading.ValueBounds
public import AISafetyAtlas.Wireheading.DelusionBox

/-! A one-program model witnesses the probability and value-bound hypotheses. -/

namespace AISafetyAtlas.Examples.Wireheading.ValueBounds

open AISafetyAtlas.Wireheading AgentEquations

/-- A deterministic unit observation has probability one. -/
public theorem unitBelief_subprobability :
    (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ())).IsSubprobability where
  nonneg := by intros; simp [DelusionBox.diracBelief]
  summable := by intros; exact Summable.of_finite
  total_le_one := by intros; simp [DelusionBox.diracBelief]

/-- The source's bounded-reward case inhabits the summability result. -/
public theorem unit_actionValue_summable (t n : ℕ) :
    Summable (fun o ↦
      (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ())).cond [] () o *
        value (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
          (DelusionBox.rlAgent (fun (_ : Unit) ↦ 1) 1) t n [((), o)]) :=
  actionValue_summable unitBelief_subprobability _ (by
    intro h
    simp only [DelusionBox.rlAgent, DelusionBox.lastReward]
    split <;> norm_num) t n [] ()

/-- The window horizon has finite support, so its absolute value is summable --
`rlAgent`'s horizon weight is `1` inside a window of `m` steps and `0` beyond
it. -/
public theorem unit_horizon_summable (t : ℕ) :
    Summable (fun k ↦ |(DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).horizon t k|) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_Icc 0 (t + 1))
  intro k hk
  simp only [Function.mem_support, ne_eq, abs_eq_zero] at hk
  by_contra hcon
  simp only [Set.mem_Icc, not_and, not_le] at hcon
  apply hk
  show (DelusionBox.windowHorizon 1 t k : ℝ) = 0
  rw [DelusionBox.windowHorizon, if_neg (by omega)]

/-- The reward is bounded by one in absolute value: it is either `0` (empty
history) or exactly `1`. -/
public theorem unit_utility_bounded (h : History Unit Unit) :
    |(DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).utility h| ≤ 1 := by
  show |DelusionBox.lastReward (fun (_ : Unit) ↦ (1:ℝ)) h| ≤ 1
  unfold DelusionBox.lastReward
  split <;> norm_num

/-- **Definition 9's infinite-horizon value equation, at the witness.** The
source's own bounded-reward, summable-horizon case. -/
public theorem unit_infiniteValue_eq (t : ℕ) (h : History Unit Unit) :
    infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h
      = (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).horizon t h.length *
          (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).utility h +
        ⨆ a, infiniteActionValue
          (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
          (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h a :=
  infiniteValue_eq unitBelief_subprobability (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1)
    unit_utility_bounded t (unit_horizon_summable t) h

/-- **The truncation error is bounded by the horizon's tail, at the witness.** -/
public theorem unit_value_error_le_tail (n : ℕ) (h : History Unit Unit) :
    |value (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) 0 n h -
      infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) 0 h| ≤
      ∑' i : ℕ, |(DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).horizon 0 (h.length + (n + i) + 1)| :=
  value_error_le_tail unitBelief_subprobability (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1)
    unit_utility_bounded 0 (unit_horizon_summable 0) n h

end AISafetyAtlas.Examples.Wireheading.ValueBounds
