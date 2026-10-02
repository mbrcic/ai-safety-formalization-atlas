module

public import AISafetyAtlas.Preference.Override

/-!
# Overriding human reward functions, at the cheapest model

`AISafetyAtlas.Preference.OverrideModel` is abstract over states, actions and
agent actions. The cheapest instance collapses all three to `Unit`: there is
one policy, one reward-independent value, and rationalising is a no-op. Every
field's inequality then reduces to a comparison of a real number with itself.
-/

namespace AISafetyAtlas.Examples.Preference

open AISafetyAtlas.Preference

/-- The cheapest `OverrideModel`: one state, one action, one agent action. -/
public def trivialOverride : OverrideModel Unit Unit Unit where
  resulting := fun _ _ => ()
  value := fun R _ => R () ()
  optValue := fun R => R () ()
  le_optValue := fun _ _ => le_refl _
  noop := ()
  rationalise := fun _ => ()
  rationalise_optimal := fun _ => rfl

/-- The zero reward, used to instantiate the model. -/
@[expose] public def zeroReward : RewardFn Unit Unit := fun _ _ => 0

/-- Regret at the zero reward is exactly zero: `optValue` and `value` agree. -/
theorem trivial_regret_eq_zero :
    OverrideModel.regret trivialOverride zeroReward () = 0 := by
  unfold OverrideModel.regret trivialOverride zeroReward
  ring

/-- Regret is nonnegative, at the trivial instance. -/
theorem trivial_regret_nonneg :
    0 ≤ OverrideModel.regret trivialOverride zeroReward () :=
  OverrideModel.regret_nonneg trivialOverride zeroReward ()

/-- Rationalising incurs no regret, at the trivial instance. -/
theorem trivial_regret_rationalise :
    OverrideModel.regret trivialOverride zeroReward
        (OverrideModel.rationalise trivialOverride zeroReward) = 0 :=
  OverrideModel.regret_rationalise trivialOverride zeroReward

/-- Equation (1): `optValue` is the greatest attained value, at the instance. -/
theorem trivial_optValue_isGreatest :
    IsGreatest
      {v : ℝ | ∃ a : Unit,
        v = OverrideModel.value trivialOverride zeroReward
          (OverrideModel.resulting trivialOverride a)}
      (OverrideModel.optValue trivialOverride zeroReward) :=
  OverrideModel.optValue_isGreatest trivialOverride zeroReward

/-- Every action admits a compatible pair witnessing the relativised override,
at threshold `0` (the actual regret). -/
theorem trivial_exists_overridesFor :
    ∃ p : Planner (RewardFn Unit Unit) (Policy Unit Unit),
      OverrideModel.OverridesFor trivialOverride p zeroReward 0 () :=
  OverrideModel.exists_overridesFor trivialOverride zeroReward 0 ()
    (by rw [trivial_regret_eq_zero])

/-- The relativised override implies the unrelativised one, at the witness
pair produced above. -/
theorem trivial_overrides_of_overridesFor :
    OverrideModel.Overrides trivialOverride zeroReward 0 () := by
  obtain ⟨p, hp⟩ := trivial_exists_overridesFor
  exact OverrideModel.overrides_of_overridesFor trivialOverride hp

/-! ## Appendix B.1's two branches, both inhabited

Print's first paragraph assumes the human's own policy is already optimal, so
inaction has zero regret; two paragraphs later it assumes a less-than-rational
human and inaction is strictly worse. The trivial model is the first case — its
one policy is optimal by construction — and `Examples.SixTargets`'s
`suboptimalOverrideModel` is the second.
-/

/-- The only planner there is, at the trivial instance, is fully rational. -/
public theorem trivial_isRationalPlanner :
    OverrideModel.IsRationalPlanner trivialOverride (fun _ _ => ()) :=
  fun _ => rfl

/-- **Print's first branch, at the witness**: inaction has zero regret. -/
public theorem trivial_regret_noop_eq_zero :
    OverrideModel.regret trivialOverride zeroReward
      (OverrideModel.noop trivialOverride) = 0 :=
  OverrideModel.regret_noop_eq_zero_of_rationalPlanner trivialOverride
    trivial_isRationalPlanner zeroReward rfl

/-- **And so inaction is not an override** at any positive threshold. -/
public theorem trivial_not_overrides_noop :
    ¬ OverrideModel.Overrides trivialOverride zeroReward 1
        (OverrideModel.noop trivialOverride) :=
  OverrideModel.not_overrides_noop_of_rationalPlanner trivialOverride
    trivial_isRationalPlanner zeroReward rfl one_pos

/-- **The closed form print draws from that branch**, at the witness: regret is
the shortfall below the untouched human. -/
public theorem trivial_regret_eq_noopValue_sub (a : Unit) :
    OverrideModel.regret trivialOverride zeroReward a =
      OverrideModel.noopValue trivialOverride zeroReward -
        OverrideModel.value trivialOverride zeroReward
          (OverrideModel.resulting trivialOverride a) :=
  OverrideModel.regret_eq_noopValue_sub_of_rationalPlanner trivialOverride
    trivial_isRationalPlanner zeroReward rfl a

/-- **The dichotomy**, at the witness that takes its left branch. -/
public theorem trivial_regret_noop_eq_zero_or_overrides :
    OverrideModel.regret trivialOverride zeroReward
        (OverrideModel.noop trivialOverride) = 0 ∨
      (0 < OverrideModel.regret trivialOverride zeroReward
            (OverrideModel.noop trivialOverride) ∧
        ∀ θ ≤ OverrideModel.regret trivialOverride zeroReward
            (OverrideModel.noop trivialOverride),
          OverrideModel.Overrides trivialOverride zeroReward θ
            (OverrideModel.noop trivialOverride)) :=
  OverrideModel.regret_noop_eq_zero_or_overrides trivialOverride zeroReward

end AISafetyAtlas.Examples.Preference
