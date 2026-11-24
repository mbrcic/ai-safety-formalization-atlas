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

/-! ## Equation (1)'s optimum is weaker than `le_optValue`

Print's counter-instance: one state, two human actions, one agent action that
leaves the human on the worse action `false`. Under the reward paying `1` for
`true`, the optimum over the agent's actions is `0`, while the policy `true`,
which no agent action produces, is worth `1`. So these data satisfy
`IsAgentOptimum` and admit no `OverrideModel`. -/

/-- The reward paying `1` for the human action `true`. -/
@[expose] public def payTrueAction : RewardFn Unit Bool := fun _ b => if b then 1 else 0

/-- **Equation (1)'s optimum, inhabited where `le_optValue` fails**: the
optimum over the agent's one action is the value of the policy it results in,
and a policy outside that range beats it. -/
public theorem agentOptimum_strictly_weaker :
    IsAgentOptimum (S := Unit) (A := Bool) (Act := Unit)
        (fun _ _ => false) (fun R π => R () (π ())) (fun R => R () false) (fun _ => ())
      ∧ ¬ ∀ (R : RewardFn Unit Bool) (π : Policy Unit Bool), R () (π ()) ≤ R () false := by
  refine ⟨⟨fun _ _ => le_refl _, fun _ => rfl⟩, fun h => ?_⟩
  have := h payTrueAction (fun _ => true)
  norm_num [payTrueAction] at this

/-- Equation (1)'s maximum at the counter-instance: `0` is the greatest value
over the agent's actions under `payTrueAction`. -/
public theorem agentOptimum_isGreatest :
    IsGreatest {v : ℝ | ∃ a : Unit, v = payTrueAction () ((fun _ _ => false : Unit → Policy Unit Bool) a ())}
      (payTrueAction () false) :=
  agentOptimum_strictly_weaker.1.isGreatest payTrueAction

/-! ## A strict override, at a model whose inaction has positive regret -/

/-- One state, two human actions, two agent actions: the agent sets the human's
action, inaction leaves it at `false`, and rationalising picks a maximiser. -/
public noncomputable def boolOverride : OverrideModel Unit Bool Bool where
  resulting := fun b _ => b
  value := fun R π => R () (π ())
  optValue := fun R => max (R () false) (R () true)
  le_optValue := fun R π => by
    cases π () with
    | false => exact le_max_left _ _
    | true => exact le_max_right _ _
  noop := false
  rationalise := fun R => decide (R () false ≤ R () true)
  rationalise_optimal := fun R => by
    by_cases h : R () false ≤ R () true
    · simp [h]
    · simp [h, max_eq_left (le_of_not_ge h)]

/-- **A strict override, inhabited**: under `payTrueAction`, inaction leaves the human
at regret `1`, and the pair returning the resulting policy explains it at the
positive threshold `1`. -/
public theorem boolOverride_strictlyOverridesFor :
    OverrideModel.StrictlyOverridesFor boolOverride
      (fun _ => OverrideModel.resulting boolOverride false) payTrueAction 1 false := by
  refine ⟨one_pos, rfl, ?_⟩
  simp [OverrideModel.regret, boolOverride, payTrueAction]

/-- **The behaviour after it does not maximise the reward**, at the witness. -/
public theorem boolOverride_value_lt :
    Explains (fun _ => OverrideModel.resulting boolOverride false) payTrueAction
        (OverrideModel.resulting boolOverride false) ∧
      OverrideModel.value boolOverride payTrueAction (OverrideModel.resulting boolOverride false) <
        OverrideModel.optValue boolOverride payTrueAction :=
  OverrideModel.StrictlyOverridesFor.value_lt_optValue boolOverride
    boolOverride_strictlyOverridesFor

/-- The existence form, and the projection to `OverridesFor`, at the witness. -/
example : ∃ p, OverrideModel.StrictlyOverridesFor boolOverride p payTrueAction
    (OverrideModel.regret boolOverride payTrueAction false) false :=
  OverrideModel.exists_strictlyOverridesFor boolOverride payTrueAction false
    (by simp [boolOverride, payTrueAction])

example : OverrideModel.OverridesFor boolOverride
    (fun _ => OverrideModel.resulting boolOverride false) payTrueAction 1 false :=
  OverrideModel.overridesFor_of_strictlyOverridesFor boolOverride
    boolOverride_strictlyOverridesFor

/-- Every override model's optimum is an agent optimum, at the witness. -/
example : IsAgentOptimum (OverrideModel.resulting boolOverride)
    (OverrideModel.value boolOverride) (OverrideModel.optValue boolOverride)
    (OverrideModel.rationalise boolOverride) :=
  OverrideModel.isAgentOptimum boolOverride

/-- Regret against an agent optimum is nonnegative, at the counter-instance. -/
example : 0 ≤ payTrueAction () false - payTrueAction () ((fun _ _ => false : Unit → Policy Unit Bool) () ()) :=
  IsAgentOptimum.sub_value_nonneg agentOptimum_strictly_weaker.1 payTrueAction ()

/-! ## Definition 11 at an agent optimum where `le_optValue` fails

Three human actions `0, 1, 2`, two agent actions: leaving the human on `0` or
forcing `1`. The reward pays the action's index, so the unreachable action `2`
is worth more than the optimum over the agent's actions, and no `OverrideModel`
has these data; yet inaction is a strict override at regret `1`. -/

/-- The reward paying the human action's index. -/
@[expose] public def payIndex : RewardFn Unit (Fin 3) := fun _ a => (a.val : ℝ)

/-- The policy each agent action results in: `false` leaves `0`, `true` forces `1`. -/
@[expose] public def threeActionResulting : Bool → Policy Unit (Fin 3) :=
  fun b _ => if b then 1 else 0

/-- The optimum over the agent's two actions. -/
@[expose] public noncomputable def threeActionOpt : RewardFn Unit (Fin 3) → ℝ :=
  fun R => max (R () 0) (R () 1)

/-- **The data are an agent optimum**, and a policy no agent action produces
beats it. -/
public theorem threeAction_isAgentOptimum :
    IsAgentOptimum threeActionResulting (fun R π => R () (π ())) threeActionOpt
        (fun R => decide (R () 0 ≤ R () 1))
      ∧ threeActionOpt payIndex < payIndex () 2 := by
  refine ⟨⟨fun R a => ?_, fun R => ?_⟩, ?_⟩
  · cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  · by_cases h : R () 0 ≤ R () 1
    · simp [threeActionResulting, threeActionOpt, h]
    · simp [threeActionResulting, threeActionOpt, h, max_eq_left (le_of_not_ge h)]
  · norm_num [threeActionOpt, payIndex]

/-- **Inaction is a strict override at that agent optimum**, threshold `1`. -/
public theorem threeAction_strictlyOverridesForAt :
    StrictlyOverridesForAt threeActionResulting (fun R π => R () (π ())) threeActionOpt
      (fun _ => threeActionResulting false) payIndex 1 false := by
  refine ⟨one_pos, rfl, ?_⟩
  norm_num [threeActionResulting, threeActionOpt, payIndex]

/-- …so the behaviour after it does not maximise the reward. -/
example : Explains (fun _ => threeActionResulting false) payIndex (threeActionResulting false) ∧
    payIndex () (threeActionResulting false ()) < threeActionOpt payIndex :=
  threeAction_strictlyOverridesForAt.value_lt

/-- The model-level predicates are the raw-data ones at the model's fields. -/
example : OverrideModel.OverridesFor boolOverride
      (fun _ => OverrideModel.resulting boolOverride false) payTrueAction 1 false ↔
    OverridesForAt (OverrideModel.resulting boolOverride) (OverrideModel.value boolOverride)
      (OverrideModel.optValue boolOverride)
      (fun _ => OverrideModel.resulting boolOverride false) payTrueAction 1 false :=
  OverrideModel.overridesFor_iff_overridesForAt boolOverride _ _ _ _

example : OverrideModel.StrictlyOverridesFor boolOverride
      (fun _ => OverrideModel.resulting boolOverride false) payTrueAction 1 false ↔
    StrictlyOverridesForAt (OverrideModel.resulting boolOverride)
      (OverrideModel.value boolOverride) (OverrideModel.optValue boolOverride)
      (fun _ => OverrideModel.resulting boolOverride false) payTrueAction 1 false :=
  OverrideModel.strictlyOverridesFor_iff_strictlyOverridesForAt boolOverride _ _ _ _

end AISafetyAtlas.Examples.Preference
