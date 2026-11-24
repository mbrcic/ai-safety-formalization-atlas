module

public import AISafetyAtlas.Preference.OverrideOnePlanner
public import AISafetyAtlas.Examples.Preference.Discounted

/-!
# One planner for the run: inaction overrides the twisted reward

The one-state MDP `AISafetyAtlas.Examples.Preference.Discounted.loopMDP` at
discount 1/2, doubled into M*. The human reward Ṙ pays 1/4 for true, the
override reward Rᵃ pays 1 for true, and the observed policy plays true on
both copies; it is the unique optimal policy of each copy's reward
(copy_zero_true_unique, copy_one_true_unique), so the pair of
the rational planner and the twisted reward Ṙᵃ is compatible with no tie rule.
The constant planner returning the observed policy stands in for that pair here.

From ŝ₀ the observed policy earns 1/2 under Ṙᵃ, from ŝ₁ it earns 2, so
inaction has regret 3/2 and overrides Ṙᵃ at threshold 1, while the pair still
outputs the one observed policy. The per-action model cannot state this case: one
observed policy has two values, one per start state.
-/

namespace AISafetyAtlas.Examples.Preference.OverrideOnePlanner

open AISafetyAtlas.Preference AISafetyAtlas.Decision AISafetyAtlas.Preference.Discounted
open scoped NNReal

/-- The human reward: 1/4 for true. -/
@[expose] public noncomputable def humanReward : RewardFn Unit Bool :=
  fun _ b => if b then 1 / 4 else 0

/-- The override reward: 1 for true. -/
@[expose] public def overrideReward : RewardFn Unit Bool := fun _ b => if b then 1 else 0

/-- The observed policy on M*: true on both copies. -/
@[expose] public def observed : Unit × Bool → Bool := fun _ => true

/-- A planner returning the observed policy. -/
@[expose] public def observedPlanner :
    Planner (RewardFn (Unit × Bool) Bool) (AISafetyAtlas.Preference.Policy (Unit × Bool) Bool) :=
  fun _ => observed

private theorem half_coe : ((2⁻¹ : ℝ≥0) : ℝ) = 1 / 2 := by norm_num

/-- From ŝ₀ the observed policy earns 1/2 under the twisted reward. -/
public theorem value_start_zero :
    augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one
        (twistReward humanReward overrideReward) observed
        (augStart () (none : Option (Unit → Bool))) = 1 / 2 := by
  simp only [augValue, augStart, Option.isSome_none,
    AISafetyAtlas.Preference.Discounted.vPi_augmentMDP]
  rw [AISafetyAtlas.Preference.Discounted.vPi_const_reward _ _ _ _ (1 / 4)
    (fun _ => by simp [twistReward, humanReward, observed])]
  rw [half_coe]; norm_num

/-- From ŝ₁ the observed policy earns 2 under the twisted reward. -/
public theorem value_start_one (π : Unit → Bool) :
    augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one
        (twistReward humanReward overrideReward) observed (augStart () (some π)) = 2 := by
  simp only [augValue, augStart, Option.isSome_some,
    AISafetyAtlas.Preference.Discounted.vPi_augmentMDP]
  rw [AISafetyAtlas.Preference.Discounted.vPi_const_reward _ _ _ _ 1
    (fun _ => by simp [twistReward, overrideReward, observed])]
  rw [half_coe]; norm_num

/-- Inaction's regret under the twisted reward is 3/2. -/
public theorem startRegret_none :
    startRegret
        (augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one)
        (augStart ()) observed (twistReward humanReward overrideReward)
        (none : Option (Unit → Bool)) = 3 / 2 := by
  have hmax : sSup (Set.range fun b : Option (Unit → Bool) =>
      augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one
        (twistReward humanReward overrideReward) observed (augStart () b)) = 2 := by
    refine IsGreatest.csSup_eq ⟨⟨some fun _ => true, value_start_one _⟩, ?_⟩
    rintro _ ⟨b, rfl⟩
    cases b with
    | none => simp only [value_start_zero]; norm_num
    | some π => simp only [value_start_one]; rfl
  rw [startRegret, hmax, value_start_zero]
  norm_num

/-- **Inaction overrides the twisted reward at threshold 1**, with the one
planner explaining the observed policy. -/
public theorem overridesFromStart_none :
    OverridesFromStart
      (augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one)
      (augStart ()) observed observedPlanner (twistReward humanReward overrideReward) 1
      (none : Option (Unit → Bool)) :=
  ⟨rfl, by rw [startRegret_none]; norm_num⟩

/-- **Appendix B.1's remark, at the witness**: the pair still outputs the observed
policy, and inaction's value falls strictly below the value from another start. -/
public theorem remark_at_witness :
    observedPlanner (twistReward humanReward overrideReward) = observed ∧
      augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one
          (twistReward humanReward overrideReward) observed
          (augStart () (none : Option (Unit → Bool))) <
        sSup (Set.range fun b : Option (Unit → Bool) =>
          augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
            AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one
            (twistReward humanReward overrideReward) observed (augStart () b)) ∧
      ∃ b : Option (Unit → Bool),
        augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
            AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one
            (twistReward humanReward overrideReward) observed
          (augStart () (none : Option (Unit → Bool))) <
          augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
            AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one
            (twistReward humanReward overrideReward) observed (augStart () b) :=
  AISafetyAtlas.Preference.OverridesFromStart.eq_and_exists_lt overridesFromStart_none one_pos

/-- Compatibility is one condition for every action, at the witness. -/
example (θ : ℝ) (a : Option (Unit → Bool)) :
    OverridesFromStart
        (augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one)
        (augStart ()) observed observedPlanner (twistReward humanReward overrideReward) θ a ↔
      θ ≤ startRegret
        (augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one)
        (augStart ()) observed (twistReward humanReward overrideReward) a :=
  AISafetyAtlas.Preference.overridesFromStart_iff rfl θ a

/-- The observed policy on each copy is the unique optimum of that copy's reward:
false earns nothing, so the pair of a rational planner and the twisted reward
needs no tie rule. -/
public theorem false_earns_zero (R : RewardFn Unit Bool)
    (hR : R () false = 0) :
    vPi AISafetyAtlas.Examples.Preference.Discounted.loopMDP R
      AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one (fun _ => false) () = 0 := by
  rw [AISafetyAtlas.Preference.Discounted.vPi_const_reward _ _ _ _ 0 (fun _ => hR)]
  simp

/-- At the mixed policy, action 0's value is `augActionValue`'s, at the witness. -/
example (πdot πa : Unit → Bool) (r : Unit × Bool → Bool → ℝ) :
    augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one r (mixPolicy πdot πa)
        (augStart () (none : Option (Unit → Bool))) =
      augActionValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one () πdot r
        (none : Option (Unit → Bool)) :=
  AISafetyAtlas.Preference.Discounted.augValue_mixPolicy_none _ _ () πdot πa r

/-- At the mixed policy, (1, πᵃ)'s value is `augActionValue`'s, at the witness. -/
example (πdot πa : Unit → Bool) (r : Unit × Bool → Bool → ℝ) :
    augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one r (mixPolicy πdot πa)
        (augStart () (some πa)) =
      augActionValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one () πdot r (some πa) :=
  AISafetyAtlas.Preference.Discounted.augValue_mixPolicy_some _ _ () πdot πa r

/-- **The one-planner regret of overriding is print's closed form**, at an optimal
human supplied by `argmaxPolicy`. -/
public theorem startRegret_overriding (πa : Unit → Bool) (Rdot : RewardFn Unit Bool) :
    startRegret
        (augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one)
        (augStart ())
        (mixPolicy (argmaxPolicy AISafetyAtlas.Examples.Preference.Discounted.loopMDP Rdot
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one ()) πa)
        (liftReward Rdot) (some πa) =
      augRegret AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one ()
        (argmaxPolicy AISafetyAtlas.Examples.Preference.Discounted.loopMDP Rdot
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one ())
        (liftReward Rdot) (some πa) :=
  AISafetyAtlas.Preference.Discounted.startRegret_liftReward_eq_augRegret _ _ () _ πa Rdot
    (AISafetyAtlas.Preference.Discounted.vPi_argmaxPolicy _ Rdot _ ()) (Or.inr rfl)

/-- The same regret is the override model's, at the witness. -/
example (πa : Unit → Bool) (Rdot : RewardFn Unit Bool) :
    startRegret
        (augValue AISafetyAtlas.Examples.Preference.Discounted.loopMDP
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one)
        (augStart ())
        (mixPolicy (argmaxPolicy AISafetyAtlas.Examples.Preference.Discounted.loopMDP Rdot
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one ()) πa)
        (liftReward Rdot) (none : Option (Unit → Bool)) =
      (discountedOverride AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one ()
        (argmaxPolicy AISafetyAtlas.Examples.Preference.Discounted.loopMDP Rdot
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one ())).regret Rdot
        (none : Option (Unit → Bool)) :=
  AISafetyAtlas.Preference.Discounted.startRegret_liftReward_of_optimal _ _ () _ πa Rdot
    (AISafetyAtlas.Preference.Discounted.vPi_argmaxPolicy _ Rdot _ ()) (Or.inl rfl)

/-- On copy 0, playing true earns strictly more under the human reward than playing
false: the observed policy is the unique optimum of that copy's reward. -/
public theorem copy_zero_true_unique :
    vPi AISafetyAtlas.Examples.Preference.Discounted.loopMDP humanReward
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one (fun _ => false) () <
      vPi AISafetyAtlas.Examples.Preference.Discounted.loopMDP humanReward
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one (fun _ => true) () := by
  rw [false_earns_zero humanReward (by simp [humanReward]),
    AISafetyAtlas.Preference.Discounted.vPi_const_reward _ _ _ _ (1 / 4)
      (fun _ => by simp [humanReward]), half_coe]
  norm_num

/-- On copy 1, playing true earns strictly more under the override reward than
playing false. -/
public theorem copy_one_true_unique :
    vPi AISafetyAtlas.Examples.Preference.Discounted.loopMDP overrideReward
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one (fun _ => false) () <
      vPi AISafetyAtlas.Examples.Preference.Discounted.loopMDP overrideReward
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one (fun _ => true) () := by
  rw [false_earns_zero overrideReward (by simp [overrideReward]),
    AISafetyAtlas.Preference.Discounted.vPi_const_reward _ _ _ _ 1
      (fun _ => by simp [overrideReward]), half_coe]
  norm_num

/-- **The per-action model is an instance of the one-planner predicate**, at the
discounted override model of the witness MDP. -/
example (πdot : Unit → Bool)
    (p : Planner (RewardFn Unit Bool) (AISafetyAtlas.Preference.Policy Unit Bool))
    (R : RewardFn Unit Bool) (θ : ℝ) (a : Option (Unit → Bool)) :
    (discountedOverride AISafetyAtlas.Examples.Preference.Discounted.loopMDP
        AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one () πdot).OverridesFor
        p R θ a ↔
      OverridesFromStart
        (fun R (_ : AISafetyAtlas.Preference.Policy Unit Bool) b =>
          (discountedOverride AISafetyAtlas.Examples.Preference.Discounted.loopMDP
            AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one () πdot).value R
            ((discountedOverride AISafetyAtlas.Examples.Preference.Discounted.loopMDP
              AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one ()
              πdot).resulting b))
        id
        ((discountedOverride AISafetyAtlas.Examples.Preference.Discounted.loopMDP
          AISafetyAtlas.Examples.Preference.Discounted.loopDiscount_lt_one () πdot).resulting a)
        p R θ a :=
  AISafetyAtlas.Preference.OverrideModel.overridesFor_iff_overridesFromStart _ p R θ a

end AISafetyAtlas.Examples.Preference.OverrideOnePlanner
