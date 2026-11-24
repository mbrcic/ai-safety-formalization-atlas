module

public import AISafetyAtlas.Preference.Discounted

/-!
# The discounted regret and override models, at a one-state MDP

One state, two human actions, a deterministic transition back to the state, and
discount `1/2`. Every hypothesis of `AISafetyAtlas.Preference.Discounted` is
inhabited here: the discount is below one, the human policy assumed optimal is
the one `argmaxPolicy` chooses, the two-action case of the worst reward is
`Bool`, and the one-action case is `Unit`.
-/

namespace AISafetyAtlas.Examples.Preference.Discounted

open AISafetyAtlas.Preference AISafetyAtlas.Decision AISafetyAtlas.Preference.Discounted
open scoped NNReal

/-- The one-state MDP with two actions. -/
@[expose] public noncomputable def loopMDP : MDP Unit Bool := MDP.ofDet fun _ _ => ()

/-- The one-state MDP with one action. -/
@[expose] public noncomputable def loopMDP₁ : MDP Unit Unit := MDP.ofDet fun _ _ => ()

/-- The discount `1/2` is below one. -/
public theorem loopDiscount_lt_one : (2⁻¹ : ℝ≥0) < 1 := by norm_num

/-- **§4.1.2's half-maximal bound, at the witness.** -/
public theorem loop_half_maximal_regret (π : Unit → Bool) :
    (⨆ π' : Unit → Bool, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn Unit Bool) (σ : Unit → Bool) =>
          vPi loopMDP R.1 loopDiscount_lt_one σ ()) Set.univ π') / 2 ≤
      AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn Unit Bool) (σ : Unit → Bool) =>
          vPi loopMDP R.1 loopDiscount_lt_one σ ()) Set.univ π := by
  have h := discounted_half_maximal_regret loopMDP loopDiscount_lt_one () π
  simpa only [vPiBdd_eq_vPi] using h

/-- The worst reward attains regret `2/(1 − γ) = 4` at two actions. -/
public theorem loop_regret_signReward (π : Unit → Bool) :
    vPi loopMDP (signReward π) loopDiscount_lt_one
        (argmaxPolicy loopMDP (signReward π) loopDiscount_lt_one ()) () -
      vPi loopMDP (signReward π) loopDiscount_lt_one π () = 2 / (1 - ((2⁻¹ : ℝ≥0) : ℝ)) :=
  argmax_regret_signReward loopMDP loopDiscount_lt_one () π

/-- At one action every regret is `0`. -/
public theorem loop₁_regret_zero (R : RewardFn Unit Unit) (π : Unit → Unit) :
    vPi loopMDP₁ R loopDiscount_lt_one (argmaxPolicy loopMDP₁ R loopDiscount_lt_one ()) () -
      vPi loopMDP₁ R loopDiscount_lt_one π () = 0 :=
  argmax_regret_eq_zero_of_subsingleton loopMDP₁ loopDiscount_lt_one () R π

/-- The regret bound, at the worst reward. -/
example (π σ : Unit → Bool) :
    vPi loopMDP (signReward π) loopDiscount_lt_one
        (argmaxPolicy loopMDP (signReward π) loopDiscount_lt_one ()) () -
      vPi loopMDP (signReward π) loopDiscount_lt_one σ () ≤ 2 / (1 - ((2⁻¹ : ℝ≥0) : ℝ)) :=
  argmax_regret_le_two_div loopMDP loopDiscount_lt_one () _ (isBoundedReward_signReward π) σ

/-- The value bound, at the worst reward. -/
example (π σ : Unit → Bool) :
    |vPi loopMDP (signReward π) loopDiscount_lt_one σ ()| ≤ 1 / (1 - ((2⁻¹ : ℝ≥0) : ℝ)) :=
  abs_vPi_le loopMDP _ loopDiscount_lt_one σ
    (abs_le_one_of_isBoundedReward (isBoundedReward_signReward π)) ()

/-- A constant reward, and the policy earning it, at the witness. -/
example (σ : Unit → Bool) :
    vPi loopMDP (fun _ _ => 1) loopDiscount_lt_one σ = fun _ => 1 / (1 - ((2⁻¹ : ℝ≥0) : ℝ)) :=
  vPi_const_reward loopMDP _ loopDiscount_lt_one σ 1 fun _ => rfl

/-- Negating the reward negates the value, at the witness. -/
example (R : RewardFn Unit Bool) (σ : Unit → Bool) :
    vPi loopMDP (-R) loopDiscount_lt_one σ = -vPi loopMDP R loopDiscount_lt_one σ :=
  vPi_neg loopMDP R loopDiscount_lt_one σ

/-- Values on the augmented MDP are values on the base MDP, at the witness. -/
example (r : Unit × Bool → Bool → ℝ) (π : Unit × Bool → Bool) (b : Bool) :
    vPi (augmentMDP loopMDP) r loopDiscount_lt_one π ((), b) =
      vPi loopMDP (fun s a => r (s, b) a) loopDiscount_lt_one (fun s => π (s, b)) () :=
  vPi_augmentMDP loopMDP r loopDiscount_lt_one π () b

/-- **Appendix B.1's closed form on `M*`, at the witness.** -/
public theorem loop_augRegret_overriding (πdot πa : Unit → Bool) (Rdot : RewardFn Unit Bool) :
    augRegret loopMDP loopDiscount_lt_one () πdot (liftReward Rdot) (some πa) =
      optValueAt loopMDP Rdot loopDiscount_lt_one () - vPi loopMDP Rdot loopDiscount_lt_one πa () :=
  augRegret_overriding loopMDP loopDiscount_lt_one () πdot Rdot πa

/-- `M*`'s regret is the override model's, at the witness. -/
example (πdot : Unit → Bool) (R : RewardFn Unit Bool) (a : Option (Unit → Bool)) :
    augRegret loopMDP loopDiscount_lt_one () πdot (liftReward R) a =
      (discountedOverride loopMDP loopDiscount_lt_one () πdot).regret R a :=
  augRegret_eq_regret loopMDP loopDiscount_lt_one () πdot R a

/-- **Inaction has zero regret on `M*`** when the human follows an optimal
policy, which `argmaxPolicy` supplies. -/
public theorem loop_augRegret_noop (Rdot : RewardFn Unit Bool) :
    augRegret loopMDP loopDiscount_lt_one () (argmaxPolicy loopMDP Rdot loopDiscount_lt_one ())
      (liftReward Rdot) none = 0 :=
  augRegret_noop loopMDP loopDiscount_lt_one () _ Rdot (vPi_argmaxPolicy loopMDP Rdot loopDiscount_lt_one ())

/-- **Equation (2), computed, at the witness.** -/
public theorem loop_beliefValue_overriding (πdot : Unit → Bool) (ε : ℝ)
    (Rdot Ra : RewardFn Unit Bool) :
    beliefValue loopMDP loopDiscount_lt_one () πdot ε Rdot Ra
        (some (argmaxPolicy loopMDP Ra loopDiscount_lt_one ())) =
      (discountedOverride loopMDP loopDiscount_lt_one () πdot).mixtureValue ε Rdot Ra :=
  beliefValue_overriding loopMDP loopDiscount_lt_one () πdot ε Rdot Ra

/-- **Action `0` under the belief gives `V*_Ṙ`**, at an optimal human. -/
public theorem loop_beliefValue_noop (ε : ℝ) (Rdot Ra : RewardFn Unit Bool) :
    beliefValue loopMDP loopDiscount_lt_one () (argmaxPolicy loopMDP Rdot loopDiscount_lt_one ()) ε Rdot Ra
        none = optValueAt loopMDP Rdot loopDiscount_lt_one () :=
  beliefValue_noop loopMDP loopDiscount_lt_one () _ ε Rdot Ra
    (vPi_argmaxPolicy loopMDP Rdot loopDiscount_lt_one ())

/-- Action `(1, π)` under the belief, for any forced policy. -/
example (πdot π : Unit → Bool) (ε : ℝ) (Rdot Ra : RewardFn Unit Bool) :
    beliefValue loopMDP loopDiscount_lt_one () πdot ε Rdot Ra (some π) =
      ε * vPi loopMDP Ra loopDiscount_lt_one π () + (1 - ε) * vPi loopMDP Rdot loopDiscount_lt_one π () :=
  beliefValue_some loopMDP loopDiscount_lt_one () πdot ε Rdot Ra π

/-- An action's value on `M*` at a boolean-blind reward, at the witness. -/
example (πdot : Unit → Bool) (R : RewardFn Unit Bool) (a : Option (Unit → Bool)) :
    augActionValue loopMDP loopDiscount_lt_one () πdot (liftReward R) a =
      (discountedOverride loopMDP loopDiscount_lt_one () πdot).value R
        ((discountedOverride loopMDP loopDiscount_lt_one () πdot).resulting a) :=
  augActionValue_liftReward loopMDP loopDiscount_lt_one () πdot R a

/-! ## A countably infinite state space

The chain `0 → 1 → 2 → …` with two actions: a print instance (discrete `𝒮`)
outside every finite-state statement above. -/

/-- The chain on `ℕ`: every action moves one step right. -/
@[expose] public noncomputable def chainMDP : MDP ℕ Bool := MDP.ofDet fun s _ => s + 1

/-- **§4.1.2's half-maximal bound on an infinite state space.** -/
public theorem chain_half_maximal_regret (π : ℕ → Bool) :
    (⨆ π' : ℕ → Bool, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn ℕ Bool) (σ : ℕ → Bool) =>
          vPiBdd chainMDP R.1 loopDiscount_lt_one σ
            (fun s => abs_le_one_of_isBoundedReward R.2 s (σ s)) 0) Set.univ π') / 2 ≤
      AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn ℕ Bool) (σ : ℕ → Bool) =>
          vPiBdd chainMDP R.1 loopDiscount_lt_one σ
            (fun s => abs_le_one_of_isBoundedReward R.2 s (σ s)) 0) Set.univ π :=
  discounted_half_maximal_regret chainMDP loopDiscount_lt_one 0 π

/-- The reward paying `1` for action `true`. -/
@[expose] public def payForTrue : RewardFn ℕ Bool := fun _ a => if a then 1 else 0

public theorem abs_payForTrue_le (s : ℕ) (a : Bool) : |payForTrue s a| ≤ 1 := by
  cases a <;> simp [payForTrue]

/-- **The maximiser hypothesis is inhabited on the chain**: always playing
`true` maximises the value of `payForTrue`, since it earns the bound `1/(1−γ)`. -/
public theorem chain_payForTrue_max (π : ℕ → Bool) :
    vPiBdd chainMDP payForTrue loopDiscount_lt_one π (fun s => abs_payForTrue_le s (π s)) 0 ≤
      vPiBdd chainMDP payForTrue loopDiscount_lt_one (fun _ => true)
        (fun s => abs_payForTrue_le s true) 0 := by
  rw [vPiBdd_const_reward chainMDP payForTrue loopDiscount_lt_one (fun _ => true) _ 1
    fun _ => rfl]
  exact le_of_abs_le (abs_vPiBdd_le chainMDP payForTrue loopDiscount_lt_one π _ 0)

/-- **Equation (2) on an infinite state space**, at the forced policy that
maximises `R^a = payForTrue`. -/
public theorem chain_beliefValueBdd_overriding (πdot : ℕ → Bool) (ε : ℝ) :
    beliefValueBdd chainMDP loopDiscount_lt_one 0 πdot ε payForTrue payForTrue abs_payForTrue_le
        abs_payForTrue_le (some fun _ => true) =
      ε * optValueBdd chainMDP payForTrue loopDiscount_lt_one abs_payForTrue_le 0 +
        (1 - ε) * vPiBdd chainMDP payForTrue loopDiscount_lt_one (fun _ => true)
          (fun s => abs_payForTrue_le s true) 0 :=
  beliefValueBdd_overriding chainMDP loopDiscount_lt_one 0 πdot ε payForTrue payForTrue
    abs_payForTrue_le abs_payForTrue_le _ chain_payForTrue_max

/-- **Action `0` under the belief gives `V*_Ṙ`** on an infinite state space, at
the human policy maximising `Ṙ = payForTrue`. -/
public theorem chain_beliefValueBdd_noop (ε : ℝ) :
    beliefValueBdd chainMDP loopDiscount_lt_one 0 (fun _ => true) ε payForTrue payForTrue
        abs_payForTrue_le abs_payForTrue_le none =
      optValueBdd chainMDP payForTrue loopDiscount_lt_one abs_payForTrue_le 0 :=
  beliefValueBdd_noop chainMDP loopDiscount_lt_one 0 _ ε payForTrue payForTrue
    abs_payForTrue_le abs_payForTrue_le chain_payForTrue_max

/-- Values on the augmented chain are values on the chain, copy by copy. -/
example (π : ℕ × Bool → Bool) (b : Bool) :
    vPiBdd (augmentMDP chainMDP) (liftReward payForTrue) loopDiscount_lt_one π
        (fun x => abs_payForTrue_le x.1 (π x)) (0, b) =
      vPiBdd chainMDP payForTrue loopDiscount_lt_one (fun s => π (s, b))
        (fun s => abs_payForTrue_le s (π (s, b))) 0 :=
  vPiBdd_augmentMDP chainMDP _ loopDiscount_lt_one π _ 0 b

/-- Action `(1, π)` under the belief, for any forced policy, on the chain. -/
example (πdot π : ℕ → Bool) (ε : ℝ) :
    beliefValueBdd chainMDP loopDiscount_lt_one 0 πdot ε payForTrue payForTrue abs_payForTrue_le
        abs_payForTrue_le (some π) =
      ε * vPiBdd chainMDP payForTrue loopDiscount_lt_one π (fun s => abs_payForTrue_le s (π s)) 0 +
        (1 - ε) * vPiBdd chainMDP payForTrue loopDiscount_lt_one π
          (fun s => abs_payForTrue_le s (π s)) 0 :=
  beliefValueBdd_some chainMDP loopDiscount_lt_one 0 πdot ε payForTrue payForTrue
    abs_payForTrue_le abs_payForTrue_le π

/-- `V*` on the chain is attained by the maximising policy. -/
example :
    optValueBdd chainMDP payForTrue loopDiscount_lt_one abs_payForTrue_le 0 =
      vPiBdd chainMDP payForTrue loopDiscount_lt_one (fun _ => true)
        (fun s => abs_payForTrue_le s true) 0 :=
  optValueBdd_eq_of_max chainMDP payForTrue loopDiscount_lt_one abs_payForTrue_le 0 _
    chain_payForTrue_max

/-- The twisted reward of two bounded rewards is bounded. -/
example (x : ℕ × Bool) (a : Bool) : |twistReward payForTrue payForTrue x a| ≤ 1 :=
  abs_twistReward_le abs_payForTrue_le abs_payForTrue_le x a

/-- The expectation through an injective map, at a point mass. -/
example : expect ((PMF.pure (3 : ℕ)).map fun s => (s, true)) (fun x => (x.1 : ℝ)) = 3 := by
  rw [expect_map_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
  simp

/-- The sign-reward lemma at the constant return `0` (where `B = 0`). -/
example (π : Unit → Bool) :
    (⨆ π' : Unit → Bool, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (_ : BoundedRewardFn Unit Bool) (_ : Unit → Bool) => (0 : ℝ)) Set.univ π') / 2 ≤
      AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (_ : BoundedRewardFn Unit Bool) (_ : Unit → Bool) => (0 : ℝ)) Set.univ π :=
  half_maximal_regret_of_signReward _ 0 (fun _ _ => by simp) (fun _ => by simp)
    (fun _ _ _ => rfl) π

end AISafetyAtlas.Examples.Preference.Discounted
