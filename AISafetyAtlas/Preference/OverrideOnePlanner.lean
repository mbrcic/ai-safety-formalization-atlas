module

public import AISafetyAtlas.Preference.Discounted

/-!
# Overriding with one planner across all agent actions (source Appendix B.1)

Armstrong and Mindermann's appendix B fixes one observed human policy π̇' on
the augmented MDP M* and calls a pair (p, R) compatible when p(R) = π̇'.
The agent's actions differ only in where the human starts: action 0 at
ŝ₀ = (ŝ, 0) and (1, Rᵃ) at ŝ₁ = (ŝ, 1). Equation (1) then compares the
values of the one policy π̇' from the actions' start states.

`AISafetyAtlas.Preference.OverrideModel.OverridesFor` asks the pair to explain
the policy each action results in, so compatibility is checked per action. This
module renders the reading in which compatibility is one condition for the
whole run, independent of the action:

* `startRegret` is equation (1) for one observed policy, at any type of
  rewards, policies, start states and agent actions, with the maximum written as
  a supremum (a maximum wherever print has one);
* `OverridesFromStart` is Definition 11 at a compatible pair, with the pair
  explaining the one observed policy;
* `OverridesFromStart.eq_and_exists_lt` is the remark of appendix B.1: after an
  override at a positive threshold the pair still outputs the observed policy,
  and that policy's value from the action's start falls strictly short of its
  value from some other action's start, hence of equation (1)'s maximum.

On M* itself (`Discounted.augValue`, `Discounted.augStart`), at the mixed policy
of π̇ and πᵃ, the values of actions 0 and (1, πᵃ) are those of
`AISafetyAtlas.Preference.Discounted.augActionValue`, and at a reward that
forgets the boolean, with π̇ optimal, the regret is the override model's
(`Discounted.startRegret_liftReward_of_optimal`).

## Scope against print

* **Objects.** Print's rewards are [-1, 1]^{𝒮*×𝒜}, its policies deterministic
  Markov policies on 𝒮*, its agent actions 0 and (1, Rᵃ). Here the general
  layer takes arbitrary types of rewards, policies, start states and actions and
  an arbitrary value function; the M* layer takes any real reward on
  𝒮 × Bool, any observed policy on 𝒮 × Bool (not only a mixed one) and any
  discount below one.
* **High regret.** Print gives no threshold; θ is arbitrary and the remark is
  proved at every θ > 0.
* **The maximum.** Print's max_{b ∈ 𝒜^a} is `sSup` over the actions' values.
  A printed max presupposes attainment (ruling of 2026-11-22, extending R3), so
  only classes where the supremum is attained are print instances; on M* only two
  start states occur and it is attained. The remark itself needs no attainment.
* **Both readings.** The per-action reading is the instance
  `OverrideModel.overridesFor_iff_overridesFromStart`, in which the value ignores
  the observed policy; the one-planner reading is the M* instance.
-/

namespace AISafetyAtlas.Preference

/-! ## The general layer -/

section General

variable {Rw Pol T Act : Type*}

/--
**Equation (1) for one observed policy** (Armstrong and Mindermann, appendix B.1,
amapp-eq1-regret, PDF p. 3: *"Reg(M*, a, Ṙ) = max_{b ∈ 𝒜^a} [V^{π̇'|b}_Ṙ −
V^{π̇'|a}_Ṙ]"*). The value of the one policy π from the start state of action b
is value R π (start b); the maximum over actions is a supremum.
-/
@[expose] public noncomputable def startRegret (value : Rw → Pol → T → ℝ)
    (start : Act → T) (π : Pol) (R : Rw) (a : Act) : ℝ :=
  sSup (Set.range fun b => value R π (start b)) - value R π (start a)

/--
**Definition 11 with one planner for the run** (Armstrong and Mindermann,
appendix B.1, Definition 11, PDF p. 3: *"Given a compatible (p, R), the agent's
action a overrides the human reward function when it puts the human in a
situation where the human policy leads to high regret for R"*). Compatibility
is p(R) = π̇' for the one observed policy, so the first conjunct does not
depend on the action; high regret is regret at least θ.
-/
@[expose] public def OverridesFromStart (value : Rw → Pol → T → ℝ) (start : Act → T)
    (π : Pol) (p : Planner Rw Pol) (R : Rw) (θ : ℝ) (a : Act) : Prop :=
  Explains p R π ∧ θ ≤ startRegret value start π R a

/-- Under a compatible pair, an action overrides exactly when its regret reaches
the threshold: the compatibility condition is the same at every action. -/
public theorem overridesFromStart_iff {value : Rw → Pol → T → ℝ} {start : Act → T}
    {π : Pol} {p : Planner Rw Pol} {R : Rw} (hc : Explains p R π) (θ : ℝ) (a : Act) :
    OverridesFromStart value start π p R θ a ↔ θ ≤ startRegret value start π R a :=
  ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

/--
**Overriding is not a change in p or R** (Armstrong and Mindermann, appendix
B.1, amapp-not-change-in-pr, PDF p. 3: *"Notice that overriding is not encoded
as a change in p or R; instead, (p, R) outputs the observed human policy,
even after overriding, but its format notes that the new behaviour is not one
compatible with maximising that reward function"*). If action a overrides at a
positive threshold, the same pair outputs the observed policy, and that policy's
value from a's start is strictly below equation (1)'s maximum and strictly below
its value from some other action's start.
-/
public theorem OverridesFromStart.eq_and_exists_lt {value : Rw → Pol → T → ℝ}
    {start : Act → T} {π : Pol} {p : Planner Rw Pol} {R : Rw} {θ : ℝ} {a : Act}
    (h : OverridesFromStart value start π p R θ a) (hθ : 0 < θ) :
    p R = π ∧ value R π (start a) < sSup (Set.range fun b => value R π (start b)) ∧
      ∃ b, value R π (start a) < value R π (start b) := by
  obtain ⟨hexp, hreg⟩ := h
  have hlt : value R π (start a) < sSup (Set.range fun b => value R π (start b)) := by
    unfold startRegret at hreg
    linarith
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty_iff_nonempty.mpr ⟨a⟩) hlt
  exact ⟨hexp, hlt, b, hb⟩

end General

/-- **The per-action model is an instance.** Definition 11 relative to a pair that
explains the policy each action results in (`OverrideModel.OverridesFor`) is
`OverridesFromStart` with the actions as start states, the resulting policy of the
action at hand as the observed policy, and a value that reads the resulting policy
of each action instead of the observed one. -/
public theorem OverrideModel.overridesFor_iff_overridesFromStart {S A Act : Type*}
    (M : OverrideModel S A Act) (p : Planner (RewardFn S A) (Policy S A)) (R : RewardFn S A)
    (θ : ℝ) (a : Act) :
    M.OverridesFor p R θ a ↔
      OverridesFromStart (fun R (_ : Policy S A) b => M.value R (M.resulting b)) id
        (M.resulting a) p R θ a := by
  have hmax : sSup (Set.range fun b : Act => M.value R (M.resulting b)) = M.optValue R := by
    refine IsGreatest.csSup_eq ?_
    have h := M.optValue_isGreatest R
    have hset : {v : ℝ | ∃ b : Act, v = M.value R (M.resulting b)} =
        Set.range fun b : Act => M.value R (M.resulting b) := by
      ext v
      simp [eq_comm]
    rwa [hset] at h
  simp only [OverrideModel.OverridesFor, OverridesFromStart, startRegret, id, hmax,
    OverrideModel.regret]

/-! ## The augmented MDP M* -/

namespace Discounted

open AISafetyAtlas.Decision
open scoped NNReal

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **The start state of an agent action on M*** (appendix B, amapp-def-augmented,
PDF p. 2): action 0 (none) starts the human at ŝ₀ = (ŝ, 0), and (1, πᵃ)
(some πᵃ) at ŝ₁ = (ŝ, 1). -/
@[expose] public def augStart (s₀ : S) (a : Option (S → A)) : S × Bool := (s₀, a.isSome)

/-- **The value on M*** of a policy on 𝒮 × Bool for a reward on 𝒮 × Bool,
from a state of M*: `vPi` on `augmentMDP`. -/
@[expose] public noncomputable def augValue (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (r : S × Bool → A → ℝ) (π : S × Bool → A) (x : S × Bool) : ℝ :=
  vPi (augmentMDP M) r hγ π x

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/-- At the mixed policy of π̇ and πᵃ, action 0's value is
`augActionValue`'s. -/
public theorem augValue_mixPolicy_none (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1) (s₀ : S)
    (πdot πa : S → A) (r : S × Bool → A → ℝ) :
    augValue M hγ r (mixPolicy πdot πa) (augStart s₀ (none : Option (S → A))) =
      augActionValue M hγ s₀ πdot r none := by
  simp only [augValue, augStart, augActionValue, Option.isSome_none, Option.getD_none,
    vPi_augmentMDP]
  simp [mixPolicy]

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/-- At the mixed policy of π̇ and πᵃ, the overriding action (1, πᵃ) has
`augActionValue`'s value. -/
public theorem augValue_mixPolicy_some (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1) (s₀ : S)
    (πdot πa : S → A) (r : S × Bool → A → ℝ) :
    augValue M hγ r (mixPolicy πdot πa) (augStart s₀ (some πa)) =
      augActionValue M hγ s₀ πdot r (some πa) := by
  simp [augValue, augStart, augActionValue]

/-- **Appendix B.1's regrets in the one-planner model.** At a reward that forgets
the boolean and an optimal π̇ (print: *"π̇ is optimal with respect to Ṙ"*),
equation (1) for the one mixed policy of π̇ and πᵃ gives actions 0 and
(1, πᵃ) the override model's regrets: 0 and V*_Ṙ − V^{πᵃ}_Ṙ. -/
public theorem startRegret_liftReward_of_optimal (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot πa : S → A) (Rdot : RewardFn S A)
    (hopt : vPi M Rdot hγ πdot s₀ = optValueAt M Rdot hγ s₀) {a : Option (S → A)}
    (ha : a = none ∨ a = some πa) :
    startRegret (augValue M hγ) (augStart s₀) (mixPolicy πdot πa) (liftReward Rdot) a =
      (discountedOverride M hγ s₀ πdot).regret Rdot a := by
  have hval : ∀ b : Option (S → A),
      augValue M hγ (liftReward Rdot) (mixPolicy πdot πa) (augStart s₀ b) =
        vPi M Rdot hγ (if b.isSome then πa else πdot) s₀ := by
    intro b
    cases b <;> simp [augValue, augStart, vPi_augmentMDP, mixPolicy, liftReward]
  have hmax : sSup (Set.range fun b : Option (S → A) =>
      augValue M hγ (liftReward Rdot) (mixPolicy πdot πa) (augStart s₀ b)) =
        optValueAt M Rdot hγ s₀ := by
    refine IsGreatest.csSup_eq ⟨⟨none, by simp only [hval]; exact hopt⟩, ?_⟩
    rintro _ ⟨b, rfl⟩
    simp only [hval]
    exact vPi_le_optValueAt M Rdot hγ s₀ _
  rw [startRegret, hmax, hval]
  rcases ha with rfl | rfl <;> rfl

/-- The same regrets are `augRegret`'s, the regret on M* in which the forced
policy varies with the action. -/
public theorem startRegret_liftReward_eq_augRegret (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot πa : S → A) (Rdot : RewardFn S A)
    (hopt : vPi M Rdot hγ πdot s₀ = optValueAt M Rdot hγ s₀) {a : Option (S → A)}
    (ha : a = none ∨ a = some πa) :
    startRegret (augValue M hγ) (augStart s₀) (mixPolicy πdot πa) (liftReward Rdot) a =
      augRegret M hγ s₀ πdot (liftReward Rdot) a := by
  rw [startRegret_liftReward_of_optimal M hγ s₀ πdot πa Rdot hopt ha, augRegret_eq_regret]

end Discounted

end AISafetyAtlas.Preference
