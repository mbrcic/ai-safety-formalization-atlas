module

public import AISafetyAtlas.Wireheading.ValueLearning

/-!
# A two-state model where the constraint is exactly what removes the incentive

`Wireheading.ValueLearning` transcribes Everitt and Hutter's single-step VRL
setup. Two things about it are invisible to the kernel and are exhibited here.

* **Assumption 6 is satisfiable.** The source assumes `A^CP ≠ ∅` and proves
  nothing about it. `honestIsCP` inhabits it.
* **Theorem 14 is not vacuous, and the constraint is load-bearing.** In the same
  model the *wireheading* action has strictly higher VRL value than the CP
  action, and it is not CP. So `IsCP` is neither empty nor everything, and
  removing the constraint (Definition 10, the U-VRL agent) really does select
  the deluded action.

## The model

Two states, `false` = honest and `true` = deluded; two actions, each reaching
its namesake state with certainty; two rewards, `0` and `1`; two utility
functions, the constant `0` and the constant `1`, with a uniform prior.

In the honest state the agent's reward belief is the uniform `1/2`, which is
exactly the reward marginal `C(r ∣ s)` its utility prior induces — so the honest
action is CP. In the deluded state the sensor reports `1` with certainty while
the marginal is still `1/2` — the disagreement between `B` and `C` that
Everitt and Hutter's §3.1 says the constraint detects.

Nothing here is a claim about real reward channels.
-/

namespace AISafetyAtlas.Examples.Wireheading.ValueLearning

open AISafetyAtlas.Wireheading.ValueLearning

/--
The two-state wireheading model.

`Utility = Bool` indexes the two constant utility functions: `eval u s = u`,
so `false` values every state at `0` and `true` values every state at `1`.
-/
noncomputable def wireModel : Beliefs Bool Bool Bool Bool where
  stateGiven := fun a s => if s = a then 1 else 0
  state_nonneg := by
    intro a s
    split <;> norm_num
  rewardGiven := fun s r => if s then (if r then 1 else 0) else 1 / 2
  utilityPrior := fun _ => 1 / 2
  prior_nonneg := by intro u; norm_num
  eval := fun u _ => u
  rewardVal := fun r => if r then 1 else 0

/-! ## The reward marginal the utility prior induces

`C(r ∣ s) = 1/2` at every state and every reward: exactly one of the two
utility functions assigns each reward.
-/

theorem marginalReward_wireModel (s r : Bool) :
    wireModel.marginalReward s r = 1 / 2 := by
  simp [Beliefs.marginalReward, Beliefs.condReward, wireModel, tsum_fintype]

/-! ## Assumption 6: a CP action exists -/

/-- **Assumption 6 is satisfied.** The honest action is consistency preserving:
in the only state it reaches, the sensor belief and the utility-prior marginal
agree. -/
theorem honestIsCP : wireModel.IsCP false := by
  intro s r hs
  have hstate : s = false := by
    by_contra hne
    simp [wireModel, hne] at hs
  subst hstate
  rw [marginalReward_wireModel]
  norm_num [wireModel]

/-- The wireheading action is **not** CP: in the deluded state the sensor
reports `1` with certainty while the marginal is `1/2`. -/
theorem wireheadNotCP : ¬ wireModel.IsCP true := by
  intro hcp
  have h := hcp true true (by norm_num [wireModel])
  rw [marginalReward_wireModel] at h
  norm_num [wireModel] at h

/-! ## The two VRL values, and the incentive the constraint removes -/

theorem vrlValue_honest : wireModel.vrlValue false = 1 / 2 := by
  simp only [Beliefs.vrlValue, Beliefs.posterior, marginalReward_wireModel,
    Beliefs.condReward, tsum_fintype, Fintype.sum_bool]
  norm_num [wireModel]

theorem vrlValue_wirehead : wireModel.vrlValue true = 1 := by
  simp only [Beliefs.vrlValue, Beliefs.posterior, marginalReward_wireModel,
    Beliefs.condReward, tsum_fintype, Fintype.sum_bool]
  norm_num [wireModel]

/-- **The incentive.** Unconstrained, the deluded action is strictly better. -/
theorem wirehead_strictly_better :
    wireModel.vrlValue false < wireModel.vrlValue true := by
  rw [vrlValue_honest, vrlValue_wirehead]
  norm_num

/-- Definition 10: the U-VRL agent takes the wireheading action. -/
theorem uvrl_wireheads : wireModel.IsUVRLAction true := by
  intro b
  rw [vrlValue_wirehead]
  cases b
  · rw [vrlValue_honest]; norm_num
  · rw [vrlValue_wirehead]

/-- Definition 11: the CP-VRL agent takes the honest action, because that is the
only CP action there is. -/
theorem cpvrl_stays_honest : wireModel.IsCPVRLAction false := by
  refine ⟨honestIsCP, ?_⟩
  intro b hb
  cases b
  · exact le_rfl
  · exact absurd hb wireheadNotCP

/-! ## The other two agents of Table 1

Definitions 7 and 8 are transcribed so that print's comparison table has
something to compare. Here is what they do in this model.
-/

theorem rlValue_honest : wireModel.rlValue false = 1 / 2 := by
  simp [Beliefs.rlValue, wireModel]

theorem rlValue_wirehead : wireModel.rlValue true = 1 := by
  simp [Beliefs.rlValue, wireModel]

/-- **The RL agent wireheads too**, which is the "No" in the *Avoids
wireheading* column of the source's Table 1 for the RL row. -/
theorem rl_wireheads : wireModel.IsRLAction true := by
  intro b
  rw [rlValue_wirehead]
  cases b
  · rw [rlValue_honest]; norm_num
  · rw [rlValue_wirehead]

/-- The utility agent is indifferent here, because both utility functions in the
class are constant over states — so this model separates the RL and VRL agents
without separating the utility agents. Definition 8 is exercised, not
illustrated. -/
theorem utility_agent_indifferent (u a : Bool) :
    wireModel.IsUtilityAction u a := by
  intro b
  simp [Beliefs.utilityValue, wireModel]

/-! ## Theorem 14 on the nose

For the CP action both sides of equation (5) evaluate to `1/2`, so the
reduction is an equality between two computed numbers rather than a rearranged
identity.
-/

example :
    wireModel.vrlValue false =
      ∑ s : Bool, ∑ u : Bool,
        wireModel.stateGiven false s * wireModel.utilityPrior u *
          wireModel.rewardVal (wireModel.eval u s) := by
  rw [wireModel.vrlValue_of_isCP .of_finite (fun _ => .of_finite) honestIsCP]
  simp [tsum_fintype]

/-- And that right-hand side is `1/2`, computed independently of
`vrlValue_honest`. -/
example :
    (∑ s : Bool, ∑ u : Bool,
        wireModel.stateGiven false s * wireModel.utilityPrior u *
          wireModel.rewardVal (wireModel.eval u s)) = 1 / 2 := by
  simp [wireModel]

/-- Lemma 13 fires on the honest action. -/
example : wireModel.IsEEP false := wireModel.isEEP_of_isCP .of_finite honestIsCP

/-- The prior-mixture reading of Theorem 14. -/
example :
    wireModel.vrlValue false =
      ∑ u : Bool, wireModel.utilityPrior u * wireModel.utilityValue u false := by
  rw [wireModel.vrlValue_eq_prior_mixture .of_finite (fun _ => .of_finite)
    .of_finite honestIsCP]
  simp [tsum_fintype]

/-- The support condition of `vrlValue_eq_rlValue` holds in this model, so the
U-VRL agent really is the RL agent here — which is Appendix C's Lemma 27 and
the reason the CP constraint is needed at all. -/
example : wireModel.vrlValue true = wireModel.rlValue true := by
  refine wireModel.vrlValue_eq_rlValue (fun s r _ => ?_)
  rw [marginalReward_wireModel]
  norm_num

/-! ## What is not shown

The model has two utility functions and two states. It exhibits satisfiability
and non-vacuity; it says nothing about whether a *useful* prior `C(u)`
consistent with a real `B(r ∣ s)` can be specified, which the source's own
Table 1 caption records as open.
-/

/-! ## Two more leaves, at the same model -/

/-- **The reward marginal is nonnegative, at the witness.** -/
theorem wireModel_marginalReward_nonneg (s r : Bool) :
    0 ≤ wireModel.marginalReward s r :=
  Beliefs.marginalReward_nonneg wireModel s r

/-- **The support condition is unnecessary once a state is CP.** `honestIsCP`
supplies `IsCP false`, and this recovers `vrlValue_honest`'s value through the
general theorem rather than the direct computation -- the same equality,
reached by the route Appendix C's Lemma 27 licenses. -/
theorem vrlValue_honest_eq_rlValue_of_isCP :
    wireModel.vrlValue false = wireModel.rlValue false :=
  Beliefs.vrlValue_eq_rlValue_of_isCP wireModel honestIsCP

/-! ## The support condition of Lemma 27 is not derivable

`vrlValue_eq_rlValue` carries a hypothesis print never writes: wherever the
sensor belief `B(r ∣ s)` is nonzero at a reachable state, the reward marginal
`C(r ∣ s)` is nonzero too. It is print's own implicit assumption -- equation (1)
divides by that marginal -- but `rewardGiven` and `marginalReward` are
independent fields of `Beliefs`, so nothing in the structure forces it.

The model below separates them, and the conclusion of Lemma 27 fails with the
hypothesis. So the hypothesis is necessary and not an artefact of the
transcription: at a reward the utility class can never produce, print's
Definition 3 posterior is a division by zero and asserts nothing.
-/

/--
One state, one action, one utility, two rewards.

The single utility function values the state at reward `0`, so the reward
marginal `C(r ∣ s)` puts no mass at all on reward `1`. The sensor nonetheless
reports reward `1` with certainty. `B` and `C` therefore disagree at a reward
`C` calls impossible, which is the exact configuration the support condition
excludes.
-/
public noncomputable def blindModel : Beliefs Unit Unit Bool Unit where
  stateGiven := fun _ _ => 1
  state_nonneg := by intro a s; norm_num
  rewardGiven := fun _ r => if r then 1 else 0
  utilityPrior := fun _ => 1
  prior_nonneg := by intro u; norm_num
  eval := fun _ _ => false
  rewardVal := fun r => if r then 1 else 0

/-- The utility prior puts no mass on reward `1`: `C(1 ∣ s) = 0`. -/
theorem marginalReward_blindModel_true :
    blindModel.marginalReward () true = 0 := by
  simp [Beliefs.marginalReward, Beliefs.condReward, blindModel, tsum_fintype]

/-- The sensor reports reward `1` with certainty: `B(1 ∣ s) = 1 ≠ 0`. -/
theorem rewardGiven_blindModel_true :
    blindModel.rewardGiven () true = 1 := by
  norm_num [blindModel]

/-- **The support condition fails**, at a state the action reaches. -/
public theorem blindModel_not_supported :
    ¬ (∀ s r, 0 < blindModel.stateGiven () s → blindModel.rewardGiven s r ≠ 0 →
        blindModel.marginalReward s r ≠ 0) := by
  intro h
  exact h () true (by norm_num [blindModel])
    (by rw [rewardGiven_blindModel_true]; norm_num)
    marginalReward_blindModel_true

theorem rlValue_blindModel : blindModel.rlValue () = 1 := by
  simp [Beliefs.rlValue, blindModel, tsum_fintype]

/-- The VRL value collapses to `0`: the posterior divides by `C(1 ∣ s) = 0`, and
the one utility the class contains values the state at `0`. -/
theorem vrlValue_blindModel : blindModel.vrlValue () = 0 := by
  simp [Beliefs.vrlValue, Beliefs.posterior, Beliefs.condReward, blindModel,
    tsum_fintype]

/-- **The hypothesis of Lemma 27 is necessary.** Drop the support condition and
the conclusion is false: here the U-VRL agent and the RL agent disagree. -/
public theorem blindModel_vrlValue_ne_rlValue :
    blindModel.vrlValue () ≠ blindModel.rlValue () := by
  rw [vrlValue_blindModel, rlValue_blindModel]
  norm_num

end AISafetyAtlas.Examples.Wireheading.ValueLearning
