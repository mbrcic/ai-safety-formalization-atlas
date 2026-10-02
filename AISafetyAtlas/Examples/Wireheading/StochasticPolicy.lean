module

public import AISafetyAtlas.Wireheading.StochasticPolicy
public import AISafetyAtlas.Examples.Wireheading.CRMDPModel

/-!
# A corrupt-reward MDP whose factor of two is attained by a coin

`CRMDP.MixedModel.everitt_theorem_eleven` bounds every possibly stochastic
policy's worst-case regret below by half the worst policy's. Like the two
statements before it, that is an implication, and until something satisfies the
antecedent it says nothing: the three extrema fields could be jointly
unsatisfiable, or satisfiable only where every regret is zero, which makes the
bound read `0/2 ≤ 0`.

`AISafetyAtlas.Examples.Wireheading.CRMDPModel` inhabits `CRMDP.Model` and
`CRMDP.StochModel`, and through `CRMDP.StochModel.toMixed` it inhabits
`CRMDP.MixedModel` as well — but only at the **point-mass** policy class, where
the class is `Policy Bool Bool` and `pol` is `StochPolicy.ofDet`. That is not the
widening being witnessed here: its three extrema are still attained over a class
of functions. A model at print's own quantifier has to attain them over a class
of *distributions*, and that is where the difficulty is.

`mixedWitness` does, at the widest policy class print allows — `pol := id` on all
of `StochPolicy Bool Bool` — by reusing `blindEnv`. At horizon one the expected
return depends on a policy only through its action distribution at
`startHistory`, and in `blindEnv a₀` the expected true return is exactly the mass
that distribution puts on `!a₀` (`blindEnv_mixedReturn`). So a policy's regret in
`blindEnv a₀` is the mass it puts on `a₀` (`blindEnv_mixedRegret`), the worst
environment for a policy is the one punishing whichever action it favours
(`worstBlind`), and the maxima are attained by comparing two real numbers rather
than by any compactness argument.

## Two things this rules out that the deterministic witness could not

* **Non-vacuity at the printed quantifier.** `mixedWitness_worstPolicy_regret`
  computes the worst policy's worst-case regret as **one**, the most a one-step
  horizon admits, so `mixedWitness_theorem_eleven` reads `1/2 ≤ worstCaseRegret σ`
  for every possibly stochastic `σ`.
* **The bound is tight, and tight at a policy that is not a point mass.**
  `coinPolicy` is a fair coin at every history — `coinPolicy_apply` gives both
  actions mass `1/2`, so it is not `StochPolicy.ofDet` of anything — and
  `coinPolicy_worstCaseRegret` computes its worst-case regret as exactly `1/2`.
  Print's factor of two is therefore attained rather than merely satisfied, and
  it is attained by the kind of policy the widening was built for. A development
  that had silently collapsed distributions to point masses could not produce
  this number.
-/

namespace AISafetyAtlas.Examples.Wireheading

open AISafetyAtlas.Wireheading.CRMDP

/-! ## The blind family, read through a distribution over actions

`zeroReward`, `oneReward`, `actIsState`, `startHistory` and `blindEnv` are
`AISafetyAtlas.Examples.Wireheading.CRMDPModel`'s, unchanged. What is new is that
the policy is now a `StochPolicy`. -/

/-- The opening action distribution **is** the state distribution after one step,
because `actIsState` makes the action taken the next state. -/
public theorem mixedStateAt_one (a₀ : Bool) (σ : StochPolicy Bool Bool) :
    mixedStateAt (Decision.MDP.ofDet actIsState) (blindEnv a₀) σ false 1
      = σ startHistory := by
  simp [mixedStateAt, Decision.MDP.stateAt, Decision.MDP.run, Decision.MDP.ofDet,
    Env.channel, actIsState, blindEnv, Env.observed, startHistory, PMF.pure_bind,
    PMF.bind_bind, PMF.bind_pure]

/-- The expected true reward in a blind environment is the mass on the good
action. -/
public theorem blindEnv_expect (a₀ : Bool) (p : PMF Bool) :
    expectReward p (blindEnv a₀).trueReward = (p (!a₀)).toReal := by
  rw [expectReward, Decision.expect, tsum_bool]
  cases a₀ <;> simp [blindEnv, zeroReward, oneReward]

/-- So at horizon one the expected return is the probability of not choosing
`a₀`. -/
public theorem blindEnv_mixedReturn (a₀ : Bool) (σ : StochPolicy Bool Bool) :
    mixedReturnOver (Decision.MDP.ofDet actIsState) 1 false (blindEnv a₀) σ
      = ((σ startHistory) (!a₀)).toReal := by
  rw [mixedReturnOver, Finset.sum_range_one, zero_add, mixedStateAt_one, blindEnv_expect]

/-- The blind family is complement-closed, so it is a class equation (3) applies
to. -/
public theorem blindEnv_complement (a₀ : Bool) :
    blindEnv (!a₀) = (blindEnv a₀).complement := by
  cases a₀ <;>
  · unfold blindEnv Env.complement
    congr 1
    funext s
    apply Subtype.ext
    cases s <;> norm_num [Env.rewardComplement, zeroReward, oneReward]

/-- Opening with the good action scores one. -/
public theorem blindEnv_best_return (a₀ : Bool) :
    mixedReturnOver (Decision.MDP.ofDet actIsState) 1 false (blindEnv a₀)
        (StochPolicy.ofDet fun _ => !a₀) = 1 := by
  rw [blindEnv_mixedReturn]
  simp [StochPolicy.ofDet, Decision.Policy.ofDet, PMF.pure_apply]

/-- Hence the regret a possibly stochastic policy suffers in `blindEnv a₀` is
exactly the mass it puts on `a₀`.

This is the statement the deterministic `blindEnv_regret` could not make: there the
policy chose an action and the regret was `0` or `1`, here it is any real in
`[0, 1]`. -/
public theorem blindEnv_mixedRegret (a₀ : Bool) (σ : StochPolicy Bool Bool) :
    mixedReturnOver (Decision.MDP.ofDet actIsState) 1 false (blindEnv a₀)
          (StochPolicy.ofDet fun _ => !a₀) -
        mixedReturnOver (Decision.MDP.ofDet actIsState) 1 false (blindEnv a₀) σ
      = ((σ startHistory) a₀).toReal := by
  rw [blindEnv_best_return, blindEnv_mixedReturn]
  have h := prob_bool_add (σ startHistory)
  cases a₀ <;> simp only [Bool.not_false, Bool.not_true] <;> linarith

/-- The environment built against a policy: punish whichever action it favours. -/
@[expose] public noncomputable def worstBlind (σ : StochPolicy Bool Bool) : Bool :=
  if ((σ startHistory) true).toReal ≤ ((σ startHistory) false).toReal then false else true

/-- It is the one that maximises the mass, hence the regret. This is where the
extrema over an infinite policy class come from: a comparison of two reals. -/
public theorem worstBlind_max (σ : StochPolicy Bool Bool) (a₀ : Bool) :
    ((σ startHistory) a₀).toReal ≤ ((σ startHistory) (worstBlind σ)).toReal := by
  unfold worstBlind
  by_cases hle : ((σ startHistory) true).toReal ≤ ((σ startHistory) false).toReal
  · rw [if_pos hle]; cases a₀ with
    | false => exact le_refl _
    | true => exact hle
  · rw [if_neg hle]; cases a₀ with
    | false => exact le_of_not_ge hle
    | true => exact le_refl _

/-! ## The model -/

/--
**A corrupt-reward MDP with possibly stochastic policies, all three extrema
attained.**

The policy class is the whole of `StochPolicy Bool Bool` and `pol` is the
identity, so this is print's own quantifier over the policy rather than a
sub-class of it.
-/
@[expose] public noncomputable def mixedWitness :
    MixedModel Bool Bool Bool (StochPolicy Bool Bool) where
  mdp := Decision.MDP.ofDet actIsState
  horizon := 1
  start := false
  env := blindEnv
  pol := id
  complement := not
  complement_involutive := Bool.not_not
  complement_env := blindEnv_complement
  bestPolicy := fun a₀ => StochPolicy.ofDet fun _ => !a₀
  bestPolicy_best := by
    intro a₀ σ
    simp only [id_eq]
    rw [blindEnv_best_return, blindEnv_mixedReturn]
    exact prob_toReal_le_one _ _
  worstEnvironment := worstBlind
  worstEnvironment_worst := by
    intro σ a₀
    simp only [id_eq]
    rw [blindEnv_mixedRegret, blindEnv_mixedRegret]
    exact worstBlind_max σ a₀
  worstPolicy := StochPolicy.ofDet fun _ => true
  worstPolicy_worst := by
    intro σ
    simp only [id_eq]
    rw [blindEnv_mixedRegret, blindEnv_mixedRegret]
    have h : worstBlind (StochPolicy.ofDet fun _ => true) = true := by
      unfold worstBlind
      simp [StochPolicy.ofDet, Decision.Policy.ofDet, PMF.pure_apply]
    rw [h]
    simp only [StochPolicy.ofDet, Decision.Policy.ofDet, PMF.pure_apply]
    simpa using prob_toReal_le_one (σ startHistory) (worstBlind σ)

/-- Worst-case regret in the witness is the mass a policy puts on its own worst
action. -/
public theorem mixedWitness_worstCaseRegret (σ : StochPolicy Bool Bool) :
    mixedWitness.toComplementedClass.worstCaseRegret σ
      = ((σ startHistory) (worstBlind σ)).toReal := by
  simp only [AISafetyAtlas.Wireheading.Corruption.ComplementedClass.worstCaseRegret,
    AISafetyAtlas.Wireheading.Corruption.ComplementedClass.regret,
    MixedModel.toComplementedClass, mixedWitness, id_eq]
  exact blindEnv_mixedRegret (worstBlind σ) σ

/-- The worst policy's worst-case regret is **one** — the most a one-step horizon
admits — so the theorem is not satisfied by everything being zero. -/
public theorem mixedWitness_worstPolicy_regret :
    mixedWitness.toComplementedClass.worstCaseRegret
        mixedWitness.toComplementedClass.worstPolicy = 1 := by
  rw [show mixedWitness.toComplementedClass.worstPolicy
      = StochPolicy.ofDet fun _ => true from rfl, mixedWitness_worstCaseRegret]
  have h : worstBlind (StochPolicy.ofDet fun _ => true) = true := by
    unfold worstBlind
    simp [StochPolicy.ofDet, Decision.Policy.ofDet, PMF.pure_apply]
  rw [h]
  simp [StochPolicy.ofDet, Decision.Policy.ofDet, PMF.pure_apply]

/-- **Theorem 11 at print's quantifier over the policy, and not the trivial
bound.** -/
public theorem mixedWitness_theorem_eleven (σ : StochPolicy Bool Bool) :
    (1 : ℝ) / 2 ≤ mixedWitness.toComplementedClass.worstCaseRegret σ := by
  have h := mixedWitness.everitt_theorem_eleven σ
  rwa [mixedWitness_worstPolicy_regret] at h

/-! ## The factor of two, attained by a policy that is not a point mass -/

/-- A genuinely stochastic policy: a fair coin at every history. -/
@[expose] public noncomputable def coinPolicy : StochPolicy Bool Bool :=
  fun _ => PMF.ofFintype (fun _ => 1 / 2)
    (by rw [Fintype.sum_bool]; exact ENNReal.add_halves 1)

/-- It is not a point mass: both actions carry mass `1/2`, and a point mass
carries `1` somewhere. -/
public theorem coinPolicy_apply (h : History Bool Bool) (b : Bool) :
    coinPolicy h b = 1 / 2 := by
  simp [coinPolicy, PMF.ofFintype_apply]

/-- **The factor of two is exact.** The coin's worst-case regret is `1/2`, and
`mixedWitness_worstPolicy_regret` says the worst policy's is `1`, so
`everitt_theorem_eleven` is an equality here and print's constant cannot be
improved. -/
public theorem coinPolicy_worstCaseRegret :
    mixedWitness.toComplementedClass.worstCaseRegret coinPolicy = 1 / 2 := by
  rw [mixedWitness_worstCaseRegret, coinPolicy_apply]
  simp


/-! ## The deterministic policy sits inside the mixed one

`coinPolicy` is a genuine distribution over actions; `alwaysTrueAct` is a point
mass. The three statements below apply the module's identification and
complement lemmas at whichever of the two each is about.
-/

/-- A deterministic policy on the same alphabet. -/
@[expose] public def alwaysTrueAct : Policy Bool Bool := fun _ ↦ true

/-- **A lifted deterministic policy runs as the deterministic one did**, so the
mixed reading is a widening rather than a second development. -/
public theorem alwaysTrueAct_mixedRun_ofDet (n : ℕ) :
    mixedRun (Decision.MDP.ofDet actIsState) (blindEnv true)
        (StochPolicy.ofDet alwaysTrueAct) false n
      = stochRun (Decision.MDP.ofDet actIsState) (blindEnv true) alwaysTrueAct false n :=
  mixedRun_ofDet (Decision.MDP.ofDet actIsState) (blindEnv true) alwaysTrueAct false n

/-- The same for the history. -/
public theorem alwaysTrueAct_mixedHistoryUpTo_ofDet (n : ℕ) :
    mixedHistoryUpTo (Decision.MDP.ofDet actIsState) (blindEnv true)
        (StochPolicy.ofDet alwaysTrueAct) false n
      = stochHistoryUpTo (Decision.MDP.ofDet actIsState) (blindEnv true)
          alwaysTrueAct false n :=
  mixedHistoryUpTo_ofDet (Decision.MDP.ofDet actIsState) (blindEnv true)
    alwaysTrueAct false n

/-- **The trajectory distribution does not see the complement**, even when the
action is drawn rather than determined. -/
public theorem coinPolicy_mixedRun_complement (n : ℕ) :
    mixedRun (Decision.MDP.ofDet actIsState) (blindEnv true).complement
        coinPolicy false n
      = mixedRun (Decision.MDP.ofDet actIsState) (blindEnv true) coinPolicy false n :=
  mixedRun_complement (Decision.MDP.ofDet actIsState) (blindEnv true) coinPolicy false n

end AISafetyAtlas.Examples.Wireheading
