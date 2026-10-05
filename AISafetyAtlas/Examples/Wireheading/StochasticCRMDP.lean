module

public import AISafetyAtlas.Wireheading.StochasticCRMDP
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The stochastic run, on a coin flip

`stochRun_ofDet` says the widening loses nothing. It does not say the widening
gains anything: an implication from point masses to point masses would be
satisfied by a definition that quietly ignored the distribution.

This file rules that out. `coinMDP` sends every state to a genuine
two-point distribution, and `coinStateAt_one_apply` shows both successor states
carry probability `1/2` — so the trajectory distribution is not a point mass, and
`stochRun` really does track the randomness rather than collapsing it.
-/

namespace AISafetyAtlas.Examples.Wireheading

open AISafetyAtlas.Wireheading.CRMDP

/-- A rewardless Markov decision process whose transition ignores the action and
flips a fair coin over `Bool`. -/
@[expose] public noncomputable def coinMDP : Decision.MDP Bool Unit :=
  ⟨fun _ _ => PMF.ofFintype (fun _ => 1 / 2)
    (by rw [Fintype.sum_bool]; exact ENNReal.add_halves 1)⟩

/-- An environment whose observed reward is the true one. -/
@[expose] public def plainEnv : Env Bool where
  trueReward := fun _ => ⟨0, by norm_num, by norm_num⟩
  corruption := fun _ r => r

/-- The only policy on a one-action alphabet. -/
@[expose] public def onlyPolicy : Policy Bool Unit := fun _ => ()

/-- **The coin is not lost.** After one step both successor states carry
probability `1/2`, so the state distribution is not concentrated anywhere. -/
public theorem coinStateAt_one_apply (b : Bool) :
    stochStateAt coinMDP plainEnv onlyPolicy false 1 b = 1 / 2 := by
  simp [stochStateAt, Decision.MDP.stateAt, Decision.MDP.run, Decision.Policy.ofDet,
    Env.channel, coinMDP, PMF.pure_bind]


/-! ## The deterministic case sits inside the stochastic one

`coinMDP` is genuinely stochastic; `flipStep` is not. The four statements below
apply the module's identification and complement lemmas at whichever of the two
each one is about.
-/

/-- A deterministic transition on the same state and action alphabet. -/
@[expose] public def flipStep : Bool → Unit → Bool := fun b _ ↦ !b

/-- **A lifted deterministic transition runs as a point mass**, so nothing is
lost in the embedding. -/
public theorem flipStep_stochRun_ofDet (n : ℕ) :
    stochRun (Decision.MDP.ofDet flipStep) plainEnv onlyPolicy false n
      = PMF.pure (run flipStep plainEnv onlyPolicy false n) :=
  stochRun_ofDet flipStep plainEnv onlyPolicy false n

/-- The same for the history. -/
public theorem flipStep_stochHistoryUpTo_ofDet (n : ℕ) :
    stochHistoryUpTo (Decision.MDP.ofDet flipStep) plainEnv onlyPolicy false n
      = PMF.pure (historyUpTo flipStep plainEnv onlyPolicy false n) :=
  stochHistoryUpTo_ofDet flipStep plainEnv onlyPolicy false n

/-- **The trajectory distribution does not see the complement**, at the coin. -/
public theorem coin_stochRun_complement (n : ℕ) :
    stochRun coinMDP plainEnv.complement onlyPolicy false n
      = stochRun coinMDP plainEnv onlyPolicy false n :=
  stochRun_complement coinMDP plainEnv onlyPolicy false n

/-- **Print's equation (3) under stochastic dynamics**: an environment and its
complement split the horizon, the returns now being expectations. -/
public theorem coin_stochReturn_add_complement (t : ℕ) :
    stochReturnOver coinMDP t false plainEnv onlyPolicy
      + stochReturnOver coinMDP t false plainEnv.complement onlyPolicy = (t : ℝ) :=
  stochReturn_add_complement coinMDP t false plainEnv onlyPolicy

end AISafetyAtlas.Examples.Wireheading
