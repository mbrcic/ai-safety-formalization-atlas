module

import AISafetyAtlas.Wireheading.RewardGrid

/-!
# The half-maximal bound, on a grid class where it is about something

`Wireheading.RewardGrid` proves Everitt et al.'s Theorem 11 over print's own
hypothesis class, with the three extrema derived from finiteness rather than
assumed. A no-free-lunch bound is worthless if the quantity it bounds is zero,
and `Corruption.ComplementedClass.everitt_theorem_eleven` would read
`0 / 2 ≤ 0` on a class where no policy ever regrets anything. This file rules
that out on the smallest instance of print's setting.

## The instance

`m = 0`, so the grid is `{0, 1}` — print's `n = 2`, `r₁ = 0 < r₂ = 1`, the
smallest uniform discretisation there is. Two states, two actions, the
transition `s, a ↦ a`, horizon `1`, start state `false`.

`binaryEnv` is the wireheading environment: the true reward is `1` only in the
`true` state, and the corruption channel reports `1` everywhere regardless. It
is in the class by construction — the class is the full product of the two
function spaces — which is exactly print's "the hypothesis classes contain all
functions".

The maximal worst-case regret on this class is at least `1`, so the printed
bound is a statement about a nonzero quantity.
-/

namespace AISafetyAtlas.Examples.Wireheading.RewardGrid

open AISafetyAtlas.Wireheading.CRMDP
open AISafetyAtlas.Wireheading.RewardGrid

/-! ## Print's sentence about the grid, at the smallest instance -/

example : (gridVal 0 0 : ℝ) = 0 := gridVal_zero

example : (gridVal 0 (Fin.last 1) : ℝ) = 1 := gridVal_last

/-- The grid is closed under complementation, which is what the uniformity of
the discretisation buys. -/
example (i : Fin 2) :
    gridVal 0 (gridRev 0 i) = Env.rewardComplement (gridVal 0 i) :=
  gridVal_gridRev i

/-! ## The instance -/

private def step : Bool → Bool → Bool := fun _ a => a

private def alwaysFalse : Policy Bool Bool := fun _ => false

private def alwaysTrue : Policy Bool Bool := fun _ => true

/-- The wireheading environment: true reward `1` only in the `true` state, and a
channel that reports `1` whatever the true reward is. -/
private def binaryEnv : GridEnv 0 Bool where
  trueReward := fun s => if s then 1 else 0
  corruption := fun _ _ => 1

/-- Its complement is in the class too — no side condition, because the class is
the full product. -/
example : GridEnv 0 Bool := binaryEnv.complement

example : binaryEnv.complement.complement = binaryEnv :=
  GridEnv.complement_involutive binaryEnv

/-- Indistinguishability inside the finite class: the channel cannot tell the
two apart. -/
example (s : Bool) : binaryEnv.complement.observed s = binaryEnv.observed s :=
  GridEnv.observed_complement binaryEnv s

/-! ## Two computed returns -/

theorem return_alwaysTrue :
    gridReturn step 1 false binaryEnv alwaysTrue = 1 := by
  unfold gridReturn returnOver
  rw [Finset.sum_range_one]
  show ((gridVal 0 (binaryEnv.trueReward true) : Reward) : ℝ) = 1
  norm_num [binaryEnv, gridVal]

theorem return_alwaysFalse :
    gridReturn step 1 false binaryEnv alwaysFalse = 0 := by
  unfold gridReturn returnOver
  rw [Finset.sum_range_one]
  show ((gridVal 0 (binaryEnv.trueReward false) : Reward) : ℝ) = 0
  norm_num [binaryEnv, gridVal]

/-! ## The bound is about something

The chain is: an explicit policy beats `alwaysFalse` in `binaryEnv` by `1`, so
the derived optimal policy does at least as well; hence the regret of
`alwaysFalse` in that one environment is at least `1`; hence its worst-case
regret over the class is at least `1`; hence the maximum worst-case regret is at
least `1`. None of the four steps evaluates a choice-defined object — each uses
the optimality property that defines it.
-/

theorem one_le_regret_alwaysFalse :
    1 ≤ gridRegret 0 step 1 false binaryEnv alwaysFalse := by
  have hbest :
      gridReturn step 1 false binaryEnv alwaysTrue ≤
        gridReturn step 1 false binaryEnv
          (bestPolicy 0 step 1 false binaryEnv) :=
    AISafetyAtlas.Wireheading.RewardGrid.bestPolicy_best 0 step 1 false binaryEnv alwaysTrue
  rw [return_alwaysTrue] at hbest
  unfold gridRegret
  rw [return_alwaysFalse]
  linarith

theorem one_le_worstCaseRegret_alwaysFalse :
    1 ≤ (toComplementedClass 0 step 1 false).worstCaseRegret alwaysFalse := by
  have h := AISafetyAtlas.Wireheading.RewardGrid.worstEnvironment_worst 0 step 1 false alwaysFalse binaryEnv
  have h2 := one_le_regret_alwaysFalse
  exact le_trans h2 h

/-- **The maximal worst-case regret on print's class is at least `1`**, so the
half-maximal bound is not a statement about zero. -/
theorem one_le_maximal_worstCaseRegret :
    1 ≤ (toComplementedClass 0 step 1 false).worstCaseRegret
      (toComplementedClass 0 step 1 false).worstPolicy := by
  have h := AISafetyAtlas.Wireheading.RewardGrid.worstPolicy_worst 0 step 1 false alwaysFalse
  exact le_trans one_le_worstCaseRegret_alwaysFalse h

/-- Theorem 11 on this instance, with a right-hand side at least `1/2`. -/
example (π : Policy Bool Bool) :
    (toComplementedClass 0 step 1 false).worstCaseRegret
        (toComplementedClass 0 step 1 false).worstPolicy / 2 ≤
      (toComplementedClass 0 step 1 false).worstCaseRegret π :=
  everitt_theorem_eleven_gridClass 0 step 1 false π

/-- And therefore every policy on this class regrets at least `1/2`: the bound
transfers a nonzero quantity, which is the whole content of a no-free-lunch
theorem. -/
theorem every_policy_regrets (π : Policy Bool Bool) :
    (1 : ℝ) / 2 ≤ (toComplementedClass 0 step 1 false).worstCaseRegret π := by
  have hbound := everitt_theorem_eleven_gridClass 0 step 1 false π
  have hmax := one_le_maximal_worstCaseRegret
  linarith

/-! ## The rest of print's grid statements, at this same instance

The embedding lemmas and print's equation (3) are applied here at `binaryEnv`,
so that each one has a grid environment where its hypotheses hold.
-/

/-- The embedded true reward is the grid true reward read on the grid. -/
theorem binaryEnv_toEnv_trueReward (s : Bool) :
    (toEnv binaryEnv).trueReward s = gridVal 0 (binaryEnv.trueReward s) :=
  AISafetyAtlas.Wireheading.RewardGrid.toEnv_trueReward binaryEnv s

/-- **A run sees the environment only through its observed reward**, and
`binaryEnv` and its complement have the same one -- which is what makes the
class indistinguishable from inside a rollout, not merely at a single state. -/
theorem run_binaryEnv_complement (pi : Policy Bool Bool) (n : Nat) :
    run step (toEnv binaryEnv.complement) pi false n
      = run step (toEnv binaryEnv) pi false n :=
  AISafetyAtlas.Wireheading.RewardGrid.run_congr_observed step _ _ pi false
    (fun s => by
      rw [toEnv_observed, toEnv_observed, GridEnv.observed_complement]) n

/-- **Print's equation (3) at this instance**: an environment and its complement
split the horizon between them, whatever the policy does. -/
theorem binaryEnv_return_add_complement (pi : Policy Bool Bool) :
    gridReturn step 1 false binaryEnv pi
        + gridReturn step 1 false binaryEnv.complement pi = (1 : Real) := by
  simpa using AISafetyAtlas.Wireheading.RewardGrid.gridReturn_add_complement step 1 false binaryEnv pi

/-- The half-maximal certificate itself, as a `Preference.HalfMaximalRegretBound`
on this class -- the packaged form of what `every_policy_regrets` uses pointwise. -/
theorem binaryClass_halfMaximalRegretBound :
    AISafetyAtlas.Preference.HalfMaximalRegretBound
      (toComplementedClass 0 step 1 false).toRegretModel :=
  AISafetyAtlas.Wireheading.RewardGrid.halfMaximalRegretBound 0 step 1 false

/-! ## What is not shown

Nothing here is a stochastic CRMDP. The transition is a function and the return
is a sum, as everywhere in this cluster, so this instance witnesses the
deterministic case of print's setting and not print's setting.
-/

/-! ## Definition 9's transition product, where it is not a singleton

`toComplementedClass` fixes one transition. Print's Definition 9 takes a product
over a given set of them, and `toFullComplementedClass` renders that. Here the
given set has two elements, so the `T`-component of the class is genuinely not a
singleton, and the maximum defining `worstCaseRegret` ranges over both.
-/

/-- Two transitions: print's `s, a ↦ a`, and the one that stays put. -/
private def transPair : Bool → (Bool → Bool → Bool)
  | false => step
  | true => fun s _ => s

/-- **The given set really has two elements.** Without this the row below would
be the singleton class again under another name. -/
theorem transPair_ne : transPair false ≠ transPair true := by
  intro h
  have hx := congrFun (congrFun h false) true
  exact absurd hx (by decide)

/-- The wireheading environment, over the first of the two transitions. -/
private def binaryFull : FullEnv 0 Bool Bool :=
  ⟨false, binaryEnv⟩

/-- Regret at that member is print's regret in the fibre it sits in. -/
theorem one_le_fullRegret_binaryFull :
    1 ≤ fullRegret 0 transPair 1 false binaryFull alwaysFalse :=
  one_le_regret_alwaysFalse

/-- So the worst-case regret over the **product** class is at least `1`. -/
theorem one_le_fullClass_worstCaseRegret_alwaysFalse :
    1 ≤ (toFullComplementedClass 0 transPair 1 false).worstCaseRegret alwaysFalse :=
  le_trans one_le_fullRegret_binaryFull
    (AISafetyAtlas.Wireheading.RewardGrid.fullWorstEnv_worst 0 transPair 1 false
      alwaysFalse binaryFull)

/-- **The maximal worst-case regret over print's Definition 9 class is at least
`1`**, transitions included, so the bound below is not about zero. -/
theorem one_le_fullClass_maximal :
    1 ≤ (toFullComplementedClass 0 transPair 1 false).worstCaseRegret
      (toFullComplementedClass 0 transPair 1 false).worstPolicy :=
  le_trans one_le_fullClass_worstCaseRegret_alwaysFalse
    (AISafetyAtlas.Wireheading.RewardGrid.fullWorstPolicy_worst 0 transPair 1 false
      alwaysFalse)

/-- **Theorem 11 over print's Definition 9 class**, with the transition product
non-trivial and the right-hand side at least `1/2`. -/
theorem every_policy_regrets_fullClass (π : Policy Bool Bool) :
    (1 : ℝ) / 2 ≤ (toFullComplementedClass 0 transPair 1 false).worstCaseRegret π := by
  have hbound :=
    AISafetyAtlas.Wireheading.RewardGrid.everitt_theorem_eleven_fullClass
      0 transPair 1 false π
  have hmax := one_le_fullClass_maximal
  linarith

/-! ## Theorem 11 with drawn dynamics, at this same instance

`everitt_theorem_eleven_stochGridClass` carries three of the row's four axes at
once: print's class, all three extrema derived, and a transition that may be a
distribution. Here it is at the two-state instance, with the transition the point
mass at `step`, so the drawn statement and the determined one are about the same
dynamics.
-/

/-- The two-state dynamics, read as a Markov decision process. -/
private noncomputable def stepMDP : Decision.MDP Bool Bool :=
  Decision.MDP.ofDet step

/-- The expected return at a point-mass transition is the determined return, so
this instance is the deterministic one seen through the drawn statement. -/
theorem stochReturnOver_stepMDP (g : GridEnv 0 Bool) (π : Policy Bool Bool) :
    stochReturnOver stepMDP 1 false (toEnv g) π = gridReturn step 1 false g π :=
  stochReturnOver_ofDet step 1 false (toEnv g) π

/-- **Theorem 11 over print's class with drawn dynamics**, at this instance. -/
theorem every_policy_regrets_stochGridClass (π : Policy Bool Bool) :
    (toStochComplementedClass 0 stepMDP 1 false).worstCaseRegret
        (toStochComplementedClass 0 stepMDP 1 false).worstPolicy / 2 ≤
      (toStochComplementedClass 0 stepMDP 1 false).worstCaseRegret π :=
  everitt_theorem_eleven_stochGridClass 0 stepMDP 1 false π

/-! ## Theorem 11 at every printed axis, and at a policy that really is mixed

`everitt_theorem_eleven_mixedGridClass` carries all four axes of the printed
statement: print's class, all three extrema derived, a drawn transition, and a
possibly stochastic policy. A witness at a point mass would compile and show
nothing, so `fairCoin` below is a genuine coin, and `fairCoin_apply` is what says
so.
-/

/-- A fair coin at every history: not `StochPolicy.ofDet` of anything. -/
private noncomputable def fairCoin : StochPolicy Bool Bool :=
  fun _ => PMF.ofFintype (fun _ => 1 / 2)
    (by rw [Fintype.sum_bool]; exact ENNReal.add_halves 1)

/-- **It is not a point mass**: both actions carry mass `1/2`. -/
theorem fairCoin_apply (h : Decision.History (Obs Bool) Bool) (b : Bool) :
    fairCoin h b = 1 / 2 := by
  simp [fairCoin, PMF.ofFintype_apply]

/-- **Theorem 11 at every printed axis**, on this instance. -/
theorem every_policy_regrets_mixedGridClass (σ : StochPolicy Bool Bool) :
    (toMixedComplementedClass 0 stepMDP 1 false).worstCaseRegret
        (toMixedComplementedClass 0 stepMDP 1 false).worstPolicy / 2 ≤
      (toMixedComplementedClass 0 stepMDP 1 false).worstCaseRegret σ :=
  everitt_theorem_eleven_mixedGridClass 0 stepMDP 1 false σ

/-- And at the coin in particular, which is the case a development that had
collapsed distributions to point masses could not state. -/
theorem fairCoin_regrets :
    (toMixedComplementedClass 0 stepMDP 1 false).worstCaseRegret
        (toMixedComplementedClass 0 stepMDP 1 false).worstPolicy / 2 ≤
      (toMixedComplementedClass 0 stepMDP 1 false).worstCaseRegret fairCoin :=
  every_policy_regrets_mixedGridClass fairCoin

/-! ## And over Definition 9's class, transitions included

Print's Theorem 11 is stated over the class of Definition 9, whose transition
component is a given set. Here that set has two elements, the transition is
drawn, the policy may be a coin, and no extremum is assumed.
-/

/-- The two transitions, read as Markov decision processes. -/
private noncomputable def transPairMDP : Bool → Decision.MDP Bool Bool :=
  fun b => Decision.MDP.ofDet (transPair b)

/-- **Theorem 11 at every axis print states it with**, on this instance. -/
theorem every_policy_regrets_fullMixedClass (σ : StochPolicy Bool Bool) :
    (toFullMixedComplementedClass 0 transPairMDP 1 false).worstCaseRegret
        (toFullMixedComplementedClass 0 transPairMDP 1 false).worstPolicy / 2 ≤
      (toFullMixedComplementedClass 0 transPairMDP 1 false).worstCaseRegret σ :=
  everitt_theorem_eleven_fullMixedClass 0 transPairMDP 1 false σ

/-- And at the coin, over a transition set that is not a singleton: every axis of
the printed statement is non-degenerate at once here. -/
theorem fairCoin_regrets_fullMixedClass :
    (toFullMixedComplementedClass 0 transPairMDP 1 false).worstCaseRegret
        (toFullMixedComplementedClass 0 transPairMDP 1 false).worstPolicy / 2 ≤
      (toFullMixedComplementedClass 0 transPairMDP 1 false).worstCaseRegret fairCoin :=
  every_policy_regrets_fullMixedClass fairCoin

/-- **The determined statement is the degenerate case of the joined one**, here
at the two-element transition set: with a point-mass transition and a point-mass
policy the joined return is the determined return, so
`everitt_theorem_eleven_fullClass` is an instance of the full statement and not a
parallel one. -/
theorem fullMixedReturn_ofDet_transPair (e : FullEnv 0 Bool Bool)
    (π : Policy Bool Bool) :
    fullMixedReturn transPairMDP 1 false e (StochPolicy.ofDet π)
      = fullReturn transPair 1 false e π :=
  fullMixedReturn_ofDet transPair 1 false e π

end AISafetyAtlas.Examples.Wireheading.RewardGrid
