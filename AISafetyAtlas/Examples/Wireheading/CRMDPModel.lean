module

public import AISafetyAtlas.Wireheading.StochasticCRMDP

/-!
# A corrupt-reward MDP whose worst-case regret is exactly one

`CRMDP.Model.everitt_theorem_eleven` and its stochastic counterpart bound every
policy's worst-case regret below by half the worst policy's. Until now nothing in
the tree inhabited `CRMDP.Model`, so both statements were implications with an
antecedent no witness had ever satisfied. Two things could have gone wrong and
neither would have been visible: the three extrema fields could have been jointly
unsatisfiable, or satisfiable only where every regret is zero, which would make
the bound `0/2 ≤ 0`.

This file rules out both. `witness` is a corrupt-reward MDP over two states and
two actions in which the worst policy's worst-case regret is **one**, the largest
a one-step horizon admits, so Theorem 11 reads `1/2 ≤ worstCaseRegret π` for
every policy. `stochWitness` carries the same numbers to the stochastic model.

## How the extrema are attained

The policy space `History Bool Bool → Bool` is infinite, so the extrema are not
had by finiteness. They are had because at horizon one the return depends on the
policy only through its value at a single history:

* the dynamics `fun _ a => a` make the action taken the next state, so the return
  is the true reward of the action chosen at the start;
* `blindEnv` pins every observed reward to zero, so the start history is the same
  for every environment in that family and a policy cannot vary its opening move
  across it.

`blindEnv a₀` then rewards every state except `a₀`, so the policy that opens with
`a₀` scores `0` where the best policy scores `1`. That is the worst environment
for that policy, and every policy has one.
-/

namespace AISafetyAtlas.Examples.Wireheading

open AISafetyAtlas.Wireheading.CRMDP

/-- The bottom of the reward range. -/
@[expose] public def zeroReward : Reward := ⟨0, by norm_num, by norm_num⟩

/-- The top of the reward range. -/
@[expose] public def oneReward : Reward := ⟨1, by norm_num, by norm_num⟩

/-- Dynamics on two states: the action taken is the next state. -/
@[expose] public def actIsState : Bool → Bool → Bool := fun _ a => a

/-- The start history every `blindEnv` presents: state `false`, reward `0`, no
actions yet. -/
@[expose] public def startHistory : History Bool Bool := ((false, zeroReward), [])

/-- An environment whose corruption channel reports `0` whatever the true reward
is, and whose true reward is `0` at `a₀` and `1` elsewhere.

The blind channel is what makes the family usable: because observed rewards carry
no information, every environment in it presents `startHistory`, so a policy's
opening move is fixed across the family and can be read off before the
environment is chosen. -/
@[expose] public def blindEnv (a₀ : Bool) : Env Bool where
  trueReward := fun s => if s = a₀ then zeroReward else oneReward
  corruption := fun _ _ => zeroReward

/-- Every `blindEnv` observes `0` everywhere. -/
public theorem blindEnv_observed (a₀ : Bool) (s : Bool) :
    (blindEnv a₀).observed s = zeroReward := rfl

/-- **At horizon one the return is the true reward of the opening action.**

This is the whole reason the extrema below can be written down. -/
public theorem returnOver_one (μ : Env Bool) (π : Policy Bool Bool) :
    returnOver actIsState 1 false μ π
      = (μ.trueReward (π ((false, μ.observed false), [])) : ℝ) := by
  rw [returnOver, Finset.sum_range_one]
  rfl

/-- In a `blindEnv` the opening action is read at `startHistory`, independently of
which environment in the family was chosen. -/
public theorem blindEnv_return (a₀ : Bool) (π : Policy Bool Bool) :
    returnOver actIsState 1 false (blindEnv a₀) π
      = ((blindEnv a₀).trueReward (π startHistory) : ℝ) := by
  rw [returnOver_one]; rfl

/-- The greedy one-step policy: open with whichever state carries the larger true
reward, and ignore the history thereafter. -/
@[expose] public noncomputable def greedy (μ : Env Bool) : Policy Bool Bool :=
  fun _ => if (μ.trueReward false : ℝ) ≤ (μ.trueReward true : ℝ) then true else false

/-- It is optimal at horizon one. -/
public theorem greedy_best (μ : Env Bool) (π : Policy Bool Bool) :
    returnOver actIsState 1 false μ π ≤ returnOver actIsState 1 false μ (greedy μ) := by
  rw [returnOver_one, returnOver_one]
  have hg : ∀ h : History Bool Bool, greedy μ h
      = if (μ.trueReward false : ℝ) ≤ (μ.trueReward true : ℝ) then true else false :=
    fun _ => rfl
  rw [hg]
  by_cases hle : (μ.trueReward false : ℝ) ≤ (μ.trueReward true : ℝ)
  · rw [if_pos hle]
    cases hπ : π ((false, μ.observed false), []) with
    | false => exact hle
    | true => exact le_refl _
  · rw [if_neg hle]
    cases hπ : π ((false, μ.observed false), []) with
    | false => exact le_refl _
    | true => exact le_of_not_ge hle

/-- Returns lie in `[0,1]` at horizon one, so no regret can exceed one. -/
public theorem returnOver_one_mem (μ : Env Bool) (π : Policy Bool Bool) :
    0 ≤ returnOver actIsState 1 false μ π ∧ returnOver actIsState 1 false μ π ≤ 1 := by
  rw [returnOver_one]
  exact ⟨(μ.trueReward _).2.1, (μ.trueReward _).2.2⟩

/-- **A policy scores nothing in the environment built against it.** -/
public theorem blindEnv_self_return (π : Policy Bool Bool) :
    returnOver actIsState 1 false (blindEnv (π startHistory)) π = 0 := by
  rw [blindEnv_return]
  show ((if π startHistory = π startHistory then zeroReward else oneReward : Reward) : ℝ) = 0
  rw [if_pos rfl]; rfl

/-- **While the greedy policy scores one there.** -/
public theorem blindEnv_greedy_return (a₀ : Bool) :
    returnOver actIsState 1 false (blindEnv a₀) (greedy (blindEnv a₀)) = 1 := by
  rw [blindEnv_return]
  have hg : greedy (blindEnv a₀) startHistory
      = if ((blindEnv a₀).trueReward false : ℝ) ≤ ((blindEnv a₀).trueReward true : ℝ)
        then true else false := rfl
  rw [hg]
  cases a₀ with
  | false =>
      show ((if (if ((0 : ℝ) ≤ 1) then true else false) = false then zeroReward else oneReward
        : Reward) : ℝ) = 1
      norm_num [oneReward]
  | true =>
      show ((if (if ((1 : ℝ) ≤ 0) then true else false) = true then zeroReward else oneReward
        : Reward) : ℝ) = 1
      norm_num [oneReward]

/-- So the regret suffered in that environment is exactly one. -/
public theorem blindEnv_regret (π : Policy Bool Bool) :
    returnOver actIsState 1 false (blindEnv (π startHistory))
        (greedy (blindEnv (π startHistory))) -
      returnOver actIsState 1 false (blindEnv (π startHistory)) π = 1 := by
  rw [blindEnv_greedy_return, blindEnv_self_return]; ring

/--
**A corrupt-reward MDP with all three extrema attained.**

`CRMDP.Model` asks for an optimal policy in every environment, a worst
environment for every policy, and a policy with maximal worst-case regret. All
three are exhibited here rather than assumed.
-/
@[expose] public noncomputable def witness : Model Bool Bool where
  transition := actIsState
  horizon := 1
  start := false
  bestPolicy := greedy
  bestPolicy_best := greedy_best
  worstEnvironment := fun π => blindEnv (π startHistory)
  worstEnvironment_worst := by
    intro π μ
    rw [blindEnv_regret]
    have hb := returnOver_one_mem μ (greedy μ)
    have hp := returnOver_one_mem μ π
    linarith [hb.2, hp.1]
  worstPolicy := fun _ => true
  worstPolicy_worst := by
    intro π
    rw [blindEnv_regret π]
    exact le_of_eq (blindEnv_regret (fun _ => true)).symm

/-- **The bound Theorem 11 gives on this model is not the trivial one.** Every
policy suffers at least half a unit of worst-case regret, on a horizon where one
unit is the most any policy can suffer. -/
public theorem witness_theorem_eleven (π : Policy Bool Bool) :
    (1 : ℝ) / 2 ≤ witness.toComplementedClass.worstCaseRegret π := by
  have h := witness.everitt_theorem_eleven π
  have hw : witness.toComplementedClass.worstCaseRegret
      witness.toComplementedClass.worstPolicy = 1 :=
    blindEnv_regret (fun _ => true)

  rwa [hw] at h

/-- And the same model, read stochastically. Its transition is the point mass at
`actIsState`, so `Model.toStoch_returnValue` says the two carry the same
numbers. -/
@[expose] public noncomputable def stochWitness : StochModel Bool Bool := witness.toStoch

/-- **The stochastic Theorem 11 is not vacuous either.** -/
public theorem stochWitness_theorem_eleven (π : Policy Bool Bool) :
    (1 : ℝ) / 2 ≤ stochWitness.toComplementedClass.worstCaseRegret π := by
  have h := stochWitness.everitt_theorem_eleven π
  have hval : ∀ μ ρ, stochWitness.toComplementedClass.returnValue μ ρ
      = witness.toComplementedClass.returnValue μ ρ := witness.toStoch_returnValue
  have hw : stochWitness.toComplementedClass.worstCaseRegret
      stochWitness.toComplementedClass.worstPolicy = 1 := by
    show stochWitness.toComplementedClass.returnValue _ _ -
      stochWitness.toComplementedClass.returnValue _ _ = 1
    rw [hval, hval]
    exact blindEnv_regret (fun _ => true)
  rwa [hw] at h

/-! ## Definition 10 as printed, at this model

`witness` has horizon `1`, so equation (3) should read `1`. With the return
Definition 10 actually prints it reads `2`. The general statements are in
`Wireheading.CRMDP`; these ground them at data.
-/

/-- **Print's equation (3) reads `2` at a horizon of `1`.** -/
public theorem witness_returnWithStart_add_complement
    (μ : Env Bool) (π : Policy Bool Bool) :
    returnWithStart actIsState 1 false μ π +
        returnWithStart actIsState 1 false μ.complement π = 2 := by
  rw [returnWithStart_add_complement]
  norm_num

/-- **So the printed Definition 10 cannot satisfy equation (3) here.** The
horizon is `1` and the complementary returns sum to `2`. This is the general
`returnWithStart_add_complement_ne` at this model, not a second computation. -/
public theorem witness_returnWithStart_ne_horizon
    (μ : Env Bool) (π : Policy Bool Bool) :
    returnWithStart actIsState 1 false μ π +
        returnWithStart actIsState 1 false μ.complement π ≠ 1 := by
  have h := returnWithStart_add_complement_ne actIsState 1 false μ π
  simpa using h

/-- **And the regret Definition 10 defines is unaffected**, at this model: the
start-state term cancels from the difference, so the printed return and the
proof's return give the same regret. -/
public theorem witness_returnWithStart_sub
    (μ : Env Bool) (π π' : Policy Bool Bool) :
    returnWithStart actIsState 1 false μ π' -
        returnWithStart actIsState 1 false μ π =
      returnOver actIsState 1 false μ π' - returnOver actIsState 1 false μ π :=
  returnWithStart_sub actIsState 1 false μ π π'

/-- The gap is exactly the start state's true reward, which `returnOver` does
not count and `Ġ` does. -/
public theorem witness_returnWithStart_eq
    (μ : Env Bool) (π : Policy Bool Bool) :
    returnWithStart actIsState 1 false μ π =
      returnOver actIsState 1 false μ π + (μ.trueReward false : ℝ) :=
  returnWithStart_eq_returnOver_add actIsState 1 false μ π

end AISafetyAtlas.Examples.Wireheading
