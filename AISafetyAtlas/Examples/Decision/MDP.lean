module

public import AISafetyAtlas.Decision.MDP
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Fintype.BigOperators

/-!
# A rewardless Markov decision process, run

`AISafetyAtlas.Decision.MDP` is a carrier, so the thing to witness is that the
run it induces really runs, and that the two facts the corrupt-reward cluster
buys from it are not vacuous.

Three models, each answering one question a reader would otherwise have to take
on trust.

* `coin` is a genuinely stochastic transition: `coin_stateAt_one_apply` computes
  both successor probabilities as `1/2`, so `Decision.MDP.run` tracks the
  randomness rather than collapsing it.
* `toggle` is deterministic: `toggle_stateAt_ofDet` is `Decision.MDP.run_ofDet`
  evaluated, showing the determined run recovered inside the drawn one.
* `seeState` and `alsoSeeState` are two *different functions* that agree
  pointwise, and `coin_run_congr` is `Decision.MDP.run_congr_obs` at them. That
  lemma is what the corrupt-reward cluster uses to make an environment and its
  complement indistinguishable, and here it is applied to a run that is not a
  point mass.

The observation map is what a consumer chooses, and `blind` is the extreme case:
an agent that sees nothing at all still has a well-defined run, because the
dynamics do not depend on what is observed.
-/

namespace AISafetyAtlas.Examples.Decision

open AISafetyAtlas.Decision

/-- A rewardless Markov decision process on two states whose single action
ignores the state and flips a fair coin. -/
@[expose] public noncomputable def coin : MDP Bool Unit :=
  ⟨fun _ _ => PMF.ofFintype (fun _ => 1 / 2)
    (by rw [Fintype.sum_bool]; exact ENNReal.add_halves 1)⟩

/-- A rewardless Markov decision process whose single action toggles the state.
-/
@[expose] public def toggle : Bool → Unit → Bool := fun s _ => !s

/-- The observation map that reveals the state. -/
@[expose] public def seeState : Bool → Bool := fun s => s

/-- A second observation map that reveals the state, written differently. -/
@[expose] public def alsoSeeState : Bool → Bool := fun s => if s then true else false

/-- The observation map that reveals nothing. -/
@[expose] public def blind : Bool → Unit := fun _ => ()

/-- The only deterministic policy on a one-action alphabet. -/
@[expose] public def onlyAction {Obs : Type} : DetPolicy Obs Unit := fun _ => ()

/-- **The run does not collapse the distribution.** After one step of `coin`,
each successor state carries probability `1/2`. -/
public theorem coin_stateAt_one_apply (b : Bool) :
    coin.stateAt seeState (Policy.ofDet onlyAction) false 1 b = 1 / 2 := by
  simp [MDP.stateAt, MDP.run, Policy.ofDet, coin, seeState, onlyAction,
    PMF.pure_bind]

/-- **A blind agent still has a run.** The observation map may throw everything
away and the dynamics are unaffected, which is the sense in which the policy type
is not part of the Markov decision process. -/
public theorem coin_blind_stateAt_one_apply (b : Bool) :
    coin.stateAt blind (Policy.ofDet onlyAction) false 1 b = 1 / 2 := by
  simp [MDP.stateAt, MDP.run, Policy.ofDet, coin, blind, onlyAction,
    PMF.pure_bind]

/-- **The determined run is recovered.** Toggling twice from `false` returns to
`false`, and the drawn run at the point-mass transition and point-mass policy is
the point mass there. -/
public theorem toggle_stateAt_ofDet :
    (MDP.ofDet toggle).stateAt seeState (Policy.ofDet onlyAction) false 2
      = PMF.pure false := by
  rw [MDP.stateAt_ofDet]
  rfl

/-- **`run_congr_obs` is not vacuous.** Two observation maps that agree pointwise
without being the same syntactic function induce the same run, and the run in
question is a genuine distribution rather than a point mass. -/
public theorem coin_run_congr (n : ℕ) :
    coin.run seeState (Policy.ofDet onlyAction) false n
      = coin.run alsoSeeState (Policy.ofDet onlyAction) false n :=
  MDP.run_congr_obs coin (fun s => by cases s <;> rfl) _ false n


/-! ## One recursion at two monads

`genRun` is the shared recursion `detRun` and `MDP.run` are instances of. Both
identifications are read here at the two models above, so the claim that they
are one recursion is checked rather than asserted.
-/

/-- **`historyUpTo_congr_obs` is not vacuous either.** The same two observation
maps give the same history distribution, not merely the same state
distribution. -/
public theorem coin_historyUpTo_congr (n : ℕ) :
    coin.historyUpTo seeState (Policy.ofDet onlyAction) false n
      = coin.historyUpTo alsoSeeState (Policy.ofDet onlyAction) false n :=
  MDP.historyUpTo_congr_obs coin (fun s ↦ by cases s <;> rfl) _ false n

/-- **The determined run is the generic run at `Id`.** -/
public theorem toggle_genRun_id (n : ℕ) :
    genRun (m := Id) toggle seeState onlyAction false n
      = detRun toggle seeState onlyAction false n :=
  genRun_id toggle seeState onlyAction false n

/-- **And the drawn run is the generic run at `PMF`**, at a transition that is
genuinely a distribution. -/
public theorem coin_genRun_pmf (n : ℕ) :
    genRun (m := PMF) coin.transition seeState (Policy.ofDet onlyAction) false n
      = coin.run seeState (Policy.ofDet onlyAction) false n :=
  genRun_pmf coin seeState (Policy.ofDet onlyAction) false n

/-! ## A maximum over the whole policy space, at a drawn transition

`exists_max_of_truncates` says a quantity a run of `n` steps determines attains
its maximum over the entire policy space, because the run can consult the policy
only on the finitely many histories shorter than `n`. The policy space itself is
infinite -- `History Bool Bool` is, since the lists are unbounded -- so this is
not finiteness of the policy type.

`pick` has two actions and a genuinely drawn transition type, and `reachTrue`
separates two policies, so the maximum below is not a maximum of a constant.
-/

/-- A two-action process: the action names the next state. -/
@[expose] public noncomputable def pick : MDP Bool Bool :=
  ⟨fun _ a => PMF.pure a⟩

/-- The chance of standing in `true` after one step, as a real number. -/
@[expose] public noncomputable def reachTrue (π : DetPolicy Bool Bool) : ℝ :=
  (pick.stateAt seeState (Policy.ofDet π) false 1 true).toReal

/-- One step consults the policy only on the empty history. -/
public theorem reachTrue_congr (π₁ π₂ : DetPolicy Bool Bool)
    (h : ∀ hst : History Bool Bool, hst.2.length < 1 → π₁ hst = π₂ hst) :
    reachTrue π₁ = reachTrue π₂ := by
  unfold reachTrue
  rw [MDP.stateAt_congr_policy (σ₁ := Policy.ofDet π₁) (σ₂ := Policy.ofDet π₂)
    pick seeState false 1 fun hst hlt => by
    simp only [Policy.ofDet, h hst hlt]]

/-- The policy that always names `true`. -/
@[expose] public def sayTrue : DetPolicy Bool Bool := fun _ => true

/-- The policy that always names `false`. -/
@[expose] public def sayFalse : DetPolicy Bool Bool := fun _ => false

public theorem reachTrue_sayTrue : reachTrue sayTrue = 1 := by
  simp [reachTrue, MDP.stateAt, MDP.run, pick, Policy.ofDet, sayTrue]

public theorem reachTrue_sayFalse : reachTrue sayFalse = 0 := by
  simp [reachTrue, MDP.stateAt, MDP.run, pick, Policy.ofDet, sayFalse]

/-- **The quantity is not constant**, so the maximum below is about something. -/
public theorem reachTrue_ne : reachTrue sayTrue ≠ reachTrue sayFalse := by
  rw [reachTrue_sayTrue, reachTrue_sayFalse]
  norm_num

/-- **The maximum over the whole policy space is attained.** The policy space is
infinite; the run of one step is what makes the maximum finite. -/
public theorem exists_max_reachTrue :
    ∃ best : DetPolicy Bool Bool, ∀ π : DetPolicy Bool Bool, reachTrue π ≤ reachTrue best :=
  exists_max_of_truncates (n := 1) true reachTrue reachTrue_congr

/-- And the minimum. -/
public theorem exists_min_reachTrue :
    ∃ worst : DetPolicy Bool Bool, ∀ π : DetPolicy Bool Bool, reachTrue worst ≤ reachTrue π :=
  exists_min_of_truncates (n := 1) true reachTrue reachTrue_congr

end AISafetyAtlas.Examples.Decision
