module

public import AISafetyAtlas.Verification.Robot
public import AISafetyAtlas.Decision.MDP

/-!
# A verified behaviour, run

`AISafetyAtlas.Verification.Robot` states Fisher, Dennis and Webster's
undecidability result over a `Behavior Scenario Action = Scenario → ℕ → Action`:
a total action trace indexed by scenario and operational cycle. Nothing in the
tree ever ran one. A behaviour was a function from cycles to actions and a run
was a different object in a different cluster, so *"an agent whose observations
are corrupted and whose policy is verified"* — the sentence the elicitation says
cannot be written today — had no type to be written at.

**A cycle is the length of the history so far.** `AISafetyAtlas.Decision.History`
is an initial observation and a list, so the cycle count is already in the
carrier and `ofBehavior` needs nothing else: at a history of length `n` the
induced policy plays what the behaviour does at cycle `n`.

## What this buys

`actionAt_ofBehavior` is the identification — the action the run takes at step
`n` is the behaviour's cycle-`n` action, with no appeal to the observations.
`alwaysSatisfies_run` then carries the verifier's acceptability predicate onto
the run: **a program the verifier accepts produces only acceptable actions along
every determined run of every world.** That is the first statement in the tree
that connects a verification verdict to a trajectory.

## Explicit non-claims

* **Open loop.** A `Behavior` does not read observations, so the induced policy
  ignores everything except how long it has been running. That is the source's
  object and not a simplification introduced here; a behaviour that reacts is a
  different type and nothing here supplies one.
* **No undecidability is re-proved.** `action_safety_unverifiable` stays where
  it is and is untouched. This module carries its *predicate* to a run, not its
  proof.
* **Determined runs only.** The drawn run is a `PMF` and is not treated here.
* **The scenario is a parameter, not a world.** `ofBehavior` fixes a scenario
  and the world is given separately by a transition and an observation map.
  Nothing here says the two agree; relating a `Scenario` to a `State` is a
  modelling choice this module deliberately leaves open.

Landscape entry: `LAND-VERIF-ROBOTRUN-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Verification.Robot

variable {Obs Action State Scenario : Type*}

/-- **A behaviour, read as a policy over the shared carrier.** The cycle is the
number of steps the history records. -/
@[expose] public def ofBehavior (sc : Scenario) (b : Behavior Scenario Action) :
    Decision.DetPolicy Obs Action :=
  fun h => b sc h.2.length

/-- **The action at step `n` is the behaviour's cycle-`n` action.** Nothing in
the history beyond its length is consulted, which is what makes this an
embedding of an open-loop trace rather than a re-encoding that gains memory. -/
public theorem actionAt_ofBehavior (f : State → Action → State) (obs : State → Obs)
    (sc : Scenario) (b : Behavior Scenario Action) (s₀ : State) (n : ℕ) :
    ofBehavior (Obs := Obs) sc b (Decision.detHistoryUpTo f obs (ofBehavior sc b) s₀ n)
      = b sc n := by
  rw [ofBehavior, Decision.detHistoryUpTo_length]

/-- The run's next state is the transition applied to that action. -/
public theorem detStateAt_ofBehavior_succ (f : State → Action → State)
    (obs : State → Obs) (sc : Scenario) (b : Behavior Scenario Action)
    (s₀ : State) (n : ℕ) :
    Decision.detStateAt f obs (ofBehavior sc b) s₀ (n + 1)
      = f (Decision.detStateAt f obs (ofBehavior sc b) s₀ n) (b sc n) := by
  show f (Decision.detRun f obs (ofBehavior sc b) s₀ n).1
      (ofBehavior sc b (Decision.detRun f obs (ofBehavior sc b) s₀ n).2) = _
  rw [show (Decision.detRun f obs (ofBehavior sc b) s₀ n).2
        = Decision.detHistoryUpTo f obs (ofBehavior sc b) s₀ n from rfl,
    actionAt_ofBehavior]
  rfl

/--
**A verified program acts acceptably along every run.**

`AlwaysSatisfies` is a statement about a behaviour's cycles. Read through
`ofBehavior` it becomes a statement about a trajectory: in any world, from any
start, at every step, the action the agent actually takes is one the verifier's
predicate accepts.
-/
public theorem alwaysSatisfies_run {Program : Type*}
    (behavior : Program → Behavior Scenario Action)
    (acceptable : Scenario → ℕ → Action → Prop) (program : Program)
    (hsat : AlwaysSatisfies behavior acceptable program)
    (f : State → Action → State) (obs : State → Obs) (sc : Scenario)
    (s₀ : State) (n : ℕ) :
    acceptable sc n
      (ofBehavior (Obs := Obs) sc (behavior program)
        (Decision.detHistoryUpTo f obs (ofBehavior sc (behavior program)) s₀ n)) := by
  rw [actionAt_ofBehavior]
  exact hsat sc n

end AISafetyAtlas.Verification.Robot
