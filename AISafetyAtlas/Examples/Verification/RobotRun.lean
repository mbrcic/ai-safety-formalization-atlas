module

public import AISafetyAtlas.Verification.RobotRun

/-!
# A verified behaviour, actually run

`alwaysSatisfies_run` carries a verifier's acceptability predicate onto a
trajectory. Read at a predicate that accepts everything it would be true and
empty, so this file fixes one that does not: the robot must alternate, and the
predicate accepts exactly that.

`stubborn_not_alwaysSatisfies` is the half that makes the other half mean
something — a behaviour that repeats itself fails the predicate, so being
accepted is a property some behaviours lack. `run_moves` is the third: the
world the behaviour is run in does not stand still.
-/

namespace AISafetyAtlas.Examples.Verification.RobotRun

open AISafetyAtlas.Verification.Robot

/-- The world counts steps. -/
@[expose] public def counter : ℕ → Bool → ℕ := fun n _ => n + 1

/-- The robot sees the count. -/
@[expose] public def seeCount : ℕ → ℕ := id

/-- The behaviour under test: alternate, cycle by cycle. -/
@[expose] public def alternate : Behavior Unit Bool := fun _ n => n % 2 == 0

/-- A behaviour that does the same thing forever. -/
@[expose] public def stubborn : Behavior Unit Bool := fun _ _ => true

/-- **The requirement**: at every cycle the action must alternate. Not a
predicate that accepts everything — `stubborn` fails it. -/
@[expose] public def mustAlternate : Unit → ℕ → Bool → Prop :=
  fun _ n a => a = (n % 2 == 0)

/-- The program is the choice of behaviour. -/
@[expose] public def behaviourOf : Bool → Behavior Unit Bool :=
  fun p => if p then alternate else stubborn

/-- **The alternating robot meets the requirement**, at every scenario and
cycle. -/
public theorem alternate_alwaysSatisfies :
    AlwaysSatisfies behaviourOf mustAlternate true :=
  fun _ _ => rfl

/-- **The stubborn one does not.** Without this the theorem below would be a
statement about a predicate nothing can fail. -/
public theorem stubborn_not_alwaysSatisfies :
    ¬ AlwaysSatisfies behaviourOf mustAlternate false := by
  intro h
  have := h () 1
  simp [behaviourOf, stubborn, mustAlternate] at this

/-- **So the two programs are told apart by the requirement**, which is what a
verifier is for. -/
public theorem behaviours_differ : behaviourOf true ≠ behaviourOf false := by
  intro h
  refine stubborn_not_alwaysSatisfies fun sc c => ?_
  rw [← h]
  exact alternate_alwaysSatisfies sc c

/-! ## Running it -/

/-- **The world moves.** One step from zero lands on one, so the trajectory is
not a fixed point and the cycle count below is counting something. -/
public theorem run_moves :
    AISafetyAtlas.Decision.detStateAt counter seeCount
        (ofBehavior () (behaviourOf true)) 0 1 ≠ 0 := by
  rw [detStateAt_ofBehavior_succ]
  simp [counter, AISafetyAtlas.Decision.detStateAt, AISafetyAtlas.Decision.detRun]

/-- The action taken at step `n` is the behaviour's cycle-`n` action. -/
public theorem action_at_step (n : ℕ) :
    ofBehavior (Obs := ℕ) () (behaviourOf true)
        (AISafetyAtlas.Decision.detHistoryUpTo counter seeCount
          (ofBehavior () (behaviourOf true)) 0 n)
      = behaviourOf true () n :=
  actionAt_ofBehavior counter seeCount () (behaviourOf true) 0 n

/--
**The verified robot acts acceptably at every step of its run.**

The verification verdict was a statement about cycles of a function; here it is
a statement about a trajectory in a world, which is the form a runtime claim has
to take.
-/
public theorem verified_run_is_acceptable (n : ℕ) :
    mustAlternate () n
      (ofBehavior (Obs := ℕ) () (behaviourOf true)
        (AISafetyAtlas.Decision.detHistoryUpTo counter seeCount
          (ofBehavior () (behaviourOf true)) 0 n)) :=
  alwaysSatisfies_run behaviourOf mustAlternate true alternate_alwaysSatisfies
    counter seeCount () 0 n

end AISafetyAtlas.Examples.Verification.RobotRun
