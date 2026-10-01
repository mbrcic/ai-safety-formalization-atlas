module

public import AISafetyAtlas.Composition.Observability

/-!
# Witness W4 — local observation collision

Two agents jointly produce a pair of Boolean outputs. The hazard is the
prohibited *composition*: both outputs `true`. A monitor scoped to agent 0
observes only the first coordinate.

The executions `(true, false)` (safe) and `(true, true)` (hazardous) produce
the same local observation `true`. By `no_perfect_monitor_of_collision`, no
monitor over that local view is both sound and complete for the joint
hazard — regardless of how the monitor is built.

## Interpretation

- Engineering: the local detector is not merely weak; it observes the wrong
  unit of analysis. Fixing it requires changing the observation scope, not
  the classifier.
- AI-safety: cross-agent prohibited compositions are invisible to any
  per-agent monitor whose view omits the other agents — the formal
  motivation for network-level monitoring.
- Non-claim: nothing about detection power of *imperfect* monitors, nor
  about any particular multi-agent system or telemetry stack.
-/

namespace AISafetyAtlas.Examples.Composition.LocalObservationCollision

open AISafetyAtlas.Observability

/-- Joint executions: agent 0's and agent 1's Boolean outputs. -/
public abbrev Execution := Bool × Bool

/-- The agent-0-scoped view: only the first coordinate is observed. -/
public def observeLocal (e : Execution) : Bool := e.1

/-- The hazardous compositions: both agents output `true`. -/
public def JointHazard : Set Execution := {e | e.1 = true ∧ e.2 = true}

/--
No monitor over the agent-0-scoped view is both sound and complete for the
joint hazard: the safe execution `(true, false)` and the hazardous execution
`(true, true)` collide observationally.
-/
public theorem no_perfect_local_monitor :
    ¬ ∃ flagged, SoundMonitor observeLocal JointHazard flagged ∧
        CompleteMonitor observeLocal JointHazard flagged :=
  no_perfect_monitor_of_collision
    (safeExec := (true, false)) (unsafeExec := (true, true))
    (fun h => Bool.noConfusion h.2) ⟨rfl, rfl⟩ rfl

end AISafetyAtlas.Examples.Composition.LocalObservationCollision
