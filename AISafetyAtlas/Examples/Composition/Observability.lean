module

public import AISafetyAtlas.Composition.Observability

/-!
# Worked example: perfect monitoring is an observability property

`AISafetyAtlas.Observability.exists_perfect_monitor_iff` says a sound and
complete monitor exists exactly when the hazard is observation-determined. This
file runs it on the smallest case where it bites: two agents, each producing one
Boolean, a hazard that is the prohibited *composition* of the two, and a monitor
scoped to agent 0 alone.

The safe execution `(true, false)` and the hazardous `(true, true)` produce the
same local observation, so the hazard is not a function of that view. By the
equivalence, no monitor over the view is both sound and complete — whatever the
monitor is built from. The witness runs the equivalence in both directions: the
forward one turns a hypothetical perfect monitor into determinacy, and the
contrapositive is what an engineer reads off it.

The companion witness `AISafetyAtlas.Examples.Composition.LocalObservationCollision`
takes the same carrier through `no_perfect_monitor_of_collision` instead.
-/

namespace AISafetyAtlas.Examples.Composition.Observability

open AISafetyAtlas.Observability

/-- Joint executions: agent 0's and agent 1's Boolean outputs. -/
public abbrev Execution := Bool × Bool

/-- The agent-0-scoped view: only the first coordinate is observed. -/
@[expose] public def observeLocal (e : Execution) : Bool := e.1

/-- The hazardous compositions: both agents output `true`. -/
@[expose] public def JointHazard : Set Execution := {e | e.1 = true ∧ e.2 = true}

/-- The two executions that collide: same observation, opposite hazard status. -/
public theorem collision :
    observeLocal (true, false) = observeLocal (true, true) := rfl

/-- **No perfect monitor over the local view**, by the collision. -/
public theorem no_perfect_local_monitor :
    ¬ ∃ flagged, SoundMonitor observeLocal JointHazard flagged ∧
        CompleteMonitor observeLocal JointHazard flagged :=
  no_perfect_monitor_of_collision
    (safeExec := (true, false)) (unsafeExec := (true, true))
    (fun h => Bool.noConfusion h.2) ⟨rfl, rfl⟩ rfl

/-- **The equivalence, backwards.** Determinacy would give a perfect monitor, and
there is none, so the joint hazard is not determined by the agent-0 view. -/
public theorem jointHazard_not_observationDetermined :
    ¬ ObservationDetermined observeLocal JointHazard := fun h =>
  no_perfect_local_monitor ((exists_perfect_monitor_iff observeLocal JointHazard).mpr h)

/-- **The equivalence, forwards**, on a view that does determine the hazard:
observing both coordinates makes the hazard a function of the observation, so a
sound and complete monitor exists. -/
public theorem perfect_monitor_of_full_view :
    ∃ flagged, SoundMonitor (id : Execution → Execution) JointHazard flagged ∧
      CompleteMonitor (id : Execution → Execution) JointHazard flagged :=
  (exists_perfect_monitor_iff id JointHazard).mpr ⟨JointHazard, rfl⟩

end AISafetyAtlas.Examples.Composition.Observability
