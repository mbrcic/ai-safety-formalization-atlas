module

public import Mathlib.Data.Set.Image
public import Mathlib.Logic.Function.Basic

/-!
# Observation and monitoring boundaries

## Statement intent

- System object: executions mapped to observations by an observation
  function; a hazard is an arbitrary set of executions.
- Monitor: a flagged set of observations; an execution raises an alarm when
  its observation is flagged. No decidability or computability is imposed.
- `ObservationDetermined`: the hazard is the preimage of some flagged
  observation set — it depends only on what the monitor observes.
- Fiber invariance is not redefined here: it is exactly Mathlib's
  `Function.FactorsThrough (· ∈ hazard) observe`.
- Conclusion (`factors_through_iff_fiber_invariant`): the hazard factors
  through observations iff it is fiber-invariant.
- Conclusion (`exists_perfect_monitor_iff`): a sound and complete monitor
  exists iff the hazard is observation-determined.
- Refutation form (`no_perfect_monitor_of_collision`): one safe and one
  hazardous execution with identical observations rule out every sound and
  complete monitor.

## Interpretation

- Mathematical: a subset factors through a map's fibers iff it is a
  preimage; a two-point collision obstructs factorization.
- Engineering: no classifier improvement can fix a missing-information
  problem; first settle whether the hazard is observable, only then optimize
  detector power.
- AI-safety: monitors scoped to insufficient observations cannot be made
  both sound and complete; the failure is the observation scope, not the
  detector.
- Non-claim: imperfect (sound but incomplete, or statistical) monitoring is
  not claimed useless; nothing here concerns detection power, timing, or
  probabilistic guarantees.
-/

@[expose] public section

namespace AISafetyAtlas.Observability

open Set Function

variable {Execution Observation : Type*}

/--
The hazard is determined by observations: some flagged observation set pulls
back to exactly the hazard. This is the plan-level `FactorsThrough` for
sets; the pointwise form is Mathlib's `Function.FactorsThrough`.
-/
public def ObservationDetermined
    (observe : Execution → Observation) (hazard : Set Execution) : Prop :=
  ∃ flagged : Set Observation, hazard = observe ⁻¹' flagged

/--
A monitor (flagged observation set) is sound when every alarm is a genuine
hazard: no false alarms.
-/
public def SoundMonitor (observe : Execution → Observation)
    (hazard : Set Execution) (flagged : Set Observation) : Prop :=
  observe ⁻¹' flagged ⊆ hazard

/--
A monitor (flagged observation set) is complete when every hazardous
execution raises an alarm: no missed hazards.
-/
public def CompleteMonitor (observe : Execution → Observation)
    (hazard : Set Execution) (flagged : Set Observation) : Prop :=
  hazard ⊆ observe ⁻¹' flagged

/--
Observation factorization: the hazard is determined by observations iff it
is fiber-invariant — membership never distinguishes two executions with the
same observation. The right-hand side is Mathlib's
`Function.FactorsThrough` applied to the hazard's membership predicate.
-/
public theorem factors_through_iff_fiber_invariant
    (observe : Execution → Observation) (hazard : Set Execution) :
    ObservationDetermined observe hazard ↔
      Function.FactorsThrough (· ∈ hazard) observe := by
  constructor
  · rintro ⟨flagged, rfl⟩ a b hab
    simp [hab]
  · intro h
    refine ⟨observe '' hazard, Set.eq_of_subset_of_subset
      (fun x hx => ⟨x, hx, rfl⟩) fun x hx => ?_⟩
    obtain ⟨y, hy, hobs⟩ := hx
    exact Eq.mp (h hobs) hy

/--
A sound and complete monitor exists iff the hazard is observation-determined.
Perfect monitoring is exactly an observability property of the hazard.
-/
public theorem exists_perfect_monitor_iff
    (observe : Execution → Observation) (hazard : Set Execution) :
    (∃ flagged, SoundMonitor observe hazard flagged ∧
        CompleteMonitor observe hazard flagged) ↔
      ObservationDetermined observe hazard := by
  constructor
  · rintro ⟨flagged, hsound, hcomplete⟩
    exact ⟨flagged, subset_antisymm hcomplete hsound⟩
  · rintro ⟨flagged, rfl⟩
    exact ⟨flagged, subset_rfl, subset_rfl⟩

/--
Observational collision: a safe and a hazardous execution with identical
observations rule out every sound and complete monitor. The obstruction is
missing information, not detector quality.
-/
public theorem no_perfect_monitor_of_collision
    {observe : Execution → Observation} {hazard : Set Execution}
    {safeExec unsafeExec : Execution}
    (hsafe : safeExec ∉ hazard) (hunsafe : unsafeExec ∈ hazard)
    (hobs : observe safeExec = observe unsafeExec) :
    ¬ ∃ flagged, SoundMonitor observe hazard flagged ∧
        CompleteMonitor observe hazard flagged := by
  rintro ⟨flagged, hsound, hcomplete⟩
  have halarm : safeExec ∈ observe ⁻¹' flagged := by
    rw [Set.mem_preimage, hobs]
    exact hcomplete hunsafe
  exact hsafe (hsound halarm)

end AISafetyAtlas.Observability
