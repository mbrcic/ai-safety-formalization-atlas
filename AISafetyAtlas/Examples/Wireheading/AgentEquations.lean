module

public import AISafetyAtlas.Wireheading.AgentEquations
public import AISafetyAtlas.Wireheading.AgentHistory

/-!
# Three structural identities, at the flattest possible model

`historyMass_nil`, `truncation_exact` and `value_succ_eq_sup'` hold for every
belief and agent -- they are about the recursion, not about any particular
reward or horizon. The constant-zero agent over a constant belief is enough to
inhabit all three.

`value_eq_of_agree_on_window` is not like that, and the second half of this file
is why. Its content is that two agents may **differ arbitrarily outside the
window** and still agree on it, so a witness at one agent applied against itself
proves nothing: the conclusion reads `value = value` and closes by `rfl` without
ever mentioning a window. The pair below is built to make the hypothesis
non-trivial -- `patient` and `impatient` agree on every history the window
reaches and disagree on the first one past it -- and the disagreement is stated
as a theorem so it cannot quietly become vacuous.

The last section runs the same theorem along an actual determined run, through
`AISafetyAtlas.Wireheading.AgentHistory`, where the window is the number of
steps taken rather than a length of an arbitrary list.
-/

namespace AISafetyAtlas.Examples.Wireheading.AgentEquations

open AISafetyAtlas.Wireheading.AgentEquations

/-- A belief that assigns every observation the same weight. -/
public def flatBelief : Belief Bool Unit where
  cond := fun _ _ _ => 1

/-- An agent with no reward and no horizon. -/
public def flatAgent : Agent Bool Unit where
  utility := fun _ => 0
  horizon := fun _ _ => 0

/-- **The empty history has mass one**, at the witness. -/
public theorem flatBelief_historyMass_nil : historyMass flatBelief [] = 1 :=
  historyMass_nil flatBelief

/-- **Truncation beyond the horizon's support changes nothing**, at the
witness -- the horizon is zero everywhere, so the hypothesis is free. -/
public theorem flatAgent_truncation_exact (t n : ℕ) (h : History Bool Unit) :
    value flatBelief flatAgent t n h = value flatBelief flatAgent t (n + 1) h :=
  truncation_exact flatBelief flatAgent t n h (fun _ _ => rfl)

/-- **The successor step is the `sup'` form**, at the witness. -/
public theorem flatAgent_value_succ_eq_sup' (t n : ℕ) (h : History Bool Unit) :
    value flatBelief flatAgent t (n + 1) h =
      flatAgent.horizon t h.length * flatAgent.utility h +
        (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
          (actionValue flatBelief flatAgent t n h) :=
  value_succ_eq_sup' flatBelief flatAgent t n h

/-! ## Two agents that agree on a window and disagree past it

The window is fixed at two steps. Both agents score every history of length at
most two as zero; `impatient` scores every longer history as one. Nothing else
differs, so any disagreement between them is a disagreement about what happens
outside the window and nothing more.
-/

/-- Indifferent everywhere, with a flat horizon. -/
public def patient : Agent Bool Unit where
  utility := fun _ => 0
  horizon := fun _ _ => 1

/-- Indifferent inside the two-step window and rewarding outside it. -/
public def impatient : Agent Bool Unit where
  utility := fun h => if h.length ≤ 2 then 0 else 1
  horizon := fun _ _ => 1

/-- **They really are different agents.** Without this the congruence below is
a statement about one agent and says nothing about a window. -/
public theorem patient_ne_impatient : patient ≠ impatient := by
  intro h
  have : patient.utility [(true, ()), (true, ()), (true, ()), (true, ())]
      = impatient.utility [(true, ()), (true, ()), (true, ()), (true, ())] := by
    rw [h]
  simp [patient, impatient] at this

/-- And the disagreement is outside the window, at the first history past it. -/
public theorem utility_ne_past_window :
    patient.utility [(true, ()), (true, ()), (true, ())]
      ≠ impatient.utility [(true, ()), (true, ()), (true, ())] := by
  simp [patient, impatient]

/-- Inside the window they agree, which is the theorem's hypothesis. -/
public theorem utility_agree_on_window (h' : History Bool Unit) (hh' : h'.length ≤ 2) :
    patient.utility h' = impatient.utility h' := by
  simp [patient, impatient, hh']

/--
**The window is what the value sees.** Two agents differing past two steps give
the same depth-two value from the empty history -- so the factorization is about
the window and not about the agents being equal, which `patient_ne_impatient`
rules out.
-/
public theorem value_agrees_on_window :
    value flatBelief patient 0 2 ([] : History Bool Unit)
      = value flatBelief impatient 0 2 ([] : History Bool Unit) :=
  AISafetyAtlas.Wireheading.AgentEquations.value_eq_of_agree_on_window flatBelief patient impatient 0 2 []
    (fun h' hh' => utility_agree_on_window h' (by simpa using hh'))
    (fun _ _ => rfl)

/-! ## The transport itself

`AgentHistory`'s round trips hold for every history, so they are exercised here
at a named one rather than left as facts about a variable. Every library result
below is written with its full name rather than opened: `Objective` carries a
`value_eq_of_agree_on_window` too, and a bare use of that leaf is evidence for
both declarations and therefore for neither.
-/

/-- A history with something in it, so the round trips below are not run at the
empty list. -/
public def sampleHistory : History Bool Unit := [(true, ()), (false, ())]

/-- **Supplying an initial observation and then forgetting it is the identity.** -/
public theorem sample_ofDecisionHistory_toDecisionHistory :
    ofDecisionHistory (toDecisionHistory () sampleHistory) = sampleHistory :=
  AISafetyAtlas.Wireheading.AgentEquations.ofDecisionHistory_toDecisionHistory () sampleHistory

/-- **And forgetting the observation a run history carries, then restoring it,
is the identity.** -/
public theorem sample_toDecisionHistory_ofDecisionHistory
    (h : AISafetyAtlas.Decision.History Unit Bool) :
    toDecisionHistory h.1 (ofDecisionHistory h) = h :=
  AISafetyAtlas.Wireheading.AgentEquations.toDecisionHistory_ofDecisionHistory h

/-- **The transport separates histories**, so no two interaction histories are
confused once they are read on the shared carrier. -/
public theorem sample_toDecisionHistory_injective :
    Function.Injective (toDecisionHistory (Action := Bool) ()) :=
  AISafetyAtlas.Wireheading.AgentEquations.toDecisionHistory_injective ()

/-- Which at `sampleHistory` says the obvious thing the injectivity is for. -/
public theorem sampleHistory_ne_nil_on_carrier :
    toDecisionHistory () sampleHistory ≠ toDecisionHistory () ([] : History Bool Unit) := by
  intro h
  exact absurd (sample_toDecisionHistory_injective h) (by decide)

/-- **The window length survives the transport**, which is what lets the
factorization be restated in steps. -/
public theorem sample_length_ofDecisionHistory
    (h : AISafetyAtlas.Decision.History Unit Bool) :
    (ofDecisionHistory h).length = h.2.length :=
  AISafetyAtlas.Wireheading.AgentEquations.length_ofDecisionHistory h

/-! ## The same theorem along a determined run

`AgentHistory` identifies these histories with the `AISafetyAtlas.Decision`
carrier's, so the window can be counted in steps of an actual run rather than in
the length of a list nobody produced. The world below is the smallest one that
runs: one bit of state, the action overwrites it, and the agent observes
nothing.
-/

/-- The transition: the action becomes the state. -/
public def flipWorld : Bool → Bool → Bool := fun _ a => a

/-- The agent sees nothing, which is the observation alphabet `Unit` the agents
above are written over. -/
public def blindObs : Bool → Unit := fun _ => ()

/-- A policy that always acts the same way. -/
public def alwaysTrue : AISafetyAtlas.Decision.DetPolicy Unit Bool := fun _ => true

/-- **A run of one step produces a history of length one.** -/
public theorem runHistory_one_length :
    (runHistory flipWorld blindObs alwaysTrue false 1).length = 1 :=
  AISafetyAtlas.Wireheading.AgentEquations.runHistory_length flipWorld blindObs alwaysTrue false 1

/-- **A run of no steps is the empty interaction history**, so the value from a
fresh start is the recursion's own base case and nothing has to be said twice. -/
public theorem runHistory_none :
    runHistory flipWorld blindObs alwaysTrue false 0 = ([] : History Bool Unit) :=
  AISafetyAtlas.Wireheading.AgentEquations.runHistory_zero flipWorld blindObs alwaysTrue false

/--
**The two agents score the run identically.** One step taken and one step looked
ahead is a two-step window, which is exactly where `patient` and `impatient`
still agree -- and by `patient_ne_impatient` they are not the same agent.
-/
public theorem value_runHistory_agrees :
    value flatBelief patient 0 1 (runHistory flipWorld blindObs alwaysTrue false 1)
      = value flatBelief impatient 0 1 (runHistory flipWorld blindObs alwaysTrue false 1) :=
  AISafetyAtlas.Wireheading.AgentEquations.value_runHistory_eq_of_agree_on_window flatBelief patient impatient 0 1 1
    flipWorld blindObs alwaysTrue false
    (fun h' hh' => utility_agree_on_window h' hh')
    (fun _ _ => rfl)

end AISafetyAtlas.Examples.Wireheading.AgentEquations
