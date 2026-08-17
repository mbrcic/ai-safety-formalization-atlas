module

public import AISafetyAtlas.Oversight.VarietyBound
public import AISafetyAtlas.Oversight.VarietyCheck

/-!
# Both corners, in one place

`Oversight.VarietyBound` says coverage and control are independent capacities.
Independence is a claim about two directions, and a claim about two directions
needs two models. Here they are, as small as they go.

**Corner one — sees everything, controls nothing.** Three situations, two
interventions, and an effect table that reports the situation back whatever the
overseer does. The observation is the identity, so the overseer knows exactly
which situation it is in and any hazard decision is available to it. It still
cannot force the outcome: there are more situations than interventions.

**Corner two — sees nothing, controls perfectly.** The same three situations,
an intervention that flattens every one of them to the same outcome, and an
overseer that observes nothing at all. It forces the target, while the hazard it
would have been asked about is not decidable from what it sees.

Neither corner is subtle, which is the point. If the two capacities could be
traded against each other, neither corner would exist.
-/

namespace AISafetyAtlas.Examples.Oversight

open AISafetyAtlas.Oversight
open AISafetyAtlas.Knowledge (Knowable)

/-! ## Corner one: full observation, insufficient repertoire -/

/-- The effect table that hands the situation back: whatever the overseer does,
the outcome is the situation it was facing. Ashby's "no repeat in a column". -/
@[expose] public def revealing : Fin 3 → Fin 2 → Fin 3 := fun σ _ => σ

/-- Every hazard decision is available: the overseer sees the situation itself. -/
public theorem knowable_of_full_observation (hazard : Fin 3 → Bool) :
    Knowable (id : Fin 3 → Fin 3) hazard :=
  ⟨hazard, fun _ => rfl⟩

/-- A fixed intervention still separates situations. -/
public theorem revealing_column_injective (a : Fin 2) :
    Function.Injective fun σ => revealing σ a :=
  fun _ _ h => h

/--
**Seeing everything is not enough.** No overseer forces the outcome, however it
maps its (perfect) observations to the two interventions available.
-/
public theorem not_forces_revealing (act : Fin 3 → Fin 2) (target : Fin 3) :
    ¬ Forces revealing (id : Fin 3 → Fin 3) act target :=
  not_forces_of_card_lt revealing_column_injective (by decide) act target

/-! ## Corner two: no observation, sufficient repertoire -/

/-- The effect table with a flattening intervention: intervention `0` sends every
situation to outcome `0`. -/
@[expose] public def flattening : Fin 3 → Fin 2 → Fin 3 := fun _ _ => 0

/-- The blind overseer. -/
@[expose] public def blind : Fin 3 → Unit := fun _ => ()

/-- The hazard it would be asked about: is this the first situation? -/
@[expose] public def firstSituation : Fin 3 → Bool := fun σ => σ = 0

/-- **It cannot see.** A decision rule reading a constant returns a constant, and
the hazard is not constant. -/
public theorem not_knowable_blind : ¬ Knowable blind firstSituation := by
  rintro ⟨decide, hdec⟩
  have h0 : firstSituation 0 = decide () := hdec 0
  have h1 : firstSituation 1 = decide () := hdec 1
  rw [show firstSituation 0 = true from by decide,
    show firstSituation 1 = false from by decide] at *
  exact absurd (h0.trans h1.symm) (by decide)

/-- **And it controls anyway.** -/
public theorem forces_flattening : Forces flattening blind (fun _ => 0) 0 :=
  forces_of_constant_effect (fun _ => rfl)

/-! ## The pair -/

/--
**Independence, witnessed.** Coverage without control, and control without
coverage, in models of three situations each.
-/
public theorem coverage_and_control_are_independent :
    (∀ hazard : Fin 3 → Bool, Knowable (id : Fin 3 → Fin 3) hazard)
      ∧ (∀ (act : Fin 3 → Fin 2) (target : Fin 3),
          ¬ Forces revealing (id : Fin 3 → Fin 3) act target)
      ∧ ¬ Knowable blind firstSituation
      ∧ Forces flattening blind (fun _ => 0) 0 :=
  ⟨knowable_of_full_observation, not_forces_revealing, not_knowable_blind, forces_flattening⟩

/-! ## The same verdict, decided

`Oversight.VarietyCheck.cannotForce` is what `atlas-check` runs on a model read
from JSON. Here it is on corner one, so the executable verdict and the proved one
are visible side by side rather than only in the harness.
-/

/-- The checker agrees: the counting obstruction applies to `revealing`. -/
public theorem cannotForce_revealing : cannotForce revealing = true := by decide

/-- And it is silent on `flattening`, which is the case where the bound's
structural hypothesis fails. A `false` verdict is not a clearance. -/
public theorem not_cannotForce_flattening : cannotForce flattening = false := by decide

/-- The executable verdict carries the same conclusion as `not_forces_revealing`,
through the agreement theorem rather than through a second argument. -/
public theorem not_forces_revealing_via_checker (act : Fin 3 → Fin 2) (target : Fin 3) :
    ¬ Forces revealing (id : Fin 3 → Fin 3) act target :=
  not_forces_of_cannotForce cannotForce_revealing _ act target

end AISafetyAtlas.Examples.Oversight
