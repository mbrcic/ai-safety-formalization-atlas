module

public import AISafetyAtlas.Oversight.VarietyCheck

/-!
# The checker's `false` is not a clearance

`Oversight.VarietyCheck` decides one sufficient reason for oversight to fail:
too few interventions to separate the situations. Its module docstring is
careful that a `false` verdict *"says nothing"* — the bound is necessary, so
failing it means the obstruction does not apply, not that oversight succeeds.

That sentence is the one statement in the module nothing had exercised.
`exists_cannotForce_false_and_forces` is its proof, and running it here is what
turns a caveat in prose into a fact about the checker: there is a table the
checker clears and on which forcing genuinely holds, so `false` and "oversight
works" are not the same verdict and cannot be read as one.

The table is the smallest there is — two situations, one intervention, one
outcome. Degenerate on purpose: the asymmetry is about what the checker *can*
conclude, and a degenerate instance settles that as well as an elaborate one
would.
-/

namespace AISafetyAtlas.Examples.Oversight.VarietyCheck

open AISafetyAtlas.Oversight

/--
**A `false` verdict is compatible with forcing.** The checker declines to find
the counting obstruction, and the effect table really is forceable — so reading
`false` as a safety clearance is reading it as the opposite of what it says.
-/
public theorem false_verdict_is_not_a_clearance :
    ∃ (effect : Fin 2 → Fin 1 → Fin 1) (act : Unit → Fin 1) (target : Fin 1),
      cannotForce effect = false ∧ Forces effect (fun _ => ()) act target :=
  exists_cannotForce_false_and_forces

end AISafetyAtlas.Examples.Oversight.VarietyCheck
