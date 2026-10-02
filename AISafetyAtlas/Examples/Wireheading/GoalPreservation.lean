module

public import AISafetyAtlas.Wireheading.GoalPreservation

/-!
# `run_optimal`, at a model with nothing to choose between

`names_surjective` demands a surjection `PolicyName → WorldAction × PolicyName`
at every history. Collapsing both to `Unit` makes it free -- there is exactly
one target to hit -- and the same collapse makes `OptimalAt` vacuous, so
`run_optimal` needs no further construction.
-/

namespace AISafetyAtlas.Examples.Wireheading.GoalPreservation

open AISafetyAtlas.Wireheading.GoalPreservation

/-- The model with nothing to choose between. -/
public noncomputable def trivialModel : Model Unit Unit Unit where
  act := fun _ _ => ((), ())
  next := fun _ _ => ()
  utility := fun _ _ => 0
  discount := 1 / 2
  discount_pos := by norm_num
  continuation := fun _ _ => 0
  coherent := by intro p h; norm_num
  names_surjective := fun _ _ => ⟨(), rfl⟩

/-- **Every history is trivially optimal for the initial policy.** -/
public theorem trivialModel_initiallyOptimal : ∀ h : Unit, trivialModel.OptimalAt () h := by
  intro h a
  exact le_refl _

/-- **Optimality propagates along the whole trajectory**, at the witness. -/
public theorem trivialModel_run_optimal (steps : ℕ) :
    trivialModel.OptimalAt (trivialModel.run steps () ()).1 (trivialModel.run steps () ()).2 :=
  Model.run_optimal trivialModel () () trivialModel_initiallyOptimal steps

end AISafetyAtlas.Examples.Wireheading.GoalPreservation
