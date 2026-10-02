module

public import AISafetyAtlas.Wireheading.GoalPreservationSource

/-!
# The one-policy model: `OptimalAt` for free

`GoalPreservationSource.Model`'s two leaves need only a model and, for the
second, a history at which the current policy is `Q`-optimal. Collapsing
`PolicyName` and `WorldAction` to `Unit` makes optimality vacuous -- there is
only one action to compare against -- and is enough to inhabit both.
-/

namespace AISafetyAtlas.Examples.Wireheading.GoalPreservationSource

open AISafetyAtlas.Wireheading.GoalPreservationSource

/-- The model with nothing to choose between. -/
public noncomputable def trivialModel : Model Unit Unit Unit Unit where
  act := fun _ _ => ((), ())
  extend := fun _ _ _ => ()
  utility := fun _ => 0
  discount := 1 / 2
  discount_pos := by norm_num
  prob := fun _ _ _ => 1
  prob_sum_one := by intro h a; simp
  prob_pos := by intro h a e; norm_num
  contValue := fun _ _ => 0
  initial := ()
  initial_dominates := by intro p h; exact le_refl 0

/-- **The initial policy is trivially optimal**, since `Unit` leaves nothing
else to compare against. -/
public theorem trivialModel_optimalAt : trivialModel.OptimalAt () () := by
  intro a
  rfl

/-- `ι(p)` is `act p`, definitionally, at the witness. -/
public theorem trivialModel_name_eq_act (p : Unit) :
    trivialModel.name p = trivialModel.act p :=
  Model.name_eq_act trivialModel p

/-- **Self-modification is value-neutral for the initial objective**, at the
witness. -/
public theorem trivialModel_qValue_selected_eq_initial :
    trivialModel.qValue () (trivialModel.act () ()) =
      trivialModel.qValue () ((trivialModel.act () ()).1, trivialModel.initial) :=
  Model.qValue_selected_eq_initial trivialModel trivialModel_optimalAt

/-- The `Q` value at the initial utility is the one the model already had. -/
public theorem trivialModel_qValueWith_utility :
    trivialModel.qValueWith trivialModel.utility = trivialModel.qValue :=
  Model.qValueWith_utility trivialModel

/-- **The utility index collapses here because the utility is fixed**, print's
Definition 3 rather than the rendering. -/
public theorem trivialModel_qValueWith_eq (t : ℕ) :
    trivialModel.qValueWith ((fun _ _ => 0 : ℕ → Unit → ℝ) t) = trivialModel.qValue :=
  Model.qValueWith_eq_qValue_of_utility_fixed trivialModel _ (fun _ => rfl) t

/-- **And the index is not vacuous.** At two different utility functions the
same model's `Q` values differ, so the collapse above is print's Definition 3
doing work and not a rendering in which the index could never have mattered. -/
public theorem trivialModel_qValueWith_ne :
    trivialModel.qValueWith (fun _ => 1) () ((), ())
      ≠ trivialModel.qValueWith (fun _ => 0) () ((), ()) := by
  simp [Model.qValueWith, trivialModel]

end AISafetyAtlas.Examples.Wireheading.GoalPreservationSource
