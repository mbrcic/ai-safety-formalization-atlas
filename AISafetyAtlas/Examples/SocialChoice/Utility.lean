module

public import AISafetyAtlas.SocialChoice.Utility

/-!
# The utility-induced preference, applied

`preference_le_iff` had no worked instance: nothing in the tree built a
concrete utility function and read its induced preorder back off the
utility values. Two alternatives and the identity utility are enough.
-/

namespace AISafetyAtlas.Examples.SocialChoice.Utility

open AISafetyAtlas.SocialChoice.Utility

/-- The identity utility on `Fin 2`: alternative `i` is worth `i`. -/
@[expose] public noncomputable def idUtility : Function (Fin 2) := fun i => (i : ℝ)

/-- **The induced preorder orders alternatives as the utility values do**,
at the identity utility on two alternatives. -/
public theorem idUtility_preference_le_iff (a b : Fin 2) :
    (preference idUtility).le a b ↔ idUtility a ≤ idUtility b :=
  preference_le_iff idUtility a b

end AISafetyAtlas.Examples.SocialChoice.Utility
