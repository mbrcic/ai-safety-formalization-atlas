module

public import AISafetyAtlas.SingularLearning.TwoSidedBand
public import AISafetyAtlas.SingularLearning.GaussianQuadratic

/-!
# Worked strict/weak band bridge

The one-dimensional quadratic germ has operational pair `(1/2,1)`.  The
generic strict/weak bridge gives the identical pair when the threshold is
written with `<`, without a boundary-measure premise.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

example : HasStrictLocalVolumeOrder (quadraticGerm 1) 0 (1 / 2) 1 := by
  have h := hasLocalVolumeOrder_quadraticGerm (q := 1) (by norm_num)
  norm_num at h
  exact hasStrictLocalVolumeOrder_of_hasLocalVolumeOrder h

end AISafetyAtlas.Examples.SingularLearning
