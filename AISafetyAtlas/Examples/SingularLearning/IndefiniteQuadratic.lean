module

public import AISafetyAtlas.SingularLearning.IndefiniteQuadratic

/-!
# Worked scalar bilinear band

This is the source-neutral four-coordinate core used by MAIS-O7: the absolute
dot product of two real two-vectors has local pair `(1,1)` at the origin.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

example : HasLocalVolumeOrder (fun w => |residualAmplitude w|) 0 1 1 :=
  hasLocalVolumeOrder_abs_residualAmplitude

end AISafetyAtlas.Examples.SingularLearning
