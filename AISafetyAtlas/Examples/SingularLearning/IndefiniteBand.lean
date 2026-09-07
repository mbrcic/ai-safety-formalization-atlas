module

public import AISafetyAtlas.SingularLearning.IndefiniteBand

/-!
# Worked reduction of the band transform

The `(2,2)` shape is MAIS-O7's origin.  The reduction applies there, turning the
four-dimensional Gaussian-Laplace transform into a two-dimensional integral over
the block radii, and the integrand is integrable for every nonnegative `T`.

Both facts are recorded at a concrete shape because the general statements carry
`NeZero` instances and a sign hypothesis; an instantiation is the cheapest check
that those are satisfiable rather than vacuous.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning MeasureTheory Set

/-- The reduction, instantiated at the signature of O7's origin. -/
example {T : ℝ} (hT : 0 ≤ T) :
    bandLaplace 2 2 T
      = (2 : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) *
          ∫ r in Ioi (0:ℝ), r ^ (2 - 1) *
            ((2 : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) *
              ∫ s in Ioi (0:ℝ), s ^ (2 - 1) *
                (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))))) := by
  simpa using bandLaplace_eq_radial 2 2 hT

/-- The transform is an integral of an integrable function, so it is not the
junk value the Bochner integral returns off its domain. -/
example {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun x : EuclideanSpace ℝ (Fin (2 + 2)) =>
      Real.exp (-‖x‖ ^ 2) * Real.exp (-T * modelBandGerm 2 2 x)) volume :=
  integrable_bandLaplace 2 2 hT

/-- **The model band theorem at O7's signature.**  The germ `|‖u‖² - ‖v‖²|` on
four coordinates has local pair `(1,1)` at the origin — unconditionally, with no
frontier hypothesis anywhere in its dependency cone. -/
example : HasLocalVolumeOrder (modelBandGerm 2 2) 0 1 1 :=
  hasLocalVolumeOrder_modelBandGerm 2 2 le_rfl

/-- The theorem is not vacuous on the dimension hypothesis: it applies at `(3,1)`
too, where the second block is one-dimensional and only the first carries the
`2 ≤ p` requirement. -/
example : HasLocalVolumeOrder (modelBandGerm 3 1) 0 1 1 :=
  hasLocalVolumeOrder_modelBandGerm 3 1 (by norm_num)

/-- **The general form, at the smallest signature it covers.**  `(1,2)` has a
one-dimensional first block, so the estimate must be run with the blocks
exchanged; the symmetry theorem does that. -/
example : HasLocalVolumeOrder (modelBandGerm 1 2) 0 1 1 :=
  hasLocalVolumeOrder_modelBandGerm_of_three_le 1 2 (by norm_num)

/-- And at the balanced signature of O7's origin, where no exchange is needed. -/
example : HasLocalVolumeOrder (modelBandGerm 2 2) 0 1 1 :=
  hasLocalVolumeOrder_modelBandGerm_of_three_le 2 2 (by norm_num)

/-- **The hyperbolic germ at the smallest shape the rung condition allows.**
`k < r < H` forces `H ≥ 2`, so the ambient dimension is at least four and the
model theorem applies. -/
example : HasLocalVolumeOrder (hyperbolicGerm 2) 0 1 1 :=
  hasLocalVolumeOrder_hyperbolicGerm 2 le_rfl

end AISafetyAtlas.Examples.SingularLearning
