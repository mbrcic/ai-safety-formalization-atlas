module

public import AISafetyAtlas.SingularLearning.QuadraticSplit

/-!
# Worked signature split

The `(2,2)` split is the shape MAIS-O7's origin calculation lives in: four
parameters carrying the indefinite form `‖u‖² - ‖v‖²`.  The two facts the Stage 3
volume argument rests on are exhibited here at that shape — the germ is
homogeneous of degree two, and the splitting is an ℓ² isometry, so a ball of the
ambient space really is the region `‖u‖² + ‖v‖² < δ²` in the two factors.

The third example is the reason the split is worth isolating: the form takes both
signs, so the germ vanishes on a set with nonempty interior in neither factor
alone.  A definite form would make the same expression a norm, and every band
estimate below would be about the wrong object.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- Degree-two homogeneity at the `(2,2)` shape. -/
example (w : EuclideanSpace ℝ (Fin (2 + 2))) (t : ℝ) (ht : 0 ≤ t) :
    modelBandGerm 2 2 (t • w) = t ^ 2 * modelBandGerm 2 2 w :=
  modelBandGerm_smul 2 2 t ht w

/-- The split is an isometry, so no radius is distorted. -/
example (u : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖splitLE 2 2 (u, v)‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
  norm_sq_splitLE 2 2 u v

/-- **The form is genuinely indefinite.**  It is positive somewhere and negative
somewhere, so `modelBandGerm` is an absolute value of something that changes
sign — the case the band estimate is for, and the case a definite form is not. -/
example : ∃ u v : EuclideanSpace ℝ (Fin 1),
    ‖u‖ ^ 2 - ‖v‖ ^ 2 > 0 ∧ ‖v‖ ^ 2 - ‖u‖ ^ 2 < 0 := by
  refine ⟨(WithLp.equiv 2 _).symm ![1], (WithLp.equiv 2 _).symm ![0], ?_, ?_⟩ <;>
    · simp [EuclideanSpace.norm_eq]

end AISafetyAtlas.Examples.SingularLearning
