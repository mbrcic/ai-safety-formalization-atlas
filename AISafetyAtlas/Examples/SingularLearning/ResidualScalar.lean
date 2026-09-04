module

public import AISafetyAtlas.SingularLearning.ResidualScalar

/-!
# Worked model: the local pair of `x²y²`, with nothing assumed

`residualGerm 1 1 1` is the smallest singular member of the reduced-rank residual family, and
`hasLocalVolumeOrder_residualGerm_one` gives its local pair unconditionally. These check the
pieces the estimate is built from, at the boundary values where a wrong constant would show.

Nothing here uses `sorry` or an added axiom, and nothing here assumes `EigenvalueLawStatement`.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-! ### The scale the estimate is measured against -/

/-- `laplaceScale (1/2) 2` is `T^{-1/2} log T`, the shape the two bounds bracket. -/
example : laplaceScale (1 / 2) 2 3 = (Real.sqrt 3)⁻¹ * Real.log 3 :=
  laplaceScale_half_two (by norm_num)

/-- The multiplicity is what makes the logarithm appear: at multiplicity one the scale would
carry `log T ^ 0 = 1` and no logarithm at all. -/
example (T : ℝ) : laplaceScale (1 / 2) 1 T = T ^ (-(1:ℝ) / 2) := by
  simp [laplaceScale]
  norm_num

/-! ### The pointwise bounds, at the two ends of the split -/

/-- At the split radius `x = T^{-1/2}` the two majorants agree: `1` and `1/(√T·|x|)` are both
`1` there, which is why the split is placed at that radius and not elsewhere. -/
example (T : ℝ) (hT : 0 < T) :
    (Real.sqrt T * |(Real.sqrt T)⁻¹|)⁻¹ = 1 := by
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [abs_of_pos (inv_pos.mpr hTs), mul_inv_cancel₀ (ne_of_gt hTs), inv_one]

/-- The integrand never exceeds the Gaussian, which is what makes it integrable. -/
example (T x : ℝ) (hT : 0 ≤ T) :
    Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) ≤ Real.exp (-x ^ 2) :=
  scalarIntegrand_le_gaussian hT x

/-- At `T = 0` the integrand is exactly the Gaussian, so `J(0) = √π`. This pins the
normalisation of `scalarJ` independently of the asymptotic bounds. -/
example : scalarJ 0 = Real.sqrt Real.pi := by
  rw [scalarJ]
  have : ∀ x : ℝ, Real.exp (-x ^ 2) * (1 + (0:ℝ) * x ^ 2) ^ (-(1 : ℝ) / 2)
      = Real.exp (-x ^ 2) := by
    intro x; norm_num
  simp only [this]
  exact integral_gaussian_eq

/-! ### The germ itself -/

/-- Degree-four homogeneity, the only structural fact the localization uses. -/
example (t : ℝ) (w : EuclideanSpace ℝ (Fin (1 * 1 + 1 * 1))) :
    residualGerm 1 1 1 (t • w) = t ^ 4 * residualGerm 1 1 1 w :=
  residualGerm_smul t w

/-- **V2b.** The anti-vacuity witness at a singular germ, with no frontier hypothesis. -/
example : HasLocalVolumeOrder (residualGerm 1 1 1) 0 (1 / 2) 2 :=
  hasLocalVolumeOrder_residualGerm_one

/-- It lands in the nondegenerate branch: the exponent is positive and the multiplicity is at
least one, so this is not the neutral `(0, 1)` convention for a germ vanishing near the base
point. -/
example : (0:ℝ) < 1 / 2 ∧ 1 ≤ 2 := ⟨by norm_num, by norm_num⟩

end AISafetyAtlas.Examples.SingularLearning
