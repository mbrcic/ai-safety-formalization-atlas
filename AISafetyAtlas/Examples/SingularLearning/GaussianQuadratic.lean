module

public import AISafetyAtlas.SingularLearning.GaussianQuadratic

/-!
# Worked models for the multivariate Gaussian integral

Two gaps in the pinned Mathlib are filled by
`AISafetyAtlas/SingularLearning/GaussianQuadratic.lean`, and both are reusable
well beyond MAIS-O70:

1. **The general positive-definite Gaussian integral.** Mathlib has only the
   isotropic case, `GaussianFourier.integral_rexp_neg_mul_sq_norm :
   ∫ v, exp(-b‖v‖²) = (π/b)^(finrank/2)`. The quadratic form with a determinant
   is absent.
2. **An integral-level change of variables under a linear map.** Mathlib has the
   measure-level `Measure.map_linearMap_addHaar_eq_smul_addHaar` and scalar
   dilations, but no corollary for `∫ f ∘ L`.

The proof avoids diagonalisation entirely: `M.PosDef` gives `M = Bᵀ B` through
the continuous functional calculus square root, `xᵀMx = ‖Bx‖²` reduces to the
isotropic case, and `Matrix.PosSemidef.det_sqrt` supplies the Jacobian
`|det B| = √(det M)` with no sign bookkeeping.

## What it buys MAIS-O70

Proposition 8.9 of the issue #3 candidate — integrating the `Y` variable out of
the residual Laplace transform, exactly. This is the first node of the residual
computation, and one the candidate *derives* rather than cites, so it sits inside
the trust boundary rather than on it.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The multivariate Gaussian integral, for any positive-definite form. -/
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(x ⬝ᵥ M.mulVec x))
      = Real.pi ^ ((n : ℝ) / 2) / Real.sqrt M.det :=
  integral_exp_neg_quadraticForm M hM

end AISafetyAtlas.Examples.SingularLearning
