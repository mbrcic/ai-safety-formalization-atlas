module

public import AISafetyAtlas.SingularLearning.ResidualLaplace

/-!
# Worked models: the Gaussian-weighted Laplace transform of `‖YX‖²_F`

Print's Theorem 8.1 determines the local pair of the residual germ at the origin. These
exercise the two halves of the chain — the unconditional reduction to an `X`-integral, and the
frontier step that evaluates it — and record the shape of the conclusion.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory Matrix

/-! ### Integrability -/

/-- The Gaussian is integrable on a matrix entry space: `Integrable.fintype_prod` applied once
over rows and once within a row. -/
example (m k : ℕ) :
    Integrable (fun X : Matrix (Fin m) (Fin k) ℝ => Real.exp (-frobeniusSq X)) volume :=
  integrable_exp_neg_frobeniusSq' m k

/-- The joint integrand is integrable on the product, which is what Fubini needs. -/
example {p n h : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    Integrable (residualGaussian p n h T) volume :=
  integrable_residualGaussian hT

/-! ### The unconditional reduction

Proposition 8.9 does the `Y`-integral exactly; nothing is assumed. -/

example (p n h : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ w : EuclideanSpace ℝ (Fin (h * n + p * h)),
        Real.exp (-T * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2)
        * ∫ X : Matrix (Fin h) (Fin n) ℝ,
            Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-(p : ℝ) / 2) :=
  gaussianLaplace_residualGerm_eq_det p n h hT

/-- **At `T = 0`** the determinant factor is `1` and the identity is the plain Gaussian
normalisation split between the two blocks. -/
example (p n h : ℕ) :
    ∫ w : EuclideanSpace ℝ (Fin (h * n + p * h)),
        Real.exp (-(0:ℝ) * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2)
        * ∫ X : Matrix (Fin h) (Fin n) ℝ,
            Real.exp (-frobeniusSq X) * (1 + (0:ℝ) • (X * Xᵀ)).det ^ (-(p : ℝ) / 2) :=
  gaussianLaplace_residualGerm_eq_det p n h le_rfl

/-! ### The frontier step and Theorem 8.1 -/

/-- **Proposition 8.13**: the `X`-integral is a multiple of the chamber integral, with one
normalising constant serving every `T`. -/
example (hEigen : EigenvalueLawStatement) (p n h : ℕ) (hh : 0 < h) (hhn : h ≤ n) :
    ∃ Z : ℝ, 0 < Z ∧ ∀ T : ℝ, 0 ≤ T →
      ∫ w : EuclideanSpace ℝ (Fin (h * n + p * h)),
          Real.exp (-T * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2)
        = Real.pi ^ ((p * h : ℝ) / 2) * Z
          * chamberJFull h T (((n : ℝ) - h - 1) / 2) ((p : ℝ) / 2) :=
  gaussianLaplace_residualGerm_eq_chamber hEigen p n h hh hhn

/-- **Theorem 8.1.** The local pair of `‖YX‖²_F` at the origin is `(E⋆, N⋆)`, conditional on
`O70-EIGEN-LAW` and nothing else. -/
example (hEigen : EigenvalueLawStatement) (p n h : ℕ) (hp : 0 < p) (hh : 0 < h) (hhn : h ≤ n) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      (chamberMinExponent h (((n : ℝ) - h - 1) / 2) ((p : ℝ) / 2))
      (chamberResonanceCount h (((n : ℝ) - h - 1) / 2) ((p : ℝ) / 2) + 1) :=
  hasLocalVolumeOrder_residualGerm hEigen p n h hp hh hhn

/-- **The scalar germ**, `(p, n, h) = (1, 1, 1)`: `f(y, x) = (yx)²` on `ℝ²`. Here `α = −1/2`,
`ρ = 1/2`, and the two vertex exponents tie, so the multiplicity is two — the case that carries
a logarithm and that a pure power comparison could not see. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (residualGerm 1 1 1) 0
      (chamberMinExponent 1 (((1 : ℕ) : ℝ) - (1 : ℕ) - 1) ((1 : ℝ) / 2) * 0
        + chamberMinExponent 1 ((((1 : ℕ) : ℝ) - (1 : ℕ) - 1) / 2) (((1 : ℕ) : ℝ) / 2))
      (chamberResonanceCount 1 ((((1 : ℕ) : ℝ) - (1 : ℕ) - 1) / 2) (((1 : ℕ) : ℝ) / 2) + 1) := by
  rw [mul_zero, zero_add]
  exact hasLocalVolumeOrder_residualGerm hEigen 1 1 1 one_pos one_pos le_rfl

/-- **A wide shape**, `h < n`: the germ is `‖YX‖²_F` on `ℝ^{3×2} × ℝ^{2×5}`. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (residualGerm 3 5 2) 0
      (chamberMinExponent 2 ((((5 : ℕ) : ℝ) - (2 : ℕ) - 1) / 2) (((3 : ℕ) : ℝ) / 2))
      (chamberResonanceCount 2 ((((5 : ℕ) : ℝ) - (2 : ℕ) - 1) / 2) (((3 : ℕ) : ℝ) / 2) + 1) :=
  hasLocalVolumeOrder_residualGerm hEigen 3 5 2 (by norm_num) (by norm_num) (by norm_num)


/-! ### The transposed shape -/

/-- **Transposition preserves Lebesgue measure**: it permutes the entries and nothing else. This
is what makes the tall case `h > n` the same frontier rather than a second one. -/
example (m k : ℕ) : MeasurePreserving (matrixTransposeEquiv m k) volume volume :=
  measurePreserving_matrixTransposeEquiv m k

/-- **The `X`-integral is transposition-invariant**, by `frobeniusSq_transpose` for the Gaussian
factor and Sylvester's identity for the determinant. -/
example (n h : ℕ) (T ρ : ℝ) :
    ∫ X : Matrix (Fin h) (Fin n) ℝ,
        Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-ρ)
      = ∫ X : Matrix (Fin n) (Fin h) ℝ,
          Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-ρ) :=
  integral_det_transpose n h T ρ

/-- **Theorem 8.1 at every positive shape**, indexed at `k = min h n` and `d = max h n`. -/
example (hEigen : EigenvalueLawStatement) (p n h : ℕ) (hp : 0 < p) (hn : 0 < n) (hh : 0 < h) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      (chamberMinExponent (min h n)
        ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2) ((p : ℝ) / 2))
      (chamberResonanceCount (min h n)
        ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2) ((p : ℝ) / 2) + 1) :=
  hasLocalVolumeOrder_residualGerm_min hEigen p n h hp hn hh

/-- **A tall shape**, `n < h`. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (residualGerm 3 2 5) 0
      (chamberMinExponent 2 ((((5 : ℕ) : ℝ) - (2 : ℕ) - 1) / 2) (((3 : ℕ) : ℝ) / 2))
      (chamberResonanceCount 2 ((((5 : ℕ) : ℝ) - (2 : ℕ) - 1) / 2) (((3 : ℕ) : ℝ) / 2) + 1) :=
  hasLocalVolumeOrder_residualGerm_tall hEigen 3 2 5 (by norm_num) (by norm_num) (by norm_num)

end AISafetyAtlas.Examples.SingularLearning
