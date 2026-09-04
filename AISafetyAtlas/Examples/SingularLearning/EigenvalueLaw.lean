module

public import AISafetyAtlas.SingularLearning.EigenvalueLaw

/-!
# Worked models: the `O70-EIGEN-LAW` frontier

`EigenvalueLawStatement` is a hypothesis, not a theorem, so the examples here are of two kinds:
checks that the proposition is well-formed and says what print says, and consequences that a
malformed transcription would fail. **None of them inhabits the proposition**, and none is
evidence that it holds.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory Matrix

/-! ### The determinant really is the eigenvalue product

The frontier is stated through `det (1 + T · X Xᵀ)` rather than through a `Fin k`-indexed vector
of eigenvalues. These check that the choice hides nothing. -/

/-- On a diagonal Gram matrix the determinant is visibly `∏ (1 + T sᵢ)`. -/
example (T a b : ℝ) :
    (1 + T • (Matrix.diagonal ![a, b])).det = (1 + T * a) * (1 + T * b) := by
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ) + T • Matrix.diagonal ![a, b]
      = Matrix.diagonal ![1 + T * a, 1 + T * b] by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]]
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]

/-- **The general identity**: for a Hermitian matrix, `det (1 + T·A) = ∏ (1 + T μᵢ)`. -/
example {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian) (T : ℝ) :
    (1 + T • A).det = ∏ i, (1 + T * hA.eigenvalues i) :=
  det_one_add_smul_eq_prod_eigenvalues hA T

/-- The Gram matrix is Hermitian, so the identity applies where the frontier uses it. -/
example {k d : ℕ} (X : Matrix (Fin k) (Fin d) ℝ) : (X * Xᵀ).IsHermitian :=
  isHermitian_gram X

/-! ### The frozen surface

`eigenvalueLawStatement_iff` writes out the right-hand side rather than naming `chamberJFull`,
so the statement lock sees the Vandermonde factor, the weight exponent and the orthant. -/

example :
    EigenvalueLawStatement ↔
      ∀ k d : ℕ, 0 < k → k ≤ d →
        ∃ Z : ℝ, 0 < Z ∧
          ∀ ρ : ℝ, 0 ≤ ρ → ∀ T : ℝ, 0 ≤ T →
            ∫ X : Fin k → Fin d → ℝ,
                Real.exp (-∑ i, ∑ j, X i j ^ 2)
                  * (1 + T • (Matrix.of X * (Matrix.of X)ᵀ)).det ^ (-ρ)
              = Z * ∫ s in Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ),
                  Real.exp (-∑ i, s i) * (∏ i, s i ^ (((d : ℝ) - k - 1) / 2))
                    * chamberAbsVandermonde s * ∏ i, (1 + T * s i) ^ (-ρ) :=
  eigenvalueLawStatement_iff

/-- **The exponent is formed in `ℝ`.** At `d = k` it is `−1/2`, not `0`: a `ℕ`-truncated
`(d − k − 1)` would collapse the weight to `1` and change the proposition. -/
example : (((3 : ℕ) : ℝ) - (3 : ℕ) - 1) / 2 = -(1/2) := by norm_num

/-- And it is `0` exactly one step up, at `d = k + 1`. -/
example : (((4 : ℕ) : ℝ) - (3 : ℕ) - 1) / 2 = 0 := by norm_num

/-! ### Consequences, assuming the frontier -/

/-- The normalisation at `T = 0`. -/
example (hEigen : EigenvalueLawStatement) {k d : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    ∃ Z : ℝ, 0 < Z ∧
      ∫ X : Fin k → Fin d → ℝ, Real.exp (-∑ i, ∑ j, X i j ^ 2)
        = Z * chamberJFull k 0 (((d : ℝ) - k - 1) / 2) 0 :=
  eigenvalueLaw_normalisation hEigen hk hkd

/-- `J(0)` is finite and positive, read off the proposition rather than assumed separately. -/
example (hEigen : EigenvalueLawStatement) :
    0 < chamberJFull 2 0 (((5 : ℕ) : ℝ) - (2 : ℕ) - 1) 0 ∨
      0 < chamberJFull 2 0 ((((5 : ℕ) : ℝ) - (2 : ℕ) - 1) / 2) 0 :=
  Or.inr (eigenvalueLaw_chamberJFull_pos hEigen (k := 2) (d := 5) (by norm_num) (by norm_num))

/-- The `1 × 1` check: `Z · J(0) = √π` at exponent `−1/2`. -/
example (hEigen : EigenvalueLawStatement) :
    ∃ Z : ℝ, 0 < Z ∧ Z * chamberJFull 1 0 (-(1/2)) 0 = Real.sqrt Real.pi :=
  eigenvalueLaw_one_one hEigen

end AISafetyAtlas.Examples.SingularLearning
