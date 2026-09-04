module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Matrix.PosDef
public import AISafetyAtlas.SingularLearning.GaussianQuadratic

/-!
# Lemma 8.10: the elementary spectral facts about the two Gram matrices

## What this module is for

The MAIS issue #3 candidate's residual computation runs
Proposition 8.9 → Lemma 8.10 → Proposition 8.13. Proposition 8.9
(`integral_exp_neg_frobenius_mul`, in `GaussianQuadratic.lean`) eliminates the `Y`
variable and leaves a determinant `det (I + T X Xᵀ)` of size `h × h`. Lemma 8.10 is
the bookkeeping that lets that determinant be rewritten in terms of the *other*
Gram matrix `Xᵀ X`, of size `n × n`, so that Proposition 8.13 may always work with
the smaller of the two. The candidate **derives** these facts rather than citing
them, so they sit inside the trust boundary and are proved here.

## What the pinned Mathlib already had

Almost all of it, which is worth recording precisely, since a library survey for
this project has more than once predicted the opposite:

* The **Weinstein–Aronszajn identity** `Matrix.det_one_add_mul_comm` is present *for
  rectangular blocks*, `det (1 + A * B) = det (1 + B * A)` with `A : Matrix m n α`
  and `B : Matrix n m α` and the two `1`s of different shapes
  (`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`). So the headline statement
  `det_one_add_smul_gram_comm` is a three-line rearrangement of the scalar, not a
  development.
* `Matrix.posSemidef_self_mul_conjTranspose` gives item 3 directly; over `ℝ` the star
  operation is trivial, so `Xᴴ` and `Xᵀ` agree.
* `Matrix.PosSemidef.eigenvalues_nonneg` and `Matrix.PosSemidef.det_nonneg`
  (`Mathlib/Analysis/Matrix/PosDef.lean`) give item 4.

The one genuinely missing piece is the trace identity in Frobenius form. Mathlib's
`Matrix.trace_transpose_mul` is a *different* statement (`trace (Aᵀ * Bᵀ) = trace (A * B)`,
a `Finset.sum_comm`), and there is no lemma equating `trace (X Xᵀ)` with the sum of
squared entries; `trace_mul_transpose` below supplies it, together with the fact that the
two Gram matrices have equal trace.

## Contents

1. `trace_mul_transpose`, `trace_transpose_mul`, `trace_gram_comm` — the trace identity.
2. `det_one_add_smul_gram_comm` — the form Proposition 8.13 consumes.
3. `posSemidef_mul_transpose`, `posSemidef_transpose_mul` — positive semidefiniteness.
4. `eigenvalues_mul_transpose_nonneg`, `det_mul_transpose_nonneg` — the cheap corollaries.
5. `integral_exp_neg_frobenius_mul_gram` — Proposition 8.13: Proposition 8.9 restated
   through the `n × n` Gram matrix `Xᵀ X`.

**This module is pure linear algebra plus one rewrite.** It says nothing about learning
coefficients or volume asymptotics.
-/

namespace AISafetyAtlas.SingularLearning

open Matrix

/-! ## The trace identity -/

/-- The trace of the `h × h` Gram matrix is the squared Frobenius norm of `X`.

Mathlib has `Matrix.trace_transpose_mul`, but that is the unrelated
`trace (Aᵀ * Bᵀ) = trace (A * B)`; the entrywise identity below is not in the pinned
revision. -/
public theorem trace_mul_transpose {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    (X * Xᵀ).trace = ∑ i, ∑ j, X i j ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]

/-- The same identity for the `n × n` Gram matrix: `trace (Xᵀ X)` is again the squared
Frobenius norm of `X`, but summed in the other order. -/
public theorem trace_transpose_mul {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    (Xᵀ * X).trace = ∑ j, ∑ i, X i j ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]

/-- The two Gram matrices have the same trace — the `k = 1` case of "same nonzero
eigenvalues with the same multiplicities". -/
public theorem trace_gram_comm {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    (X * Xᵀ).trace = (Xᵀ * X).trace :=
  Matrix.trace_mul_comm X Xᵀ

/-! ## Equality of the two characteristic determinants

This is the form Proposition 8.13 actually consumes, and it is the precise sense in which
`X Xᵀ` and `Xᵀ X` "have the same nonzero eigenvalues with the same multiplicities": the
two polynomials `T ↦ det (1 + T • G)` agree, so the nonzero spectra agree with
multiplicity, the two matrices differing only in the multiplicity of the eigenvalue `0`
(forced by the shape difference `h` versus `n`). -/

/-- **Sylvester's determinant identity for the two Gram matrices.**
`det (I_h + T X Xᵀ) = det (I_n + T Xᵀ X)` for every scalar `T`, with the two identity
matrices of different sizes.

One-line consequence of Mathlib's rectangular Weinstein–Aronszajn identity
`Matrix.det_one_add_mul_comm`, after moving the scalar onto one factor. -/
public theorem det_one_add_smul_gram_comm {h n : ℕ} (T : ℝ) (X : Matrix (Fin h) (Fin n) ℝ) :
    (1 + T • (X * Xᵀ)).det = (1 + T • (Xᵀ * X)).det := by
  rw [show T • (X * Xᵀ) = (T • X) * Xᵀ from (Matrix.smul_mul T X Xᵀ).symm,
    show T • (Xᵀ * X) = Xᵀ * (T • X) from (Matrix.mul_smul Xᵀ T X).symm,
    Matrix.det_one_add_mul_comm]

/-- The unscaled Sylvester identity, `det (I + X Xᵀ) = det (I + Xᵀ X)`. -/
public theorem det_one_add_gram_comm {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    (1 + X * Xᵀ).det = (1 + Xᵀ * X).det :=
  Matrix.det_one_add_mul_comm X Xᵀ

/-! ## Positive semidefiniteness -/

/-- The `h × h` Gram matrix is positive semidefinite. Over `ℝ` the conjugate transpose is
the transpose, so this is `Matrix.posSemidef_self_mul_conjTranspose`. -/
public theorem posSemidef_mul_transpose {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    (X * Xᵀ).PosSemidef := by
  simpa using Matrix.posSemidef_self_mul_conjTranspose X

/-- The `n × n` Gram matrix is positive semidefinite. -/
public theorem posSemidef_transpose_mul {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    (Xᵀ * X).PosSemidef := by
  simpa using Matrix.posSemidef_conjTranspose_mul_self X

/-! ## Nonnegativity of the spectrum and of the determinant -/

/-- Every eigenvalue of `X Xᵀ` is nonnegative. -/
public theorem eigenvalues_mul_transpose_nonneg {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ)
    (i : Fin h) : 0 ≤ (posSemidef_mul_transpose X).1.eigenvalues i :=
  (posSemidef_mul_transpose X).eigenvalues_nonneg i

/-- Every eigenvalue of `Xᵀ X` is nonnegative. -/
public theorem eigenvalues_transpose_mul_nonneg {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ)
    (j : Fin n) : 0 ≤ (posSemidef_transpose_mul X).1.eigenvalues j :=
  (posSemidef_transpose_mul X).eigenvalues_nonneg j

/-- `det (X Xᵀ) ≥ 0`. -/
public theorem det_mul_transpose_nonneg {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    0 ≤ (X * Xᵀ).det :=
  (posSemidef_mul_transpose X).det_nonneg

/-- `det (Xᵀ X) ≥ 0`. -/
public theorem det_transpose_mul_nonneg {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    0 ≤ (Xᵀ * X).det :=
  (posSemidef_transpose_mul X).det_nonneg

/-- For `0 ≤ T` the matrix `I + T X Xᵀ` appearing in Proposition 8.9 is positive definite,
hence its determinant is positive: the base of the power in Proposition 8.9 is never zero
and never negative. -/
public theorem posDef_one_add_smul_mul_transpose {h n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (X : Matrix (Fin h) (Fin n) ℝ) : (1 + T • (X * Xᵀ)).PosDef :=
  Matrix.PosDef.one.add_posSemidef ((posSemidef_mul_transpose X).smul hT)

/-- Consequently the determinant in Proposition 8.13's smaller Gram matrix is positive
too — by `det_one_add_smul_gram_comm` it is the same number. -/
public theorem det_one_add_smul_transpose_mul_pos {h n : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (X : Matrix (Fin h) (Fin n) ℝ) : 0 < (1 + T • (Xᵀ * X)).det := by
  rw [← det_one_add_smul_gram_comm]
  exact (posDef_one_add_smul_mul_transpose hT X).det_pos

/-! ## Proposition 8.13: the residual integral through the smaller Gram matrix -/

/-- **Proposition 8.13.** Proposition 8.9 (`integral_exp_neg_frobenius_mul`) composed with
Lemma 8.10: the `Y`-integral of the residual depends on `X` only through the `n × n` Gram
matrix `Xᵀ X`.

Together with the `h × h` form already proved in `GaussianQuadratic.lean`, this says the
integrand may be evaluated through whichever of `X Xᵀ`, `Xᵀ X` is smaller — the point of
the candidate's Proposition 8.13. -/
public theorem integral_exp_neg_frobenius_mul_gram {p h n : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (X : Matrix (Fin h) (Fin n) ℝ) :
    ∫ Y : Fin p → Fin h → ℝ,
        Real.exp (-T * ∑ i, ∑ j, (Matrix.of Y * X) i j ^ 2 - ∑ i, ∑ j, Y i j ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2) * (1 + T • (Xᵀ * X)).det ^ (-(p : ℝ) / 2) := by
  rw [integral_exp_neg_frobenius_mul T hT X, det_one_add_smul_gram_comm]

/-! ## Worked examples -/

/-- The trace identity on a `1 × 2` matrix: `trace (X Xᵀ)` is the sum of the two squares. -/
example (a b : ℝ) :
    (!![a, b] * !![a, b]ᵀ).trace = a ^ 2 + b ^ 2 := by
  rw [trace_mul_transpose]
  simp [Fin.sum_univ_succ]

/-- Sylvester's identity in the extreme rectangular case `h = 2`, `n = 1`: a `2 × 2`
determinant on the left, a `1 × 1` determinant on the right. -/
example (T a b : ℝ) :
    (1 + T • (!![a; b] * !![a; b]ᵀ)).det = 1 + T * (a ^ 2 + b ^ 2) := by
  rw [det_one_add_smul_gram_comm]
  simp [Matrix.det_unique, Matrix.mul_apply, Fin.sum_univ_succ, sq]

/-- Proposition 8.13 at `T = 0`: both Gram matrices drop out and the integral is the plain
Gaussian normalisation `π ^ (ph/2)`. -/
example (p h n : ℕ) (X : Matrix (Fin h) (Fin n) ℝ) :
    ∫ Y : Fin p → Fin h → ℝ,
        Real.exp (-0 * ∑ i, ∑ j, (Matrix.of Y * X) i j ^ 2 - ∑ i, ∑ j, Y i j ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2) := by
  rw [integral_exp_neg_frobenius_mul_gram 0 le_rfl X]
  simp

end AISafetyAtlas.SingularLearning
