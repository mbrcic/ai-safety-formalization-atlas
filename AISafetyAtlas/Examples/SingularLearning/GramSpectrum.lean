module

public import AISafetyAtlas.SingularLearning.GramSpectrum

/-!
# Worked models for the Gram-matrix step

Lemma 8.10 and Proposition 8.13 of the MAIS issue #3 candidate. Both are steps
the candidate *derives* rather than cites, so they sit inside the trust boundary
and are proved here rather than assumed.

The content: the residual integrand depends on `X` only through the **smaller**
of the two Gram matrices, because `det (1 + T·XXᵀ) = det (1 + T·XᵀX)` even though
the two identity matrices have different shapes.

## What Mathlib had, and what it did not

The library survey was optimistic-and-correct on three items and wrong on the one
that looked easiest — the reverse of the pattern this project has otherwise seen.

* **Present, and it makes Prop 8.13 a three-line proof:**
  `Matrix.det_one_add_mul_comm` (Weinstein–Aronszajn) holds for *rectangular*
  blocks, with the two `1`s of genuinely different sizes.
* **Present:** `Matrix.posSemidef_self_mul_conjTranspose`,
  `Matrix.PosSemidef.eigenvalues_nonneg`, `Matrix.PosSemidef.det_nonneg`.
* **Absent:** the Frobenius trace identity. `Matrix.trace_transpose_mul` exists
  but says something else — `trace (Aᵀ * Bᵀ) = trace (A * B)`. Nothing equates
  `trace (X * Xᵀ)` with `∑ i, ∑ j, X i j ^ 2`.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open scoped Matrix

/-- The Frobenius trace identity, which Mathlib does not have. -/
example {h n : ℕ} (X : Matrix (Fin h) (Fin n) ℝ) :
    (X * Xᵀ).trace = ∑ i, ∑ j, X i j ^ 2 :=
  trace_mul_transpose X

/-- **Lemma 8.10's usable form.** The two Gram matrices give the same
determinant, so the residual integrand may be read on whichever is smaller. -/
example {h n : ℕ} (T : ℝ) (X : Matrix (Fin h) (Fin n) ℝ) :
    (1 + T • (X * Xᵀ)).det = (1 + T • (Xᵀ * X)).det :=
  det_one_add_smul_gram_comm T X

end AISafetyAtlas.Examples.SingularLearning
