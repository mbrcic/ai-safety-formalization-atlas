module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The multivariate Gaussian integral, and the exact `Y` integral of Proposition 8.9

## The gap this module fills

The pinned Mathlib has the **isotropic** Gaussian integral over a finite-dimensional real
inner-product space,

    GaussianFourier.integral_rexp_neg_mul_sq_norm :
      0 < b → ∫ v : V, exp (-b * ‖v‖ ^ 2) = (π / b) ^ (finrank ℝ V / 2 : ℝ) ,

and the one-dimensional `integral_gaussian`. It does **not** have the general
positive-definite quadratic form with a determinant,

    ∫ x, exp (-(xᵀ M x)) dx = π ^ (n/2) / √(det M) ,     M positive definite,

in any spelling: there is no `Matrix.PosDef` Gaussian-integral lemma, and the multivariate
Gaussian of `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` is built from
characteristic functions rather than from a density, so it does not supply this identity
either. `integral_exp_neg_quadraticForm` below is that missing statement, and
`integral_exp_neg_quadraticForm_pi` is the same integral over the plain product space
`Fin n → ℝ` (whose ambient norm is the *supremum* norm, so the quadratic form, not a norm,
is what is written).

## Route

Not by diagonalising. A positive-definite `M` factors as `M = Bᵀ B`
(`exists_transpose_mul_self_of_posDef`, from the continuous-functional-calculus square root
`CFC.sqrt`, whose determinant Mathlib already computes as `√(det M)`), so the quadratic form
is the squared Euclidean norm of `B x` and a single **linear change of variables** `y = B x`
reduces the whole statement to the isotropic case. The Jacobian is
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`, which says a linear self-map
with nonzero determinant pushes an additive Haar measure to `|det f|⁻¹ • μ`; combined with
`MeasurableEmbedding.integral_map` and `integral_smul_measure` this gives the reusable
`integral_comp_linearMap`, itself absent from Mathlib (only the scalar-dilation special cases
`Measure.integral_comp_smul` and friends are there).

## Proposition 8.9

`integral_exp_neg_frobenius_mul` is Proposition 8.9 of the MAIS issue #3 candidate: the exact
elimination of the `Y` variable,

    ∫ exp (-T ‖Y X‖²_F - ‖Y‖²_F) dY = π ^ (ph/2) · det (I + T X Xᵀ) ^ (-p/2) ,

which is the first step of the candidate's residual computation, and a step it **derives**
rather than cites. The proof reads the Frobenius norms row by row: `‖Y X‖²_F = ∑_y ‖yᵀ X‖²`
and `‖Y‖²_F = ∑_y ‖y‖²` over the `p` rows `y` of `Y`, so the integrand is a product of `p`
identical factors `exp (-(yᵀ (I + T X Xᵀ) y))` and the integral is the `p`-th power of one
`h`-dimensional Gaussian integral. `I + T X Xᵀ` is positive definite for `T ≥ 0` because
`X Xᵀ` is positive semidefinite (`Matrix.posSemidef_self_mul_conjTranspose`).

The headline statement integrates over `Y : Fin p → Fin h → ℝ` and writes the two Frobenius
norms as explicit double sums, because `Matrix (Fin p) (Fin h) ℝ` carries no `MeasureSpace`
instance and Mathlib's Frobenius norm on matrices is not a global instance.
`integral_exp_neg_frobenius_mul_norm` restates it with Mathlib's Frobenius norm under the
`local instance` convention already used by `Loss.lean`.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Matrix Real WithLp
open scoped Matrix MatrixOrder

/-! ## Change of variables along a linear map -/

/-- **Linear change of variables.** For an additive Haar measure `μ` on a finite-dimensional
real normed space and a linear self-map `f` with nonzero determinant,

    ∫ x, g (f x) ∂μ = |det f|⁻¹ • ∫ y, g y ∂μ .

Mathlib has the measure-level statement
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` but not this integral-level
corollary; only the scalar-dilation special cases (`Measure.integral_comp_smul` and friends)
are available. No hypothesis on `g` is needed, because `f` is a homeomorphism and hence a
measurable embedding. -/
public theorem integral_comp_linearMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) (g : E → F) :
    ∫ x, g (f x) ∂μ = |LinearMap.det f|⁻¹ • ∫ y, g y ∂μ := by
  have hemb : MeasurableEmbedding f :=
    (f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  rw [← hemb.integral_map (μ := μ) g, Measure.map_linearMap_addHaar_eq_smul_addHaar μ hf,
    integral_smul_measure]
  simp [abs_inv]

/-! ## The square-root factorization -/

/-- Every positive-definite real matrix factors as `M = Bᵀ * B` with `B.det = √(det M)`.

The witness is the continuous-functional-calculus square root `CFC.sqrt M`, which is
self-adjoint (hence symmetric over `ℝ`) and squares to `M`; its determinant is `√(det M)` by
`Matrix.PosSemidef.det_sqrt`. Positive definiteness is used only through
`Matrix.nonneg_iff_posSemidef`, i.e. to know `0 ≤ M` in the matrix order. -/
public theorem exists_transpose_mul_self_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) : ∃ B : Matrix (Fin n) (Fin n) ℝ, M = Bᵀ * B ∧ B.det = √M.det := by
  have hnn : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hsh : (CFC.sqrt M)ᵀ = CFC.sqrt M :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian
  refine ⟨CFC.sqrt M, ?_, ?_⟩
  · rw [hsh, CFC.sqrt_mul_sqrt_self M hnn]
  · rw [hM.posSemidef.det_sqrt, RCLike.sqrt_of_nonneg hM.posSemidef.det_nonneg]
    simp

/-! ## The multivariate Gaussian integral -/

/-- **The multivariate Gaussian integral.** For a positive-definite `M : ℝ^{n×n}`,

    ∫_{ℝⁿ} exp (-(xᵀ M x)) dx = π ^ (n/2) / √(det M) .

The integral is taken over `EuclideanSpace ℝ (Fin n)`, whose `volume` is Lebesgue measure;
the quadratic form is written on the underlying vector `ofLp x : Fin n → ℝ`.

Absent from the pinned Mathlib, which has only the isotropic case
`GaussianFourier.integral_rexp_neg_mul_sq_norm`. The proof writes `M = Bᵀ B` and applies
`integral_comp_linearMap` to `y = B x`, whose Jacobian `|det B| = √(det M)` is exactly the
determinant factor. -/
public theorem integral_exp_neg_quadraticForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) :
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(ofLp x ⬝ᵥ M *ᵥ ofLp x))
      = Real.pi ^ ((n : ℝ) / 2) / √M.det := by
  obtain ⟨B, hBM, hBdet⟩ := exists_transpose_mul_self_of_posDef hM
  have hdetB : LinearMap.det (Matrix.toEuclideanLin B : _ →ₗ[ℝ] _) = B.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hne : LinearMap.det (Matrix.toEuclideanLin B : _ →ₗ[ℝ] _) ≠ 0 := by
    rw [hdetB, hBdet]
    exact ne_of_gt (Real.sqrt_pos.mpr hM.det_pos)
  -- `xᵀ M x = ‖B x‖²`, with the Euclidean norm.
  have key : ∀ x : EuclideanSpace ℝ (Fin n),
      Real.exp (-(ofLp x ⬝ᵥ M *ᵥ ofLp x))
        = Real.exp (-1 * ‖(Matrix.toEuclideanLin B : _ →ₗ[ℝ] _) x‖ ^ 2) := by
    intro x
    rw [hBM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      neg_one_mul, EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  simp only [key]
  rw [integral_comp_linearMap volume hne fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-1 * ‖y‖ ^ 2),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0 : ℝ) < 1), hdetB, hBdet]
  simp [abs_of_nonneg (Real.sqrt_nonneg M.det), smul_eq_mul, div_eq_inv_mul]

/-- The multivariate Gaussian integral over the plain product space `Fin n → ℝ`, whose
`volume` is the same Lebesgue measure. Transported from `integral_exp_neg_quadraticForm`
along `PiLp.volume_preserving_toLp`.

The quadratic form, rather than a norm, is what is written: the ambient norm on `Fin n → ℝ`
is the supremum norm, so `‖·‖` here would state a different — and false — theorem. -/
public theorem integral_exp_neg_quadraticForm_pi {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) :
    ∫ v : Fin n → ℝ, Real.exp (-(v ⬝ᵥ M *ᵥ v)) = Real.pi ^ ((n : ℝ) / 2) / √M.det := by
  have h := integral_exp_neg_quadraticForm M hM
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at h
  simpa using h

/-! ## Proposition 8.9: the `Y` integral is exact -/

/-- **Proposition 8.9 of the MAIS issue #3 candidate**: the `Y` integral is exact,

    ∫ exp (-T ‖Y X‖²_F - ‖Y‖²_F) dY = π ^ (ph/2) · det (I + T X Xᵀ) ^ (-p/2)

for `T ≥ 0`. This is the candidate's exact elimination of the `Y` variable — the first step
of its residual computation, and one it derives rather than cites.

`Y` ranges over `Fin p → Fin h → ℝ` rather than over `Matrix (Fin p) (Fin h) ℝ`, because the
latter carries no `MeasureSpace` instance; the two types are definitionally equal, and
`Matrix.of` is the transport. Both Frobenius norms are written as explicit double sums so
that the statement carries no norm instance; `integral_exp_neg_frobenius_mul_norm` is the
same statement with Mathlib's Frobenius norm.

The integrand factors over the `p` rows of `Y` into copies of
`exp (-(yᵀ (I + T X Xᵀ) y))`, so `integral_fintype_prod_volume_eq_pow` reduces the claim to
the `p`-th power of `integral_exp_neg_quadraticForm_pi` at `M = I + T X Xᵀ`, which is
positive definite by `Matrix.PosDef.one.add_posSemidef` and
`Matrix.posSemidef_self_mul_conjTranspose`. -/
public theorem integral_exp_neg_frobenius_mul {p h n : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (X : Matrix (Fin h) (Fin n) ℝ) :
    ∫ Y : Fin p → Fin h → ℝ,
        Real.exp (-T * ∑ i, ∑ j, (Matrix.of Y * X) i j ^ 2 - ∑ i, ∑ j, Y i j ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2) * (1 + T • (X * Xᵀ)).det ^ (-(p : ℝ) / 2) := by
  set A : Matrix (Fin h) (Fin h) ℝ := 1 + T • (X * Xᵀ) with hA
  have hApd : A.PosDef :=
    Matrix.PosDef.one.add_posSemidef ((Matrix.posSemidef_self_mul_conjTranspose X).smul hT)
  -- Row by row, the exponent is a sum of `p` copies of the quadratic form of `A`.
  have hfac : ∀ Y : Fin p → Fin h → ℝ,
      Real.exp (-T * ∑ i, ∑ j, (Matrix.of Y * X) i j ^ 2 - ∑ i, ∑ j, Y i j ^ 2)
        = ∏ i, Real.exp (-(Y i ⬝ᵥ A *ᵥ Y i)) := by
    intro Y
    have hrow : ∀ i : Fin p, Y i ⬝ᵥ A *ᵥ Y i
        = (∑ j, Y i j ^ 2) + T * ∑ j, (Matrix.of Y * X) i j ^ 2 := by
      intro i
      rw [hA, Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec, Matrix.smul_mulVec,
        dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.mulVec_transpose]
      simp [dotProduct, Matrix.mul_apply, Matrix.vecMul, sq]
    rw [← Real.exp_sum]
    congr 1
    simp only [hrow, neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  simp only [hfac]
  rw [integral_fintype_prod_volume_eq_pow
    (f := fun v : Fin h → ℝ => Real.exp (-(v ⬝ᵥ A *ᵥ v))),
    integral_exp_neg_quadraticForm_pi A hApd]
  rw [Fintype.card_fin, div_pow, ← Real.rpow_natCast (Real.pi ^ ((h : ℝ) / 2)) p,
    ← Real.rpow_mul Real.pi_nonneg, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast (A.det ^ ((1 : ℝ) / 2)) p, ← Real.rpow_mul hApd.det_pos.le,
    div_eq_mul_inv, ← Real.rpow_neg hApd.det_pos.le]
  ring_nf

/-! ## The Frobenius-norm form -/

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/-- The squared Frobenius norm of a real matrix is the sum of its squared entries. -/
public theorem frobenius_norm_sq {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℝ) :
    ‖M‖ ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

/-- Proposition 8.9 with Mathlib's Frobenius norm in place of the explicit double sums.

The Frobenius norm on matrices is a `local` instance rather than a global one (matrices carry
several natural norms), following the convention of `Loss.lean`; a consumer wanting this form
must reinstate `Matrix.frobeniusNormedAddCommGroup`, or use the instance-free
`integral_exp_neg_frobenius_mul`. -/
public theorem integral_exp_neg_frobenius_mul_norm {p h n : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (X : Matrix (Fin h) (Fin n) ℝ) :
    ∫ Y : Fin p → Fin h → ℝ,
        Real.exp (-T * ‖(Matrix.of Y : Matrix (Fin p) (Fin h) ℝ) * X‖ ^ 2
          - ‖(Matrix.of Y : Matrix (Fin p) (Fin h) ℝ)‖ ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2) * (1 + T • (X * Xᵀ)).det ^ (-(p : ℝ) / 2) := by
  simpa only [frobenius_norm_sq, Matrix.of_apply] using
    integral_exp_neg_frobenius_mul (p := p) T hT X

end Frobenius

/-! ## Worked examples -/

/-- The one-dimensional case of the general integral: `∫ exp (-a x²) dx = √(π/a)`,
recovered from `integral_exp_neg_quadraticForm_pi` at `n = 1`. -/
example (a : ℝ) (ha : 0 < a) :
    ∫ v : Fin 1 → ℝ, Real.exp (-(v ⬝ᵥ (a • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ v))
      = Real.pi ^ ((1 : ℝ) / 2) / √a := by
  have hpd : (a • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
    simpa using (Matrix.PosDef.one (n := Fin 1) (R := ℝ)).smul (a := a) ha
  rw [integral_exp_neg_quadraticForm_pi _ hpd]
  simp

/-- Proposition 8.9 at `T = 0`: the determinant factor disappears and the integral is the
plain Gaussian normalisation `π ^ (ph/2)`. -/
example (p h n : ℕ) (X : Matrix (Fin h) (Fin n) ℝ) :
    ∫ Y : Fin p → Fin h → ℝ,
        Real.exp (-(0 : ℝ) * ∑ i, ∑ j, (Matrix.of Y * X) i j ^ 2 - ∑ i, ∑ j, Y i j ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2) := by
  rw [integral_exp_neg_frobenius_mul (p := p) 0 le_rfl X]
  simp

end AISafetyAtlas.SingularLearning
