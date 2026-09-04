module

public import AISafetyAtlas.SingularLearning.ResidualGerm
public import AISafetyAtlas.SingularLearning.EigenvalueLaw
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Gaussian-weighted Laplace transform of `‖Y X‖²_F`

`hasLocalVolumeOrder_of_gaussianLaplace` takes a two-sided estimate on

    L_G(T) = ∫_{ℝ^D} e^{-T f(w)} e^{-‖w‖²} dw

and returns the local pair. This module computes `L_G` for the residual germ, which is what
§8.3–8.4 of the MAIS issue #3 candidate does.

## The computation

Two steps, and only the second is a frontier.

* **`gaussianLaplace_residualGerm_eq_det`** is unconditional. Transport the integral from
  Euclidean coordinates to the matrix pair — `matrixPairEquiv` is measure preserving and an
  isometry, so neither the measure nor the Gaussian weight moves — then Fubini, then
  Proposition 8.9 (`integral_exp_neg_frobenius_mul`, proved) for the inner `Y`-integral:

      L_G(T) = π^{ph/2} ∫_{ℝ^{h×n}} e^{-‖X‖²_F} det(1 + T·X Xᵀ)^{-p/2} dX .

* **`gaussianLaplace_residualGerm_eq_chamber`** applies `EigenvalueLawStatement` to the
  remaining `X`-integral, at the shape `k = h ≤ n = d`. This is the only step that leaves the
  atlas's proved cone, and the hypothesis is visible in the statement.

The wide case `h ≤ n` is the one the frontier is stated for, following the candidate's own
reduction ("replacing `X` by `Xᵀ` if `h > n` changes neither `‖X‖_F` nor `G(X)` nor the law of
the entries"). The transposed case needs a measure-preserving transpose on the entry space and
`det_one_add_smul_gram_comm`; it is not done here.

## Integrability

Fubini needs the joint integrand to be integrable on the product. It is dominated by
`e^{-‖X‖²_F} e^{-‖Y‖²_F}`, a product of Gaussians, and Gaussian integrability on a matrix space
is `Integrable.fintype_prod` applied twice — once over rows, once over entries within a row. No
Euclidean structure is used, so no transport is needed for this step.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Matrix

/-! ## Gaussian integrability on a matrix space -/

/-- `x ↦ e^{-∑ xⱼ²}` is integrable on `Fin k → ℝ`. -/
public theorem integrable_exp_neg_sum_sq (k : ℕ) :
    Integrable (fun x : Fin k → ℝ => Real.exp (-∑ j, x j ^ 2)) volume := by
  have hbase : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) volume := by
    simpa using integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
  have hfun : (fun x : Fin k → ℝ => Real.exp (-∑ j, x j ^ 2))
      = fun x : Fin k → ℝ => ∏ j, Real.exp (-(x j ^ 2)) := by
    funext x
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hfun, volume_pi]
  exact Integrable.fintype_prod (fun _ => hbase)

/-- `X ↦ e^{-‖X‖²_F}` is integrable on the entry space of an `m × k` matrix. -/
public theorem integrable_exp_neg_frobeniusSq (m k : ℕ) :
    Integrable (fun X : Fin m → Fin k → ℝ => Real.exp (-∑ i, ∑ j, X i j ^ 2)) volume := by
  have hfun : (fun X : Fin m → Fin k → ℝ => Real.exp (-∑ i, ∑ j, X i j ^ 2))
      = fun X : Fin m → Fin k → ℝ => ∏ i, Real.exp (-∑ j, X i j ^ 2) := by
    funext X
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hfun, volume_pi]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_sum_sq k)

/-- The same, phrased with `frobeniusSq` on the matrix type. `Matrix` is a `def` for the arrow
type and `instMeasureSpaceMatrix` is the arrow type's measure, so this is the previous lemma
with the sum folded up. -/
public theorem integrable_exp_neg_frobeniusSq' (m k : ℕ) :
    Integrable (fun X : Matrix (Fin m) (Fin k) ℝ => Real.exp (-frobeniusSq X)) volume :=
  integrable_exp_neg_frobeniusSq m k

/-! ## The joint integrand -/

variable {p n h : ℕ}

/-- The Gaussian-weighted integrand of the residual germ, on the matrix pair. -/
@[expose] public noncomputable def residualGaussian (p n h : ℕ) (T : ℝ)
    (z : Matrix (Fin h) (Fin n) ℝ × Matrix (Fin p) (Fin h) ℝ) : ℝ :=
  Real.exp (-T * frobeniusSq (z.2 * z.1)) * Real.exp (-(frobeniusSq z.1 + frobeniusSq z.2))

public theorem measurable_residualGaussian (T : ℝ) : Measurable (residualGaussian p n h T) := by
  unfold residualGaussian frobeniusSq
  simp only [Matrix.mul_apply]
  fun_prop

/-- **The joint integrand is integrable.** It is dominated by `e^{-‖X‖²_F} e^{-‖Y‖²_F}`, a
product of Gaussians on the two entry spaces. -/
public theorem integrable_residualGaussian {T : ℝ} (hT : 0 ≤ T) :
    Integrable (residualGaussian p n h T) volume := by
  have hdom : Integrable
      (fun z : Matrix (Fin h) (Fin n) ℝ × Matrix (Fin p) (Fin h) ℝ =>
        Real.exp (-frobeniusSq z.1) * Real.exp (-frobeniusSq z.2)) volume :=
    (integrable_exp_neg_frobeniusSq' h n).mul_prod (integrable_exp_neg_frobeniusSq' p h)
  refine hdom.mono' (measurable_residualGaussian T).aestronglyMeasurable ?_
  filter_upwards with z
  have hnn : 0 ≤ residualGaussian p n h T z := by
    unfold residualGaussian
    positivity
  rw [Real.norm_of_nonneg hnn, residualGaussian, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : 0 ≤ T * frobeniusSq (z.2 * z.1) :=
    mul_nonneg hT (frobeniusSq_nonneg _)
  linarith

/-! ## The evaluation -/

/-- **The inner `Y`-integral, by Proposition 8.9.** The Gaussian factor in `X` is a constant for
this integral, and what is left is exactly print's Proposition 8.9. -/
public theorem integral_residualGaussian_inner {T : ℝ} (hT : 0 ≤ T)
    (X : Matrix (Fin h) (Fin n) ℝ) :
    ∫ Y : Matrix (Fin p) (Fin h) ℝ, residualGaussian p n h T (X, Y)
      = Real.exp (-frobeniusSq X) * (Real.pi ^ ((p * h : ℝ) / 2)
          * (1 + T • (X * Xᵀ)).det ^ (-(p : ℝ) / 2)) := by
  have hfun : ∀ Y : Matrix (Fin p) (Fin h) ℝ, residualGaussian p n h T (X, Y)
      = Real.exp (-frobeniusSq X)
        * Real.exp (-T * ∑ i, ∑ j, (Matrix.of Y * X) i j ^ 2 - ∑ i, ∑ j, Y i j ^ 2) := by
    intro Y
    rw [residualGaussian, ← Real.exp_add, ← Real.exp_add]
    refine congrArg Real.exp ?_
    show -T * frobeniusSq (Y * X) + -(frobeniusSq X + frobeniusSq Y)
      = -frobeniusSq X + (-T * ∑ i, ∑ j, (Y * X) i j ^ 2 - ∑ i, ∑ j, Y i j ^ 2)
    simp only [frobeniusSq]
    ring
  simp only [hfun]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact integral_exp_neg_frobenius_mul T hT X

/-- **The Gaussian-weighted Laplace transform, reduced to an integral over `X` alone.**

Unconditional: the transport is measure preserving and isometric, Fubini applies because the
joint integrand is dominated by a product of Gaussians, and the inner integral is
Proposition 8.9. -/
public theorem gaussianLaplace_residualGerm_eq_det (p n h : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ w : EuclideanSpace ℝ (Fin (h * n + p * h)),
        Real.exp (-T * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2)
      = Real.pi ^ ((p * h : ℝ) / 2)
        * ∫ X : Matrix (Fin h) (Fin n) ℝ,
            Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-(p : ℝ) / 2) := by
  classical
  -- transport to the matrix pair
  have hemb : MeasurableEmbedding (matrixPairEquiv p n h) := by
    rw [coe_matrixPairEquiv]
    exact (matrixPairMeasurableEquiv p n h).measurableEmbedding
  have htr := (measurePreserving_matrixPairEquiv p n h).integral_comp hemb
    (fun w : EuclideanSpace ℝ (Fin (h * n + p * h)) =>
      Real.exp (-T * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2))
  have hval : ∀ z : Matrix (Fin h) (Fin n) ℝ × Matrix (Fin p) (Fin h) ℝ,
      Real.exp (-T * residualGerm p n h (matrixPairEquiv p n h z))
          * Real.exp (-‖matrixPairEquiv p n h z‖ ^ 2)
        = residualGaussian p n h T z := by
    intro z
    have hX : residualX p n h (matrixPairEquiv p n h z) = z.1 := by
      rw [residualX, LinearEquiv.symm_apply_apply]
    have hY : residualY p n h (matrixPairEquiv p n h z) = z.2 := by
      rw [residualY, LinearEquiv.symm_apply_apply]
    have hnorm : ‖matrixPairEquiv p n h z‖ ^ 2 = frobeniusSq z.1 + frobeniusSq z.2 := by
      rw [show z = (z.1, z.2) from rfl, norm_sq_matrixPairEquiv]
    rw [residualGerm, hX, hY, hnorm, residualGaussian]
  simp only [hval] at htr
  rw [← htr, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod _ (by
      rw [← MeasureTheory.Measure.volume_eq_prod]
      exact integrable_residualGaussian hT)]
  simp only [integral_residualGaussian_inner hT]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  ring

/-! ## The frontier step -/

/-- **The Gaussian-weighted Laplace transform as a chamber integral.**

The remaining `X`-integral is exactly what `EigenvalueLawStatement` evaluates, at the wide shape
`k = h ≤ n = d`. The normalising constant `Z` is produced once and serves every `T`, which is
how the frontier is stated.

This is print's Proposition 8.13. The frontier hypothesis is visible in the type; nothing else
in the chain leaves the atlas's proved cone. -/
public theorem gaussianLaplace_residualGerm_eq_chamber (hEigen : EigenvalueLawStatement)
    (p n h : ℕ) (hh : 0 < h) (hhn : h ≤ n) :
    ∃ Z : ℝ, 0 < Z ∧ ∀ T : ℝ, 0 ≤ T →
      ∫ w : EuclideanSpace ℝ (Fin (h * n + p * h)),
          Real.exp (-T * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2)
        = Real.pi ^ ((p * h : ℝ) / 2) * Z
          * chamberJFull h T (((n : ℝ) - h - 1) / 2) ((p : ℝ) / 2) := by
  obtain ⟨Z, hZ, hlaw⟩ := hEigen h n hh hhn
  refine ⟨Z, hZ, fun T hT => ?_⟩
  rw [gaussianLaplace_residualGerm_eq_det p n h hT]
  have hX : ∫ X : Matrix (Fin h) (Fin n) ℝ,
        Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-(p : ℝ) / 2)
      = Z * chamberJFull h T (((n : ℝ) - h - 1) / 2) ((p : ℝ) / 2) := by
    have h := hlaw ((p : ℝ) / 2) (by positivity) T hT
    rw [← h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    rw [neg_div]
    rfl
  rw [hX]
  ring

/-! ## Theorem 8.1: the local pair of the residual germ

The chain closes. `gaussianLaplace_residualGerm_eq_chamber` evaluates the Gaussian-weighted
Laplace transform as a multiple of the chamber integral; `chamberCor816` bounds that integral
two-sidedly by `H_{E⋆, N⋆}`; and `hasLocalVolumeOrder_of_gaussianLaplace` turns a two-sided
Laplace estimate into the local pair.

The exponent is `E⋆ = chamberMinExponent` and the multiplicity is `N⋆ = chamberResonanceCount + 1`,
at `α = (n − h − 1)/2` and `ρ = p/2`. `O70Proof.lean` identifies both with the candidate's
`residualMinCost / 2` and `residualMultiplicity`. -/

/-- The step from a chamber-integral evaluation of the Gaussian-weighted Laplace transform to
the local pair, with the chamber parameters left abstract. Both the wide and the tall case are
instances of it; only the shape `(k, α)` differs. -/
private theorem hasLocalVolumeOrder_of_chamber {p n h k : ℕ} {α Z : ℝ}
    (hα : (-1 : ℝ) < α) (hk : 0 < k) (hp : 0 < p) (hZ : 0 < Z)
    (hlap : ∀ T : ℝ, 0 ≤ T →
      ∫ w : EuclideanSpace ℝ (Fin (h * n + p * h)),
          Real.exp (-T * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2)
        = Real.pi ^ ((p * h : ℝ) / 2) * Z * chamberJFull k T α ((p : ℝ) / 2)) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      (chamberMinExponent k α ((p : ℝ) / 2))
      (chamberResonanceCount k α ((p : ℝ) / 2) + 1) := by
  set ρ := (p : ℝ) / 2 with hρdef
  have hρ : (0 : ℝ) < ρ := by
    rw [hρdef]
    have : (0 : ℝ) < p := by exact_mod_cast hp
    linarith
  obtain ⟨c, C, hc, -, hbounds⟩ := chamberCor816 (k := k) (α := α) (ρ := ρ) hα hρ hk
  have hpi : (0 : ℝ) < Real.pi ^ ((p * h : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hscale : ∀ T : ℝ, 3 ≤ T →
      laplaceScale (chamberMinExponent k α ρ) (chamberResonanceCount k α ρ + 1) T
        = T ^ (-chamberMinExponent k α ρ) * Real.log T ^ chamberResonanceCount k α ρ := by
    intro T _
    rw [laplaceScale, Nat.add_sub_cancel]
  refine hasLocalVolumeOrder_of_gaussianLaplace (k := 4)
    (C := Real.pi ^ ((p * h : ℝ) / 2) * Z * C) measurable_residualGerm
    (fun _ => residualGerm_nonneg _) residualGerm_hom
    (chamberMinExponent_pos hα hρ hk) (Nat.le_add_left 1 _)
    (show (0:ℝ) < Real.pi ^ ((p * h : ℝ) / 2) * Z * c by positivity) ?_ ?_
  · intro T hT
    rw [hlap T (by linarith), hscale T hT]
    have hlo := (hbounds T hT).1
    have hstep := mul_le_mul_of_nonneg_left hlo
      (by positivity : (0:ℝ) ≤ Real.pi ^ ((p * h : ℝ) / 2) * Z)
    calc Real.pi ^ ((p * h : ℝ) / 2) * Z * c
          * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ chamberResonanceCount k α ρ)
        = Real.pi ^ ((p * h : ℝ) / 2) * Z
          * (c * (T ^ (-chamberMinExponent k α ρ)
              * Real.log T ^ chamberResonanceCount k α ρ)) := by ring
      _ ≤ Real.pi ^ ((p * h : ℝ) / 2) * Z * chamberJFull k T α ρ := hstep
  · intro T hT
    rw [hlap T (by linarith), hscale T hT]
    have hhi := (hbounds T hT).2
    have hstep := mul_le_mul_of_nonneg_left hhi
      (by positivity : (0:ℝ) ≤ Real.pi ^ ((p * h : ℝ) / 2) * Z)
    calc Real.pi ^ ((p * h : ℝ) / 2) * Z * chamberJFull k T α ρ
        ≤ Real.pi ^ ((p * h : ℝ) / 2) * Z
          * (C * (T ^ (-chamberMinExponent k α ρ)
              * Real.log T ^ chamberResonanceCount k α ρ)) := hstep
      _ = Real.pi ^ ((p * h : ℝ) / 2) * Z * C
          * (T ^ (-chamberMinExponent k α ρ)
              * Real.log T ^ chamberResonanceCount k α ρ) := by ring

/-- **Theorem 8.1**, at the wide shape `h ≤ n`, conditional on `O70-EIGEN-LAW`.

The local pair of `‖Y X‖²_F` at the origin is `(E⋆, N⋆)` — print's `(λ₀, m₀)`. The frontier
hypothesis is the only one; everything else in the chain is proved in the atlas. -/
public theorem hasLocalVolumeOrder_residualGerm (hEigen : EigenvalueLawStatement)
    (p n h : ℕ) (hp : 0 < p) (hh : 0 < h) (hhn : h ≤ n) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      (chamberMinExponent h (((n : ℝ) - h - 1) / 2) ((p : ℝ) / 2))
      (chamberResonanceCount h (((n : ℝ) - h - 1) / 2) ((p : ℝ) / 2) + 1) := by
  obtain ⟨Z, hZ, hlap⟩ := gaussianLaplace_residualGerm_eq_chamber hEigen p n h hh hhn
  refine hasLocalVolumeOrder_of_chamber ?_ hh hp hZ hlap
  have : (h : ℝ) ≤ n := by exact_mod_cast hhn
  linarith

/-! ## The transposed shape

`EigenvalueLawStatement` is stated for a wide matrix, `k ≤ d`, following the candidate's own
reduction: "replacing `X` by `Xᵀ` if `h > n` changes neither `‖X‖_F` nor `G(X)` nor the law of
the entries" (proof of Proposition 8.11). Formally that reduction needs three things, and all
three are elementary:

* transposition is a coordinate permutation of the entry space, hence measure preserving;
* `‖Xᵀ‖²_F = ‖X‖²_F`; and
* `det(1 + T·XᵀX) = det(1 + T·XXᵀ)`, Sylvester's identity, already proved as
  `det_one_add_smul_gram_comm`.

So the tall case is not a second frontier — it is the same frontier read at the transposed
matrix. -/

/-- Transposition, as a measurable equivalence of the two entry spaces. It is the coordinate
permutation `(i, j) ↦ (j, i)`, wrapped in the currying of `Coordinates.lean`. -/
@[expose] public noncomputable def matrixTransposeEquiv (m k : ℕ) :
    Matrix (Fin m) (Fin k) ℝ ≃ᵐ Matrix (Fin k) (Fin m) ℝ :=
  (MeasurableEquiv.curry (Fin m) (Fin k) ℝ).symm.trans <|
    (MeasurableEquiv.arrowCongr' (Equiv.prodComm (Fin m) (Fin k))
      (MeasurableEquiv.refl ℝ)).trans (MeasurableEquiv.curry (Fin k) (Fin m) ℝ)

@[simp] public theorem matrixTransposeEquiv_apply (m k : ℕ) (X : Matrix (Fin m) (Fin k) ℝ) :
    matrixTransposeEquiv m k X = Xᵀ := rfl

/-- **Transposition preserves Lebesgue measure**: it permutes coordinates and nothing else. -/
public theorem measurePreserving_matrixTransposeEquiv (m k : ℕ) :
    MeasurePreserving (matrixTransposeEquiv m k) volume volume := by
  have h1 := measurePreserving_curry_symm (Fin m) (Fin k) ℝ
  have h2 := volume_preserving_arrowCongr' (Equiv.prodComm (Fin m) (Fin k))
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  have h3 : MeasurePreserving (MeasurableEquiv.curry (Fin k) (Fin m) ℝ)
      (volume : Measure (Fin k × Fin m → ℝ)) volume :=
    MeasurePreserving.symm _ (measurePreserving_curry_symm (Fin k) (Fin m) ℝ)
  exact h3.comp (h2.comp h1)

/-- **The `X`-integral is transposition-invariant.** Both the Gaussian weight and the
determinant factor are, the first by `frobeniusSq_transpose` and the second by Sylvester. -/
public theorem integral_det_transpose (n h : ℕ) (T ρ : ℝ) :
    ∫ X : Matrix (Fin h) (Fin n) ℝ,
        Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-ρ)
      = ∫ X : Matrix (Fin n) (Fin h) ℝ,
          Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-ρ) := by
  have htr := (measurePreserving_matrixTransposeEquiv n h).integral_comp
    (matrixTransposeEquiv n h).measurableEmbedding
    (fun X : Matrix (Fin h) (Fin n) ℝ =>
      Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-ρ))
  rw [← htr]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [matrixTransposeEquiv_apply, frobeniusSq_transpose, Matrix.transpose_transpose]
  rw [← det_one_add_smul_gram_comm]

/-- **Proposition 8.13 at the tall shape `n ≤ h`.** The same frontier, read at the transposed
matrix. -/
public theorem gaussianLaplace_residualGerm_eq_chamber_tall (hEigen : EigenvalueLawStatement)
    (p n h : ℕ) (hn : 0 < n) (hnh : n ≤ h) :
    ∃ Z : ℝ, 0 < Z ∧ ∀ T : ℝ, 0 ≤ T →
      ∫ w : EuclideanSpace ℝ (Fin (h * n + p * h)),
          Real.exp (-T * residualGerm p n h w) * Real.exp (-‖w‖ ^ 2)
        = Real.pi ^ ((p * h : ℝ) / 2) * Z
          * chamberJFull n T (((h : ℝ) - n - 1) / 2) ((p : ℝ) / 2) := by
  obtain ⟨Z, hZ, hlaw⟩ := hEigen n h hn hnh
  refine ⟨Z, hZ, fun T hT => ?_⟩
  rw [gaussianLaplace_residualGerm_eq_det p n h hT,
    show (-(p : ℝ) / 2) = -((p : ℝ) / 2) from neg_div 2 (p : ℝ),
    integral_det_transpose n h T ((p : ℝ) / 2)]
  have hX : ∫ X : Matrix (Fin n) (Fin h) ℝ,
        Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-((p : ℝ) / 2))
      = Z * chamberJFull n T (((h : ℝ) - n - 1) / 2) ((p : ℝ) / 2) := by
    have hl := hlaw ((p : ℝ) / 2) (by positivity) T hT
    rw [← hl]
    rfl
  rw [hX]
  ring

/-- **Theorem 8.1 at the tall shape `n ≤ h`.** -/
public theorem hasLocalVolumeOrder_residualGerm_tall (hEigen : EigenvalueLawStatement)
    (p n h : ℕ) (hp : 0 < p) (hn : 0 < n) (hnh : n ≤ h) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      (chamberMinExponent n (((h : ℝ) - n - 1) / 2) ((p : ℝ) / 2))
      (chamberResonanceCount n (((h : ℝ) - n - 1) / 2) ((p : ℝ) / 2) + 1) := by
  obtain ⟨Z, hZ, hlap⟩ := gaussianLaplace_residualGerm_eq_chamber_tall hEigen p n h hn hnh
  refine hasLocalVolumeOrder_of_chamber ?_ hn hp hZ hlap
  have : (n : ℝ) ≤ h := by exact_mod_cast hnh
  linarith

/-- **Theorem 8.1 at every shape.** The wide case is the frontier read directly; the tall case
is the frontier read at the transposed matrix. Both give the pair at `k = min h n`,
`d = max h n`. -/
public theorem hasLocalVolumeOrder_residualGerm_min (hEigen : EigenvalueLawStatement)
    (p n h : ℕ) (hp : 0 < p) (hn : 0 < n) (hh : 0 < h) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      (chamberMinExponent (min h n)
        ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2) ((p : ℝ) / 2))
      (chamberResonanceCount (min h n)
        ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2) ((p : ℝ) / 2) + 1) := by
  rcases le_total h n with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    exact hasLocalVolumeOrder_residualGerm hEigen p n h hp hh hle
  · rw [min_eq_right hle, max_eq_left hle]
    exact hasLocalVolumeOrder_residualGerm_tall hEigen p n h hp hn hle

end AISafetyAtlas.SingularLearning
