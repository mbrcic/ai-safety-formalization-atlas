module

public import AISafetyAtlas.SingularLearning.ResidualScalar
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The smallest nondegenerate indefinite quadratic band

The scalar MAIS issue #5 candidate reduces its origin calculation to the two-sided band of
the bilinear form `x₀y₀ + x₁y₁`.  Squaring that form gives
`residualGerm 1 1 2`.  This module computes the latter germ's local volume order without the
`EigenvalueLawStatement` frontier and then transfers the result through the square map.

The only integral left after `gaussianLaplace_residualGerm_eq_det` is radial on `ℝ²`:

    ∫ exp (-‖x‖²) / sqrt (1 + T ‖x‖²) dx.

Polar integration turns it into a one-dimensional integral with numerator `r`.  For `T ≥ 3`
that integral is bounded above by `T⁻¹/² ∫ exp (-r²) dr`, and a fixed annulus
`1 < r ≤ 2` supplies a positive lower multiple of `T⁻¹/²`.  Thus the squared germ has
pair `(1/2, 1)`, while the absolute bilinear form has pair `(1, 1)`.

No analytic Morse lemma, eigenvalue law, or asymptotic statement is assumed here.  Every
coordinate transport used by the integral is explicitly measure preserving.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set Filter Topology
open scoped Matrix

/-! ## A multiplicity-one square-root transfer -/

/-- The sublevel set of `f²` at `ε²` is the sublevel set of `|f|` at `ε`, for `ε ≥ 0`. -/
public theorem sublevelVolume_sq_eq_abs {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    {δ ε : ℝ} (hε : 0 ≤ ε) :
    sublevelVolume (fun x => f x ^ 2) w δ (ε ^ 2) =
      sublevelVolume (fun x => |f x|) w δ ε := by
  unfold sublevelVolume
  apply congrArg ENNReal.toReal
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [sq_le_sq, abs_of_nonneg hε]

/-- Squaring halves the exponent, equivalently taking absolute square roots doubles it.

This transfer is intentionally restricted to multiplicity `1`: after substituting `ε²`, a
logarithmic factor would also acquire the constant `2^(m-1)`.  That extension is routine but is
not needed by the scalar saddle and keeping this interface narrow makes its fidelity obvious. -/
public theorem hasLocalVolumeOrder_abs_of_sq {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {w : EuclideanSpace ℝ (Fin n)} {lam : ℝ}
    (h : HasLocalVolumeOrder (fun x => f x ^ 2) w lam 1) :
    HasLocalVolumeOrder (fun x => |f x|) w (2 * lam) 1 := by
  have hsqt : Tendsto (fun ε : ℝ => ε ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : ContinuousAt (fun ε : ℝ => ε ^ 2) 0 := by fun_prop
      have ht := hc.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
      simpa using ht
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : 0 < ε := hε
      exact sq_pos_of_pos hε0
  rcases h with ⟨hz, hlam, hm⟩ | ⟨hlam, hm, δ₀, hδ₀, hb⟩
  · refine Or.inl ⟨?_, by simp [hlam], rfl⟩
    filter_upwards [hz] with x hx
    have hfx : f x = 0 := sq_eq_zero_iff.mp hx
    simp [hfx]
  · refine Or.inr ⟨by positivity, le_refl 1, δ₀, hδ₀, ?_⟩
    intro δ hδ
    obtain ⟨c, C, hc, hcC, hbounds⟩ := hb δ hδ
    refine ⟨c, C, hc, hcC, ?_⟩
    filter_upwards [hsqt.eventually hbounds, self_mem_nhdsWithin] with ε hbd hε
    have hscale : volumeScale lam 1 (ε ^ 2) = volumeScale (2 * lam) 1 ε := by
      rw [volumeScale, volumeScale]
      simp only [Nat.reduceSub, pow_zero, mul_one]
      rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
      congr 1
    rw [← sublevelVolume_sq_eq_abs f w hε.le, ← hscale]
    exact hbd

/-! ## The two-dimensional determinant integral -/

/-- A `2×1` real matrix is a two-dimensional Euclidean vector, measurably. -/
@[expose] public noncomputable def matrixTwoOneEquiv :
    Matrix (Fin 2) (Fin 1) ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.curry (Fin 2) (Fin 1) ℝ).symm |>.trans <|
    (MeasurableEquiv.arrowCongr' (Equiv.prodUnique (Fin 2) (Fin 1))
      (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

/-- The matrix-to-vector map preserves Lebesgue measure. -/
public theorem measurePreserving_matrixTwoOneEquiv :
    MeasurePreserving matrixTwoOneEquiv volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    ((MeasureTheory.volume_preserving_arrowCongr'
      (Equiv.prodUnique (Fin 2) (Fin 1)) (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id volume)).comp
        (measurePreserving_curry_symm _ _ _))

/-- The same map preserves the squared norm entry by entry. -/
public theorem norm_sq_matrixTwoOneEquiv (X : Matrix (Fin 2) (Fin 1) ℝ) :
    ‖matrixTwoOneEquiv X‖ ^ 2 = X 0 0 ^ 2 + X 1 0 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

/-- The radial one-dimensional integral. -/
@[expose] public noncomputable def radialJ2 (T : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), y * Real.exp (-y ^ 2) *
    (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2)

/-- The determinant integral after transporting the `2×1` matrix to `ℝ²`. -/
@[expose] public noncomputable def twoJ (T : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin 2), Real.exp (-‖x‖ ^ 2) *
    (1 + T * ‖x‖ ^ 2) ^ (-(1 : ℝ) / 2)

@[expose] public noncomputable def radialIntegrand (T y : ℝ) : ℝ :=
  y * (Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))

/-- Polar integration in two dimensions.  The unit-ball factor is retained symbolically; only
its positivity matters below. -/
public theorem twoJ_eq_radial (T : ℝ) :
    twoJ T = 2 * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) * radialJ2 T := by
  rw [twoJ, radialJ2]
  have h := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun y : ℝ => Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
  simpa [finrank_euclideanSpace_fin, mul_assoc] using h

public theorem radialIntegrand_nonneg {T y : ℝ} (hT : 0 ≤ T) (hy : 0 ≤ y) :
    0 ≤ radialIntegrand T y := by
  rw [radialIntegrand]
  exact mul_nonneg hy (scalarIntegrand_nonneg hT y)

/-- Pointwise upper estimate on the positive ray. -/
public theorem radialIntegrand_le {T y : ℝ} (hT : 0 < T) (hy : 0 < y) :
    radialIntegrand T y ≤ (Real.sqrt T)⁻¹ * Real.exp (-y ^ 2) := by
  have h := scalarIntegrand_le_hyperbola hT (x := y) (ne_of_gt hy)
  rw [abs_of_pos hy] at h
  rw [radialIntegrand]
  calc
    y * (Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
        ≤ y * (Real.exp (-y ^ 2) * (Real.sqrt T * y)⁻¹) :=
      mul_le_mul_of_nonneg_left h hy.le
    _ = (Real.sqrt T)⁻¹ * Real.exp (-y ^ 2) := by
      field_simp [ne_of_gt hy, ne_of_gt (Real.sqrt_pos.mpr hT)]

/-- The radial integrand is integrable on the positive ray. -/
public theorem integrableOn_radialIntegrand {T : ℝ} (hT : 0 < T) :
    IntegrableOn (radialIntegrand T) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => (Real.sqrt T)⁻¹ * Real.exp (-y ^ 2)) (Ioi 0) :=
    (integrable_gaussian.const_mul _).integrableOn
  refine hg.mono' ?_ ?_
  · have hc : Continuous (radialIntegrand T) := by
      unfold radialIntegrand
      exact continuous_id.mul (continuous_scalarIntegrand hT.le)
    exact hc.aestronglyMeasurable.restrict
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    rw [Real.norm_of_nonneg (radialIntegrand_nonneg hT.le hy0.le)]
    exact radialIntegrand_le hT hy0

/-- The fixed-annulus pointwise minorant used for the lower bound. -/
public theorem radialIntegrand_ge_on_annulus {T y : ℝ} (hT : 3 ≤ T)
    (hy : y ∈ Ioc (1 : ℝ) 2) :
    Real.exp (-4) * (Real.sqrt 5 * Real.sqrt T)⁻¹ ≤ radialIntegrand T y := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hy0 : 0 < y := by linarith [hy.1]
  rw [radialIntegrand, rpow_neg_half_eq hT0.le]
  have hsq : y ^ 2 ≤ 4 := by nlinarith [hy.2, hy0]
  have hinside : 1 + T * y ^ 2 ≤ 5 * T := by nlinarith
  have hsqrt : Real.sqrt (1 + T * y ^ 2) ≤ Real.sqrt 5 * Real.sqrt T := by
    calc
      Real.sqrt (1 + T * y ^ 2) ≤ Real.sqrt (5 * T) := Real.sqrt_le_sqrt hinside
      _ = Real.sqrt 5 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
  have hinv : (Real.sqrt 5 * Real.sqrt T)⁻¹ ≤
      (Real.sqrt (1 + T * y ^ 2))⁻¹ := by gcongr
  have hexp : Real.exp (-4) ≤ Real.exp (-y ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    Real.exp (-4) * (Real.sqrt 5 * Real.sqrt T)⁻¹
        ≤ Real.exp (-y ^ 2) * (Real.sqrt 5 * Real.sqrt T)⁻¹ := by gcongr
    _ ≤ Real.exp (-y ^ 2) * (Real.sqrt (1 + T * y ^ 2))⁻¹ := by gcongr
    _ ≤ y * Real.exp (-y ^ 2) * (Real.sqrt (1 + T * y ^ 2))⁻¹ := by
      have hp : 0 ≤ Real.exp (-y ^ 2) * (Real.sqrt (1 + T * y ^ 2))⁻¹ := by positivity
      nlinarith [hy.1]
    _ = y * (Real.exp (-y ^ 2) * (Real.sqrt (1 + T * y ^ 2))⁻¹) := by ring

/-- Lower radial estimate at every `T ≥ 3`. -/
public theorem radialJ2_lower {T : ℝ} (hT : 3 ≤ T) :
    Real.exp (-4) * (Real.sqrt 5 * Real.sqrt T)⁻¹ ≤ radialJ2 T := by
  have hT0 : (0 : ℝ) < T := by linarith
  let c : ℝ := Real.exp (-4) * (Real.sqrt 5 * Real.sqrt T)⁻¹
  have hconst : IntegrableOn (fun _y : ℝ => c) (Ioc 1 2) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hminor : ∀ y ∈ Ioc (1 : ℝ) 2, c ≤ radialIntegrand T y := by
    intro y hy
    exact radialIntegrand_ge_on_annulus hT hy
  have hstep : ∫ y in Ioc (1 : ℝ) 2, c ≤
      ∫ y in Ioc (1 : ℝ) 2, radialIntegrand T y :=
    setIntegral_mono_on hconst
      ((integrableOn_radialIntegrand hT0).mono_set (by
        intro y hy
        exact one_pos.trans hy.1)) measurableSet_Ioc hminor
  have hextend : (∫ y in Ioc (1 : ℝ) 2, radialIntegrand T y) ≤
      ∫ y in Ioi (0 : ℝ), radialIntegrand T y := by
    refine setIntegral_mono_set (integrableOn_radialIntegrand hT0) ?_
      (show Ioc (1 : ℝ) 2 ⊆ Ioi 0 by
        intro y hy
        exact one_pos.trans hy.1).eventuallyLE
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    exact radialIntegrand_nonneg hT0.le hy.le
  have heval : (∫ _y in Ioc (1 : ℝ) 2, c) = c := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num)]
    norm_num
  change c ≤ radialJ2 T
  rw [← heval]
  simpa only [radialJ2, radialIntegrand, mul_assoc] using hstep.trans hextend

/-- Upper radial estimate at every positive `T`. -/
public theorem radialJ2_upper {T : ℝ} (hT : 0 < T) :
    radialJ2 T ≤ (Real.sqrt T)⁻¹ * Real.sqrt Real.pi := by
  have hmajInt : (∫ y in Ioi (0 : ℝ), radialIntegrand T y)
      ≤ ∫ y in Ioi (0 : ℝ), (Real.sqrt T)⁻¹ * Real.exp (-y ^ 2) := by
    refine setIntegral_mono_on (integrableOn_radialIntegrand hT)
      ((integrable_gaussian.const_mul _).integrableOn) measurableSet_Ioi ?_
    intro y hy
    exact radialIntegrand_le hT hy
  have hgauss : (∫ y in Ioi (0 : ℝ), Real.exp (-y ^ 2)) ≤ Real.sqrt Real.pi := by
    have hle := setIntegral_le_integral (s := Ioi (0 : ℝ)) integrable_gaussian
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)
    rwa [integral_gaussian_eq] at hle
  rw [integral_const_mul] at hmajInt
  simpa only [radialJ2, radialIntegrand, mul_assoc] using
    hmajInt.trans (mul_le_mul_of_nonneg_left hgauss (by positivity))

@[expose] public noncomputable def unitDiskVolume : ℝ :=
  volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)

public theorem unitDiskVolume_pos : 0 < unitDiskVolume := by
  unfold unitDiskVolume
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne

/-- Two-sided `T⁻¹/²` bounds for the two-dimensional determinant integral. -/
public theorem twoJ_lower {T : ℝ} (hT : 3 ≤ T) :
    (2 * unitDiskVolume * (Real.exp (-4) / Real.sqrt 5)) * (Real.sqrt T)⁻¹ ≤ twoJ T := by
  rw [twoJ_eq_radial, show volume.real
    (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = unitDiskVolume from rfl]
  have hstep := mul_le_mul_of_nonneg_left (radialJ2_lower hT)
    (show 0 ≤ (2 : ℝ) * unitDiskVolume from
      mul_nonneg (by norm_num) unitDiskVolume_pos.le)
  calc
    (2 * unitDiskVolume * (Real.exp (-4) / Real.sqrt 5)) * (Real.sqrt T)⁻¹
        = 2 * unitDiskVolume * (Real.exp (-4) * (Real.sqrt 5 * Real.sqrt T)⁻¹) := by
          field_simp [ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)),
            ne_of_gt (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < T))]
    _ ≤ 2 * unitDiskVolume * radialJ2 T := hstep

public theorem twoJ_upper {T : ℝ} (hT : 0 < T) :
    twoJ T ≤ (2 * unitDiskVolume * Real.sqrt Real.pi) * (Real.sqrt T)⁻¹ := by
  rw [twoJ_eq_radial, show volume.real
    (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = unitDiskVolume from rfl]
  have hstep := mul_le_mul_of_nonneg_left (radialJ2_upper hT)
    (show 0 ≤ (2 : ℝ) * unitDiskVolume from
      mul_nonneg (by norm_num) unitDiskVolume_pos.le)
  calc
    2 * unitDiskVolume * radialJ2 T
        ≤ 2 * unitDiskVolume * ((Real.sqrt T)⁻¹ * Real.sqrt Real.pi) := hstep
    _ = (2 * unitDiskVolume * Real.sqrt Real.pi) * (Real.sqrt T)⁻¹ := by ring

/-! ## Back to the residual germ -/

/-- The `2×1` determinant integral is `twoJ`. -/
public theorem integral_det_two_one (T : ℝ) :
    (∫ X : Matrix (Fin 2) (Fin 1) ℝ,
      Real.exp (-frobeniusSq X) *
        (1 + T • (X * Xᵀ)).det ^ (-(1 : ℝ) / 2)) = twoJ T := by
  have hpoint : ∀ X : Matrix (Fin 2) (Fin 1) ℝ,
      Real.exp (-frobeniusSq X) *
          (1 + T • (X * Xᵀ)).det ^ (-(1 : ℝ) / 2)
        = Real.exp (-‖matrixTwoOneEquiv X‖ ^ 2) *
          (1 + T * ‖matrixTwoOneEquiv X‖ ^ 2) ^ (-(1 : ℝ) / 2) := by
    intro X
    have hf : frobeniusSq X = X 0 0 ^ 2 + X 1 0 ^ 2 := by
      simp [frobeniusSq, Fin.sum_univ_two]
    have hd : (1 + T • (X * Xᵀ)).det =
        1 + T * (X 0 0 ^ 2 + X 1 0 ^ 2) := by
      rw [Matrix.det_fin_two]
      simp [Matrix.mul_apply]
      ring
    rw [norm_sq_matrixTwoOneEquiv, hf, hd]
  have h := measurePreserving_matrixTwoOneEquiv.integral_comp
    matrixTwoOneEquiv.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin 2) => Real.exp (-‖x‖ ^ 2) *
      (1 + T * ‖x‖ ^ 2) ^ (-(1 : ℝ) / 2))
  rw [twoJ, ← h]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- Gaussian-weighted Laplace transform of `residualGerm 1 1 2`. -/
public theorem gaussianLaplace_residualGerm_one_one_two {T : ℝ} (hT : 0 ≤ T) :
    (∫ w : EuclideanSpace ℝ (Fin (2 * 1 + 1 * 2)),
      Real.exp (-T * residualGerm 1 1 2 w) * Real.exp (-‖w‖ ^ 2))
      = Real.pi * twoJ T := by
  rw [gaussianLaplace_residualGerm_eq_det 1 1 2 hT]
  norm_num
  have hi := integral_det_two_one T
  have hi' : (∫ X : Matrix (Fin 2) (Fin 1) ℝ,
      Real.exp (-frobeniusSq X) *
        (1 + T • (X * Xᵀ)).det ^ (-((1 : ℝ) / 2))) = twoJ T := by
    simpa only [neg_div] using hi
  rw [hi']

public theorem laplaceScale_half_one {T : ℝ} (hT : 0 < T) :
    laplaceScale (1 / 2) 1 T = (Real.sqrt T)⁻¹ := by
  rw [laplaceScale, show (1 : ℕ) - 1 = 0 from rfl, pow_zero, mul_one,
    ← rpow_neg_half hT.le]
  norm_num

/-- **The squared two-vector dot-product germ has pair `(1/2, 1)`, unconditionally.** -/
public theorem hasLocalVolumeOrder_residualGerm_one_one_two :
    HasLocalVolumeOrder (residualGerm 1 1 2) 0 (1 / 2) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hdisk : 0 < unitDiskVolume := unitDiskVolume_pos
  refine hasLocalVolumeOrder_of_gaussianLaplace (k := 4)
    continuous_residualGerm.measurable residualGerm_nonneg
    (fun t _ w => residualGerm_smul t w) (by norm_num) (by norm_num)
    (c := Real.pi * (2 * unitDiskVolume * (Real.exp (-4) / Real.sqrt 5)))
    (C := Real.pi * (2 * unitDiskVolume * Real.sqrt Real.pi)) (by positivity) ?_ ?_
  · intro T hT
    have hT0 : (0 : ℝ) < T := by linarith
    rw [gaussianLaplace_residualGerm_one_one_two hT0.le, laplaceScale_half_one hT0]
    have h := mul_le_mul_of_nonneg_left (twoJ_lower hT) hpi.le
    nlinarith
  · intro T hT
    have hT0 : (0 : ℝ) < T := by linarith
    rw [gaussianLaplace_residualGerm_one_one_two hT0.le, laplaceScale_half_one hT0]
    have h := mul_le_mul_of_nonneg_left (twoJ_upper hT0) hpi.le
    nlinarith

/-- The unsquared scalar residual, i.e. the dot product of the two hidden vectors. -/
@[expose] public noncomputable def residualAmplitude
    (w : EuclideanSpace ℝ (Fin (2 * 1 + 1 * 2))) : ℝ :=
  (residualY 1 1 2 w * residualX 1 1 2 w) 0 0

public theorem residualGerm_one_one_two_eq_sq
    (w : EuclideanSpace ℝ (Fin (2 * 1 + 1 * 2))) :
    residualGerm 1 1 2 w = residualAmplitude w ^ 2 := by
  simp [residualGerm, residualAmplitude, frobeniusSq]

/-- **The absolute two-vector dot product has pair `(1, 1)`, unconditionally.** -/
public theorem hasLocalVolumeOrder_abs_residualAmplitude :
    HasLocalVolumeOrder (fun w => |residualAmplitude w|) 0 1 1 := by
  have hsq : HasLocalVolumeOrder (fun w => residualAmplitude w ^ 2) 0 (1 / 2) 1 := by
    have hfun :
        (fun w : EuclideanSpace ℝ (Fin (2 * 1 + 1 * 2)) => residualAmplitude w ^ 2) =
          residualGerm 1 1 2 :=
      funext fun w => (residualGerm_one_one_two_eq_sq w).symm
    rw [hfun]
    exact hasLocalVolumeOrder_residualGerm_one_one_two
  have h := hasLocalVolumeOrder_abs_of_sq hsq
  norm_num at h
  exact h

end AISafetyAtlas.SingularLearning
