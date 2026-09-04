module

public import AISafetyAtlas.SingularLearning.ResidualLaplace

/-!
# The scalar residual germ, unconditionally

`ResidualLaplace.lean` reduces the Gaussian-weighted Laplace transform of `residualGerm p n h`
to an integral over `X` alone, and that reduction — `gaussianLaplace_residualGerm_eq_det` — is
**unconditional**. The eigenvalue law enters only afterwards, to evaluate the determinant
integral in general.

At the smallest singular shape `p = n = h = 1` it does not have to. There `X` is a single real
number, the determinant is `1 + T x²`, and the integral is

    J(T) = ∫_ℝ e^{-x²} (1 + T x²)^{-1/2} dx ,

which this module sandwiches between two multiples of `T^{-1/2} log T` by an elementary split at
`|x| = T^{-1/2}`. Feeding those bounds to `hasLocalVolumeOrder_of_gaussianLaplace`, itself
frontier-free, gives the local pair of `x²y²` with **no hypothesis at all**.

## Why this shape and not another

`residualGerm 1 1 1` is `‖YX‖²_F` at `1×1`, that is `x²y²`. It is the smallest germ in the
family whose multiplicity is `2` rather than `1`, and it is the verification plan's V2b: the
anti-vacuity witness that shows `HasLocalVolumeOrder` is inhabited somewhere *singular*, not
only at the regular quadratic of `hasExactLocalPair_quadraticGerm`. Proved under
`EigenvalueLawStatement` it could not serve that purpose, because a witness standing behind a
hypothesis with no known inhabitant is not a witness.

## The estimate

Both bounds come from the same two facts and a split at `δ = T^{-1/2}`:

* `(1 + T x²)^{-1/2} ≤ 1` everywhere, and `≤ 1/(√T |x|)` everywhere, so the inner interval
  contributes at most its length `2δ` and the outer one at most `(2/√T) ∫_δ^∞ e^{-x²}/x`, which
  splits again at `1` into `(1/2) log T` and a tail below `e^{-1}`;
* on `δ ≤ x ≤ 1` we have `1 ≤ T x²`, hence `1 + T x² ≤ 2 T x²` and
  `(1 + T x²)^{-1/2} ≥ 1/(√2 √T x)`, while `e^{-x²} ≥ e^{-1}`, so that interval alone already
  contributes `≍ T^{-1/2} log T`.

Nothing here is asymptotic in the sense of a limit: both bounds hold at every `T ≥ 3`, which is
the hypothesis `hasLocalVolumeOrder_of_gaussianLaplace` wants.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set
open scoped Matrix

/-- `J(T)`, the one-dimensional integral the `1×1` determinant integral collapses to. -/
@[expose] public noncomputable def scalarJ (T : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2)

/-! ## Pointwise facts about the integrand -/

variable {T : ℝ}

public theorem one_add_mul_sq_pos (hT : 0 ≤ T) (x : ℝ) : (0:ℝ) < 1 + T * x ^ 2 := by
  have : 0 ≤ T * x ^ 2 := mul_nonneg hT (sq_nonneg x)
  linarith

/-- `y ^ (-1/2)` is the inverse square root, where the estimates are easier. -/
public theorem rpow_neg_half {y : ℝ} (hy : 0 ≤ y) :
    y ^ (-(1 : ℝ) / 2) = (Real.sqrt y)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy]
  norm_num

/-- The integrand written as an inverse square root. -/
public theorem rpow_neg_half_eq (hT : 0 ≤ T) (x : ℝ) :
    (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) = (Real.sqrt (1 + T * x ^ 2))⁻¹ :=
  rpow_neg_half (one_add_mul_sq_pos hT x).le

public theorem scalarIntegrand_nonneg (hT : 0 ≤ T) (x : ℝ) :
    0 ≤ Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) := by
  rw [rpow_neg_half_eq hT]
  positivity

/-- Everywhere: the factor is at most `1`. -/
public theorem scalarIntegrand_le_gaussian (hT : 0 ≤ T) (x : ℝ) :
    Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) ≤ Real.exp (-x ^ 2) := by
  rw [rpow_neg_half_eq hT]
  have hb : (1:ℝ) ≤ 1 + T * x ^ 2 := by nlinarith [mul_nonneg hT (sq_nonneg x)]
  have h1 : (1:ℝ) ≤ Real.sqrt (1 + T * x ^ 2) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (1 + T * x ^ 2) := Real.sqrt_le_sqrt hb
  have hle : (Real.sqrt (1 + T * x ^ 2))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]; exact h1
  nlinarith [Real.exp_pos (-x ^ 2), hle]

/-- Off the origin: the factor is at most `1/(√T · |x|)`. This is the bound that produces the
`T^{-1/2}` and, integrated against `dx/x`, the logarithm. It is false at `x = 0`, where the
right-hand side is `0`, which is exactly why the estimate is split at `|x| = T^{-1/2}`. -/
public theorem scalarIntegrand_le_hyperbola (hT : 0 < T) {x : ℝ} (hx : x ≠ 0) :
    Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2)
      ≤ Real.exp (-x ^ 2) * (Real.sqrt T * |x|)⁻¹ := by
  rw [rpow_neg_half_eq hT.le]
  have hxpos : 0 < |x| := abs_pos.mpr hx
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hkey : Real.sqrt T * |x| ≤ Real.sqrt (1 + T * x ^ 2) := by
    have h1 : Real.sqrt T * |x| = Real.sqrt (T * x ^ 2) := by
      rw [Real.sqrt_mul hT.le, Real.sqrt_sq_eq_abs]
    rw [h1]
    exact Real.sqrt_le_sqrt (by linarith)
  have hinv : (Real.sqrt (1 + T * x ^ 2))⁻¹ ≤ (Real.sqrt T * |x|)⁻¹ := by
    gcongr
  nlinarith [Real.exp_pos (-x ^ 2), hinv]

/-! ## Integrability -/

public theorem integrable_gaussian : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
  have h := integrable_exp_neg_mul_sq (b := 1) one_pos
  simpa using h

public theorem continuous_scalarIntegrand (hT : 0 ≤ T) :
    Continuous fun x : ℝ => Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) := by
  have : (fun x : ℝ => Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2))
      = fun x : ℝ => Real.exp (-x ^ 2) * (Real.sqrt (1 + T * x ^ 2))⁻¹ :=
    funext fun x => by rw [rpow_neg_half_eq hT]
  rw [this]
  refine (Real.continuous_exp.comp (by fun_prop)).mul ?_
  refine (Real.continuous_sqrt.comp (by fun_prop)).inv₀ fun x => ?_
  exact ne_of_gt (Real.sqrt_pos.mpr (one_add_mul_sq_pos hT x))

public theorem integrable_scalarIntegrand (hT : 0 ≤ T) :
    Integrable fun x : ℝ => Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) := by
  refine integrable_gaussian.mono' (continuous_scalarIntegrand hT).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (scalarIntegrand_nonneg hT x)]
  exact scalarIntegrand_le_gaussian hT x

/-! ## The lower bound

On `T^{-1/2} ≤ x ≤ 1` we have `1 ≤ T x²`, so `1 + T x² ≤ 2 T x²` and the factor is at least
`1/(√2 √T x)`; the Gaussian is at least `e^{-1}`. That interval alone contributes
`≍ T^{-1/2} log T`. -/

public theorem one_le_sqrt_of_three_le (hT : 3 ≤ T) : (1:ℝ) ≤ Real.sqrt T := by
  calc (1:ℝ) = Real.sqrt 1 := by simp
    _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)

/-- The pointwise minorant on the middle interval. -/
public theorem scalarIntegrand_ge_on_middle (hT : 3 ≤ T) {x : ℝ}
    (hx1 : (Real.sqrt T)⁻¹ ≤ x) (hx2 : x ≤ 1) :
    Real.exp (-1) * (Real.sqrt 2 * Real.sqrt T * x)⁻¹
      ≤ Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hxpos : 0 < x := lt_of_lt_of_le (inv_pos.mpr hTs) hx1
  rw [rpow_neg_half_eq hT0.le]
  -- `1 ≤ T x²` on the interval, hence `1 + T x² ≤ 2 T x²`.
  have hTx : (1:ℝ) ≤ T * x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hx1 hTs.le
    have hsq : Real.sqrt T * (Real.sqrt T)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hTs)
    nlinarith [Real.sq_sqrt hT0.le, Real.sqrt_nonneg T, mul_le_mul hx1 hx1
      (le_of_lt (inv_pos.mpr hTs)) hxpos.le]
  have hbound : 1 + T * x ^ 2 ≤ 2 * (T * x ^ 2) := by linarith
  have hsqrt : Real.sqrt (1 + T * x ^ 2) ≤ Real.sqrt 2 * Real.sqrt T * x := by
    have h2 : Real.sqrt (2 * (T * x ^ 2)) = Real.sqrt 2 * Real.sqrt T * x := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hT0.le, Real.sqrt_sq hxpos.le, mul_assoc]
    calc Real.sqrt (1 + T * x ^ 2) ≤ Real.sqrt (2 * (T * x ^ 2)) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt 2 * Real.sqrt T * x := h2
  have hden : 0 < Real.sqrt 2 * Real.sqrt T * x := by positivity
  have hinv : (Real.sqrt 2 * Real.sqrt T * x)⁻¹ ≤ (Real.sqrt (1 + T * x ^ 2))⁻¹ := by
    gcongr
  have hexp : Real.exp (-1) ≤ Real.exp (-x ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hinvpos : 0 < (Real.sqrt (1 + T * x ^ 2))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (one_add_mul_sq_pos hT0.le x))
  calc Real.exp (-1) * (Real.sqrt 2 * Real.sqrt T * x)⁻¹
      ≤ Real.exp (-1) * (Real.sqrt (1 + T * x ^ 2))⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
    _ ≤ Real.exp (-x ^ 2) * (Real.sqrt (1 + T * x ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right hexp hinvpos.le

/-- **The lower bound.** `J(T) ≥ (e⁻¹/√2) · T^{-1/2} · (log T)/2` at every `T ≥ 3`. -/
public theorem scalarJ_lower (hT : 3 ≤ T) :
    Real.exp (-1) / (Real.sqrt 2 * Real.sqrt T) * (Real.log T / 2) ≤ scalarJ T := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have h1T := one_le_sqrt_of_three_le hT
  set δ : ℝ := (Real.sqrt T)⁻¹ with hδdef
  have hδpos : 0 < δ := inv_pos.mpr hTs
  have hδ1 : δ ≤ 1 := (inv_le_one₀ hTs).mpr h1T
  set c : ℝ := Real.exp (-1) / (Real.sqrt 2 * Real.sqrt T) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]; positivity
  -- The minorant, in the form the interval integral evaluates.
  have hminor : ∀ x ∈ Ioc δ 1,
      c * x⁻¹ ≤ Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hδpos hx.1.le
    have := scalarIntegrand_ge_on_middle hT (x := x) hx.1.le hx.2
    calc c * x⁻¹ = Real.exp (-1) * (Real.sqrt 2 * Real.sqrt T * x)⁻¹ := by
          rw [hcdef, mul_inv, div_eq_mul_inv]; ring
      _ ≤ _ := this
  -- Both sides are integrable on the interval.
  have hcont : ContinuousOn (fun x : ℝ => c * x⁻¹) (Icc δ 1) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id fun x hx => ?_)
    exact ne_of_gt (lt_of_lt_of_le hδpos hx.1)
  have hgint : IntegrableOn (fun x : ℝ => c * x⁻¹) (Ioc δ 1) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hfint : IntegrableOn
      (fun x : ℝ => Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2)) (Ioc δ 1) :=
    (integrable_scalarIntegrand hT0.le).integrableOn
  -- Compare on the interval, then extend to the line.
  have hstep : ∫ x in Ioc δ 1, c * x⁻¹
      ≤ ∫ x in Ioc δ 1, Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) :=
    setIntegral_mono_on hgint hfint measurableSet_Ioc hminor
  have hextend : (∫ x in Ioc δ 1, Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ scalarJ T :=
    setIntegral_le_integral (integrable_scalarIntegrand hT0.le)
      (Filter.Eventually.of_forall (scalarIntegrand_nonneg hT0.le))
  -- Evaluate the minorant's integral.
  have heval : ∫ x in Ioc δ 1, c * x⁻¹ = c * (Real.log T / 2) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hδ1,
      integral_inv_of_pos hδpos one_pos]
    congr 1
    rw [hδdef, one_div, inv_inv, Real.log_sqrt hT0.le]
  linarith [hstep, hextend, heval.symm.le, heval.le]

/-! ## The upper bound

The integrand depends on `x` only through `x²`, so it is `g |x|` for the same `g`, and
`integral_comp_abs` halves the line. On `(0, ∞)` the estimate splits at `δ = T^{-1/2}` and at
`1`: below `δ` the integrand is at most `1`, between `δ` and `1` it is at most `1/(√T y)` whose
integral is the logarithm, and above `1` the Gaussian is integrable and `1/(√T y) ≤ 1/√T`. -/

public theorem scalarJ_eq_two_mul_Ioi (T : ℝ) :
    scalarJ T = 2 * ∫ y in Ioi 0, Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2) := by
  rw [scalarJ, ← integral_comp_abs
    (f := fun y : ℝ => Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [sq_abs])

public theorem scalarIntegrand_le_one (hT : 0 ≤ T) (x : ℝ) :
    Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2) ≤ 1 := by
  refine le_trans (scalarIntegrand_le_gaussian hT x) ?_
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg x]

/-- Below `δ = T^{-1/2}` the integrand is at most `1`, so the piece is at most `δ`. -/
public theorem scalarJ_piece_inner (hT : 3 ≤ T) :
    (∫ y in Ioc 0 (Real.sqrt T)⁻¹,
        Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2)) ≤ (Real.sqrt T)⁻¹ := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hle : (∫ y in Ioc 0 (Real.sqrt T)⁻¹,
      Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ ∫ _y in Ioc 0 (Real.sqrt T)⁻¹, (1:ℝ) := by
    refine setIntegral_mono_on ((integrable_scalarIntegrand hT0.le).integrableOn)
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc ?_
    intro y _
    exact scalarIntegrand_le_one hT0.le y
  refine hle.trans ?_
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (inv_pos.mpr hTs).le]
  simp

/-- Between `δ` and `1` the integrand is at most `1/(√T · y)`, whose integral is the logarithm.
This is the piece that carries the multiplicity. -/
public theorem scalarJ_piece_log (hT : 3 ≤ T) :
    (∫ y in Ioc (Real.sqrt T)⁻¹ 1,
        Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ (Real.sqrt T)⁻¹ * (Real.log T / 2) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have h1T := one_le_sqrt_of_three_le hT
  have hδ1 : (Real.sqrt T)⁻¹ ≤ 1 := (inv_le_one₀ hTs).mpr h1T
  have hδpos : 0 < (Real.sqrt T)⁻¹ := inv_pos.mpr hTs
  have hcont : ContinuousOn (fun y : ℝ => (Real.sqrt T)⁻¹ * y⁻¹) (Icc (Real.sqrt T)⁻¹ 1) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id fun y hy => ?_)
    exact ne_of_gt (lt_of_lt_of_le hδpos hy.1)
  have hgint : IntegrableOn (fun y : ℝ => (Real.sqrt T)⁻¹ * y⁻¹) (Ioc (Real.sqrt T)⁻¹ 1) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hstep : (∫ y in Ioc (Real.sqrt T)⁻¹ 1,
      Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ ∫ y in Ioc (Real.sqrt T)⁻¹ 1, (Real.sqrt T)⁻¹ * y⁻¹ := by
    refine setIntegral_mono_on ((integrable_scalarIntegrand hT0.le).integrableOn)
      hgint measurableSet_Ioc ?_
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hδpos hy.1.le
    have hhyp := scalarIntegrand_le_hyperbola hT0 (x := y) (ne_of_gt hypos)
    refine hhyp.trans ?_
    rw [abs_of_pos hypos, mul_inv]
    have hexp : Real.exp (-y ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg y]
    have : 0 < (Real.sqrt T)⁻¹ * y⁻¹ := by positivity
    nlinarith [hexp, this, Real.exp_pos (-y ^ 2)]
  refine hstep.trans ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hδ1,
    integral_inv_of_pos hδpos one_pos]
  have : Real.log (1 / (Real.sqrt T)⁻¹) = Real.log T / 2 := by
    rw [one_div, inv_inv, Real.log_sqrt hT0.le]
  rw [this]

public theorem integral_gaussian_eq : (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
  have h := integral_gaussian 1
  simpa using h

/-- Above `1` the Gaussian carries the integrability and `1/(√T y) ≤ 1/√T`. -/
public theorem scalarJ_piece_tail (hT : 3 ≤ T) :
    (∫ y in Ioi (1:ℝ), Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ (Real.sqrt T)⁻¹ * Real.sqrt Real.pi := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hstep : (∫ y in Ioi (1:ℝ), Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ ∫ y in Ioi (1:ℝ), (Real.sqrt T)⁻¹ * Real.exp (-y ^ 2) := by
    refine setIntegral_mono_on ((integrable_scalarIntegrand hT0.le).integrableOn)
      ((integrable_gaussian.const_mul _).integrableOn) measurableSet_Ioi ?_
    intro y hy
    have hy1 : (1:ℝ) ≤ y := le_of_lt hy
    have hypos : 0 < y := by linarith
    have hhyp := scalarIntegrand_le_hyperbola hT0 (x := y) (ne_of_gt hypos)
    refine hhyp.trans ?_
    rw [abs_of_pos hypos, mul_inv]
    have hyinv : y⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hypos]; exact hy1
    have hpos : 0 < (Real.sqrt T)⁻¹ := inv_pos.mpr hTs
    calc Real.exp (-y ^ 2) * ((Real.sqrt T)⁻¹ * y⁻¹)
        = (Real.exp (-y ^ 2) * (Real.sqrt T)⁻¹) * y⁻¹ := by ring
      _ ≤ (Real.exp (-y ^ 2) * (Real.sqrt T)⁻¹) * 1 := by gcongr
      _ = (Real.sqrt T)⁻¹ * Real.exp (-y ^ 2) := by ring
  refine hstep.trans ?_
  rw [integral_const_mul]
  have hle : (∫ y in Ioi (1:ℝ), Real.exp (-y ^ 2)) ≤ ∫ y : ℝ, Real.exp (-y ^ 2) :=
    setIntegral_le_integral integrable_gaussian
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)
  rw [integral_gaussian_eq] at hle
  have hpos : 0 < (Real.sqrt T)⁻¹ := inv_pos.mpr hTs
  nlinarith [hle, hpos]

/-- **The upper bound.** `J(T) ≤ (3 + 2√π) · T^{-1/2} · log T` at every `T ≥ 3`. -/
public theorem scalarJ_upper (hT : 3 ≤ T) :
    scalarJ T ≤ (3 + 2 * Real.sqrt Real.pi) * ((Real.sqrt T)⁻¹ * Real.log T) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have h1T := one_le_sqrt_of_three_le hT
  have hδpos : 0 < (Real.sqrt T)⁻¹ := inv_pos.mpr hTs
  have hδ1 : (Real.sqrt T)⁻¹ ≤ 1 := (inv_le_one₀ hTs).mpr h1T
  have hint : Integrable fun y : ℝ => Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2) :=
    integrable_scalarIntegrand hT0.le
  have hsplit1 :
      (∫ y in (0:ℝ)..(Real.sqrt T)⁻¹,
          Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
        + ∫ y in Ioi (Real.sqrt T)⁻¹, Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2)
      = ∫ y in Ioi (0:ℝ), Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2) :=
    intervalIntegral.integral_interval_add_Ioi hint.integrableOn hint.integrableOn
  have hsplit2 :
      (∫ y in (Real.sqrt T)⁻¹..(1:ℝ),
          Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
        + ∫ y in Ioi (1:ℝ), Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2)
      = ∫ y in Ioi (Real.sqrt T)⁻¹, Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2) :=
    intervalIntegral.integral_interval_add_Ioi hint.integrableOn hint.integrableOn
  rw [intervalIntegral.integral_of_le hδpos.le] at hsplit1
  rw [intervalIntegral.integral_of_le hδ1] at hsplit2
  have hb1 := scalarJ_piece_inner hT
  have hb2 := scalarJ_piece_log hT
  have hb3 := scalarJ_piece_tail hT
  have htotal : (∫ y in Ioi (0:ℝ), Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ (Real.sqrt T)⁻¹ * (1 + Real.log T / 2 + Real.sqrt Real.pi) := by
    rw [← hsplit1, ← hsplit2]
    have : (Real.sqrt T)⁻¹ * (1 + Real.log T / 2 + Real.sqrt Real.pi)
        = (Real.sqrt T)⁻¹ + (Real.sqrt T)⁻¹ * (Real.log T / 2)
          + (Real.sqrt T)⁻¹ * Real.sqrt Real.pi := by ring
    rw [this]
    linarith [hb1, hb2, hb3]
  have hlog := one_le_log_of_three_le hT
  have hπ : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  rw [scalarJ_eq_two_mul_Ioi]
  have hstep : 2 * (∫ y in Ioi (0:ℝ), Real.exp (-y ^ 2) * (1 + T * y ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ 2 * ((Real.sqrt T)⁻¹ * (1 + Real.log T / 2 + Real.sqrt Real.pi)) := by
    linarith [htotal]
  refine hstep.trans ?_
  have habsorb : 2 * (1 + Real.log T / 2 + Real.sqrt Real.pi)
      ≤ (3 + 2 * Real.sqrt Real.pi) * Real.log T := by nlinarith [hlog, hπ]
  calc 2 * ((Real.sqrt T)⁻¹ * (1 + Real.log T / 2 + Real.sqrt Real.pi))
      = (Real.sqrt T)⁻¹ * (2 * (1 + Real.log T / 2 + Real.sqrt Real.pi)) := by ring
    _ ≤ (Real.sqrt T)⁻¹ * ((3 + 2 * Real.sqrt Real.pi) * Real.log T) := by
        exact mul_le_mul_of_nonneg_left habsorb hδpos.le
    _ = (3 + 2 * Real.sqrt Real.pi) * ((Real.sqrt T)⁻¹ * Real.log T) := by ring

/-! ## From the `1×1` determinant integral to `J` -/

/-- A `1×1` real matrix is a real number, measurably and measure-preservingly. -/
@[expose] public noncomputable def matrixOneEquiv : Matrix (Fin 1) (Fin 1) ℝ ≃ᵐ ℝ :=
  (MeasurableEquiv.funUnique (Fin 1) (Fin 1 → ℝ)).trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

public theorem coe_matrixOneEquiv :
    ⇑matrixOneEquiv = fun X : Matrix (Fin 1) (Fin 1) ℝ => X 0 0 := rfl

public theorem measurePreserving_matrixOneEquiv :
    MeasurePreserving matrixOneEquiv
      (volume : Measure (Matrix (Fin 1) (Fin 1) ℝ)) volume :=
  (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).comp
    (MeasureTheory.volume_preserving_funUnique (Fin 1) (Fin 1 → ℝ))

public theorem integral_matrix_one_one (g : ℝ → ℝ) :
    (∫ X : Matrix (Fin 1) (Fin 1) ℝ, g (X 0 0)) = ∫ x : ℝ, g x := by
  have h := measurePreserving_matrixOneEquiv.integral_comp
    matrixOneEquiv.measurableEmbedding g
  rw [coe_matrixOneEquiv] at h
  exact h

/-- The `1×1` determinant integral **is** `J`. -/
public theorem integral_det_one_one (T : ℝ) :
    (∫ X : Matrix (Fin 1) (Fin 1) ℝ,
        Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-(1 : ℝ) / 2))
      = scalarJ T := by
  have hpt : ∀ X : Matrix (Fin 1) (Fin 1) ℝ,
      Real.exp (-frobeniusSq X) * (1 + T • (X * Xᵀ)).det ^ (-(1 : ℝ) / 2)
        = Real.exp (-(X 0 0) ^ 2) * (1 + T * (X 0 0) ^ 2) ^ (-(1 : ℝ) / 2) := by
    intro X
    have hfro : frobeniusSq X = X 0 0 ^ 2 := by simp [frobeniusSq]
    have hdet : (1 + T • (X * Xᵀ)).det = 1 + T * X 0 0 ^ 2 := by
      rw [Matrix.det_fin_one]
      simp [Matrix.mul_apply, sq]
    rw [hfro, hdet]
  simp only [hpt]
  rw [scalarJ, ← integral_matrix_one_one
    (fun x : ℝ => Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2))]

/-- **The Gaussian-weighted Laplace transform of the scalar residual germ.** Unconditional:
`gaussianLaplace_residualGerm_eq_det` needs no frontier, and at `1×1` the determinant integral
is `J`. -/
public theorem gaussianLaplace_residualGerm_one (hT : 0 ≤ T) :
    (∫ w : EuclideanSpace ℝ (Fin (1 * 1 + 1 * 1)),
        Real.exp (-T * residualGerm 1 1 1 w) * Real.exp (-‖w‖ ^ 2))
      = Real.sqrt Real.pi * scalarJ T := by
  have h := gaussianLaplace_residualGerm_eq_det 1 1 1 hT
  simp only [Nat.cast_one, one_mul] at h
  rw [h, integral_det_one_one T]
  rw [Real.sqrt_eq_rpow]

public theorem laplaceScale_half_two (hT : 0 < T) :
    laplaceScale (1 / 2) 2 T = (Real.sqrt T)⁻¹ * Real.log T := by
  rw [laplaceScale, ← rpow_neg_half hT.le]
  norm_num

/-! ## V2b, with no hypothesis -/

/-- **The local pair of `x²y²`, unconditionally.**

`residualGerm 1 1 1` is `‖YX‖²_F` at `1×1`, that is `x²y²`. Its two-sided local volume order is
`(1/2, 2)` — exponent one half, multiplicity two — and this proof carries **no frontier
hypothesis**: `hasLocalVolumeOrder_of_gaussianLaplace` is frontier-free,
`gaussianLaplace_residualGerm_eq_det` is frontier-free, and the remaining one-dimensional
estimate is the elementary split above.

This is the verification plan's V2b. It matters that it is unconditional: the point of an
anti-vacuity witness is to show the relation is inhabited at a *singular* germ, and a witness
proved under `EigenvalueLawStatement` — a hypothesis with no known inhabitant — could not show
that. `hasExactLocalPair_quadraticGerm` covers the regular case, multiplicity one; this is the
first singular one. -/
public theorem hasLocalVolumeOrder_residualGerm_one :
    HasLocalVolumeOrder (residualGerm 1 1 1) 0 (1 / 2) 2 := by
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine hasLocalVolumeOrder_of_gaussianLaplace (k := 4)
    continuous_residualGerm.measurable residualGerm_nonneg
    (fun t _ w => residualGerm_smul t w) (by norm_num) (by norm_num)
    (c := Real.sqrt Real.pi * (Real.exp (-1) / (2 * Real.sqrt 2)))
    (C := Real.sqrt Real.pi * (3 + 2 * Real.sqrt Real.pi)) (by positivity) ?_ ?_
  · intro T hT
    have hT0 : (0:ℝ) < T := by linarith
    have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [gaussianLaplace_residualGerm_one hT0.le, laplaceScale_half_two hT0]
    have hrw : Real.sqrt Real.pi * (Real.exp (-1) / (2 * Real.sqrt 2))
          * ((Real.sqrt T)⁻¹ * Real.log T)
        = Real.sqrt Real.pi
          * (Real.exp (-1) / (Real.sqrt 2 * Real.sqrt T) * (Real.log T / 2)) := by
      field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (scalarJ_lower hT) hπ.le
  · intro T hT
    have hT0 : (0:ℝ) < T := by linarith
    rw [gaussianLaplace_residualGerm_one hT0.le, laplaceScale_half_two hT0]
    have hrw : Real.sqrt Real.pi * (3 + 2 * Real.sqrt Real.pi)
          * ((Real.sqrt T)⁻¹ * Real.log T)
        = Real.sqrt Real.pi
          * ((3 + 2 * Real.sqrt Real.pi) * ((Real.sqrt T)⁻¹ * Real.log T)) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (scalarJ_upper hT) hπ.le

end AISafetyAtlas.SingularLearning
