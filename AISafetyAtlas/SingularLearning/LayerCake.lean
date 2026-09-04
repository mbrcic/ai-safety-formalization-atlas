module

public import AISafetyAtlas.SingularLearning.Tauberian
public import AISafetyAtlas.SingularLearning.LocalPair
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The layer cake: the Laplace transform is the Laplace average of the sublevel volume

`Tauberian.lean` works with `laplaceAverage V T = T ∫₀^∞ e^{-Ts} V(s) ds` and says of the
identification with an actual Laplace transform:

> **That identification is stated here and not proved**: proving it needs Stieltjes measure
> machinery, and every result below is about the integrated form, so nothing downstream depends
> on the identification being formal.

Nothing downstream of `Tauberian.lean` did. The O70 chain does: what §8 of the MAIS issue #3
candidate computes is `∫ e^{-T f(w)} dw`, and what the local pair is a statement about is
`vol {f ≤ ε}`. This module proves they are the same object, so the identification stops being an
assertion.

## The proof, and why no Stieltjes measure appears

The candidate's own display (8.4) is the argument, and Mathlib's layer cake supplies it. Apply
`Integrable.integral_eq_integral_Ioc_meas_le` to `F = e^{-T K}`, which is nonnegative and at most
`1` because `K ≥ 0`:

    ∫_B e^{-T K} = ∫_{t ∈ (0,1]} vol {x ∈ B : t ≤ e^{-T K x}} dt .

Then substitute `t = e^{-T ε}`, a decreasing bijection of `(0, ∞)` onto `(0, 1)` with
`|dt/dε| = T e^{-T ε}`, and note that `t ≤ e^{-T K x}` reads `K x ≤ ε` after taking logarithms.
The endpoint `t = 1` is a single point and contributes nothing. What comes out is exactly
`T ∫₀^∞ e^{-T ε} vol{K ≤ ε} dε`.

`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` does the substitution; no
Lebesgue–Stieltjes integral is constructed anywhere.

## Hypotheses

`K` measurable and nonnegative, and `T > 0`. Nothing about analyticity, and nothing about the
ball beyond its being a ball — a ball has finite volume, which is what makes `e^{-T K}`
integrable on it.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set Filter Topology

variable {n : ℕ}

/-! ## The substitution `t = e^{-Tε}` -/

/-- `ε ↦ e^{-Tε}` maps `(0, ∞)` onto `(0, 1)`. -/
public theorem image_exp_neg_mul_Ioi {T : ℝ} (hT : 0 < T) :
    (fun ε : ℝ => Real.exp (-T * ε)) '' Set.Ioi 0 = Set.Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨ε, hε, rfl⟩
    have hε0 : (0:ℝ) < ε := hε
    refine ⟨Real.exp_pos _, ?_⟩
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith)
  · rintro ⟨ht0, ht1⟩
    refine ⟨-Real.log t / T, ?_, ?_⟩
    · have hlog : Real.log t < 0 := Real.log_neg ht0 ht1
      have : (0:ℝ) < -Real.log t := by linarith
      exact div_pos this hT
    · show Real.exp (-T * (-Real.log t / T)) = t
      rw [show -T * (-Real.log t / T) = Real.log t by field_simp, Real.exp_log ht0]

/-- `ε ↦ e^{-Tε}` is injective on `(0, ∞)`. -/
public theorem injOn_exp_neg_mul {T : ℝ} (hT : 0 < T) :
    Set.InjOn (fun ε : ℝ => Real.exp (-T * ε)) (Set.Ioi 0) := by
  intro x _ y _ hxy
  have h : -T * x = -T * y := Real.exp_injective hxy
  have : T * x = T * y := by linarith
  exact mul_left_cancel₀ hT.ne' this

/-- The derivative of the substitution. -/
public theorem hasDerivWithinAt_exp_neg_mul {T ε : ℝ} :
    HasDerivWithinAt (fun s : ℝ => Real.exp (-T * s)) (-T * Real.exp (-T * ε)) (Set.Ioi 0) ε := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (-T * s)) (Real.exp (-T * id ε) * (-T * 1)) ε :=
    ((hasDerivAt_id ε).const_mul (-T)).exp
  simpa [mul_comm] using h.hasDerivWithinAt

/-! ## The identification -/

/-- The `t`-superlevel set of `e^{-T K}` is the `ε`-sublevel set of `K`, at `t = e^{-Tε}`. -/
public theorem superlevel_exp_eq_sublevel {K : EuclideanSpace ℝ (Fin n) → ℝ} {T ε : ℝ}
    (hT : 0 < T) :
    {x | Real.exp (-T * ε) ≤ Real.exp (-T * K x)} = {x | K x ≤ ε} := by
  ext x
  simp only [Set.mem_ofPred_eq, Real.exp_le_exp]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **The layer cake, in the form the O70 chain consumes.** The Laplace transform of a
nonnegative measurable germ over a ball is the Laplace average of its sublevel volume.

This is exactly display (8.4) of the candidate, and it retires the one identification that
`Tauberian.lean` asserts without proof. -/
public theorem integral_exp_neg_mul_eq_laplaceAverage
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (δ : ℝ) {T : ℝ}
    (hT : 0 < T) (hKnn : ∀ x, 0 ≤ K x) (hKm : Measurable K) :
    ∫ x in Metric.ball w δ, Real.exp (-T * K x)
      = laplaceAverage (sublevelVolume K w δ) T := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin n)) := volume.restrict (Metric.ball w δ) with hμ
  have hballfin : volume (Metric.ball w δ) ≠ ⊤ := (measure_ball_lt_top (x := w) (r := δ)).ne
  have hμfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hballfin
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-T * K x) with hF
  have hFm : Measurable F := Real.measurable_exp.comp ((measurable_const.mul hKm))
  have hFnn : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  have hFbd : F ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [hF]
    simp only
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by nlinarith [hKnn x])
  have hFint : Integrable F μ := by
    refine (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable ?_
    filter_upwards [hFnn, hFbd] with x h1 h2
    rw [Real.norm_of_nonneg h1]
    exact h2
  -- Mathlib's layer cake, on `(0, 1]`.
  have key := hFint.integral_eq_integral_Ioc_meas_le hFnn hFbd
  -- The endpoint contributes nothing.
  have hIoc : ∫ t in Set.Ioc (0:ℝ) 1, μ.real {a | t ≤ F a}
      = ∫ t in Set.Ioo (0:ℝ) 1, μ.real {a | t ≤ F a} := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- The substitution.
  have hsub : ∫ t in Set.Ioo (0:ℝ) 1, μ.real {a | t ≤ F a}
      = ∫ ε in Set.Ioi (0:ℝ), |(-T * Real.exp (-T * ε))| •
          μ.real {a | Real.exp (-T * ε) ≤ F a} := by
    rw [← image_exp_neg_mul_Ioi hT]
    exact MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun _ _ => hasDerivWithinAt_exp_neg_mul) (injOn_exp_neg_mul hT) _
  -- Identify the integrand.
  have hval : ∀ ε : ℝ, |(-T * Real.exp (-T * ε))| • μ.real {a | Real.exp (-T * ε) ≤ F a}
      = T * (Real.exp (-T * ε) * sublevelVolume K w δ ε) := by
    intro ε
    have habs : |(-T * Real.exp (-T * ε))| = T * Real.exp (-T * ε) := by
      rw [abs_mul, abs_neg, abs_of_pos hT, abs_of_pos (Real.exp_pos _)]
    have hset : {a | Real.exp (-T * ε) ≤ F a} = {x | K x ≤ ε} :=
      superlevel_exp_eq_sublevel (K := K) hT
    have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | K x ≤ ε} :=
      measurableSet_le hKm measurable_const
    have hsets : {x : EuclideanSpace ℝ (Fin n) | K x ≤ ε} ∩ Metric.ball w δ
        = {x ∈ Metric.ball w δ | K x ≤ ε} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    have hμval : μ.real {x | K x ≤ ε} = sublevelVolume K w δ ε := by
      rw [measureReal_def, hμ, Measure.restrict_apply hmeas, hsets, sublevelVolume]
    rw [habs, hset, hμval, smul_eq_mul, mul_assoc]
  rw [hF] at key
  rw [key, hIoc, hsub]
  simp only [hval]
  rw [laplaceAverage, ← MeasureTheory.integral_const_mul]

end AISafetyAtlas.SingularLearning
