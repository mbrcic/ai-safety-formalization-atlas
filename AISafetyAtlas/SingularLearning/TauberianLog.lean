module

public import AISafetyAtlas.SingularLearning.Tauberian
public import AISafetyAtlas.SingularLearning.LaplaceScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Tauberian bridge, carrying the multiplicity

`Tauberian.lean` transfers `V(ε) ≍ ε^lam` to `laplaceAverage V T ≍ T^{-lam}` and back, by an
elementary route: monotonicity of `V` plus one split of the integration range. Its docstring
records what it does not do:

> **Not proved here.** … that the transfer preserves the multiplicity `m` of `eq:volume`, i.e.
> the logarithmic factor — every statement below is a pure power comparison, and a
> `(log 1/ε)^{m-1}` factor is invisible to it

That is an accurate statement about those declarations and **not** a limitation of the method.
This module carries the logarithm across, by the same split, and changes nothing in
`Tauberian.lean`: every statement there stands, and the two ingredients that do not see the
exponent at all — `volume_le_laplace` and `tendsto_gammaTail_atTop` — are reused verbatim.

## Why the logarithm survives the split

The one step that could have noticed the logarithm is the far piece of the split,

    T ∫_{A/T}^{s₁} e^{-Ts} · C · s^lam · log(1/s)^{m-1} ds .

On the range the bound is applied to — `s > A/T ≥ 1/T`, since `A ≥ 1` — one has
`log (1/s) ≤ log T`; and `s ≤ s₁ < e⁻¹` makes `log (1/s) > 1 > 0`, so raising to the power
`m - 1` preserves the inequality. The logarithm therefore comes out of the integral as the
constant `(log T)^{m-1}`, leaving exactly the `gammaTail A lam` of `Tauberian.lean`, and the far
piece is bounded by `C · gammaTail A lam · laplaceScale lam m T`.

Nothing else in the argument mentions the exponent. The near piece is `V (A/T)` by monotonicity,
and the third piece — the range `s > s₁`, which `Tauberian.lean` did not need because its power
bound was global — is at most `Vmax · e^{-T s₁}`, exponentially small and so negligible against
any `laplaceScale`.

## Why the bound on `V` is local here and global there

`Tauberian.lean` assumes `∀ s > 0, V s ≤ C * s ^ lam`. The `volumeScale` analogue is false at
`s ≥ 1`: `log (1/s) ≤ 0` there, and for even `m - 1` it would be a wrong-signed bound on a
nonnegative `V`. So the hypothesis is split in two, as it must be:

* `V s ≤ C * volumeScale lam m s` on `(0, s₁]`, with `s₁ < e⁻¹` so that `log (1/s) > 1`; and
* `V s ≤ Vmax` everywhere, which a sublevel volume inside a fixed ball satisfies for free.

Boundedness also replaces the power bound as the integrability hypothesis, and is cheaper: a
monotone function bounded above is dominated by `Vmax · e^{-Ts}`, with no Gamma integral.

## The identification with an actual Laplace transform

`laplaceAverage V T` is an integral against `V`, not against a germ. `LayerCake.lean` proves
that for `V = sublevelVolume K w δ` it is the Laplace transform `∫_{B(w,δ)} e^{-T K}`, so the
consumer of this module does not have to assume the identification `Tauberian.lean` states in
prose.

## The four results

* `laplace_le_of_logBound` — the three-way split. This is the only new computation.
* `volume_le_of_laplace_le_log` — upper half of the converse: `volume_le_laplace` read at
  `T = 1/ε`, which needs nothing new because that direction never sees the scale.
* `exists_volume_ge_of_laplace_ge_log` — lower half, the bootstrap in the split point `A`.
* `volume_comparable_of_laplace_comparable_log` — the two packaged together.

The lower constant is inexplicit, as in `Tauberian.lean`: pushing `A` out costs a constant that
depends on `C`. The exponent **and** the multiplicity are recovered exactly.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set Filter Topology

/-! ## The logarithm comes out of the integral -/

/-- On `(1/T, s₁]` with `s₁ < e⁻¹` and `T ≥ e`, the logarithmic factor of `volumeScale` is
between `1` and `(log T)^{m-1}`. This is the whole reason the split of `Tauberian.lean` carries
the multiplicity: over the range that matters the logarithm is constant to within the factor the
conclusion already has. -/
public theorem volumeScale_le_rpow_mul_log {lam s₁ T s : ℝ} {m : ℕ}
    (hs₁ : s₁ < Real.exp (-1)) (hT : Real.exp 1 ≤ T) (hs : 1 / T < s) (hsle : s ≤ s₁) :
    volumeScale lam m s ≤ s ^ lam * Real.log T ^ (m - 1) := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hs0 : (0:ℝ) < s := lt_trans (by positivity) hs
  have hlogs : Real.log (1 / s) ≤ Real.log T := by
    rw [Real.log_div one_ne_zero hs0.ne', Real.log_one, zero_sub, neg_le]
    have h : Real.log (1 / T) ≤ Real.log s := Real.log_le_log (by positivity) hs.le
    rwa [Real.log_div one_ne_zero hT0.ne', Real.log_one, zero_sub] at h
  have hlogs0 : (0:ℝ) ≤ Real.log (1 / s) := by
    rw [Real.log_div one_ne_zero hs0.ne', Real.log_one, zero_sub, neg_nonneg]
    have h : Real.log s ≤ Real.log (Real.exp (-1)) := Real.log_le_log hs0 (hsle.trans hs₁.le)
    rw [Real.log_exp] at h
    linarith
  rw [volumeScale]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogs0 hlogs _)
    (Real.rpow_nonneg hs0.le lam)

/-- `laplaceScale` is at least `T ^ (-lam)` once `T ≥ e` and the multiplicity is at least one:
the logarithmic factor is a factor `≥ 1`. Used to make the exponentially small tail negligible
against the scale without a second limit.

`1 ≤ m` is deliberately absent: `m - 1` is `ℕ`-subtraction, so `m = 0` and `m = 1` give the same
scale and the bound holds for both. -/
public theorem rpow_le_laplaceScale {lam T : ℝ} {m : ℕ} (hT : Real.exp 1 ≤ T) :
    T ^ (-lam) ≤ laplaceScale lam m T := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlogT : (1:ℝ) ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hT
  have hpow : (1:ℝ) ≤ Real.log T ^ (m - 1) := one_le_pow₀ hlogT
  rw [laplaceScale]
  nlinarith [Real.rpow_pos_of_pos hT0 (-lam)]

/-! ## Integrability from boundedness -/

/-- A monotone function bounded above is integrable against `e^{-Ts}` on `(0, ∞)`. Cheaper than
`integrableOn_of_power_bound`, and available in the intended application: a sublevel volume
inside a fixed ball is bounded by the ball's volume. -/
public theorem integrableOn_of_bounded {V : ℝ → ℝ} {T Vmax : ℝ} (hV : Monotone V)
    (hVnn : ∀ s > 0, 0 ≤ V s) (hVmax : ∀ s, V s ≤ Vmax) (hT : 0 < T) :
    IntegrableOn (fun s => Real.exp (-T * s) * V s) (Set.Ioi 0) := by
  have hdom : IntegrableOn (fun s => Vmax * Real.exp (-T * s)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_mul hT 0).const_mul Vmax
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul
      hV.measurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hVnn s hs0))]
    calc Real.exp (-T * s) * V s ≤ Real.exp (-T * s) * Vmax :=
          mul_le_mul_of_nonneg_left (hVmax s) (Real.exp_pos _).le
      _ = Vmax * Real.exp (-T * s) := by ring

/-! ## The three-way split -/

/-- The tail beyond a fixed `s₁` is exponentially small. This is the piece `Tauberian.lean` did
not need, because there the power bound held on all of `(0, ∞)`. -/
public theorem laplace_tail_le {V : ℝ → ℝ} {T Vmax s₁ : ℝ}
    (hint : IntegrableOn (fun s => Real.exp (-T * s) * V s) (Set.Ioi s₁))
    (hVmax : ∀ s, V s ≤ Vmax) (hT : 0 < T) :
    T * ∫ s in Set.Ioi s₁, Real.exp (-T * s) * V s ≤ Vmax * Real.exp (-(T * s₁)) := by
  have hle : ∫ s in Set.Ioi s₁, Real.exp (-T * s) * V s
      ≤ ∫ s in Set.Ioi s₁, Real.exp (-T * s) * Vmax :=
    setIntegral_mono_on hint ((integrableOn_exp_neg_mul hT s₁).mul_const _) measurableSet_Ioi
      (fun s _ => mul_le_mul_of_nonneg_left (hVmax s) (Real.exp_pos _).le)
  have hval : ∫ s in Set.Ioi s₁, Real.exp (-T * s) * Vmax
      = Vmax * Real.exp (-(T * s₁)) / T := by
    rw [MeasureTheory.integral_mul_const, integral_exp_neg_mul_Ioi hT]
    ring
  have := mul_le_mul_of_nonneg_left (hle.trans (le_of_eq hval)) hT.le
  refine this.trans (le_of_eq ?_)
  field_simp

/-- **The split, with the logarithm.** For `T ≥ e`, `A ≥ 1` and `A/T ≤ s₁ < e⁻¹`,

    laplaceAverage V T ≤ V (A/T) + C · gammaTail A lam · laplaceScale lam m T
                         + Vmax · e^{-T s₁} .

This is `laplace_le_of_power_bound` of `Tauberian.lean` with `s ^ lam` replaced by
`volumeScale lam m s`, one extra piece for the range where the local bound is unavailable, and
`volumeScale_le_rpow_mul_log` to pull the logarithm out. -/
public theorem laplace_le_of_logBound {V : ℝ → ℝ} {T lam C A s₁ Vmax : ℝ} {m : ℕ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hVmax : ∀ s, V s ≤ Vmax) (hC : 0 ≤ C) (hs₁e : s₁ < Real.exp (-1))
    (hbound : ∀ s ∈ Set.Ioc (0:ℝ) s₁, V s ≤ C * volumeScale lam m s)
    (hT : Real.exp 1 ≤ T) (hA : 1 ≤ A) (hAT : A / T ≤ s₁) :
    laplaceAverage V T
      ≤ V (A / T) + C * gammaTail A lam * laplaceScale lam m T
        + Vmax * Real.exp (-(T * s₁)) := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hAT0 : (0:ℝ) < A / T := div_pos hA0 hT0
  have hlam' : (-1:ℝ) < lam := by linarith
  have hlogT : (1:ℝ) ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hT
  have hlogTpow : (0:ℝ) ≤ Real.log T ^ (m - 1) := by positivity
  have hint := integrableOn_of_bounded hV hVnn hVmax hT0
  -- Split `(0, ∞)` into `(0, A/T]`, `(A/T, s₁]` and `(s₁, ∞)`.
  have hsplit1 : ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V s
      = (∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s)
        + ∫ s in Set.Ioi (A / T), Real.exp (-T * s) * V s := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hAT0.le)),
      Set.Ioc_union_Ioi_eq_Ioi hAT0.le]
  have hsplit2 : ∫ s in Set.Ioi (A / T), Real.exp (-T * s) * V s
      = (∫ s in Set.Ioc (A / T) s₁, Real.exp (-T * s) * V s)
        + ∫ s in Set.Ioi s₁, Real.exp (-T * s) * V s := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hAT0.le)))
      (hint.mono_set (Set.Ioi_subset_Ioi (hAT0.le.trans hAT))),
      Set.Ioc_union_Ioi_eq_Ioi hAT]
  -- Near piece.
  have hpart1 : ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s ≤ V (A / T) / T := by
    have h1 : ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s
        ≤ ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V (A / T) := by
      refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self)
        (((integrableOn_exp_neg_mul hT0 0).mono_set Set.Ioc_subset_Ioi_self).mul_const _)
        measurableSet_Ioc ?_
      intro s hs
      exact mul_le_mul_of_nonneg_left (hV hs.2) (Real.exp_pos _).le
    have h2 : ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V (A / T)
        ≤ ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V (A / T) :=
      setIntegral_mono_set ((integrableOn_exp_neg_mul hT0 0).mul_const _)
        (Filter.Eventually.of_forall fun _ =>
          mul_nonneg (Real.exp_pos _).le (hVnn _ hAT0)) Set.Ioc_subset_Ioi_self.eventuallyLE
    have h3 : ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V (A / T) = V (A / T) / T := by
      rw [MeasureTheory.integral_mul_const, integral_exp_neg_mul_Ioi hT0]
      simp
      ring
    linarith
  -- Middle piece: the local bound, with the logarithm pulled out.
  have hpart2 : ∫ s in Set.Ioc (A / T) s₁, Real.exp (-T * s) * V s
      ≤ C * Real.log T ^ (m - 1) * (T ^ (-lam) * T⁻¹ * gammaTail A lam) := by
    have hdom : IntegrableOn
        (fun s => C * Real.log T ^ (m - 1) * (Real.exp (-T * s) * s ^ lam))
        (Set.Ioi (A / T)) :=
      ((integrableOn_exp_neg_mul_rpow hT0 hlam').mono_set
        (Set.Ioi_subset_Ioi hAT0.le)).const_mul _
    have h1 : ∫ s in Set.Ioc (A / T) s₁, Real.exp (-T * s) * V s
        ≤ ∫ s in Set.Ioc (A / T) s₁,
            C * Real.log T ^ (m - 1) * (Real.exp (-T * s) * s ^ lam) := by
      refine setIntegral_mono_on
        (hint.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hAT0.le)))
        (hdom.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc ?_
      intro s hs
      have hs0 : (0:ℝ) < s := hAT0.trans hs.1
      have hTs : 1 / T < s := lt_of_le_of_lt (by
        rw [div_le_div_iff_of_pos_right hT0]
        exact hA) hs.1
      have hb1 : V s ≤ C * volumeScale lam m s := hbound s ⟨hs0, hs.2⟩
      have hb2 : C * volumeScale lam m s ≤ C * (s ^ lam * Real.log T ^ (m - 1)) :=
        mul_le_mul_of_nonneg_left (volumeScale_le_rpow_mul_log hs₁e hT hTs hs.2) hC
      have hb : V s ≤ C * Real.log T ^ (m - 1) * s ^ lam := by nlinarith
      have := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-T * s)).le
      nlinarith [Real.exp_pos (-T * s)]
    have h2 : ∫ s in Set.Ioc (A / T) s₁,
          C * Real.log T ^ (m - 1) * (Real.exp (-T * s) * s ^ lam)
        ≤ ∫ s in Set.Ioi (A / T),
          C * Real.log T ^ (m - 1) * (Real.exp (-T * s) * s ^ lam) := by
      refine setIntegral_mono_set hdom ?_ Set.Ioc_subset_Ioi_self.eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0:ℝ) < s := hAT0.trans hs
      have : (0:ℝ) ≤ s ^ lam := Real.rpow_nonneg hs0.le lam
      positivity
    have h3 : ∫ s in Set.Ioi (A / T),
          C * Real.log T ^ (m - 1) * (Real.exp (-T * s) * s ^ lam)
        = C * Real.log T ^ (m - 1) * (T ^ (-lam) * T⁻¹ * gammaTail A lam) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_rpow_Ioi hT0 hA0]
    linarith
  -- Tail piece.
  have hpart3 : T * ∫ s in Set.Ioi s₁, Real.exp (-T * s) * V s
      ≤ Vmax * Real.exp (-(T * s₁)) :=
    laplace_tail_le (hint.mono_set (Set.Ioi_subset_Ioi (hAT0.le.trans hAT))) hVmax hT0
  rw [laplaceAverage, hsplit1, hsplit2]
  have hexpand : T * ((∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s)
        + ((∫ s in Set.Ioc (A / T) s₁, Real.exp (-T * s) * V s)
          + ∫ s in Set.Ioi s₁, Real.exp (-T * s) * V s))
      = T * (∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s)
        + T * (∫ s in Set.Ioc (A / T) s₁, Real.exp (-T * s) * V s)
        + T * ∫ s in Set.Ioi s₁, Real.exp (-T * s) * V s := by ring
  rw [hexpand]
  have h1 := mul_le_mul_of_nonneg_left hpart1 hT0.le
  have h2 := mul_le_mul_of_nonneg_left hpart2 hT0.le
  have he1 : T * (V (A / T) / T) = V (A / T) := by field_simp
  have he2 : T * (C * Real.log T ^ (m - 1) * (T ^ (-lam) * T⁻¹ * gammaTail A lam))
      = C * gammaTail A lam * laplaceScale lam m T := by
    rw [laplaceScale]
    field_simp
  rw [he1] at h1
  rw [he2] at h2
  linarith

/-! ## The converse, both halves -/

/-- **Upper half.** A `laplaceScale` upper bound on the Laplace average forces a `volumeScale`
upper bound on the volume, with constant `e·K₂`.

This is `volume_le_laplace` read at `T = 1/ε` and needs nothing new: that direction of the
transfer never looks at the scale. -/
public theorem volume_le_of_laplace_le_log {V : ℝ → ℝ} {lam K₂ T₀ ε Vmax : ℝ} {m : ℕ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hVmax : ∀ s, V s ≤ Vmax) (hT₀ : 0 < T₀)
    (hlap : ∀ T ≥ T₀, laplaceAverage V T ≤ K₂ * laplaceScale lam m T)
    (hε : 0 < ε) (hεle : ε ≤ 1 / T₀) :
    V ε ≤ Real.exp 1 * K₂ * volumeScale lam m ε := by
  have hTpos : (0:ℝ) < 1 / ε := by positivity
  have hTge : 1 / ε ≥ T₀ := by
    rw [ge_iff_le, le_div_iff₀ hε]
    rw [le_div_iff₀ hT₀] at hεle
    linarith
  have hinvinv : 1 / (1 / ε) = ε := one_div_one_div ε
  have hint := integrableOn_of_bounded hV hVnn hVmax hTpos
  have ha := volume_le_laplace hV hVnn hint hTpos
  rw [hinvinv] at ha
  have hscale : laplaceScale lam m (1 / ε) = volumeScale lam m ε := by
    rw [laplaceScale_eq_volumeScale lam m hTpos, hinvinv]
  have hchain : Real.exp (-1) * V ε ≤ K₂ * volumeScale lam m ε := by
    have h := ha.trans (hlap (1 / ε) hTge)
    rwa [hscale] at h
  have hexp : Real.exp 1 * (Real.exp (-1) * V ε) = V ε := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  calc V ε = Real.exp 1 * (Real.exp (-1) * V ε) := hexp.symm
    _ ≤ Real.exp 1 * (K₂ * volumeScale lam m ε) :=
        mul_le_mul_of_nonneg_left hchain (Real.exp_pos 1).le
    _ = Real.exp 1 * K₂ * volumeScale lam m ε := by ring

/-- The exponentially small tail is eventually below any fixed multiple of the scale. The single
limit the bootstrap needs beyond `tendsto_gammaTail_atTop`. -/
public theorem eventually_tail_le_laplaceScale {lam Vmax s₁ c : ℝ} {m : ℕ}
    (hs₁ : 0 < s₁) (hc : 0 < c) :
    ∀ᶠ T in atTop, Vmax * Real.exp (-(T * s₁)) ≤ c * laplaceScale lam m T := by
  have hlim : Filter.Tendsto (fun T : ℝ => Vmax * (T ^ lam * Real.exp (-s₁ * T)))
      atTop (nhds 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam s₁ hs₁).const_mul Vmax
  filter_upwards [hlim.eventually_le_const hc, Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_gt_atTop (0:ℝ)] with T hTlim hTe hT0
  have hscale : T ^ (-lam) ≤ laplaceScale lam m T := rpow_le_laplaceScale hTe
  have hpow : (0:ℝ) < T ^ lam := Real.rpow_pos_of_pos hT0 lam
  have hinv : T ^ (-lam) = (T ^ lam)⁻¹ := by
    rw [Real.rpow_neg hT0.le]
  have hkey : Vmax * Real.exp (-(T * s₁)) ≤ c * T ^ (-lam) := by
    have hexp : Real.exp (-s₁ * T) = Real.exp (-(T * s₁)) := by ring_nf
    rw [hexp] at hTlim
    rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hpow]
    have hcomm : Vmax * Real.exp (-(T * s₁)) * T ^ lam
        = Vmax * (T ^ lam * Real.exp (-(T * s₁))) := by ring
    rw [hcomm]
    exact hTlim
  exact hkey.trans (mul_le_mul_of_nonneg_left hscale hc.le)

/-- **Lower half — the bootstrap.** A `laplaceScale` lower bound on the Laplace average forces a
`volumeScale` lower bound on the volume near `0`.

Two constants must be chosen rather than fixed: the split point `A`, pushed out until
`C · gammaTail A lam` is at most a third of the lower constant, and the threshold `T₁` beyond
which the exponential tail is another third. What survives is a third of the lower bound, and
`V (A/T) = V ε` at `ε = A/T`. -/
public theorem exists_volume_ge_of_laplace_ge_log {V : ℝ → ℝ} {lam C K₁ T₀ s₁ Vmax : ℝ} {m : ℕ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hVmax : ∀ s, V s ≤ Vmax) (hC : 0 ≤ C) (hs₁ : 0 < s₁) (hs₁e : s₁ < Real.exp (-1))
    (hbound : ∀ s ∈ Set.Ioc (0:ℝ) s₁, V s ≤ C * volumeScale lam m s)
    (hK₁ : 0 < K₁)
    (hlap : ∀ T ≥ T₀, K₁ * laplaceScale lam m T ≤ laplaceAverage V T) :
    ∃ c > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0:ℝ) ε₀, c * volumeScale lam m ε ≤ V ε := by
  -- Push the split point out.
  have htend : Filter.Tendsto (fun A => C * gammaTail A lam) Filter.atTop (nhds 0) := by
    simpa using (tendsto_gammaTail_atTop lam).const_mul C
  obtain ⟨A, hAtail, hA1⟩ :=
    ((htend.eventually_lt_const (by linarith : (0:ℝ) < K₁ / 3)).and
      (Filter.eventually_ge_atTop (1:ℝ))).exists
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hAlam : (0:ℝ) < A ^ lam := Real.rpow_pos_of_pos hA0 lam
  -- Push the threshold out.
  obtain ⟨T₁, hT₁⟩ := ((eventually_tail_le_laplaceScale (lam := lam) (Vmax := Vmax) hs₁
    (by linarith : (0:ℝ) < K₁ / 3)).and
      ((Filter.eventually_ge_atTop (Real.exp 1)).and
        ((Filter.eventually_ge_atTop (A / s₁)).and
          (Filter.eventually_ge_atTop T₀)))).exists_forall_of_atTop
  refine ⟨K₁ / (3 * A ^ lam), by positivity, min (A / T₁) (Real.exp (-1)), ?_, ?_⟩
  · have hT₁0 : (0:ℝ) < T₁ := lt_of_lt_of_le (Real.exp_pos 1) (hT₁ T₁ le_rfl).2.1
    exact lt_min (by positivity) (Real.exp_pos _)
  rintro ε ⟨hε, hεle⟩
  have hεA : ε ≤ A / T₁ := hεle.trans (min_le_left _ _)
  have hε1 : ε ≤ Real.exp (-1) := hεle.trans (min_le_right _ _)
  set T := A / ε with hTdef
  have hT0 : (0:ℝ) < T := div_pos hA0 hε
  have hT₁0 : (0:ℝ) < T₁ := lt_of_lt_of_le (Real.exp_pos 1) (hT₁ T₁ le_rfl).2.1
  have hTge : T₁ ≤ T := by
    rw [hTdef, le_div_iff₀ hε]
    rw [le_div_iff₀ hT₁0] at hεA
    linarith
  obtain ⟨htail, hTe, hTs₁, hTT₀⟩ := hT₁ T hTge
  have hAT : A / T ≤ s₁ := by
    rw [div_le_iff₀ hT0]
    rw [div_le_iff₀ hs₁] at hTs₁
    linarith
  have hATε : A / T = ε := by
    rw [hTdef]
    field_simp
  have hb := laplace_le_of_logBound hV hVnn hlam hVmax hC hs₁e hbound hTe hA1 hAT
  rw [hATε] at hb
  have hmain := (hlap T hTT₀).trans hb
  -- Compare the two scales.
  have hscale : A ^ (-lam) * volumeScale lam m ε ≤ laplaceScale lam m T := by
    have hlogA : (0:ℝ) ≤ Real.log A := Real.log_nonneg hA1
    have hlogε : (1:ℝ) ≤ Real.log (1 / ε) := by
      rw [Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub, le_neg]
      have h : Real.log ε ≤ Real.log (Real.exp (-1)) := Real.log_le_log hε hε1
      rwa [Real.log_exp] at h
    have hlogT : Real.log (1 / ε) ≤ Real.log T := by
      rw [hTdef, Real.log_div hA0.ne' hε.ne', Real.log_div one_ne_zero hε.ne', Real.log_one,
        zero_sub]
      linarith
    have hpowlog : Real.log (1 / ε) ^ (m - 1) ≤ Real.log T ^ (m - 1) :=
      pow_le_pow_left₀ (by linarith) hlogT _
    have hrpow : T ^ (-lam) = A ^ (-lam) * ε ^ lam := by
      rw [hTdef, Real.div_rpow hA0.le hε.le, Real.rpow_neg hε.le, div_inv_eq_mul]
    have hnn : (0:ℝ) ≤ A ^ (-lam) * ε ^ lam := by positivity
    rw [laplaceScale, volumeScale, hrpow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpowlog hnn
  have hVS : (0:ℝ) ≤ volumeScale lam m ε := by
    rw [volumeScale]
    have hlogε : (0:ℝ) ≤ Real.log (1 / ε) := by
      rw [Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub, neg_nonneg]
      have h : Real.log ε ≤ Real.log (Real.exp (-1)) := Real.log_le_log hε hε1
      rw [Real.log_exp] at h
      linarith
    positivity
  have hLS : (0:ℝ) ≤ laplaceScale lam m T := le_trans (by positivity) hscale
  have hgam : C * gammaTail A lam ≤ K₁ / 3 := hAtail.le
  have hstep : K₁ / 3 * laplaceScale lam m T ≤ V ε := by
    linarith [mul_le_mul_of_nonneg_right hgam hLS, htail, hmain]
  have hfinal : K₁ / (3 * A ^ lam) * volumeScale lam m ε ≤ K₁ / 3 * laplaceScale lam m T := by
    have hAneg : A ^ (-lam) = (A ^ lam)⁻¹ := by rw [Real.rpow_neg hA0.le]
    rw [hAneg] at hscale
    have := mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ K₁ / 3)
    calc K₁ / (3 * A ^ lam) * volumeScale lam m ε
        = K₁ / 3 * ((A ^ lam)⁻¹ * volumeScale lam m ε) := by field_simp
      _ ≤ K₁ / 3 * laplaceScale lam m T := this
  exact hfinal.trans hstep

/-- **The converse, packaged.** Two-sided `laplaceScale` behaviour of the Laplace average gives
two-sided `volumeScale` behaviour of the volume near `0` — exponent and multiplicity both. -/
public theorem volume_comparable_of_laplace_comparable_log
    {V : ℝ → ℝ} {lam C K₁ K₂ T₀ s₁ Vmax : ℝ} {m : ℕ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hVmax : ∀ s, V s ≤ Vmax) (hC : 0 ≤ C) (hs₁ : 0 < s₁) (hs₁e : s₁ < Real.exp (-1))
    (hbound : ∀ s ∈ Set.Ioc (0:ℝ) s₁, V s ≤ C * volumeScale lam m s)
    (hK₁ : 0 < K₁) (hT₀ : 0 < T₀)
    (hlo : ∀ T ≥ T₀, K₁ * laplaceScale lam m T ≤ laplaceAverage V T)
    (hup : ∀ T ≥ T₀, laplaceAverage V T ≤ K₂ * laplaceScale lam m T) :
    ∃ c₁ > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0:ℝ) ε₀,
      c₁ * volumeScale lam m ε ≤ V ε ∧ V ε ≤ Real.exp 1 * K₂ * volumeScale lam m ε := by
  obtain ⟨c, hc, δ, hδ, hlow⟩ :=
    exists_volume_ge_of_laplace_ge_log hV hVnn hlam hVmax hC hs₁ hs₁e hbound hK₁ hlo
  refine ⟨c, hc, min δ (1 / T₀), lt_min hδ (by positivity), ?_⟩
  rintro ε ⟨hε, hεle⟩
  exact ⟨hlow ε ⟨hε, hεle.trans (min_le_left _ _)⟩,
    volume_le_of_laplace_le_log hV hVnn hVmax hT₀ hup hε (hεle.trans (min_le_right _ _))⟩

/-- **The converse, with the volume bound derived rather than assumed.**

`volume_comparable_of_laplace_comparable_log` takes the `volumeScale` upper bound on `V` as a
hypothesis, because that is what its lower half consumes. A consumer does not have to supply it:
the upper half produces it, from the same Laplace upper bound, and with no circularity — the
upper half uses no bound at all.

This is the interface the germ-level consumers use: monotone, nonnegative, bounded `V`, plus a
two-sided `laplaceScale` estimate on its Laplace average, and nothing else. -/
public theorem volume_comparable_of_laplace_log {V : ℝ → ℝ} {lam K₁ K₂ T₀ Vmax : ℝ} {m : ℕ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hVmax : ∀ s, V s ≤ Vmax) (hK₁ : 0 < K₁) (hT₀ : 0 < T₀)
    (hlo : ∀ T ≥ T₀, K₁ * laplaceScale lam m T ≤ laplaceAverage V T)
    (hup : ∀ T ≥ T₀, laplaceAverage V T ≤ K₂ * laplaceScale lam m T) :
    ∃ c₁ > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0:ℝ) ε₀,
      c₁ * volumeScale lam m ε ≤ V ε ∧ V ε ≤ Real.exp 1 * K₂ * volumeScale lam m ε := by
  -- `K₂` is positive, because the two bounds meet at a point where the scale is.
  set T₂ := max (Real.exp 1) T₀ with hT₂
  have hT₂e : Real.exp 1 ≤ T₂ := le_max_left _ _
  have hT₂₀ : T₀ ≤ T₂ := le_max_right _ _
  have hT₂0 : (0:ℝ) < T₂ := lt_of_lt_of_le (Real.exp_pos 1) hT₂e
  have hscale : (0:ℝ) < laplaceScale lam m T₂ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hT₂0 (-lam)) (rpow_le_laplaceScale hT₂e)
  have hK₁K₂ : K₁ ≤ K₂ := by
    have h1 := hlo T₂ hT₂₀
    have h2 := hup T₂ hT₂₀
    exact le_of_mul_le_mul_right (by linarith) hscale
  have hK₂ : 0 < K₂ := lt_of_lt_of_le hK₁ hK₁K₂
  have hC : (0:ℝ) ≤ Real.exp 1 * K₂ := by positivity
  -- The `volumeScale` upper bound on `V`, from the upper half.
  set s₁ := min (1 / T₀) (Real.exp (-1) / 2) with hs₁def
  have hs₁ : (0:ℝ) < s₁ := lt_min (by positivity) (by positivity)
  have hs₁e : s₁ < Real.exp (-1) := by
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    have := Real.exp_pos (-1)
    linarith
  have hbound : ∀ s ∈ Set.Ioc (0:ℝ) s₁, V s ≤ Real.exp 1 * K₂ * volumeScale lam m s := by
    rintro s ⟨hs0, hs⟩
    exact volume_le_of_laplace_le_log hV hVnn hVmax hT₀ hup hs0
      (hs.trans (min_le_left _ _))
  exact volume_comparable_of_laplace_comparable_log hV hVnn hlam hVmax hC hs₁ hs₁e hbound
    hK₁ hT₀ hlo hup

end AISafetyAtlas.SingularLearning
