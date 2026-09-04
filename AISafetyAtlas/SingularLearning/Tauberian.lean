module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Tauberian bridge: sublevel volume against the Laplace transform

Singular learning theory keeps two different objects in play.

* The **sublevel volume** `V(ε) = vol {K ≤ ε}`. This is what `MAIS-A6.tex` `def:local` and
  `eq:volume` speak about, and it is the form in which
  `AISafetyAtlas/SingularLearning/LocalPair.lean` states the local pair: `HasExactLocalPair` and
  `HasLocalVolumeOrder` are both relations on `sublevelVolume`.
* The **Laplace transform** `L(T) = ∫ e^{-T·K(x)} dx`. This is what is actually *computable* for
  the models of interest, because it factors through Gaussian and Wishart integrals — no
  resolution of singularities and no sublevel-set measure is ever evaluated directly.

Nothing connects the two unless a transfer theorem is proved. This module proves that transfer,
in both directions, and it does so by the **elementary route**: monotonicity of `V` plus a single
split of the integration range. There is no complex analysis here, no Wiener–Ikehara theorem, no
Karamata regular variation, and nothing from those theories is imported. The price of staying
elementary is that the transfer is two-sided *in order of magnitude* only: it moves
`V(ε) ≍ ε^lam` to `L(T) ≍ T^{-lam}` and back, and it does not move the constant.

## What `laplaceAverage` is, and why it is written this way

`laplaceAverage V T = T ∫₀^∞ e^{-Ts} V(s) ds`.

For `V` nondecreasing with `V(0⁺) = 0` this is the integration-by-parts form of the
Lebesgue–Stieltjes integral `∫₀^∞ e^{-Ts} dV(s)`, which for `V(s) = vol {K ≤ s}` is exactly the
Laplace transform `∫ e^{-T·K(x)} dx` by the layer-cake formula. **That identification is stated
here and not proved**: proving it needs Stieltjes measure machinery, and every result below is
about the integrated form, so nothing downstream depends on the identification being formal.

Working with an abstract nondecreasing `V : ℝ → ℝ` rather than with a specific germ is
deliberate: the transfer is a fact about monotone functions and does not know what a loss
landscape is.

## The two bounds, and exactly which hypotheses each one consumed

* `volume_le_laplace` (**Laplace dominates volume**), `e^{-1} · V(1/T) ≤ laplaceAverage V T`.
  Consumed: `Monotone V`; `0 ≤ V s` for `s > 0`; integrability of `s ↦ e^{-Ts} V s` on `(0, ∞)`;
  `0 < T`. It consumed **no** power bound, **no** exponent hypothesis (no exponent occurs), and
  no hypothesis on `V` off `(0, ∞)`. Monotonicity is used once, to replace `V s` by `V (1/T)` on
  `s ≥ 1/T`; nonnegativity is used once, to enlarge the domain from `(1/T, ∞)` back to `(0, ∞)`.

* `laplace_le_of_power_bound` (**volume dominates Laplace, given a power bound**),
  `laplaceAverage V T ≤ V (A/T) + C · gammaTail A lam · T^{-lam}` for every split point `A > 0`.
  Consumed: `Monotone V`; `0 ≤ V s` for `s > 0`; `0 < lam`; `∀ s > 0, V s ≤ C * s ^ lam`;
  `0 < T`; `0 < A`. It did **not** consume `0 ≤ C`: with `V` nonnegative the power bound already
  forces `C ≥ 0`, so requiring it separately would be a redundant hypothesis.

## Where `0 < lam` is really needed, and where it is not

`0 < lam` is an explicit hypothesis of every headline theorem, never a silent assumption. The
honest accounting is finer than that, and is recorded in the statements themselves: the two
integrability lemmas `integrableOn_exp_neg_mul_rpow` and `integrableOn_of_power_bound` are stated
with `-1 < lam`, which is what their proofs consume — `-1 < lam` is exactly the convergence of
the Gamma integrand `e^{-u} u^lam` at `0`, and it is the real boundary of the method. Everything
above them keeps `0 < lam`, because that is the regime in which the conclusion has content: at
`lam = 0` the comparison `V(ε) ≍ ε^lam` asserts no decay at all, `V(0⁺)` need not vanish, and the
transfer, while still true as an inequality, says nothing about a learning coefficient. Nothing
in this file may be read as evidence about `lam = 0`.

## The corollaries (both directions closed)

* `laplace_comparable_of_volume_comparable`: from `c₁ ε^lam ≤ V ε` at small `ε` **and** a global
  power upper bound, `e^{-1} c₁ T^{-lam} ≤ laplaceAverage V T ≤ c₂ (1 + gammaTail 1 lam) T^{-lam}`
  for `T ≥ 1/ε₀`. The split point is taken to be `A = 1`; no limit in `A` is needed.
* `volume_comparable_of_laplace_comparable`: conversely, from `K₁ T^{-lam} ≤ laplaceAverage V T ≤
  K₂ T^{-lam}` for large `T`, together with the power upper bound on `V`, one gets
  `c₁ ε^lam ≤ V ε ≤ e·K₂ ε^lam` at small `ε`. The upper half is `volume_le_laplace` read
  backwards. The lower half is the bootstrap: the split point `A` must be pushed out far enough
  that `C · gammaTail A lam ≤ K₁/2`, which is possible because `gammaTail A lam → 0`
  (`tendsto_gammaTail_atTop`). This is the only place where a limit is taken.

The lower power bound on `V` is *not* assumed in the converse and *is* concluded; the upper power
bound is assumed in both directions, because without it `laplaceAverage V T` need not even be
defined (a monotone `V` may grow fast enough to destroy integrability).

**Not proved here.** That `laplaceAverage` equals `∫ e^{-Ts} dV(s)` — see above, and
`LayerCake.lean` for the form the O70 chain needs; that the transfer preserves the multiplicity
`m` of `eq:volume`, i.e. the logarithmic factor — every statement *below* is a pure power
comparison, and a `(log 1/ε)^{m-1}` factor is invisible to it, which is why `TauberianLog.lean`
redoes the split with the factor carried; and any statement whatsoever about a specific model's
`K`.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set Filter Topology

/-! ## The two transforms -/

/-- The Laplace-type average of a sublevel function,
`laplaceAverage V T = T ∫₀^∞ e^{-Ts} V(s) ds`.

For `V` nondecreasing with `V(0⁺) = 0` this is the integration-by-parts form of
`∫₀^∞ e^{-Ts} dV(s)`, hence — when `V(s) = vol {K ≤ s}` — of the Laplace transform
`∫ e^{-T·K(x)} dx`. The integrated form is used so that no Lebesgue–Stieltjes machinery is
needed; the agreement is asserted in the module docstring and is not proved. -/
@[expose] public noncomputable def laplaceAverage (V : ℝ → ℝ) (T : ℝ) : ℝ :=
  T * ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V s

/-- The Gamma tail `∫_A^∞ e^{-u} u^lam du`: the exact error constant produced by the split in
`laplace_le_of_power_bound`.

It is kept as an integral rather than replaced by a crude explicit majorant because the only two
properties ever used are `gammaTail_nonneg` and `tendsto_gammaTail_atTop`, and both are cheaper
to prove for the integral than for a hand-rolled bound. It is *not* dressed up as the incomplete
Gamma function: no special-function API is invoked anywhere below. -/
@[expose] public noncomputable def gammaTail (A lam : ℝ) : ℝ :=
  ∫ u in Set.Ioi A, Real.exp (-u) * u ^ lam

/-- The scaled Gamma integrand `s ↦ e^{-Ts} s^lam` is integrable on `(0, ∞)`.

This is `Real.GammaIntegral_convergent` at parameter `lam + 1`, pushed through the scaling
`s ↦ T · s` by `integrableOn_Ioi_comp_mul_left_iff`. The hypothesis is `-1 < lam`, not `0 < lam`:
that is precisely the convergence of `e^{-u} u^lam` at the origin, and it is what the proof
consumes. -/
public theorem integrableOn_exp_neg_mul_rpow {T lam : ℝ} (hT : 0 < T) (hlam : -1 < lam) :
    IntegrableOn (fun s => Real.exp (-T * s) * s ^ lam) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ lam) (Set.Ioi 0) := by
    have := Real.GammaIntegral_convergent (s := lam + 1) (by linarith)
    simpa using this
  have hscale : IntegrableOn (fun x : ℝ => Real.exp (-(T * x)) * (T * x) ^ lam) (Set.Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u) * u ^ lam) 0 hT).2 (by simpa using hg)
    simpa using this
  have hmul := hscale.const_mul ((T ^ lam)⁻¹)
  refine MeasureTheory.IntegrableOn.congr_fun hmul ?_ measurableSet_Ioi
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  have hTlam : (T : ℝ) ^ lam ≠ 0 := (Real.rpow_pos_of_pos hT lam).ne'
  simp only [neg_mul]
  rw [Real.mul_rpow hT.le hx0.le]
  field_simp

/-- `s ↦ e^{-Ts}` is integrable on any right ray, for `T > 0`. -/
public theorem integrableOn_exp_neg_mul {T : ℝ} (hT : 0 < T) (c : ℝ) :
    IntegrableOn (fun s => Real.exp (-T * s)) (Set.Ioi c) := by
  simpa using integrableOn_exp_mul_Ioi (a := -T) (by linarith) c

/-- `∫_a^∞ e^{-Ts} ds = e^{-Ta} / T`. Proved by rescaling `integral_exp_neg_Ioi` along
`integral_comp_mul_left_Ioi`; at `a = 0` it gives the normalization `T ∫₀^∞ e^{-Ts} ds = 1` that
makes `laplaceAverage` an average. -/
public theorem integral_exp_neg_mul_Ioi {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ∫ s in Set.Ioi a, Real.exp (-T * s) = Real.exp (-(T * a)) / T := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u)) a hT
  rw [integral_exp_neg_Ioi] at h
  simpa [neg_mul, div_eq_inv_mul] using h

/-! ## (a) The Laplace average dominates the volume -/

/-- **(a) Laplace dominates volume.** `e^{-1} · V(1/T) ≤ laplaceAverage V T`.

Restrict the integral to `s ≥ 1/T`, where monotonicity gives `V s ≥ V (1/T)`, and use
`T ∫_{1/T}^∞ e^{-Ts} ds = e^{-1}`. The enlargement back to `(0, ∞)` is where nonnegativity of `V`
is used; monotonicity is used only for the constant comparison.

Hypotheses consumed: `Monotone V`, nonnegativity of `V` on `(0, ∞)`, integrability of the
integrand, and `0 < T`. No power bound and no exponent hypothesis: this direction is free. -/
public theorem volume_le_laplace {V : ℝ → ℝ} {T : ℝ} (hV : Monotone V)
    (hVnn : ∀ s > 0, 0 ≤ V s)
    (hint : IntegrableOn (fun s => Real.exp (-T * s) * V s) (Set.Ioi 0)) (hT : 0 < T) :
    Real.exp (-1) * V (1 / T) ≤ laplaceAverage V T := by
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have hconst : IntegrableOn (fun s => Real.exp (-T * s) * V (1 / T)) (Set.Ioi (1 / T)) :=
    (integrableOn_exp_neg_mul hT (1 / T)).mul_const _
  have hstep2 : ∫ s in Set.Ioi (1 / T), Real.exp (-T * s) * V (1 / T)
      ≤ ∫ s in Set.Ioi (1 / T), Real.exp (-T * s) * V s := by
    refine setIntegral_mono_on hconst (hint.mono_set (Ioi_subset_Ioi hTinv.le))
      measurableSet_Ioi ?_
    intro s hs
    exact mul_le_mul_of_nonneg_left (hV (le_of_lt hs)) (Real.exp_pos _).le
  have hstep1 : ∫ s in Set.Ioi (1 / T), Real.exp (-T * s) * V s
      ≤ ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V s := by
    refine setIntegral_mono_set hint ?_ (Ioi_subset_Ioi hTinv.le).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.exp_pos _).le (hVnn s hs)
  have hval : ∫ s in Set.Ioi (1 / T), Real.exp (-T * s) * V (1 / T)
      = V (1 / T) * (Real.exp (-1) / T) := by
    rw [MeasureTheory.integral_mul_const, integral_exp_neg_mul_Ioi hT,
      mul_one_div_cancel hT.ne']
    ring
  have hmain := mul_le_mul_of_nonneg_left (hval ▸ hstep2.trans hstep1) hT.le
  rw [laplaceAverage]
  refine le_trans (le_of_eq ?_) hmain
  field_simp

/-! ## (b) The volume dominates the Laplace average, given a power bound -/

/-- A power upper bound plus monotonicity makes the Laplace integrand integrable, so
`laplaceAverage V T` is not an ill-defined symbol in the results below.

Domination by `C · e^{-Ts} s^lam` via `Integrable.mono'`; measurability of `V` is
`Monotone.measurable`, which is why monotonicity appears in an integrability lemma at all. Stated
with `-1 < lam`, the honest hypothesis. -/
public theorem integrableOn_of_power_bound {V : ℝ → ℝ} {T lam C : ℝ} (hV : Monotone V)
    (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : -1 < lam)
    (hbound : ∀ s > 0, V s ≤ C * s ^ lam) (hT : 0 < T) :
    IntegrableOn (fun s => Real.exp (-T * s) * V s) (Set.Ioi 0) := by
  have hdom : IntegrableOn (fun s => C * (Real.exp (-T * s) * s ^ lam)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_mul_rpow hT hlam).const_mul C
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul
      hV.measurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    have h1 : Real.exp (-T * s) * V s ≤ Real.exp (-T * s) * (C * s ^ lam) :=
      mul_le_mul_of_nonneg_left (hbound s hs0) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hVnn s hs0))]
    calc Real.exp (-T * s) * V s ≤ Real.exp (-T * s) * (C * s ^ lam) := h1
      _ = C * (Real.exp (-T * s) * s ^ lam) := by ring

/-- The substitution `u = T·s` on the far piece:
`∫_{A/T}^∞ e^{-Ts} s^lam ds = T^{-lam} · T⁻¹ · gammaTail A lam`.

`0 < A` is needed, not decoration: it puts the ray `(A/T, ∞)` inside `(0, ∞)`, where
`(T·s)^lam = T^lam · s^lam` holds. -/
public theorem integral_exp_neg_mul_rpow_Ioi {T lam A : ℝ} (hT : 0 < T) (hA : 0 < A) :
    ∫ s in Set.Ioi (A / T), Real.exp (-T * s) * s ^ lam
      = T ^ (-lam) * T⁻¹ * gammaTail A lam := by
  have hAT : (0:ℝ) < A / T := div_pos hA hT
  have hTA : T * (A / T) = A := by field_simp
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u) * u ^ lam) (A / T) hT
  rw [hTA] at h
  have hlhs : ∫ x in Set.Ioi (A / T), Real.exp (-(T * x)) * (T * x) ^ lam
      = T ^ lam * ∫ s in Set.Ioi (A / T), Real.exp (-T * s) * s ^ lam := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0:ℝ) < x := hAT.trans hx
    simp only [neg_mul]
    rw [Real.mul_rpow hT.le hx0.le]
    ring
  rw [hlhs] at h
  have hTlam : (T : ℝ) ^ lam ≠ 0 := (Real.rpow_pos_of_pos hT lam).ne'
  rw [Real.rpow_neg hT.le, gammaTail]
  rw [smul_eq_mul] at h
  field_simp at h ⊢
  linarith [h]

/-- **(b) Volume dominates Laplace, given a power bound.**
`laplaceAverage V T ≤ V (A/T) + C · gammaTail A lam · T^{-lam}`, for every split point `A > 0`.

Split `∫₀^∞ = ∫_0^{A/T} + ∫_{A/T}^∞`. On the near piece monotonicity gives `V s ≤ V (A/T)`, and
the mass is at most `T ∫₀^∞ e^{-Ts} ds = 1`; on the far piece the power bound and the
substitution `u = T·s` give the Gamma tail. The bound is uniform in `A`, and the freedom in `A`
is what the converse Tauberian direction later spends.

Hypotheses consumed: `Monotone V`, nonnegativity on `(0, ∞)`, `0 < lam`, the power bound,
`0 < T`, `0 < A`. `0 ≤ C` is deliberately absent: it follows from the power bound at any `s > 0`
together with `V s ≥ 0`, so assuming it would be redundant. -/
public theorem laplace_le_of_power_bound {V : ℝ → ℝ} {T lam C A : ℝ} (hV : Monotone V)
    (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hbound : ∀ s > 0, V s ≤ C * s ^ lam) (hT : 0 < T) (hA : 0 < A) :
    laplaceAverage V T ≤ V (A / T) + C * gammaTail A lam * T ^ (-lam) := by
  have hlam' : (-1:ℝ) < lam := by linarith
  have hAT : (0:ℝ) < A / T := div_pos hA hT
  have hint := integrableOn_of_power_bound hV hVnn hlam' hbound hT
  have hsplit : ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V s
      = (∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s)
        + ∫ s in Set.Ioi (A / T), Real.exp (-T * s) * V s := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hAT.le)),
      Set.Ioc_union_Ioi_eq_Ioi hAT.le]
  have hpart1 : ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s ≤ V (A / T) / T := by
    have h1 : ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V s
        ≤ ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V (A / T) := by
      refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self)
        (((integrableOn_exp_neg_mul hT 0).mono_set Set.Ioc_subset_Ioi_self).mul_const _)
        measurableSet_Ioc ?_
      intro s hs
      exact mul_le_mul_of_nonneg_left (hV hs.2) (Real.exp_pos _).le
    have h2 : ∫ s in Set.Ioc (0:ℝ) (A / T), Real.exp (-T * s) * V (A / T)
        ≤ ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V (A / T) := by
      refine setIntegral_mono_set ((integrableOn_exp_neg_mul hT 0).mul_const _)
        (Filter.Eventually.of_forall fun s =>
          mul_nonneg (Real.exp_pos _).le (hVnn _ hAT)) Set.Ioc_subset_Ioi_self.eventuallyLE
    have h3 : ∫ s in Set.Ioi (0:ℝ), Real.exp (-T * s) * V (A / T) = V (A / T) / T := by
      rw [MeasureTheory.integral_mul_const, integral_exp_neg_mul_Ioi hT]
      simp
      ring
    linarith
  have hpart2 : ∫ s in Set.Ioi (A / T), Real.exp (-T * s) * V s
      ≤ C * gammaTail A lam * T ^ (-lam) / T := by
    have h1 : ∫ s in Set.Ioi (A / T), Real.exp (-T * s) * V s
        ≤ ∫ s in Set.Ioi (A / T), C * (Real.exp (-T * s) * s ^ lam) := by
      refine setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi hAT.le))
        (((integrableOn_exp_neg_mul_rpow hT hlam').mono_set
          (Set.Ioi_subset_Ioi hAT.le)).const_mul C) measurableSet_Ioi ?_
      intro s hs
      have hs0 : (0:ℝ) < s := hAT.trans hs
      have h := mul_le_mul_of_nonneg_left (hbound s hs0) (Real.exp_pos (-T * s)).le
      linarith [h]
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_rpow_Ioi hT hA] at h1
    refine h1.trans (le_of_eq ?_)
    field_simp
  rw [laplaceAverage, hsplit]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hpart1 hpart2) hT.le
  refine hsum.trans (le_of_eq ?_)
  field_simp

/-! ## (c) The two-sided corollaries -/

/-- The Gamma tail is nonnegative on `A ≥ 0`. -/
public theorem gammaTail_nonneg {A lam : ℝ} (hA : 0 ≤ A) : 0 ≤ gammaTail A lam := by
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro u hu
  have hu0 : (0:ℝ) < u := lt_of_le_of_lt hA hu
  positivity

/-- The Gamma tail vanishes as the split point recedes. This single limit is the whole
bootstrap in the converse direction, and it is `MeasureTheory.tendsto_integral_Ioi_zero` — which
needs no integrability hypothesis, since a non-integrable integrand makes every tail `0` by
convention. No hypothesis on `lam` is required. -/
public theorem tendsto_gammaTail_atTop (lam : ℝ) :
    Filter.Tendsto (fun A => gammaTail A lam) Filter.atTop (nhds 0) :=
  MeasureTheory.tendsto_integral_Ioi_zero
    (f := fun u : ℝ => Real.exp (-u) * u ^ lam) Filter.tendsto_id

/-- `(1/T)^lam = T^{-lam}` for `T > 0`: the rpow bookkeeping shared by both corollaries. -/
public theorem rpow_neg_one_div {T lam : ℝ} (hT : 0 < T) : (1 / T) ^ lam = T ^ (-lam) := by
  rw [Real.rpow_neg hT.le, one_div, Real.inv_rpow hT.le]

/-- **(c), forward.** Two-sided power behaviour of the volume transfers to two-sided
`T^{-lam}` behaviour of the Laplace average.

From `c₁ ε^lam ≤ V ε` on `(0, ε₀]` and the global power upper bound `V s ≤ c₂ s^lam`:

    e^{-1} · c₁ · T^{-lam} ≤ laplaceAverage V T ≤ c₂ · (1 + gammaTail 1 lam) · T^{-lam}

for every `T ≥ 1/ε₀`. Both constants are explicit and neither involves a limit: the split point
of (b) is fixed at `A = 1`.

The lower bound needs only the lower power bound near `0`; the upper bound needs the power bound
at *every* `s > 0`, because a monotone `V` is unconstrained at large `s` and could otherwise
destroy the transform. -/
public theorem laplace_comparable_of_volume_comparable {V : ℝ → ℝ} {lam c₁ c₂ ε₀ T : ℝ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hlower : ∀ ε ∈ Set.Ioc (0:ℝ) ε₀, c₁ * ε ^ lam ≤ V ε)
    (hupper : ∀ s > 0, V s ≤ c₂ * s ^ lam)
    (hT : 0 < T) (hTε : 1 / ε₀ ≤ T) :
    Real.exp (-1) * c₁ * T ^ (-lam) ≤ laplaceAverage V T ∧
      laplaceAverage V T ≤ c₂ * (1 + gammaTail 1 lam) * T ^ (-lam) := by
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have h1T : 1 / T ≤ ε₀ := by
    rw [div_le_iff₀ hT]
    have hmul := mul_le_mul_of_nonneg_left hTε hε₀.le
    rw [mul_one_div_cancel hε₀.ne'] at hmul
    linarith
  have hpow : (1 / T) ^ lam = T ^ (-lam) := rpow_neg_one_div hT
  have hint := integrableOn_of_power_bound hV hVnn (by linarith : (-1:ℝ) < lam) hupper hT
  constructor
  · have ha := volume_le_laplace hV hVnn hint hT
    have hlo := hlower (1 / T) ⟨hTinv, h1T⟩
    rw [hpow] at hlo
    have := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (-1)).le
    calc Real.exp (-1) * c₁ * T ^ (-lam) = Real.exp (-1) * (c₁ * T ^ (-lam)) := by ring
      _ ≤ Real.exp (-1) * V (1 / T) := this
      _ ≤ laplaceAverage V T := ha
  · have hb := laplace_le_of_power_bound hV hVnn hlam hupper hT (A := 1) one_pos
    have hup := hupper (1 / T) hTinv
    rw [hpow] at hup
    calc laplaceAverage V T ≤ V (1 / T) + c₂ * gammaTail 1 lam * T ^ (-lam) := hb
      _ ≤ c₂ * T ^ (-lam) + c₂ * gammaTail 1 lam * T ^ (-lam) := by linarith
      _ = c₂ * (1 + gammaTail 1 lam) * T ^ (-lam) := by ring

/-- **(c), converse, upper half.** A `T^{-lam}` upper bound on the Laplace average forces a
`ε^lam` upper bound on the volume, with constant `e·K₂`.

This is just (a) read backwards at `T = 1/ε`; it needs no bootstrap. The power bound `hbound`
enters only to make the integrand integrable, so that (a) applies. -/
public theorem volume_le_of_laplace_le {V : ℝ → ℝ} {lam C K₂ T₀ ε : ℝ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hbound : ∀ s > 0, V s ≤ C * s ^ lam) (hT₀ : 0 < T₀)
    (hlap : ∀ T ≥ T₀, laplaceAverage V T ≤ K₂ * T ^ (-lam))
    (hε : 0 < ε) (hεle : ε ≤ 1 / T₀) :
    V ε ≤ Real.exp 1 * K₂ * ε ^ lam := by
  have hTpos : (0:ℝ) < 1 / ε := by positivity
  have hTge : 1 / ε ≥ T₀ := by
    rw [ge_iff_le, le_div_iff₀ hε]
    rw [le_div_iff₀ hT₀] at hεle
    linarith
  have hinvinv : 1 / (1 / ε) = ε := one_div_one_div ε
  have hint := integrableOn_of_power_bound hV hVnn (by linarith : (-1:ℝ) < lam) hbound hTpos
  have ha := volume_le_laplace hV hVnn hint hTpos
  rw [hinvinv] at ha
  have hpow : (1 / ε) ^ (-lam) = ε ^ lam := by
    rw [← rpow_neg_one_div hTpos, hinvinv]
  have hchain : Real.exp (-1) * V ε ≤ K₂ * ε ^ lam := by
    have := ha.trans (hlap (1 / ε) hTge)
    rwa [hpow] at this
  have hexp : Real.exp 1 * (Real.exp (-1) * V ε) = V ε := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  calc V ε = Real.exp 1 * (Real.exp (-1) * V ε) := hexp.symm
    _ ≤ Real.exp 1 * (K₂ * ε ^ lam) := mul_le_mul_of_nonneg_left hchain (Real.exp_pos 1).le
    _ = Real.exp 1 * K₂ * ε ^ lam := by ring

/-- **(c), converse, lower half — the bootstrap.** A `T^{-lam}` *lower* bound on the Laplace
average forces a `ε^lam` lower bound on the volume near `0`.

This is the one place where the split point `A` of (b) must be chosen rather than fixed: push `A`
out until `C · gammaTail A lam ≤ K₁/2`, which `tendsto_gammaTail_atTop` permits, and then (b) at
that `A` and `T = A/ε` leaves at least half of the Laplace lower bound for `V (A/T) = V ε`. The
resulting constant `K₁ / (2 A^lam)` depends on how far `A` had to be pushed, i.e. on `C`, and is
therefore not explicit — the elementary route recovers the exponent, not the constant.

`0 ≤ C` is again not needed: the tail estimate is applied as a product with a positive
factor. -/
public theorem exists_volume_ge_of_laplace_ge {V : ℝ → ℝ} {lam C K₁ T₀ : ℝ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hbound : ∀ s > 0, V s ≤ C * s ^ lam) (hK₁ : 0 < K₁) (hT₀ : 0 < T₀)
    (hlap : ∀ T ≥ T₀, K₁ * T ^ (-lam) ≤ laplaceAverage V T) :
    ∃ c > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0:ℝ) ε₀, c * ε ^ lam ≤ V ε := by
  -- Choose a split point `A ≥ 1` so far out that the Gamma tail is below `K₁ / 2`.
  have htend : Filter.Tendsto (fun A => C * gammaTail A lam) Filter.atTop (nhds 0) := by
    simpa using (tendsto_gammaTail_atTop lam).const_mul C
  obtain ⟨A, hAtail, hA1⟩ :=
    ((htend.eventually_lt_const (by linarith : (0:ℝ) < K₁ / 2)).and
      (Filter.eventually_ge_atTop (1:ℝ))).exists
  have hA : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hAlam : (0:ℝ) < A ^ lam := Real.rpow_pos_of_pos hA lam
  refine ⟨K₁ / (2 * A ^ lam), by positivity, A / T₀, by positivity, ?_⟩
  rintro ε ⟨hε, hεle⟩
  have hTpos : (0:ℝ) < A / ε := div_pos hA hε
  have hTge : A / ε ≥ T₀ := by
    rw [ge_iff_le, le_div_iff₀ hε]
    rw [le_div_iff₀ hT₀] at hεle
    linarith
  have hATε : A / (A / ε) = ε := by field_simp
  have hb := laplace_le_of_power_bound hV hVnn hlam hbound hTpos hA
  rw [hATε] at hb
  have hmain := (hlap (A / ε) hTge).trans hb
  have hpow : (A / ε) ^ (-lam) = ε ^ lam / A ^ lam := by
    rw [Real.rpow_neg hTpos.le, Real.div_rpow hA.le hε.le]
    field_simp
  rw [hpow] at hmain
  have htailpos : 0 ≤ gammaTail A lam := gammaTail_nonneg hA.le
  have hεlam : (0:ℝ) < ε ^ lam := Real.rpow_pos_of_pos hε lam
  have hfrac : (0:ℝ) < ε ^ lam / A ^ lam := by positivity
  have hstep : K₁ * (ε ^ lam / A ^ lam) - C * gammaTail A lam * (ε ^ lam / A ^ lam) ≤ V ε := by
    linarith
  have hhalf : C * gammaTail A lam ≤ K₁ / 2 := hAtail.le
  have hkey : K₁ / 2 * (ε ^ lam / A ^ lam) ≤ V ε := by
    nlinarith [mul_le_mul_of_nonneg_right hhalf hfrac.le]
  calc K₁ / (2 * A ^ lam) * ε ^ lam = K₁ / 2 * (ε ^ lam / A ^ lam) := by field_simp
    _ ≤ V ε := hkey

/-- **(c), converse, packaged.** Two-sided `T^{-lam}` behaviour of the Laplace average, plus the
power upper bound on `V`, gives two-sided `ε^lam` behaviour of the volume near `0`.

The lower constant is inexplicit (see `exists_volume_ge_of_laplace_ge`); the upper constant is
`e·K₂`. Together with `laplace_comparable_of_volume_comparable` this closes the transfer in both
directions at the level of order of magnitude.

**Not concluded:** nothing about the multiplicity `m` of `eq:volume`. A logarithmic factor
`(log 1/ε)^{m-1}` is invisible to a pure power comparison, and no claim about it may be read out
of this theorem. -/
public theorem volume_comparable_of_laplace_comparable {V : ℝ → ℝ} {lam C K₁ K₂ T₀ : ℝ}
    (hV : Monotone V) (hVnn : ∀ s > 0, 0 ≤ V s) (hlam : 0 < lam)
    (hbound : ∀ s > 0, V s ≤ C * s ^ lam) (hK₁ : 0 < K₁) (hT₀ : 0 < T₀)
    (hlo : ∀ T ≥ T₀, K₁ * T ^ (-lam) ≤ laplaceAverage V T)
    (hup : ∀ T ≥ T₀, laplaceAverage V T ≤ K₂ * T ^ (-lam)) :
    ∃ c₁ > 0, ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc (0:ℝ) ε₀,
      c₁ * ε ^ lam ≤ V ε ∧ V ε ≤ Real.exp 1 * K₂ * ε ^ lam := by
  obtain ⟨c, hc, δ, hδ, hlow⟩ := exists_volume_ge_of_laplace_ge hV hVnn hlam hbound hK₁ hT₀ hlo
  refine ⟨c, hc, min δ (1 / T₀), lt_min hδ (by positivity), ?_⟩
  rintro ε ⟨hε, hεle⟩
  exact ⟨hlow ε ⟨hε, hεle.trans (min_le_left _ _)⟩,
    volume_le_of_laplace_le hV hVnn hlam hbound hT₀ hup hε (hεle.trans (min_le_right _ _))⟩

/-! ## Worked sanity checks -/

/-- The zero germ has zero Laplace average: the bridge is not vacuously true by
`laplaceAverage` being ill-formed. -/
example (T : ℝ) : laplaceAverage (fun _ => (0:ℝ)) T = 0 := by
  simp [laplaceAverage]

/-- Both directions are applied to the same object: for the constant-`0` germ the
lower bound of `volume_le_laplace` is `0`, which the average meets. -/
example {T : ℝ} (hT : 0 < T) :
    Real.exp (-1) * (fun _ => (0:ℝ)) (1 / T) ≤ laplaceAverage (fun _ => (0:ℝ)) T :=
  volume_le_laplace (monotone_const) (fun _ _ => le_refl 0)
    (by simp) hT

end AISafetyAtlas.SingularLearning
