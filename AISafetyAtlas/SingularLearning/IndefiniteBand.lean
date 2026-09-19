module

public import AISafetyAtlas.SingularLearning.QuadraticSplit
public import AISafetyAtlas.SingularLearning.DyadicLocalization
public import AISafetyAtlas.SingularLearning.ResidualGerm
public import AISafetyAtlas.SingularLearning.CoordTransfer
public import AISafetyAtlas.SingularLearning.DiffeoTransfer

/-!
# The Gaussian-Laplace transform of the model band germ

`hasLocalVolumeOrder_of_gaussianLaplace` reduces a local pair to two-sided
bounds on

    `∫ exp (-T · f x) · exp (-‖x‖²) dx`,

so the whole of Stage 3 rests on estimating that integral for
`f = modelBandGerm p q`.  This module performs the reduction of that integral to
a two-dimensional one, and does not yet estimate it.

The reduction is three unconditional moves and one integrability obligation:

* transport through `splitLE`, which is measure preserving, turning the integral
  over `EuclideanSpace ℝ (Fin (p + q))` into one over the product;
* Fubini, which is the only step needing integrability — supplied by
  `integrable_exp_neg_sq_norm_mul`, since `exp (-T · germ) ≤ 1`;
* the radial formula in each factor.  `integral_fun_norm_addHaar` carries no
  integrability hypothesis, so `radial_two` is unconditional and can be reused
  by any germ that depends on the two block norms alone.

After the reduction the remaining object is

    `∫₀^∞ ∫₀^∞ r^(p-1) s^(q-1) exp (-T |r² - s²|) exp (-(r² + s²)) ds dr`,

whose behaviour is `Θ(1/T)` when `p + q ≥ 3` and `Θ(log T / T)` when
`p = q = 1`.  That dichotomy is the reason the printed statement carries a
dimension hypothesis, and it is why the two-dimensional case is a genuine
boundary rather than a convenience.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

/-- **The two-factor radial reduction.**  An integrand depending only on the two
block norms collapses to a double integral over the radii.  Both applications of
the radial formula are unconditional, so this identity needs no integrability
hypothesis of its own; the Fubini step that precedes it does. -/
public theorem radial_two (p q : ℕ) [NeZero p] [NeZero q] (G : ℝ → ℝ → ℝ) :
    (∫ u : EuclideanSpace ℝ (Fin p), ∫ v : EuclideanSpace ℝ (Fin q), G ‖u‖ ‖v‖)
      = (p : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) *
          ∫ r in Ioi (0:ℝ), r ^ (p - 1) *
            ((q : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1) *
              ∫ s in Ioi (0:ℝ), s ^ (q - 1) * G r s))) := by
  have inner : ∀ u : EuclideanSpace ℝ (Fin p),
      (∫ v : EuclideanSpace ℝ (Fin q), G ‖u‖ ‖v‖)
        = (q : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1) *
            ∫ s in Ioi (0:ℝ), s ^ (q - 1) * G ‖u‖ s) := by
    intro u
    simpa using MeasureTheory.integral_fun_norm_addHaar
      (volume : Measure (EuclideanSpace ℝ (Fin q))) (fun t => G ‖u‖ t)
  simp_rw [inner]
  simpa using MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin p)))
    (fun r => (q : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1) *
      ∫ s in Ioi (0:ℝ), s ^ (q - 1) * G r s))

/-- The Gaussian-weighted Laplace transform of the model band germ: the object
`hasLocalVolumeOrder_of_gaussianLaplace` asks about. -/
@[expose] public noncomputable def bandLaplace (p q : ℕ) (T : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin (p + q)),
    Real.exp (-‖x‖ ^ 2) * Real.exp (-T * modelBandGerm p q x)

/-- The integrand is integrable, because the Gaussian is and the Laplace factor
is bounded by one whenever `T` is nonnegative. -/
public theorem integrable_bandLaplace (p q : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun x : EuclideanSpace ℝ (Fin (p + q)) =>
      Real.exp (-‖x‖ ^ 2) * Real.exp (-T * modelBandGerm p q x)) volume := by
  refine integrable_exp_neg_sq_norm_mul (D := p + q)
    ((measurable_modelBandGerm p q).const_mul (-T)).exp (fun _ => (Real.exp_pos _).le)
    (fun x => ?_)
  refine Real.exp_le_one_iff.mpr ?_
  have := modelBandGerm_nonneg p q x
  nlinarith [this, hT]

/-- The transported integrand on the product, written in the two block norms.
The transport itself needs no sign condition on `T`; integrability does, and is
separate. -/
public theorem bandLaplace_eq_prod (p q : ℕ) (T : ℝ) :
    bandLaplace p q T
      = ∫ z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q),
          Real.exp (-(‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) *
            Real.exp (-T * |‖z.1‖ ^ 2 - ‖z.2‖ ^ 2|) := by
  have hemb : MeasurableEmbedding (splitLE p q) := by
    rw [coe_splitLE]; exact (euclideanProdEquiv p q).measurableEmbedding
  have h := (measurePreserving_splitLE p q).integral_comp hemb
    (fun x : EuclideanSpace ℝ (Fin (p + q)) =>
      Real.exp (-‖x‖ ^ 2) * Real.exp (-T * modelBandGerm p q x))
  rw [bandLaplace, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  obtain ⟨u, v⟩ := z
  simp only
  rw [norm_sq_splitLE, modelBandGerm_splitLE]

/-- **The reduction.**  The Gaussian-Laplace transform of the model band germ is
a two-dimensional integral over the two block radii, with the constants the
radial formula supplies.  Everything after this point is one-variable analysis;
nothing further refers to the ambient Euclidean space. -/
public theorem bandLaplace_eq_radial (p q : ℕ) [NeZero p] [NeZero q] {T : ℝ} (hT : 0 ≤ T) :
    bandLaplace p q T
      = (p : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) *
          ∫ r in Ioi (0:ℝ), r ^ (p - 1) *
            ((q : ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1) *
              ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
                (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))))) := by
  have hemb : MeasurableEmbedding (splitLE p q) := by
    rw [coe_splitLE]; exact (euclideanProdEquiv p q).measurableEmbedding
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) =>
      Real.exp (-(‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) * Real.exp (-T * |‖z.1‖ ^ 2 - ‖z.2‖ ^ 2|)) volume := by
    have h := ((measurePreserving_splitLE p q).integrable_comp_emb hemb
      (g := fun x : EuclideanSpace ℝ (Fin (p + q)) =>
        Real.exp (-‖x‖ ^ 2) * Real.exp (-T * modelBandGerm p q x))).2
        (integrable_bandLaplace p q hT)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    obtain ⟨u, v⟩ := z
    simp only [Function.comp_apply]
    rw [norm_sq_splitLE, modelBandGerm_splitLE]
  rw [bandLaplace_eq_prod]
  exact (integral_prod _ hint).trans
    (radial_two p q (fun r s => Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))

/-! ## The one-variable estimates

Both bounds are elementary once one inequality is in hand: for positive `r` and
`s`,

    `|r² - s²| = |r - s| (r + s) ≥ r |r - s|`,

so the Laplace factor is at least as sharp as a one-sided exponential of width
`1 / (T r)` around `s = r`.  The upper bound is that width times a bounded
weight; the lower bound is the same width from below, on a box where every
factor is bounded away from zero.
-/

/-- A polynomial weight against a Gaussian is bounded, with an explicit
constant.  Used to pull `s^(q-1) exp(-s²)` out of the inner integral. -/
public theorem pow_mul_exp_neg_sq_le (m : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    s ^ m * Real.exp (-s ^ 2) ≤ max (1:ℝ) (Nat.factorial m : ℝ) := by
  rcases le_total s 1 with h | h
  · have h1 : s ^ m ≤ 1 := pow_le_one₀ hs h
    have h2 : Real.exp (-s ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc s ^ m * Real.exp (-s ^ 2) ≤ 1 * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
      _ ≤ max (1:ℝ) (Nat.factorial m : ℝ) := le_max_left _ _
  · have hkey : (s ^ 2) ^ m / (Nat.factorial m) ≤ Real.exp (s ^ 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) m
    have hexp : Real.exp (-s ^ 2) = (Real.exp (s ^ 2))⁻¹ := by rw [← Real.exp_neg]
    have hpos : (0:ℝ) < Real.exp (s ^ 2) := Real.exp_pos _
    have hmono : s ^ m ≤ (s ^ 2) ^ m := by
      rw [← pow_mul]; exact pow_le_pow_right₀ h (by omega)
    have hfac : (0:ℝ) < (Nat.factorial m : ℝ) := by positivity
    have hb : (s ^ 2) ^ m * Real.exp (-s ^ 2) ≤ (Nat.factorial m : ℝ) := by
      rw [hexp, mul_inv_le_iff₀ hpos]
      calc (s ^ 2) ^ m = ((s ^ 2) ^ m / (Nat.factorial m : ℝ)) * (Nat.factorial m : ℝ) := by
            field_simp
        _ ≤ Real.exp (s ^ 2) * (Nat.factorial m : ℝ) :=
            mul_le_mul_of_nonneg_right hkey hfac.le
        _ = (Nat.factorial m : ℝ) * Real.exp (s ^ 2) := by ring
    calc s ^ m * Real.exp (-s ^ 2) ≤ (s ^ 2) ^ m * Real.exp (-s ^ 2) :=
          mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
      _ ≤ (Nat.factorial m : ℝ) := hb
      _ ≤ max (1:ℝ) (Nat.factorial m : ℝ) := le_max_right _ _

/-- **The inequality the whole estimate turns on.**  The indefinite form is at
least `r` times the distance from `s` to `r`, so the band around the null cone
has width `O(1 / (T r))` in the second radius. -/
public theorem abs_sq_sub_sq_ge {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    r * |r - s| ≤ |r ^ 2 - s ^ 2| := by
  have hfac : r ^ 2 - s ^ 2 = (r - s) * (r + s) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ r + s)]
  nlinarith [abs_nonneg (r - s)]

/-- The half-line to the right of the peak contributes exactly `1 / c`. -/
public theorem integral_exp_neg_right {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∫ s in Ioi r, Real.exp (-(c * (s - r))) = 1 / c := by
  have hrw : ∀ s : ℝ, Real.exp (-(c * (s - r))) = Real.exp (c * r) * Real.exp (-c * s) := by
    intro s; rw [← Real.exp_add]; ring_nf
  simp_rw [hrw]
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hc r]
  rw [eq_div_iff (ne_of_gt hc)]
  field_simp
  rw [← Real.exp_add]
  ring_nf
  simp

/-- The segment to the left of the peak contributes at most `1 / c`. -/
public theorem integral_exp_neg_left {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioc (0:ℝ) r, Real.exp (-(c * (r - s))) ≤ 1 / c := by
  have h1 : ∫ s in Ioc (0:ℝ) r, Real.exp (-(c * (r - s)))
      = ∫ s in (0:ℝ)..r, Real.exp (-(c * (r - s))) := by
    rw [intervalIntegral.integral_of_le hr]
  have h2 : ∫ s in (0:ℝ)..r, Real.exp (-(c * (r - s)))
      = ∫ u in (0:ℝ)..r, Real.exp (-(c * u)) := by
    simpa using intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := r)
      (fun u => Real.exp (-(c * u))) r
  have h3 : ∫ u in (0:ℝ)..r, Real.exp (-(c * u)) = (1 - Real.exp (-(c * r))) / c := by
    simp [intervalIntegral.integral_comp_mul_left (fun x => Real.exp (-x)) (ne_of_gt hc)]
    ring_nf
  rw [h1, h2, h3, div_le_div_iff_of_pos_right hc]
  linarith [Real.exp_pos (-(c * r))]

/-- **The width bound.**  A one-sided exponential peak of rate `c` has total mass
at most `2 / c` on the positive half-line, wherever the peak sits.  This is the
whole content of "the band has width `O(1 / (T r))`". -/
public theorem exp_abs_width {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioi (0:ℝ), Real.exp (-(c * |r - s|)) ≤ 2 / c := by
  have hLint : IntegrableOn (fun s : ℝ => Real.exp (-(c * |r - s|))) (Ioc 0 r) volume := by
    refine (Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_)
    · exact (measure_Ioc_lt_top).ne
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · filter_upwards with s
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ c * |r - s| := by positivity
      linarith
  have hRint : IntegrableOn (fun s : ℝ => Real.exp (-(c * |r - s|))) (Ioi r) volume := by
    have hb : IntegrableOn (fun s : ℝ => Real.exp (c * r) * Real.exp (-c * s)) (Ioi r) volume :=
      (exp_neg_integrableOn_Ioi r hc).const_mul _
    refine hb.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only
    rw [← Real.exp_add, abs_of_nonpos (by simp only [Set.mem_Ioi] at hs; linarith)]
    ring_nf
  have hunion : ∫ s in Ioi (0:ℝ), Real.exp (-(c * |r - s|))
      = (∫ s in Ioc (0:ℝ) r, Real.exp (-(c * |r - s|)))
        + ∫ s in Ioi r, Real.exp (-(c * |r - s|)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hr,
      MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hLint hRint]
  have hL : ∫ s in Ioc (0:ℝ) r, Real.exp (-(c * |r - s|)) ≤ 1 / c := by
    refine le_trans (le_of_eq ?_) (integral_exp_neg_left hc hr)
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    rw [abs_of_nonneg (by simp only [Set.mem_Ioc] at hs; linarith [hs.2])]
  have hR : ∫ s in Ioi r, Real.exp (-(c * |r - s|)) = 1 / c := by
    refine Eq.trans ?_ (integral_exp_neg_right hc r)
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [abs_of_nonpos (by simp only [Set.mem_Ioi] at hs; linarith)]
    ring_nf
  have htwo : (2:ℝ) / c = 1 / c + 1 / c := by ring
  rw [hunion, hR, htwo]
  linarith [hL]

/-- The peak is integrable on the positive half-line.  Split out because the
inner estimate needs it as a dominating function, not only as a bound. -/
public theorem integrableOn_exp_abs {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℝ => Real.exp (-(c * |r - s|))) (Ioi 0) volume := by
  have hLint : IntegrableOn (fun s : ℝ => Real.exp (-(c * |r - s|))) (Ioc 0 r) volume := by
    refine (Measure.integrableOn_of_bounded (M := 1) (measure_Ioc_lt_top).ne
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_)
    filter_upwards with s
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ c * |r - s| := by positivity
    linarith
  have hRint : IntegrableOn (fun s : ℝ => Real.exp (-(c * |r - s|))) (Ioi r) volume := by
    have hb : IntegrableOn (fun s : ℝ => Real.exp (c * r) * Real.exp (-c * s)) (Ioi r) volume :=
      (exp_neg_integrableOn_Ioi r hc).const_mul _
    refine hb.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only
    rw [← Real.exp_add, abs_of_nonpos (by simp only [Set.mem_Ioi] at hs; linarith)]
    ring_nf
  rw [← Set.Ioc_union_Ioi_eq_Ioi hr]
  exact hLint.union hRint

/-- The inner integrand is integrable on the positive half-line.  Needed twice:
by the upper estimate as the left-hand side of a comparison, and by the lower
estimate, which shrinks the domain and so must know the integral is finite. -/
public theorem integrableOn_innerBand (q : ℕ) {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => s ^ (q - 1) *
      (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) (Ioi 0) volume := by
  set M : ℝ := max (1:ℝ) (Nat.factorial (q - 1) : ℝ) with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < T * r := mul_pos hT hr
  have hdom : IntegrableOn
      (fun s : ℝ => (M * Real.exp (-r ^ 2)) * Real.exp (-(T * r * |r - s|))) (Ioi 0) volume :=
    (integrableOn_exp_abs hc hr.le).const_mul _
  refine Integrable.mono' hdom ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : (0:ℝ) ≤ s := le_of_lt hs
  rw [Real.norm_of_nonneg (by positivity)]
  have hw : s ^ (q - 1) * Real.exp (-s ^ 2) ≤ M := pow_mul_exp_neg_sq_le (q - 1) hs0
  have hband : T * (r * |r - s|) ≤ T * |r ^ 2 - s ^ 2| :=
    mul_le_mul_of_nonneg_left (abs_sq_sub_sq_ge hr.le hs0) hT.le
  have hexp : Real.exp (-T * |r ^ 2 - s ^ 2|) ≤ Real.exp (-(T * r * |r - s|)) := by
    apply Real.exp_le_exp.mpr; nlinarith [hband]
  have hgauss : Real.exp (-(r ^ 2 + s ^ 2)) = Real.exp (-r ^ 2) * Real.exp (-s ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  calc s ^ (q - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))
      = (s ^ (q - 1) * Real.exp (-s ^ 2)) * Real.exp (-r ^ 2)
          * Real.exp (-T * |r ^ 2 - s ^ 2|) := by rw [hgauss]; ring
    _ ≤ M * Real.exp (-r ^ 2) * Real.exp (-(T * r * |r - s|)) := by
        have h3 : (0:ℝ) ≤ Real.exp (-T * |r ^ 2 - s ^ 2|) := (Real.exp_pos _).le
        have hstep : (s ^ (q - 1) * Real.exp (-s ^ 2)) * Real.exp (-r ^ 2)
            ≤ M * Real.exp (-r ^ 2) :=
          mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
        exact mul_le_mul hstep hexp h3 (by positivity)

/-- **The inner estimate.**  Integrating out the second radius costs the width of
the band, `2 / (T r)`, times a bounded weight — and keeps the Gaussian in `r`.
Discarding `exp (-r²)` here would be fatal: the outer integral would then be
`∫ r^(p-2) dr`, which diverges at infinity for every `p`.  This is where the
`|r² - s²| ≥ r |r - s|` inequality is spent. -/
public theorem inner_band_le (q : ℕ) {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    (∫ s in Ioi (0:ℝ),
        s ^ (q - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
      ≤ (max (1:ℝ) (Nat.factorial (q - 1) : ℝ) * Real.exp (-r ^ 2)) * (2 / (T * r)) := by
  set M : ℝ := max (1:ℝ) (Nat.factorial (q - 1) : ℝ) with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set K : ℝ := M * Real.exp (-r ^ 2) with hK
  have hKpos : 0 < K := by positivity
  have hc : 0 < T * r := mul_pos hT hr
  have hdom : IntegrableOn (fun s : ℝ => K * Real.exp (-(T * r * |r - s|))) (Ioi 0) volume :=
    (integrableOn_exp_abs hc hr.le).const_mul K
  have hle : ∀ s ∈ Ioi (0:ℝ),
      s ^ (q - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))
        ≤ K * Real.exp (-(T * r * |r - s|)) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hw : s ^ (q - 1) * Real.exp (-s ^ 2) ≤ M := pow_mul_exp_neg_sq_le (q - 1) hs0
    have hband : T * (r * |r - s|) ≤ T * |r ^ 2 - s ^ 2| :=
      mul_le_mul_of_nonneg_left (abs_sq_sub_sq_ge hr.le hs0) hT.le
    have hexp : Real.exp (-T * |r ^ 2 - s ^ 2|) ≤ Real.exp (-(T * r * |r - s|)) := by
      apply Real.exp_le_exp.mpr; nlinarith [hband]
    have hgauss : Real.exp (-(r ^ 2 + s ^ 2)) = Real.exp (-r ^ 2) * Real.exp (-s ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    calc s ^ (q - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))
        = (s ^ (q - 1) * Real.exp (-s ^ 2)) * Real.exp (-r ^ 2)
            * Real.exp (-T * |r ^ 2 - s ^ 2|) := by rw [hgauss]; ring
      _ ≤ M * Real.exp (-r ^ 2) * Real.exp (-(T * r * |r - s|)) := by
          have h3 : (0:ℝ) ≤ Real.exp (-T * |r ^ 2 - s ^ 2|) := (Real.exp_pos _).le
          have hstep : (s ^ (q - 1) * Real.exp (-s ^ 2)) * Real.exp (-r ^ 2)
              ≤ M * Real.exp (-r ^ 2) :=
            mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
          exact mul_le_mul hstep hexp h3 (by positivity)
      _ = K * Real.exp (-(T * r * |r - s|)) := by rw [hK]
  refine le_trans (MeasureTheory.setIntegral_mono_on ?_ hdom measurableSet_Ioi hle) ?_
  · refine Integrable.mono' hdom ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0:ℝ) ≤ s := le_of_lt hs
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle s hs
  · rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (exp_abs_width hc hr.le) hKpos.le

/-- A Gaussian moment is dominated by a plain exponential, with no case split:
`r^n ≤ n! exp r` from the exponential series, and `2r - r² - 1 = -(r-1)² ≤ 0`. -/
public theorem pow_mul_exp_neg_sq_le_exp_neg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ n * Real.exp (-r ^ 2) ≤ (Nat.factorial n : ℝ) * Real.exp 1 * Real.exp (-r) := by
  have hfac : (0:ℝ) < (Nat.factorial n : ℝ) := by positivity
  have hpow : r ^ n ≤ (Nat.factorial n : ℝ) * Real.exp r := by
    have := Real.pow_div_factorial_le_exp r hr n
    rw [div_le_iff₀ hfac] at this
    linarith [this]
  have hstep : Real.exp r * Real.exp (-r ^ 2) ≤ Real.exp 1 * Real.exp (-r) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (r - 1)])
  calc r ^ n * Real.exp (-r ^ 2)
      ≤ ((Nat.factorial n : ℝ) * Real.exp r) * Real.exp (-r ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (Nat.factorial n : ℝ) * (Real.exp r * Real.exp (-r ^ 2)) := by ring
    _ ≤ (Nat.factorial n : ℝ) * (Real.exp 1 * Real.exp (-r)) :=
        mul_le_mul_of_nonneg_left hstep hfac.le
    _ = (Nat.factorial n : ℝ) * Real.exp 1 * Real.exp (-r) := by ring

/-- The Gaussian moment is integrable on the positive half-line. -/
public theorem integrableOn_pow_mul_exp_neg_sq (n : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ n * Real.exp (-r ^ 2)) (Ioi 0) volume := by
  have hdom : IntegrableOn
      (fun r : ℝ => (Nat.factorial n : ℝ) * Real.exp 1 * Real.exp (-1 * r)) (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  refine Integrable.mono' hdom ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0:ℝ) ≤ r := le_of_lt hr
  rw [Real.norm_of_nonneg (by positivity)]
  have := pow_mul_exp_neg_sq_le_exp_neg n hr0
  simpa [neg_mul] using this

/-- **The outer estimate.**  Integrating the inner bound against the first
radius converts the width `2 / (T r)` into `2 / T` times a Gaussian moment.  The
single `r` in the denominator is what consumes one power of `r^(p-1)`, which is
why the hypothesis is `2 ≤ p`: at `p = 1` the moment would be `∫ r^(-1) exp(-r²)`
and diverges at the origin. -/
public theorem outer_band_le (p q : ℕ) (hp : 2 ≤ p) {T : ℝ} (hT : 0 < T) :
    (∫ r in Ioi (0:ℝ), r ^ (p - 1) *
        (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))))
      ≤ (2 * max (1:ℝ) (Nat.factorial (q - 1) : ℝ) / T) *
          ∫ r in Ioi (0:ℝ), r ^ (p - 2) * Real.exp (-r ^ 2) := by
  set M : ℝ := max (1:ℝ) (Nat.factorial (q - 1) : ℝ) with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdom : IntegrableOn
      (fun r : ℝ => 2 * M / T * (r ^ (p - 2) * Real.exp (-r ^ 2))) (Ioi 0) volume :=
    (integrableOn_pow_mul_exp_neg_sq (p - 2)).const_mul _
  have hle : ∀ r ∈ Ioi (0:ℝ),
      r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
        ≤ 2 * M / T * (r ^ (p - 2) * Real.exp (-r ^ 2)) := by
    intro r hr
    have hr0 : (0:ℝ) < r := hr
    have hsplit : p - 1 = (p - 2) + 1 := by omega
    have hpow : r ^ (p - 1) = r ^ (p - 2) * r := by rw [hsplit, pow_succ]
    calc r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
        ≤ r ^ (p - 1) * ((M * Real.exp (-r ^ 2)) * (2 / (T * r))) :=
          mul_le_mul_of_nonneg_left (inner_band_le q hT hr0) (by positivity)
      _ = 2 * M / T * (r ^ (p - 2) * Real.exp (-r ^ 2)) := by
          rw [hpow]; field_simp
  have hnonneg : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun r =>
      r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0:ℝ) ≤ r := le_of_lt hr
    refine mul_nonneg (by positivity) ?_
    refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  have hae : (fun r => r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))))
      ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun r => 2 * M / T * (r ^ (p - 2) * Real.exp (-r ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr using hle r hr
  refine le_trans (MeasureTheory.integral_mono_of_nonneg hnonneg hdom hae) ?_
  rw [MeasureTheory.integral_const_mul]

/-- The constant in the upper bound.  Explicit rather than existential, so that a
reader can see it depends on the two block dimensions and nothing else. -/
@[expose] public noncomputable def bandUpperConst (p q : ℕ) : ℝ :=
  (p : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) *
    ((q : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1)) *
    (2 * max (1:ℝ) (Nat.factorial (q - 1) : ℝ)) *
    (∫ r in Ioi (0:ℝ), r ^ (p - 2) * Real.exp (-r ^ 2))

/-- **The upper bound.**  `bandLaplace p q T ≤ C / T` once the first block has
dimension at least two.  Since `p + q ≥ 3` forces one of the two blocks to have
dimension at least two, and the germ is symmetric in the blocks, this covers
every signature outside the two-dimensional boundary. -/
public theorem bandLaplace_le (p q : ℕ) [NeZero p] [NeZero q] (hp : 2 ≤ p)
    {T : ℝ} (hT : 0 < T) :
    bandLaplace p q T ≤ bandUpperConst p q / T := by
  rw [bandLaplace_eq_radial p q hT.le]
  set Vp := (volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) with hVpdef
  set Vq := (volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1) with hVqdef
  have hVp : 0 ≤ Vp := measureReal_nonneg
  have hVq : 0 ≤ Vq := measureReal_nonneg
  have hcongr : (∫ r in Ioi (0:ℝ), r ^ (p - 1) *
        ((q : ℝ) * (Vq * ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))))
      = ((q : ℝ) * Vq) * ∫ r in Ioi (0:ℝ), r ^ (p - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    ring
  rw [hcongr]
  have hbound := outer_band_le p q hp hT
  have hqVq : 0 ≤ (q : ℝ) * Vq := by positivity
  have hstep : ((q : ℝ) * Vq) * (∫ r in Ioi (0:ℝ), r ^ (p - 1) *
        (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))))
      ≤ ((q : ℝ) * Vq) * ((2 * max (1:ℝ) (Nat.factorial (q - 1) : ℝ) / T) *
          ∫ r in Ioi (0:ℝ), r ^ (p - 2) * Real.exp (-r ^ 2)) :=
    mul_le_mul_of_nonneg_left hbound hqVq
  have hpVp : 0 ≤ (p : ℝ) * Vp := by positivity
  have := mul_le_mul_of_nonneg_left hstep hVp
  have h2 := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ (p:ℝ))
  refine h2.trans_eq ?_
  rw [bandUpperConst, ← hVpdef, ← hVqdef]
  field_simp

/-! ## The lower bound

The band is thin in one direction only, which is why the region witnessing the
lower bound cannot be a product: the first radius ranges over a fixed interval
while the second is pinned to within `1 / (4T)` of it.  On that region every
factor is bounded below by an absolute constant, and the `1/T` in the answer is
the width of the region rather than anything about the integrand.
-/

/-- **The inner lower bound.**  For a first radius in `[1,2]`, the inner integral
is at least a fixed constant times the band width. -/
public theorem innerBand_ge (q : ℕ) {T r : ℝ} (hT : 3 ≤ T) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    Real.exp (-15) * (1 / (4 * T))
      ≤ ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hr0 : (0:ℝ) < r := by linarith
  set δ : ℝ := 1 / (4 * T) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδsmall : δ ≤ 1 / 12 := by
    rw [hδdef]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hsub : Ioo r (r + δ) ⊆ Ioi (0:ℝ) := fun s hs => lt_trans hr0 hs.1
  -- On the small interval every factor is bounded below.
  have hpt : ∀ s ∈ Ioo r (r + δ), Real.exp (-15)
      ≤ s ^ (q - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs0 : (1:ℝ) ≤ s := le_of_lt (lt_of_le_of_lt hr1 hs1)
    have hs3 : s ≤ 3 := by linarith [hδsmall]
    have hpow : (1:ℝ) ≤ s ^ (q - 1) := one_le_pow₀ hs0
    have hgauss : Real.exp (-13) ≤ Real.exp (-(r ^ 2 + s ^ 2)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have hdiff : |r ^ 2 - s ^ 2| ≤ 5 * δ := by
      rw [abs_le]
      refine ⟨?_, ?_⟩ <;> nlinarith [hδ0.le]
    have hband : Real.exp (-2) ≤ Real.exp (-T * |r ^ 2 - s ^ 2|) := by
      apply Real.exp_le_exp.mpr
      have h5 : T * |r ^ 2 - s ^ 2| ≤ T * (5 * δ) :=
        mul_le_mul_of_nonneg_left hdiff hT0.le
      have hTδ : T * (5 * δ) = 5 / 4 := by rw [hδdef]; field_simp
      nlinarith [h5, hTδ]
    calc Real.exp (-15) = 1 * (Real.exp (-13) * Real.exp (-2)) := by
          rw [← Real.exp_add]; norm_num
      _ ≤ s ^ (q - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
          have h1 : (0:ℝ) ≤ Real.exp (-13) * Real.exp (-2) := by positivity
          exact mul_le_mul hpow (mul_le_mul hgauss hband (Real.exp_pos _).le
            (Real.exp_pos _).le) h1 (by positivity)
  -- The constant integrates to the width.
  have hconst : ∫ _s in Ioo r (r + δ), Real.exp (-15) = Real.exp (-15) * δ := by
    rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ r + δ - r)]
    simp [mul_comm]
  have hstep1 : Real.exp (-15) * δ
      ≤ ∫ s in Ioo r (r + δ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    rw [← hconst]
    refine MeasureTheory.setIntegral_mono_on
      (integrableOn_const (by simp [Real.volume_Ioo]))
      ((integrableOn_innerBand q hT0 hr0).mono_set hsub) measurableSet_Ioo hpt
  have hstep2 : (∫ s in Ioo r (r + δ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
      ≤ ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    refine MeasureTheory.setIntegral_mono_set (integrableOn_innerBand q hT0 hr0) ?_
      (LE.le.eventuallyLE hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  calc Real.exp (-15) * (1 / (4 * T)) = Real.exp (-15) * δ := by rw [hδdef]
    _ ≤ _ := hstep1
    _ ≤ _ := hstep2

/-- The outer integrand is integrable.  Its measurability is the one place a
parametric integral has to be handled: `fun_prop` cannot see through
`∫ s in Ioi 0, …`, and the lemma that can is
`StronglyMeasurable.integral_prod_right'` applied to the restricted measure. -/
public theorem integrableOn_outerBand (p q : ℕ) (hp : 2 ≤ p) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun r : ℝ => r ^ (p - 1) *
      (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))) (Ioi 0) volume := by
  set M : ℝ := max (1:ℝ) (Nat.factorial (q - 1) : ℝ) with hM
  have hsm : StronglyMeasurable (fun r : ℝ =>
      ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    have hjoint : StronglyMeasurable (fun z : ℝ × ℝ => z.2 ^ (q - 1) *
        (Real.exp (-(z.1 ^ 2 + z.2 ^ 2)) * Real.exp (-T * |z.1 ^ 2 - z.2 ^ 2|))) := by
      fun_prop
    exact hjoint.integral_prod_right' (ν := volume.restrict (Ioi (0:ℝ)))
  have hdom : IntegrableOn
      (fun r : ℝ => 2 * M / T * (r ^ (p - 2) * Real.exp (-r ^ 2))) (Ioi 0) volume :=
    (integrableOn_pow_mul_exp_neg_sq (p - 2)).const_mul _
  refine Integrable.mono' hdom
    (((stronglyMeasurable_id.pow (p - 1)).mul hsm).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0:ℝ) < r := hr
  have hnn : (0:ℝ) ≤ r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
      (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    refine mul_nonneg (by positivity) ?_
    refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  rw [Real.norm_of_nonneg hnn]
  have hsplit : p - 1 = (p - 2) + 1 := by omega
  have hpow : r ^ (p - 1) = r ^ (p - 2) * r := by rw [hsplit, pow_succ]
  calc r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
      ≤ r ^ (p - 1) * ((M * Real.exp (-r ^ 2)) * (2 / (T * r))) :=
        mul_le_mul_of_nonneg_left (inner_band_le q hT hr0) (by positivity)
    _ = 2 * M / T * (r ^ (p - 2) * Real.exp (-r ^ 2)) := by
        rw [hpow]; field_simp

/-- The constant in the lower bound. -/
@[expose] public noncomputable def bandLowerConst (p q : ℕ) : ℝ :=
  (p : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) *
    ((q : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1)) *
    Real.exp (-15) / 4

/-- **The lower bound.**  `c / T ≤ bandLaplace p q T` for `T ≥ 3`.  The witness
region is `r ∈ (1,2)` with `s` pinned to within `1/(4T)` of `r`; the `1/T` is the
width of that region, not a property of the integrand. -/
public theorem bandLaplace_ge (p q : ℕ) [NeZero p] [NeZero q] (hp : 2 ≤ p)
    {T : ℝ} (hT : 3 ≤ T) :
    bandLowerConst p q / T ≤ bandLaplace p q T := by
  have hT0 : (0:ℝ) < T := by linarith
  rw [bandLaplace_eq_radial p q hT0.le]
  set Vp := (volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) with hVpdef
  set Vq := (volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1) with hVqdef
  have hVp : 0 ≤ Vp := measureReal_nonneg
  have hVq : 0 ≤ Vq := measureReal_nonneg
  have hcongr : (∫ r in Ioi (0:ℝ), r ^ (p - 1) *
        ((q : ℝ) * (Vq * ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))))
      = ((q : ℝ) * Vq) * ∫ r in Ioi (0:ℝ), r ^ (p - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    ring
  rw [hcongr]
  -- The outer integral is at least the integral over the witness interval.
  have hsub : Ioo (1:ℝ) 2 ⊆ Ioi (0:ℝ) := fun r hr => lt_trans one_pos hr.1
  have hpt : ∀ r ∈ Ioo (1:ℝ) 2, Real.exp (-15) * (1 / (4 * T))
      ≤ r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    intro r hr
    have hr1 : (1:ℝ) ≤ r := le_of_lt hr.1
    have hr2 : r ≤ 2 := le_of_lt hr.2
    have hpow : (1:ℝ) ≤ r ^ (p - 1) := one_le_pow₀ hr1
    have hin := innerBand_ge q hT hr1 hr2
    have hnn : (0:ℝ) ≤ Real.exp (-15) * (1 / (4 * T)) := by positivity
    calc Real.exp (-15) * (1 / (4 * T)) = 1 * (Real.exp (-15) * (1 / (4 * T))) := by ring
      _ ≤ r ^ (p - 1) * (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) :=
          mul_le_mul hpow hin hnn (by positivity)
  have hconst : ∫ _r in Ioo (1:ℝ) 2, Real.exp (-15) * (1 / (4 * T))
      = Real.exp (-15) * (1 / (4 * T)) := by
    rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (2:ℝ) - 1)]
    norm_num
  have hlow : Real.exp (-15) * (1 / (4 * T))
      ≤ ∫ r in Ioi (0:ℝ), r ^ (p - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    have h1 : ∫ _r in Ioo (1:ℝ) 2, Real.exp (-15) * (1 / (4 * T))
        ≤ ∫ r in Ioo (1:ℝ) 2, r ^ (p - 1) *
            (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
              (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) :=
      MeasureTheory.setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo]))
        ((integrableOn_outerBand p q hp hT0).mono_set hsub) measurableSet_Ioo hpt
    have h2 : (∫ r in Ioo (1:ℝ) 2, r ^ (p - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))))
        ≤ ∫ r in Ioi (0:ℝ), r ^ (p - 1) *
            (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
              (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
      refine MeasureTheory.setIntegral_mono_set (integrableOn_outerBand p q hp hT0) ?_
        (LE.le.eventuallyLE hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : (0:ℝ) ≤ r := le_of_lt hr
      refine mul_nonneg (by positivity) ?_
      refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
      have : (0:ℝ) ≤ s := le_of_lt hs
      positivity
    rw [hconst] at h1
    linarith
  have hqVq : 0 ≤ (q : ℝ) * Vq := by positivity
  have h3 := mul_le_mul_of_nonneg_left hlow hqVq
  have h4 := mul_le_mul_of_nonneg_left h3 hVp
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ (p:ℝ))
  refine le_trans (le_of_eq ?_) h5
  rw [bandLowerConst, ← hVpdef, ← hVqdef]
  field_simp

/-! ## Assembly -/

/-- The unit ball has positive finite volume, so the radial constants are
positive.  Needed because `hasLocalVolumeOrder_of_gaussianLaplace` asks for a
strictly positive lower constant. -/
public theorem unitBallReal_pos (n : ℕ) :
    0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

/-- At the pair `(1,1)` the Laplace scale is just `1 / T`. -/
public theorem laplaceScale_one_one (T : ℝ) : laplaceScale 1 1 T = 1 / T := by
  rw [laplaceScale]
  simp [Real.rpow_neg_one]

/-- **Stage 3, the model case.**  The band germ of a nondegenerate indefinite
form of signature `(p, q)` has local pair `(1, 1)` at the origin, whenever the
first block has dimension at least two.

The two-sided Laplace bounds are `bandLaplace_ge` and `bandLaplace_le`; the
homogeneity that lets a single radius settle the pair is `modelBandGerm_smul`.
Nothing here is assumed: no frontier hypothesis appears in the statement or in
any lemma it uses. -/
public theorem hasLocalVolumeOrder_modelBandGerm (p q : ℕ) [NeZero p] [NeZero q] (hp : 2 ≤ p) :
    HasLocalVolumeOrder (modelBandGerm p q) 0 1 1 := by
  have hswap : ∀ T : ℝ, (∫ x : EuclideanSpace ℝ (Fin (p + q)),
      Real.exp (-T * modelBandGerm p q x) * Real.exp (-‖x‖ ^ 2)) = bandLaplace p q T := by
    intro T
    rw [bandLaplace]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hcpos : 0 < bandLowerConst p q := by
    rw [bandLowerConst]
    have h1 : (0:ℝ) < (p : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    have h2 : (0:ℝ) < (q : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have h3 := unitBallReal_pos p
    have h4 := unitBallReal_pos q
    positivity
  refine hasLocalVolumeOrder_of_gaussianLaplace (k := 2)
    (measurable_modelBandGerm p q) (modelBandGerm_nonneg p q)
    (fun t ht x => modelBandGerm_smul p q t ht x)
    one_pos le_rfl (C := bandUpperConst p q) hcpos (fun T hT => ?_) (fun T hT => ?_)
  · have hT0 : (0:ℝ) < T := by linarith
    rw [hswap, laplaceScale_one_one, ← div_eq_mul_one_div]
    exact bandLaplace_ge p q hp hT
  · have hT0 : (0:ℝ) < T := by linarith
    rw [hswap, laplaceScale_one_one, ← div_eq_mul_one_div]
    exact bandLaplace_le p q hp hT0

/-- The germ read through the block swap is the germ of the swapped signature.
`|a - b| = |b - a|` is the whole content; the rest is bookkeeping about which
packaging of the splitting is in play. -/
public theorem modelBandGerm_comp_euclideanSwap (p q : ℕ) :
    modelBandGerm q p ∘ (euclideanSwap p q) = modelBandGerm p q := by
  funext w
  obtain ⟨⟨u, v⟩, rfl⟩ := (euclideanProdEquiv p q).surjective w
  simp only [Function.comp_apply, euclideanSwap_apply]
  rw [← coe_splitLE, ← coe_splitLE]
  exact (modelBandGerm_splitLE_swap p q u v).symm

/-- The swap fixes the origin. -/
public theorem euclideanSwap_zero (p q : ℕ) : euclideanSwap p q 0 = 0 := by
  have h0 : euclideanProdEquiv p q (0, 0) = 0 := by
    rw [← coe_splitLE]; exact map_zero (splitLE p q)
  have h0' : euclideanProdEquiv q p (0, 0) = 0 := by
    rw [← coe_splitLE]; exact map_zero (splitLE q p)
  calc euclideanSwap p q 0 = euclideanSwap p q (euclideanProdEquiv p q (0, 0)) := by rw [h0]
    _ = euclideanProdEquiv q p (0, 0) := euclideanSwap_apply p q 0 0
    _ = 0 := h0'

/-- **Stage 3, every signature off the two-dimensional boundary.**  A
nondegenerate indefinite form in the model coordinates has local band pair
`(1,1)` whenever both blocks are nonempty and the ambient dimension is at least
three.

The dimension hypothesis is used exactly once, and honestly: `3 ≤ p + q` with
both blocks nonempty forces one block to have dimension at least two, and the
germ is symmetric under exchanging the blocks, so the estimate can always be run
with the larger block outside.  At `p = q = 1` no such choice exists, which is
the boundary case where the pair is `(1,2)` rather than `(1,1)`. -/
public theorem hasLocalVolumeOrder_modelBandGerm_of_three_le (p q : ℕ)
    [NeZero p] [NeZero q] (hpq : 3 ≤ p + q) :
    HasLocalVolumeOrder (modelBandGerm p q) 0 1 1 := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · -- `p = 1`, so the other block carries the dimension.
    have hp1 : p = 1 := by
      have := Nat.pos_of_ne_zero (NeZero.ne p); omega
    have hq2 : 2 ≤ q := by omega
    have hsw := hasLocalVolumeOrder_modelBandGerm q p hq2
    rw [← euclideanSwap_zero p q] at hsw
    have hcomp := hasLocalVolumeOrder_comp_isometry (euclideanSwap p q)
      (measurePreserving_euclideanSwap p q) (isometry_euclideanSwap p q) hsw
    rwa [modelBandGerm_comp_euclideanSwap] at hcomp
  · exact hasLocalVolumeOrder_modelBandGerm p q hp

/-! ## Transport to an arbitrary congruent form

Sylvester's law of inertia says every nondegenerate real quadratic form is
congruent to a signed sum of squares.  What the volume order needs from that is
only a linear change of coordinates carrying `|Q|` to the model germ: a linear
equivalence is not measure preserving, but it distorts volume by a constant
Jacobian and balls by bounded amounts, so the pair is unchanged.  That is what
`hasLocalVolumeOrder_comp_continuousLinearEquiv` supplies.

Stating the transport separately from the construction of the change of
coordinates keeps the two obligations apart: this theorem is proved here, and a
caller who produces the coordinates from Sylvester gets the pair with nothing
further to check.
-/

/-- **Any form congruent to the model has the model's band pair.**  Given a
linear change of coordinates carrying `|Q|` to `modelBandGerm p q`, the germ
`|Q|` has local pair `(1,1)` at the origin.

No hypothesis is placed on `Q` beyond the supplied congruence: nondegeneracy and
indefiniteness are exactly what produce the congruence in the first place, and
restating them here would be assuming what the caller already had to prove. -/
public theorem hasLocalVolumeOrder_abs_of_congruent (p q : ℕ) [NeZero p] [NeZero q]
    (hpq : 3 ≤ p + q) {Q : EuclideanSpace ℝ (Fin (p + q)) → ℝ}
    (e : EuclideanSpace ℝ (Fin (p + q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)))
    (hQ : ∀ x, |Q x| = modelBandGerm p q (e x)) :
    HasLocalVolumeOrder (fun x => |Q x|) 0 1 1 := by
  have hmodel : HasLocalVolumeOrder (modelBandGerm p q) (e 0) 1 1 := by
    rw [map_zero]
    exact hasLocalVolumeOrder_modelBandGerm_of_three_le p q hpq
  have hcomp := hasLocalVolumeOrder_comp_continuousLinearEquiv e hmodel
  have hfun : (fun x => |Q x|) = modelBandGerm p q ∘ e := funext hQ
  rw [hfun]
  exact hcomp

/-! ## Sorting the signs of a diagonalised form

Mathlib's Sylvester's law of inertia returns a weight vector `w` with entries
`±1` and an isometry onto Mathlib's weightedSumSquares at those weights.  What
the model germ needs is
the same data with the positive entries collected first, so that the sum splits
as `‖u‖² - ‖v‖²` over two blocks.  These two lemmas do that: the first sorts the
index set, the second evaluates the sum in the sorted order.

Both are pure algebra -- no measure, no topology -- which is why they are stated
over an arbitrary index bijection rather than being tangled into the analytic
argument.
-/

/-- **Sorting the signs.**  A `±1` weight vector on `Fin n` induces a splitting of
the index set into a positive block and a negative block. -/
public theorem exists_sign_split {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1) :
    ∃ (p q : ℕ) (_ : p + q = n) (τ : Fin p ⊕ Fin q ≃ Fin n),
      (∀ a : Fin p, w (τ (Sum.inl a)) = 1) ∧ (∀ b : Fin q, w (τ (Sum.inr b)) = -1) := by
  classical
  set P := {i : Fin n // w i = 1}
  set N := {i : Fin n // ¬ w i = 1}
  set σ : P ⊕ N ≃ Fin n := Equiv.sumCompl (fun i => w i = 1)
  set p := Fintype.card P with hp
  set q := Fintype.card N with hq
  have hpq : p + q = n := by
    have hcard := Fintype.card_congr σ
    rw [Fintype.card_sum] at hcard
    simpa [hp, hq] using hcard
  set eP : P ≃ Fin p := Fintype.equivFin P
  set eN : N ≃ Fin q := Fintype.equivFin N
  refine ⟨p, q, hpq, ((eP.symm.sumCongr eN.symm).trans σ), ?_, ?_⟩
  · intro a
    have hval : (σ (Sum.inl (eP.symm a)) : Fin n) = ((eP.symm a : P) : Fin n) := rfl
    show w (σ (Sum.inl (eP.symm a))) = 1
    rw [hval]; exact (eP.symm a).2
  · intro b
    have hval : (σ (Sum.inr (eN.symm b)) : Fin n) = ((eN.symm b : N) : Fin n) := rfl
    show w (σ (Sum.inr (eN.symm b))) = -1
    rw [hval]
    rcases hw ((eN.symm b : N) : Fin n) with h | h
    · exact h
    · exact absurd h (eN.symm b).2

/-- **The weighted sum in sorted order.**  Once the signs are sorted, a `±1`
weighted sum of squares is literally the difference of two sums of squares — the
shape `modelBandGerm` takes the absolute value of. -/
public theorem sum_weighted_sq_eq_split {n p q : ℕ}
    (w : Fin n → ℝ) (τ : Fin p ⊕ Fin q ≃ Fin n)
    (hpos : ∀ a : Fin p, w (τ (Sum.inl a)) = 1)
    (hneg : ∀ b : Fin q, w (τ (Sum.inr b)) = -1)
    (y : Fin n → ℝ) :
    ∑ i, w i * (y i * y i)
      = (∑ a : Fin p, (y (τ (Sum.inl a))) ^ 2) - ∑ b : Fin q, (y (τ (Sum.inr b))) ^ 2 := by
  rw [← Fintype.sum_equiv τ (fun s => w (τ s) * (y (τ s) * y (τ s)))
      (fun i => w i * (y i * y i)) (fun s => by simp)]
  rw [Fintype.sum_sum_type]
  simp only [hpos, hneg, one_mul, neg_one_mul]
  rw [Finset.sum_neg_distrib]
  ring_nf

/-- The coordinate sorting, as a linear equivalence onto the two blocks.  Same
shape as `splitLE` with the index bijection `τ` in place of `finSumFinEquiv`;
measure preservation is not needed here, because the transport that consumes it
allows an arbitrary constant Jacobian. -/
@[expose] public noncomputable def sortProd {n p q : ℕ} (τ : Fin p ⊕ Fin q ≃ Fin n) :
    (Fin n → ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
  (LinearEquiv.funCongrLeft ℝ ℝ τ).trans <|
    (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℝ ℝ).trans
      ((WithLp.linearEquiv 2 ℝ (Fin p → ℝ)).symm.prodCongr
        (WithLp.linearEquiv 2 ℝ (Fin q → ℝ)).symm)

public theorem sortProd_fst {n p q : ℕ} (τ : Fin p ⊕ Fin q ≃ Fin n) (y : Fin n → ℝ) (a : Fin p) :
    ((sortProd τ y).1).ofLp a = y (τ (Sum.inl a)) := rfl

public theorem sortProd_snd {n p q : ℕ} (τ : Fin p ⊕ Fin q ≃ Fin n) (y : Fin n → ℝ) (b : Fin q) :
    ((sortProd τ y).2).ofLp b = y (τ (Sum.inr b)) := rfl

public theorem norm_sq_sortProd_fst {n p q : ℕ} (τ : Fin p ⊕ Fin q ≃ Fin n) (y : Fin n → ℝ) :
    ‖(sortProd τ y).1‖ ^ 2 = ∑ a : Fin p, (y (τ (Sum.inl a))) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp [sortProd_fst, sq_abs]

public theorem norm_sq_sortProd_snd {n p q : ℕ} (τ : Fin p ⊕ Fin q ≃ Fin n) (y : Fin n → ℝ) :
    ‖(sortProd τ y).2‖ ^ 2 = ∑ b : Fin q, (y (τ (Sum.inr b))) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp [sortProd_snd, sq_abs]

/-- **From a diagonalisation to the band pair.**  A germ presented as the
absolute value of a `±1`-weighted sum of squares in *some* linear coordinates has
local pair `(1,1)`, provided both signs occur and the ambient dimension is at
least three.

This is the interface Sylvester's law of inertia feeds: it supplies exactly the
weight vector `w`, the coordinates `f`, and — through `exists_sign_split` — the
index bijection `τ` sorting the signs.  Nondegeneracy is not restated as a
hypothesis because it is what produces the `±1` weights in the first place. -/
public theorem hasLocalVolumeOrder_abs_of_diagonal {n p q : ℕ} [NeZero p] [NeZero q]
    (hpq : p + q = n) (h3 : 3 ≤ n) {Q : EuclideanSpace ℝ (Fin n) → ℝ}
    (w : Fin n → ℝ) (f : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ))
    (τ : Fin p ⊕ Fin q ≃ Fin n)
    (hpos : ∀ a : Fin p, w (τ (Sum.inl a)) = 1)
    (hneg : ∀ b : Fin q, w (τ (Sum.inr b)) = -1)
    (hQ : ∀ x, Q x = ∑ i, w i * (f x i * f x i)) :
    HasLocalVolumeOrder (fun x => |Q x|) 0 1 1 := by
  subst hpq
  set e : EuclideanSpace ℝ (Fin (p + q)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (p + q)) :=
    (f.trans (sortProd τ)).trans (splitLE p q) with he
  refine hasLocalVolumeOrder_abs_of_congruent p q h3 e.toContinuousLinearEquiv (fun x => ?_)
  have hcoe : (e.toContinuousLinearEquiv : _ → _) x = splitLE p q (sortProd τ (f x)) := rfl
  rw [hcoe]
  rcases hsp : sortProd τ (f x) with ⟨u, v⟩
  have hu : ‖u‖ ^ 2 = ∑ a : Fin p, (f x (τ (Sum.inl a))) ^ 2 := by
    rw [← norm_sq_sortProd_fst τ (f x), hsp]
  have hv : ‖v‖ ^ 2 = ∑ b : Fin q, (f x (τ (Sum.inr b))) ^ 2 := by
    rw [← norm_sq_sortProd_snd τ (f x), hsp]
  rw [modelBandGerm_splitLE, hu, hv, hQ x, sum_weighted_sq_eq_split w τ hpos hneg (f x)]

/-! ## The two-dimensional boundary

At `p = q = 1` the estimate above fails, and not for want of technique: the band
`|r² - s²| ≤ 1/T` has width `1/(T r)` in the second radius at *every* radius `r`,
and with no `r^(p-1)` weight to damp it the outer integral becomes `∫ dr / r`,
which contributes a logarithm.  The lemmas here exhibit that logarithm, which is
what makes `3 ≤ p + q` a real hypothesis rather than an artefact of the proof.

The window is taken at radii `r ≥ T^(-1/2)`, below which the band is wider than
the radius itself and the argument would double-count.
-/

/-- **The inner bound at a small radius.**  For `1 ≤ T r²` and `r ≤ 1`, the inner
integral of the `(1,1)` germ is at least a constant times `1 / (T r)`.  The `1/r`
is what the outer integral turns into a logarithm. -/
public theorem innerBand_one_ge {T r : ℝ} (hT : 3 ≤ T) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hTr : 1 ≤ T * r ^ 2) :
    Real.exp (-6) * (1 / (4 * T * r))
      ≤ ∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
  have hT0 : (0:ℝ) < T := by linarith
  set δ : ℝ := 1 / (4 * T * r) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  -- `1 ≤ T r²` is exactly what makes the window narrower than the radius.
  have hδr : δ ≤ r / 4 := by
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith [hTr, hr0]
  have hsub : Ioo r (r + δ) ⊆ Ioi (0:ℝ) := fun s hs => lt_trans hr0 hs.1
  have hpt : ∀ s ∈ Ioo r (r + δ), Real.exp (-6)
      ≤ s ^ (1 - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hs2r : s ≤ 2 * r := by linarith [hδr]
    have hs2' : s ≤ 2 := by linarith [hs2r, hr1]
    have hgauss : Real.exp (-5) ≤ Real.exp (-(r ^ 2 + s ^ 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hr1, hs2', hr0.le, (le_of_lt (lt_trans hr0 hs1))]
    have hdiff : |r ^ 2 - s ^ 2| ≤ 3 * r * δ := by
      rw [abs_le]
      refine ⟨?_, ?_⟩ <;> nlinarith [hδ0.le, hs1.le, hs2.le, hr0.le, hs2r]
    have hband : Real.exp (-1) ≤ Real.exp (-T * |r ^ 2 - s ^ 2|) := by
      apply Real.exp_le_exp.mpr
      have h1 : T * |r ^ 2 - s ^ 2| ≤ T * (3 * r * δ) :=
        mul_le_mul_of_nonneg_left hdiff hT0.le
      have h2 : T * (3 * r * δ) = 3 / 4 := by
        rw [hδdef]; field_simp
      nlinarith [h1, h2]
    have hpow : s ^ (1 - 1) = 1 := by norm_num
    rw [hpow, one_mul]
    calc Real.exp (-6) = Real.exp (-5) * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|) :=
          mul_le_mul hgauss hband (Real.exp_pos _).le (Real.exp_pos _).le
  have hconst : ∫ _s in Ioo r (r + δ), Real.exp (-6) = Real.exp (-6) * δ := by
    rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ r + δ - r)]
    simp [mul_comm]
  have hstep1 : Real.exp (-6) * δ
      ≤ ∫ s in Ioo r (r + δ), s ^ (1 - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    rw [← hconst]
    exact MeasureTheory.setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo]))
      ((integrableOn_innerBand 1 hT0 hr0).mono_set hsub) measurableSet_Ioo hpt
  have hstep2 : (∫ s in Ioo r (r + δ), s ^ (1 - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
      ≤ ∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    refine MeasureTheory.setIntegral_mono_set (integrableOn_innerBand 1 hT0 hr0) ?_
      (LE.le.eventuallyLE hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  calc Real.exp (-6) * (1 / (4 * T * r)) = Real.exp (-6) * δ := by rw [hδdef]
    _ ≤ _ := hstep1
    _ ≤ _ := hstep2

/-- The inner integral, as a function of the first radius, is strongly
measurable.  `fun_prop` cannot see through a parametric integral; this is the
lemma that can. -/
public theorem stronglyMeasurable_innerBand (q : ℕ) (T : ℝ) :
    StronglyMeasurable (fun r : ℝ =>
      ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
  have hjoint : StronglyMeasurable (fun z : ℝ × ℝ => z.2 ^ (q - 1) *
      (Real.exp (-(z.1 ^ 2 + z.2 ^ 2)) * Real.exp (-T * |z.1 ^ 2 - z.2 ^ 2|))) := by
    fun_prop
  exact hjoint.integral_prod_right' (ν := volume.restrict (Ioi (0:ℝ)))

/-- The Gaussian on the positive half-line is integrable; its integral is the
constant the crude inner bound uses. -/
public theorem integrableOn_exp_neg_sq_Ioi :
    IntegrableOn (fun s : ℝ => Real.exp (-s ^ 2)) (Ioi 0) volume := by
  have h : Integrable (fun s : ℝ => Real.exp (-(1:ℝ) * s ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by norm_num)
  simpa using h.integrableOn

/-- **The crude inner bound.**  Dropping the Laplace factor bounds the inner
integral by a Gaussian in `r` times a constant.  Too weak for the estimate, but
enough for integrability — and unlike the sharp bound it survives at `p = 1`,
where `r^(p-2)` is not integrable at the origin. -/
public theorem innerBand_le_gaussian (q : ℕ) {T r : ℝ} (hT : 0 ≤ T) :
    (∫ s in Ioi (0:ℝ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
      ≤ Real.exp (-r ^ 2) * ∫ s in Ioi (0:ℝ), s ^ (q - 1) * Real.exp (-s ^ 2) := by
  have hdom : IntegrableOn
      (fun s : ℝ => Real.exp (-r ^ 2) * (s ^ (q - 1) * Real.exp (-s ^ 2))) (Ioi 0) volume := by
    have hb : IntegrableOn (fun s : ℝ => s ^ (q - 1) * Real.exp (-s ^ 2)) (Ioi 0) volume :=
      integrableOn_pow_mul_exp_neg_sq (q - 1)
    exact hb.const_mul _
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun s => s ^ (q - 1) *
      (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  have hle : (fun s => s ^ (q - 1) *
      (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))
      ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun s => Real.exp (-r ^ 2) * (s ^ (q - 1) * Real.exp (-s ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs
    have hgauss : Real.exp (-(r ^ 2 + s ^ 2)) = Real.exp (-r ^ 2) * Real.exp (-s ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    have hlap : Real.exp (-T * |r ^ 2 - s ^ 2|) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ T * |r ^ 2 - s ^ 2| := by positivity
      linarith
    calc s ^ (q - 1) * (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))
        = (s ^ (q - 1) * Real.exp (-s ^ 2)) * Real.exp (-r ^ 2)
            * Real.exp (-T * |r ^ 2 - s ^ 2|) := by rw [hgauss]; ring
      _ ≤ (s ^ (q - 1) * Real.exp (-s ^ 2)) * Real.exp (-r ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hlap (by positivity)
      _ = Real.exp (-r ^ 2) * (s ^ (q - 1) * Real.exp (-s ^ 2)) := by ring
  refine le_trans (MeasureTheory.integral_mono_of_nonneg hnn hdom hle) ?_
  rw [MeasureTheory.integral_const_mul]

/-- The inner integral is integrable in the first radius, with no dimension
hypothesis. -/
public theorem integrableOn_innerBand_outer (q : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun r : ℝ =>
      ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
        (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) (Ioi 0) volume := by
  set G : ℝ := ∫ s in Ioi (0:ℝ), s ^ (q - 1) * Real.exp (-s ^ 2) with hG
  have hGnn : 0 ≤ G := by
    rw [hG]
    refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  have hdom : IntegrableOn (fun r : ℝ => Real.exp (-r ^ 2) * G) (Ioi 0) volume :=
    integrableOn_exp_neg_sq_Ioi.mul_const _
  refine Integrable.mono' hdom ((stronglyMeasurable_innerBand q T).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hnn : (0:ℝ) ≤ ∫ s in Ioi (0:ℝ), s ^ (q - 1) *
      (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)) := by
    refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  rw [Real.norm_of_nonneg hnn]
  exact innerBand_le_gaussian q hT

/-- `∫ dr / r` over the window that produces the logarithm. -/
public theorem integral_one_div_Ioo {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∫ r in Ioo a (1:ℝ), 1 / r = Real.log (1 / a) := by
  have hnot : (0:ℝ) ∉ Set.uIcc a 1 := by
    rw [Set.uIcc_of_le ha1]
    intro h
    exact absurd h.1 (not_le.mpr ha)
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha1,
    integral_one_div hnot]

/-- **The outer bound at the boundary signature.**  Integrating the small-radius
inner bound over `r ∈ (T^(-1/2), 1)` turns `1 / (T r)` into `log T / T`.  This is
the logarithm that the `(1,1)` signature has and the theorem's hypothesis
excludes. -/
public theorem outerBand_one_ge {T : ℝ} (hT : 3 ≤ T) :
    Real.exp (-6) * Real.log T / (8 * T)
      ≤ ∫ r in Ioi (0:ℝ), r ^ (1 - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) < T := by linarith
  set a : ℝ := 1 / Real.sqrt T with hadef
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have ha : 0 < a := by rw [hadef]; positivity
  have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0.le
  have hsqrt1 : 1 < Real.sqrt T := by nlinarith [hsq, hsqrt, hT1]
  have ha1 : a ≤ 1 := by
    rw [hadef, div_le_one hsqrt]; linarith
  have hsub : Ioo a (1:ℝ) ⊆ Ioi (0:ℝ) := fun r hr => lt_trans ha hr.1
  -- the pointwise bound on the window
  have hpt : ∀ r ∈ Ioo a (1:ℝ), Real.exp (-6) / (4 * T) * (1 / r)
      ≤ r ^ (1 - 1) * (∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hr0 : 0 < r := lt_trans ha hr1
    have hTr : 1 ≤ T * r ^ 2 := by
      have : a ^ 2 ≤ r ^ 2 := by nlinarith [hr1.le, ha.le]
      have haa : a ^ 2 = 1 / T := by
        rw [hadef, div_pow, one_pow, hsq]
      rw [haa] at this
      calc (1:ℝ) = T * (1 / T) := by field_simp
        _ ≤ T * r ^ 2 := mul_le_mul_of_nonneg_left this hT0.le
    have hin := innerBand_one_ge hT hr0 hr2.le hTr
    have hpow : r ^ (1 - 1) = 1 := by norm_num
    rw [hpow, one_mul]
    refine le_trans (le_of_eq ?_) hin
    field_simp
  -- the window integral of `1/r`
  have hconst : ∫ r in Ioo a (1:ℝ), Real.exp (-6) / (4 * T) * (1 / r)
      = Real.exp (-6) / (4 * T) * Real.log (1 / a) := by
    rw [MeasureTheory.integral_const_mul, integral_one_div_Ioo ha ha1]
  have hintc : IntegrableOn
      (fun r : ℝ => Real.exp (-6) / (4 * T) * (1 / r)) (Ioo a 1) volume := by
    have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Set.Icc a 1) := by
      refine ContinuousOn.div continuousOn_const continuousOn_id (fun r hr => ?_)
      exact ne_of_gt (lt_of_lt_of_le ha hr.1)
    have hb : IntegrableOn (fun r : ℝ => 1 / r) (Ioo a 1) volume :=
      (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    exact hb.const_mul _
  have h1 : ∫ r in Ioo a (1:ℝ), Real.exp (-6) / (4 * T) * (1 / r)
      ≤ ∫ r in Ioo a (1:ℝ), r ^ (1 - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) :=
    MeasureTheory.setIntegral_mono_on hintc
      (((integrableOn_innerBand_outer 1 hT0.le).mono_set hsub).congr_fun
        (fun r _ => by norm_num) measurableSet_Ioo)
      measurableSet_Ioo hpt
  have h2 : (∫ r in Ioo a (1:ℝ), r ^ (1 - 1) *
        (∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))))
      ≤ ∫ r in Ioi (0:ℝ), r ^ (1 - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    refine MeasureTheory.setIntegral_mono_set
      (((integrableOn_innerBand_outer 1 hT0.le)).congr_fun
        (fun r _ => by norm_num) measurableSet_Ioi) ?_ (LE.le.eventuallyLE hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0:ℝ) ≤ r := le_of_lt hr
    refine mul_nonneg (by positivity) ?_
    refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    have : (0:ℝ) ≤ s := le_of_lt hs
    positivity
  have hlog : Real.log (1 / a) = Real.log T / 2 := by
    rw [hadef, one_div_one_div, Real.log_sqrt hT0.le]
  rw [hconst, hlog] at h1
  refine le_trans (le_of_eq ?_) (le_trans h1 h2)
  field_simp
  ring

/-- **The two-dimensional boundary, at the transform.**  At the signature
`(1,1)` the Gaussian-Laplace transform is at least a constant times
`log T / T` — strictly larger than the `C / T` that the pair `(1,1)` would
require.  This is the sense in which `3 ≤ p + q` is not removable. -/
public theorem bandLaplace_one_one_ge {T : ℝ} (hT : 3 ≤ T) :
    (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) ^ 2 *
        (Real.exp (-6) * Real.log T / (8 * T))
      ≤ bandLaplace 1 1 T := by
  have hT0 : (0:ℝ) < T := by linarith
  rw [bandLaplace_eq_radial 1 1 hT0.le]
  set V := (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) with hV
  have hVnn : 0 ≤ V := measureReal_nonneg
  have hcongr : (∫ r in Ioi (0:ℝ), r ^ (1 - 1) *
        (((1:ℕ) : ℝ) * (V * ∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
          (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|)))))
      = V * ∫ r in Ioi (0:ℝ), r ^ (1 - 1) *
          (∫ s in Ioi (0:ℝ), s ^ (1 - 1) *
            (Real.exp (-(r ^ 2 + s ^ 2)) * Real.exp (-T * |r ^ 2 - s ^ 2|))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    push_cast
    ring
  rw [hcongr]
  have hstep := mul_le_mul_of_nonneg_left (outerBand_one_ge hT) hVnn
  have hstep2 := mul_le_mul_of_nonneg_left hstep hVnn
  have hstep3 := mul_le_mul_of_nonneg_left hstep2 (by norm_num : (0:ℝ) ≤ ((1:ℕ) : ℝ))
  refine le_trans (le_of_eq ?_) hstep3
  push_cast
  ring

/-! ## The hyperbolic germ

The pairing `⟨x, y⟩` on `ℝ^H × ℝ^H` is the indefinite form the saddle Hessian
degenerates to when both diagonal blocks vanish, and by `LossExpansion` it is
what the loss germ is comparable to there.  It is a signature-`(H,H)` form, so
the model theorem applies as soon as `2 ≤ H` — which the rung condition
`k < r < H` supplies.

The change of coordinates is polarisation, `⟨x,y⟩ = ‖(x+y)/2‖² - ‖(x-y)/2‖²`, and
it is a linear equivalence rather than an isometry, which is exactly the case
`hasLocalVolumeOrder_abs_of_congruent` was stated for.
-/

/-- Polarisation as a linear equivalence of the two blocks. -/
@[expose] public noncomputable def polarPair (H : ℕ) :
    (EuclideanSpace ℝ (Fin H) × EuclideanSpace ℝ (Fin H)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin H) × EuclideanSpace ℝ (Fin H)) where
  toFun p := ((2:ℝ)⁻¹ • (p.1 + p.2), (2:ℝ)⁻¹ • (p.1 - p.2))
  invFun q := (q.1 + q.2, q.1 - q.2)
  map_add' p q := by simp [Prod.ext_iff]; constructor <;> module
  map_smul' c p := by simp [Prod.ext_iff]; constructor <;> module
  left_inv p := by simp [Prod.ext_iff]; constructor <;> module
  right_inv q := by simp [Prod.ext_iff]; constructor <;> module

/-- The polarising change of coordinates on the ambient space. -/
@[expose] public noncomputable def hyperbolicEquiv (H : ℕ) :
    EuclideanSpace ℝ (Fin (H + H)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (H + H)) :=
  ((splitLE H H).symm.trans (polarPair H)).trans (splitLE H H)

/-- **The hyperbolic germ** `|⟨x, y⟩|`, read on the ambient space through the
block split. -/
@[expose] public noncomputable def hyperbolicGerm (H : ℕ)
    (w : EuclideanSpace ℝ (Fin (H + H))) : ℝ :=
  |inner ℝ ((splitLE H H).symm w).1 ((splitLE H H).symm w).2|

/-- **The hyperbolic germ has local pair `(1,1)`.**  Unconditional, for `2 ≤ H`.

This is the germ the O77 loss reduces to at a rung where both diagonal blocks of
the Hessian vanish, so it is the point at which the Stage 3 band layer actually
meets the Stage 4 saddle analysis. The hypothesis `2 ≤ H` is supplied by the
rung condition `k < r < H`; at `H = 1` the ambient dimension is two and the pair
is the logarithmic one instead. -/
public theorem hasLocalVolumeOrder_hyperbolicGerm (H : ℕ) (hH : 2 ≤ H) :
    HasLocalVolumeOrder (hyperbolicGerm H) 0 1 1 := by
  have hne : NeZero H := ⟨by omega⟩
  refine hasLocalVolumeOrder_abs_of_congruent H H (by omega)
    (hyperbolicEquiv H).toContinuousLinearEquiv (fun w => ?_)
  have hcoe : ((hyperbolicEquiv H).toContinuousLinearEquiv : _ → _) w
      = splitLE H H (polarPair H ((splitLE H H).symm w)) := rfl
  rw [hcoe, modelBandGerm_splitLE]
  congr 1
  have hp1 : ((polarPair H) ((splitLE H H).symm w)).1
      = (2:ℝ)⁻¹ • (((splitLE H H).symm w).1 + ((splitLE H H).symm w).2) := rfl
  have hp2 : ((polarPair H) ((splitLE H H).symm w)).2
      = (2:ℝ)⁻¹ • (((splitLE H H).symm w).1 - ((splitLE H H).symm w).2) := rfl
  rw [hp1, hp2, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹), mul_pow]
  rw [@norm_add_sq_real, @norm_sub_sq_real]
  ring

end AISafetyAtlas.SingularLearning
