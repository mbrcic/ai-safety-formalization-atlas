module

public import AISafetyAtlas.SingularLearning.PairTransfer

/-!
# Strict two-sided bands

MAIS-O7 and MAIS-O77 define their local invariant with the strict band
`|L(x) - L(w)| < ε`, whereas `HasLocalVolumeOrder` uses the weak sublevel
`K(x) ≤ ε`.  This module makes that boundary explicit and discharges it at the
two-sided-order level.

No null-boundary or regular-value assumption is needed.  For every positive
`ε`, the strict band is squeezed between the weak sublevels at `ε / 2` and
`ε`.  Rescaling `ε` by the fixed constant `2` preserves both the exponent and
the logarithmic multiplicity, so a weak volume order implies the same strict
volume order.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set Filter Topology

variable {n : ℕ}

/-- The nonnegative germ whose sublevels are two-sided bands around the value
of `L` at `w`. -/
@[expose] public noncomputable def centeredBandGerm
    (L : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => |L x - L w|

/-- Volume of the strict `ε`-sublevel inside the ball of radius `δ`. -/
@[expose] public noncomputable def strictSublevelVolume
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (δ ε : ℝ) : ℝ :=
  (volume {x ∈ Metric.ball w δ | K x < ε}).toReal

/-- The source-facing strict-band analogue of `HasLocalVolumeOrder`. -/
@[expose] public noncomputable def HasStrictLocalVolumeOrder
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (lam : ℝ) (m : ℕ) : Prop :=
  ((∀ᶠ x in nhds w, K x = 0) ∧ lam = 0 ∧ m = 1) ∨
    (0 < lam ∧ 1 ≤ m ∧ ∃ δ₀ > 0, ∀ δ ∈ Ioo 0 δ₀, ∃ cLower cUpper : ℝ,
      0 < cLower ∧ cLower ≤ cUpper ∧
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        cLower * volumeScale lam m ε ≤ strictSublevelVolume K w δ ε ∧
          strictSublevelVolume K w δ ε ≤ cUpper * volumeScale lam m ε)

public theorem strictSublevelVolume_ne_top
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (δ ε : ℝ) :
    volume {x ∈ Metric.ball w δ | K x < ε} ≠ ⊤ := by
  have hsub : {x ∈ Metric.ball w δ | K x < ε} ⊆ Metric.ball w δ :=
    fun _ hx => hx.1
  have hle := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsub
  exact ne_top_of_le_ne_top (measure_ball_lt_top (x := w) (r := δ)).ne hle

/-- A weak sublevel at `ε/2` is contained in the strict sublevel at `ε`. -/
public theorem sublevelVolume_half_le_strict
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (δ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    sublevelVolume K w δ (ε / 2) ≤ strictSublevelVolume K w δ ε := by
  refine ENNReal.toReal_mono (strictSublevelVolume_ne_top K w δ ε) (measure_mono ?_)
  rintro x ⟨hxball, hxK⟩
  exact ⟨hxball, lt_of_le_of_lt hxK (by linarith)⟩

/-- Every strict sublevel is contained in the weak sublevel at the same
threshold. -/
public theorem strictSublevelVolume_le_sublevel
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (δ ε : ℝ) :
    strictSublevelVolume K w δ ε ≤ sublevelVolume K w δ ε := by
  refine ENNReal.toReal_mono (sublevelVolume_ne_top K w δ ε) (measure_mono ?_)
  rintro x ⟨hxball, hxK⟩
  exact ⟨hxball, hxK.le⟩

/-- Dividing a positive threshold by two tends to zero through positive
thresholds. -/
private theorem tendsto_half_nhdsGT :
    Tendsto (fun ε : ℝ => ε / 2) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin 0 (Ioi 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : ContinuousAt (fun ε : ℝ => ε / 2) 0 := by fun_prop
    have ht := hc.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
    simpa using ht
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    exact div_pos hε0 (by norm_num)

/-- **Strict/weak band bridge at two-sided order.**  Weak-sublevel bounds imply
the same pair for strict sublevels, with no boundary-measure hypothesis. -/
public theorem hasStrictLocalVolumeOrder_of_hasLocalVolumeOrder
    {K : EuclideanSpace ℝ (Fin n) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {lam : ℝ} {m : ℕ} (h : HasLocalVolumeOrder K w lam m) :
    HasStrictLocalVolumeOrder K w lam m := by
  rcases h with hzero | ⟨hlam, hm, δ₀, hδ₀, hbounds⟩
  · exact Or.inl hzero
  refine Or.inr ⟨hlam, hm, δ₀, hδ₀, fun δ hδ => ?_⟩
  obtain ⟨cLower, cUpper, hcLower, hcLU, hweak⟩ := hbounds δ hδ
  obtain ⟨a, b, ha, hab, hscale⟩ :=
    exists_volumeScale_div_bounds lam m (c := 2) (by norm_num)
  refine ⟨cLower * a, max (cLower * a) cUpper, mul_pos hcLower ha,
    le_max_left _ _, ?_⟩
  filter_upwards [tendsto_half_nhdsGT.eventually hweak, hweak, hscale,
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hhalf hsame hsc hε
  have hweakStrict := sublevelVolume_half_le_strict K w δ hε.1
  have hstrictWeak := strictSublevelVolume_le_sublevel K w δ ε
  have hscale_nonneg : 0 ≤ volumeScale lam m ε := by
    rw [volumeScale]
    have hlog : 0 < Real.log (1 / ε) :=
      Real.log_pos (by rw [lt_div_iff₀ hε.1]; linarith [hε.2])
    exact mul_nonneg (Real.rpow_nonneg hε.1.le _) (pow_nonneg hlog.le _)
  have hlower : cLower * a * volumeScale lam m ε ≤
      sublevelVolume K w δ (ε / 2) := by
    calc
      cLower * a * volumeScale lam m ε
          = cLower * (a * volumeScale lam m ε) := by ring
      _ ≤ cLower * volumeScale lam m (ε / 2) :=
        mul_le_mul_of_nonneg_left hsc.1 hcLower.le
      _ ≤ sublevelVolume K w δ (ε / 2) := hhalf.1
  have hupper : sublevelVolume K w δ ε ≤
      max (cLower * a) cUpper * volumeScale lam m ε := by
    exact hsame.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      hscale_nonneg)
  exact ⟨hlower.trans hweakStrict, hstrictWeak.trans hupper⟩

end AISafetyAtlas.SingularLearning
