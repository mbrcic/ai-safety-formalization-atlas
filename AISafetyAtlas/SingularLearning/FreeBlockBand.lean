module

public import AISafetyAtlas.SingularLearning.ShiftedBand

/-!
# A free block carrying an arbitrary continuous shift

`ShiftedBand.lean` proves the **level-uniform** band estimate: for the model
form `Q(ξ) = ‖u‖² - ‖v‖²` of signature `(p, q)`, the band `|Q(ξ) - c| ≤ ε`
inside the ball of radius `δ` has volume between `shiftedBandLowerConst p q δ * ε`
and `shiftedBandConst p q δ * ε`, with the *upper* constant free of the level `c`
and the lower one holding at every level with `|c| ≤ δ²/32`.

This module adds the third block.  The variable `ζ` ranges over a free
`s`-dimensional factor and enters only through an arbitrary shift `g ζ`, and the
band is the two-sided one around level zero for `Q(ξ) + g(ζ)`.  The proof is
exactly the printed one: the `ζ`-slice of the band at a fixed `ζ` is the
level-`(-(g ζ))` band of `ShiftedBand`, so Fubini in the free block turns the
level-uniform estimate into an estimate for the whole product.

## The shape that is actually proved

Two choices are made here and both are visible in the statements.

* The ambient space is the **product** `EuclideanSpace ℝ (Fin (p+q)) ×
  EuclideanSpace ℝ (Fin s)` with the product measure, not a single
  `EuclideanSpace ℝ (Fin (p+q+s))`.  The two are measurably isomorphic, but the
  isomorphism is not needed for the estimate and is not built here.
* The neighbourhood is a **product box** `‖w.1‖ ≤ δ ∧ ‖w.2‖ ≤ δ`, not a ball of
  the product.  That is the "sufficiently small product neighbourhood" of the
  printed statement, and it is what makes the slice a `shiftedBandSet` on the
  nose.

Neither choice weakens anything: the level-uniform input is used at full
strength, and the `ζ`-box of the lower bound is shrunk to a radius `ρ ≤ δ` on
which `|g ζ| ≤ δ²/32`, which is the printed "shrink the ζ-box".

## What the shift has to satisfy

The upper bound asks nothing of `g` beyond measurability: the level-uniform
constant does not see the level, so no matter how `g` moves the level, each
slice is bounded by the same `shiftedBandConst p q δ * ε`.  That is the whole
content of "integrating the uniform bound over the fixed ζ-box gives `O(ε)`".

The lower bound cannot be unconditional, for the reason `shiftedBandVolume_ge`
records: at a level the form does not attain inside the ball the band is empty.
`measure_freeBlockBandSet_ge` therefore carries the hypothesis that `|g ζ| ≤
δ²/32` on the shrunken box, and `exists_radius_of_continuousAt` discharges it
from continuity of `g` at the origin together with `g 0 = 0` — the printed
hypothesis on `g`.

`exists_freeBlockBand_bounds` packages the two sides as the `Θ(ε)` of the
printed Lemma 2.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

/-- The band of half-width `ε` around level zero for `modelBandForm p q ξ + g ζ`,
inside the product box of radius `δ`: `‖ξ‖ ≤ δ` in the quadratic block and
`‖ζ‖ ≤ δ` in the free block.

The box, rather than a ball of the product, is deliberate — it is the "product
neighbourhood" of the printed statement, and it is what makes the `ζ`-slice
literally a `shiftedBandSet`. -/
@[expose] public noncomputable def freeBlockBandSet (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin (p + q)) × EuclideanSpace ℝ (Fin s)) :=
  {w | ‖w.1‖ ≤ δ ∧ ‖w.2‖ ≤ δ ∧ |modelBandForm p q w.1 + g w.2| ≤ ε}

public theorem measurableSet_freeBlockBandSet (p q s : ℕ)
    {g : EuclideanSpace ℝ (Fin s) → ℝ} (hg : Measurable g) (δ ε : ℝ) :
    MeasurableSet (freeBlockBandSet p q s g δ ε) := by
  have h1 : Measurable fun w : EuclideanSpace ℝ (Fin (p + q)) ×
      EuclideanSpace ℝ (Fin s) => ‖w.1‖ := measurable_fst.norm
  have h2 : Measurable fun w : EuclideanSpace ℝ (Fin (p + q)) ×
      EuclideanSpace ℝ (Fin s) => ‖w.2‖ := measurable_snd.norm
  have h3 : Measurable fun w : EuclideanSpace ℝ (Fin (p + q)) ×
      EuclideanSpace ℝ (Fin s) => modelBandForm p q w.1 + g w.2 :=
    (((continuous_modelBandForm p q).measurable).comp measurable_fst).add
      (hg.comp measurable_snd)
  have h4 : MeasurableSet {w : EuclideanSpace ℝ (Fin (p + q)) ×
      EuclideanSpace ℝ (Fin s) | |modelBandForm p q w.1 + g w.2| ≤ ε} := by
    have hrw : {w : EuclideanSpace ℝ (Fin (p + q)) ×
        EuclideanSpace ℝ (Fin s) | |modelBandForm p q w.1 + g w.2| ≤ ε}
        = (fun w : EuclideanSpace ℝ (Fin (p + q)) × EuclideanSpace ℝ (Fin s) =>
            modelBandForm p q w.1 + g w.2) ⁻¹' Set.Icc (-ε) ε := by
      ext w
      simp [abs_le, Set.mem_Icc]
    rw [hrw]
    exact h3 measurableSet_Icc
  exact (measurableSet_le h1 measurable_const).inter
    ((measurableSet_le h2 measurable_const).inter h4)

/-- The band sits inside the product of the two closed balls. -/
public theorem freeBlockBandSet_subset (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ) :
    freeBlockBandSet p q s g δ ε
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (p + q))) δ ×ˢ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ := by
  rintro w ⟨h1, h2, -⟩
  exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using h1,
    by simpa [Metric.mem_closedBall, dist_zero_right] using h2⟩

public theorem measure_freeBlockBandSet_ne_top (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ) :
    volume (freeBlockBandSet p q s g δ ε) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (freeBlockBandSet_subset p q s g δ ε))
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_closedBall_lt_top.ne measure_closedBall_lt_top.ne

/-! ## The slices in the free block -/

/-- **The slice identity.**  At a `ζ` inside the free-block box, the slice of the
band is exactly the level-`(-(g ζ))` band of `ShiftedBand`.  The sign is the one
the definitions force: `|F + g ζ| = |F - (-(g ζ))|`. -/
public theorem freeBlockBandSet_slice (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ)
    {ζ : EuclideanSpace ℝ (Fin s)} (hζ : ‖ζ‖ ≤ δ) :
    (fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet p q s g δ ε
      = shiftedBandSet p q (-(g ζ)) δ ε := by
  ext ξ
  simp only [freeBlockBandSet, shiftedBandSet, Set.mem_preimage, Set.mem_ofPred_eq,
    sub_neg_eq_add]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hζ, h.2⟩⟩

/-- Outside the free-block box the slice is empty. -/
public theorem freeBlockBandSet_slice_of_not_mem (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ)
    {ζ : EuclideanSpace ℝ (Fin s)} (hζ : ¬ ‖ζ‖ ≤ δ) :
    (fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet p q s g δ ε = ∅ := by
  ext ξ
  simp only [freeBlockBandSet, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  exact fun _ h => absurd h hζ

/-- **Fubini in the free block.**  The volume of the band is the integral of its
`ζ`-slices, which is the step the printed proof calls "integrating over the
ζ-box". -/
public theorem measure_freeBlockBandSet_eq_lintegral (p q s : ℕ)
    {g : EuclideanSpace ℝ (Fin s) → ℝ} (hg : Measurable g) (δ ε : ℝ) :
    volume (freeBlockBandSet p q s g δ ε)
      = ∫⁻ ζ : EuclideanSpace ℝ (Fin s),
          volume ((fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet p q s g δ ε) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_freeBlockBandSet p q s hg δ ε)]

/-! ## The two bounds -/

/-- **The upper bound.**  Nothing is asked of the shift `g` beyond
measurability: the level-uniform constant of `ShiftedBand` bounds every slice at
once, whatever level `g ζ` moves it to, so integrating over the free-block box
costs only that box's volume. -/
public theorem measure_freeBlockBandSet_le (p q s : ℕ) (hp : 2 ≤ p)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (hg : Measurable g) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume (freeBlockBandSet p q s g δ ε)
      ≤ ENNReal.ofReal (shiftedBandConst p q δ * ε)
        * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ) := by
  rw [measure_freeBlockBandSet_eq_lintegral p q s hg δ ε]
  have hb : ∀ ζ : EuclideanSpace ℝ (Fin s),
      volume ((fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet p q s g δ ε)
        ≤ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ).indicator
            (fun _ => ENNReal.ofReal (shiftedBandConst p q δ * ε)) ζ := by
    intro ζ
    by_cases hζ : ‖ζ‖ ≤ δ
    · have hmem : ζ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hζ
      rw [freeBlockBandSet_slice p q s g δ ε hζ, Set.indicator_of_mem hmem]
      rw [← ENNReal.ofReal_toReal (measure_shiftedBandSet_ne_top p q (-(g ζ)) δ ε)]
      exact ENNReal.ofReal_le_ofReal (shiftedBandVolume_le p q hp (-(g ζ)) hδ hε)
    · rw [freeBlockBandSet_slice_of_not_mem p q s g δ ε hζ]
      simp
  calc ∫⁻ ζ : EuclideanSpace ℝ (Fin s),
        volume ((fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet p q s g δ ε)
      ≤ ∫⁻ ζ : EuclideanSpace ℝ (Fin s),
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ).indicator
            (fun _ => ENNReal.ofReal (shiftedBandConst p q δ * ε)) ζ := lintegral_mono hb
    _ = ENNReal.ofReal (shiftedBandConst p q δ * ε)
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ) :=
        lintegral_indicator_const measurableSet_closedBall _

/-- **The lower bound.**  On a shrunken free-block box of radius `ρ ≤ δ` where
the shift stays inside the admissible level window `|g ζ| ≤ δ²/32`, every slice
carries at least `shiftedBandLowerConst p q δ * ε`, and integrating over that box
gives the printed "at least `cε` for every ζ in a fixed positive-volume box".

The level restriction is inherited from `shiftedBandVolume_ge` and cannot be
dropped: at a level the form does not attain inside the ball the slice is
empty.

No positivity is asked of `ρ`.  It is not needed — a degenerate box makes the
left side zero and the inequality trivial — and `exists_freeBlockBand_bounds`
supplies a positive `ρ` where positivity is what makes the constant positive. -/
public theorem measure_freeBlockBandSet_ge (p q s : ℕ) [NeZero q] (hp : 2 ≤ p)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (hg : Measurable g) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hρδ : ρ ≤ δ)
    (hsmall : ∀ ζ : EuclideanSpace ℝ (Fin s), ‖ζ‖ ≤ ρ → |g ζ| ≤ δ ^ 2 / 32)
    (hε0 : 0 ≤ ε) (hε : ε ≤ δ ^ 2 / 4) :
    ENNReal.ofReal (shiftedBandLowerConst p q δ * ε)
        * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) ρ)
      ≤ volume (freeBlockBandSet p q s g δ ε) := by
  rw [measure_freeBlockBandSet_eq_lintegral p q s hg δ ε]
  have hb : ∀ ζ : EuclideanSpace ℝ (Fin s),
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) ρ).indicator
          (fun _ => ENNReal.ofReal (shiftedBandLowerConst p q δ * ε)) ζ
        ≤ volume ((fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet p q s g δ ε) := by
    intro ζ
    by_cases hζ : ζ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) ρ
    · have hnρ : ‖ζ‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_zero_right] using hζ
      have hnδ : ‖ζ‖ ≤ δ := hnρ.trans hρδ
      have hc : |(-(g ζ))| ≤ δ ^ 2 / 32 := by
        rw [abs_neg]; exact hsmall ζ hnρ
      rw [Set.indicator_of_mem hζ, freeBlockBandSet_slice p q s g δ ε hnδ,
        ← ENNReal.ofReal_toReal (measure_shiftedBandSet_ne_top p q (-(g ζ)) δ ε)]
      exact ENNReal.ofReal_le_ofReal (shiftedBandVolume_ge p q hp hδ hc hε0 hε)
    · rw [Set.indicator_of_notMem hζ]
      exact zero_le
  calc ENNReal.ofReal (shiftedBandLowerConst p q δ * ε)
        * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) ρ)
      = ∫⁻ ζ : EuclideanSpace ℝ (Fin s),
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) ρ).indicator
            (fun _ => ENNReal.ofReal (shiftedBandLowerConst p q δ * ε)) ζ :=
        (lintegral_indicator_const measurableSet_closedBall _).symm
    _ ≤ ∫⁻ ζ : EuclideanSpace ℝ (Fin s),
          volume ((fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet p q s g δ ε) := lintegral_mono hb

/-! ## Shrinking the free-block box -/

/-- **The printed "shrink the ζ-box".**  A shift continuous at the origin and
vanishing there stays inside the admissible level window on some ball, and that
ball may be taken inside the box of radius `δ`. -/
public theorem exists_radius_of_continuousAt {s : ℕ} {g : EuclideanSpace ℝ (Fin s) → ℝ}
    (hg : Continuous g) (hg0 : g 0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ρ ≤ δ ∧ ∀ ζ : EuclideanSpace ℝ (Fin s), ‖ζ‖ ≤ ρ → |g ζ| ≤ δ ^ 2 / 32 := by
  have hpos : (0:ℝ) < δ ^ 2 / 32 := by positivity
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := 0)) _ hpos
  refine ⟨min (r / 2) δ, lt_min (by linarith) hδ, min_le_right _ _, ?_⟩
  intro ζ hζ
  have h1 : ‖ζ‖ ≤ r / 2 := hζ.trans (min_le_left _ _)
  have h2 : dist ζ (0 : EuclideanSpace ℝ (Fin s)) < r := by
    rw [dist_zero_right]; linarith
  have := hball h2
  rw [hg0, Real.dist_eq, sub_zero] at this
  exact this.le

/-! ## The packaged two-sided statement -/

/-- **The printed Lemma 2.**  With a quadratic block of signature `(p, q)`,
`2 ≤ p` and `q ≠ 0`, and a free block carrying any continuous shift vanishing at
the origin, the band `|Q(ξ) + g(ζ)| ≤ ε` in the product box of radius `δ` has
volume `Θ(ε)`: there are constants `0 < c₁ ≤ c₂` and a threshold `ε₀ > 0` with
`c₁ ε ≤ vol ≤ c₂ ε` for every `0 ≤ ε ≤ ε₀`.

The upper constant is the level-uniform one times the whole `ζ`-box; the lower
one is the level-uniform lower constant times the shrunken `ζ`-box on which the
shift is small.  Both are positive, so the statement is a genuine two-sided
order and not a bound against zero. -/
public theorem exists_freeBlockBand_bounds (p q s : ℕ) [NeZero q] (hp : 2 ≤ p)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (hg : Continuous g) (hg0 : g 0 = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        c₁ * ε ≤ (volume (freeBlockBandSet p q s g δ ε)).toReal ∧
          (volume (freeBlockBandSet p q s g δ ε)).toReal ≤ c₂ * ε := by
  obtain ⟨ρ, hρ, hρδ, hsmall⟩ := exists_radius_of_continuousAt hg hg0 hδ
  set Vρ : ℝ := (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) ρ)).toReal with hVρ
  set Vδ : ℝ := (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ)).toReal with hVδ
  have hVρpos : 0 < Vρ := by
    rw [hVρ]
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ hρ).ne'
      measure_closedBall_lt_top.ne
  have hVρle : Vρ ≤ Vδ := by
    rw [hVρ, hVδ]
    exact ENNReal.toReal_mono measure_closedBall_lt_top.ne
      (measure_mono (Metric.closedBall_subset_closedBall hρδ))
  have hLpos : 0 < shiftedBandLowerConst p q δ := shiftedBandLowerConst_pos p q hδ
  have hLC : shiftedBandLowerConst p q δ ≤ shiftedBandConst p q δ :=
    shiftedBandLowerConst_le p q hp hδ
  refine ⟨shiftedBandLowerConst p q δ * Vρ, shiftedBandConst p q δ * Vδ, δ ^ 2 / 4,
    mul_pos hLpos hVρpos, ?_, by positivity, ?_⟩
  · exact mul_le_mul hLC hVρle hVρpos.le (hLpos.le.trans hLC)
  · intro ε hε0 hε
    have hne := measure_freeBlockBandSet_ne_top p q s g δ ε
    constructor
    · have h := measure_freeBlockBandSet_ge p q s hp g hg.measurable hδ hρδ hsmall hε0 hε
      have hmono := ENNReal.toReal_mono hne h
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hmono
      refine le_trans (le_of_eq ?_) hmono
      rw [hVρ]; ring
    · have h := measure_freeBlockBandSet_le p q s hp g hg.measurable hδ.le hε0
      have hfin : ENNReal.ofReal (shiftedBandConst p q δ * ε)
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin s)) δ) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
      have hmono := ENNReal.toReal_mono hfin h
      have hnn : (0:ℝ) ≤ shiftedBandConst p q δ * ε :=
        mul_nonneg (shiftedBandConst_nonneg p q hδ.le) hε0
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn] at hmono
      refine hmono.trans (le_of_eq ?_)
      rw [hVδ]; ring

end AISafetyAtlas.SingularLearning
