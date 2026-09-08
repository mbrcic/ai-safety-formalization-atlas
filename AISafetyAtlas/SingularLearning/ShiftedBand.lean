module

public import AISafetyAtlas.SingularLearning.IndefiniteBand

/-!
# Level-uniform bands of an indefinite quadratic form

`IndefiniteBand.lean` computes the local volume order of `|Q|` at the origin,
where `Q = ‖u‖² - ‖v‖²` is the nondegenerate indefinite model form of signature
`(p, q)`.  Every estimate there is about the band around level **zero**, because
that is the only band `HasLocalVolumeOrder` sees: a sublevel set of a
nonnegative germ is a band around zero by construction.

This module proves the **level-uniform** statement: the band `|Q(w) - c| ≤ ε`
inside the ball of radius `δ`, for an *arbitrary* level `c`, has volume at most
`shiftedBandConst p q δ * ε` — one constant serving every level at once.  That
is strictly more than the level-zero estimate gives, and it is not obtainable
from it by translation, because translating the level does not translate the
window.

## Why the argument is different from the level-zero one

The level-zero proof goes through a Gaussian-Laplace transform, which needs the
germ's degree-two homogeneity (`modelBandGerm_smul`).  A band around a nonzero
level is not homogeneous, so that route is unavailable and the estimate has to
be done directly on the set.

The direct argument, in the first block:

* fix `v`; the slice is `{u : ‖u‖² ∈ [c + ‖v‖² - ε, c + ‖v‖² + ε]}`, a spherical
  shell of radii `ρ₋ ≤ ρ₊` clipped to the window (`measureReal_sliceBand_le`);
* the clipped radii satisfy `ρ₊² - ρ₋² ≤ 2ε` and `ρ₊ ≤ δ` whatever the level is,
  which is where the uniformity in `c` comes from;
* `pow_sub_pow_le_mul_sq_sub_sq` turns that into
  `ρ₊^p - ρ₋^p ≤ p · δ^(p-2) · (ρ₊² - ρ₋²)`, so the shell volume is `≲ ε`;
* Fubini over the second block (`measure_bandWindow_le`) multiplies by the
  volume of the `q`-window.

The hypothesis `2 ≤ p` enters exactly once, in the exponent `δ^(p-2)`, and it is
the same place the level-zero proof needs it.  As there, `p = 1` is handled by
the block swap (`shiftedBandVolume_le_of_three_le`), which reuses
`euclideanSwap` rather than redoing the estimate: the *signed* form changes sign
under the swap, and `|(-x) - (-c)| = |x - c|`.

## What the lower bound can and cannot say

`shiftedBandVolume_ge` is the matching lower bound, and it is necessarily
conditional on the level: at a level the form does not attain inside the ball
the band is empty and no positive lower bound exists.  The condition taken here
is `|c| ≤ δ²/32` together with `ε ≤ δ²/4`, which leaves room for a whole annulus
`δ/4 ≤ ‖v‖ ≤ δ/2` of the second block, each of whose slices sweeps a shell of
the first.  `exists_shiftedBand_bounds` packages the two sides with a single
ordered pair of constants.

**This module states nothing about `HasLocalVolumeOrder`.**  A level-uniform
band estimate is a different object from a local pair, and identifying the two
would be a claim this file does not prove.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

/-- Elementary difference-of-powers estimate. -/
public theorem pow_sub_pow_le_mul_sq_sub_sq (k : ℕ) {x y d : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x) (hxd : x ≤ d) :
    x ^ (k + 2) - y ^ (k + 2) ≤ ((k : ℝ) + 2) * d ^ k * (x ^ 2 - y ^ 2) := by
  induction k with
  | zero =>
      norm_num
      nlinarith
  | succ k ih =>
      have hx : 0 ≤ x := hy.trans hyx
      have hd : 0 ≤ d := hx.trans hxd
      have hyd : y ≤ d := hyx.trans hxd
      have hdk : (0:ℝ) ≤ d ^ k := pow_nonneg hd k
      have hsq : 0 ≤ x ^ 2 - y ^ 2 := by nlinarith
      have hpow : y ^ (k + 1) ≤ d ^ (k + 1) := pow_le_pow_left₀ hy hyd _
      have hA : x * (x ^ (k + 2) - y ^ (k + 2))
          ≤ ((k : ℝ) + 2) * d ^ (k + 1) * (x ^ 2 - y ^ 2) := by
        have hnn : (0:ℝ) ≤ ((k : ℝ) + 2) * d ^ k * (x ^ 2 - y ^ 2) :=
          mul_nonneg (mul_nonneg (by positivity) hdk) hsq
        have h1 := mul_le_mul_of_nonneg_left ih hx
        have h2 := mul_le_mul_of_nonneg_right hxd hnn
        have h3 : d * (((k : ℝ) + 2) * d ^ k * (x ^ 2 - y ^ 2))
            = ((k : ℝ) + 2) * d ^ (k + 1) * (x ^ 2 - y ^ 2) := by ring
        rw [h3] at h2
        linarith
      have hB : y ^ (k + 2) * (x - y) ≤ d ^ (k + 1) * (x ^ 2 - y ^ 2) := by
        have e1 : y ^ (k + 2) * (x - y) = y ^ (k + 1) * (y * (x - y)) := by ring
        have h1 : y ^ (k + 1) * (y * (x - y)) ≤ d ^ (k + 1) * (y * (x - y)) :=
          mul_le_mul_of_nonneg_right hpow (by nlinarith)
        have h2 : d ^ (k + 1) * (y * (x - y)) ≤ d ^ (k + 1) * (x ^ 2 - y ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hd _)
          nlinarith
        rw [e1]
        linarith
      have e : x ^ (k + 1 + 2) - y ^ (k + 1 + 2)
          = x * (x ^ (k + 2) - y ^ (k + 2)) + y ^ (k + 2) * (x - y) := by ring
      rw [e]
      push_cast
      linarith

/-! ## Shell volumes in one block -/

/-- A set trapped between two concentric radii has volume at most the volume of
the spherical shell it sits in. -/
public theorem measureReal_le_shell {p : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin p))]
    {A : Set (EuclideanSpace ℝ (Fin p))} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hAR : ∀ u ∈ A, ‖u‖ ≤ R) (hAr : ∀ u ∈ A, r ≤ ‖u‖) :
    (volume A).toReal ≤ (R ^ p - r ^ p) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal := by
  set V : ENNReal := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1) with hV
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hsubR : A ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) R := by
    intro u hu
    simpa [Metric.mem_closedBall, dist_zero_right] using hAR u hu
  have hballR : Metric.ball (0 : EuclideanSpace ℝ (Fin p)) r ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) R := by
    exact (Metric.ball_subset_closedBall).trans (Metric.closedBall_subset_closedBall hrR)
  have hdisj : Disjoint A (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) r) := by
    rw [Set.disjoint_left]
    intro u huA huB
    have h1 : ‖u‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using huB
    exact absurd (hAr u huA) (not_le.mpr h1)
  have hunion : volume (A ∪ Metric.ball (0 : EuclideanSpace ℝ (Fin p)) r) = volume A + volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) r) :=
    measure_union hdisj measurableSet_ball
  have hle : volume A + volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) r) ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) R) := by
    rw [← hunion]
    exact measure_mono (Set.union_subset hsubR hballR)
  have hclosed : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) R) = ENNReal.ofReal (R ^ p) * V := by
    rw [Measure.addHaar_closedBall volume (0 : EuclideanSpace ℝ (Fin p)) (hr.trans hrR), finrank_euclideanSpace_fin]
  have hopen : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) r) = ENNReal.ofReal (r ^ p) * V := by
    rw [Measure.addHaar_ball volume (0 : EuclideanSpace ℝ (Fin p)) hr, finrank_euclideanSpace_fin]
  have hAtop : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hclosed]; finiteness) (measure_mono hsubR)
  rw [hclosed, hopen] at hle
  have := ENNReal.toReal_mono (by finiteness) hle
  rw [ENNReal.toReal_add hAtop (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr p),
    ENNReal.toReal_ofReal (pow_nonneg (hr.trans hrR) p)] at this
  nlinarith [this]

/-- **The level-uniform slice estimate.**  In a block of dimension at least two,
the set of `u` with `‖u‖ ≤ δ` whose squared norm lies within `ε` of an arbitrary
level `a` has volume at most a constant multiple of `ε`, and the constant does
not depend on `a`. -/
public theorem measureReal_sliceBand_le {p : ℕ} (hp : 2 ≤ p) {δ ε a : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    (volume {u : EuclideanSpace ℝ (Fin p) | ‖u‖ ≤ δ ∧ |‖u‖ ^ 2 - a| ≤ ε}).toReal
      ≤ 2 * (p : ℝ) * δ ^ (p - 2) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have hmax : max (0:ℝ) (a - ε) ≤ max (0:ℝ) (a + ε) := max_le_max le_rfl (by linarith)
  set sm : ℝ := min (δ ^ 2) (max 0 (a - ε)) with hsm
  set sp : ℝ := min (δ ^ 2) (max 0 (a + ε)) with hsp
  have hsm0 : 0 ≤ sm := le_min (sq_nonneg δ) (le_max_left _ _)
  have hsp0 : 0 ≤ sp := le_min (sq_nonneg δ) (le_max_left _ _)
  have hss : sm ≤ sp := min_le_min le_rfl hmax
  have hgap : sp - sm ≤ 2 * ε := by
    rw [hsm, hsp]
    simp only [min_def, max_def]
    split_ifs <;> linarith
  set r : ℝ := Real.sqrt sm with hrdef
  set R : ℝ := Real.sqrt sp with hRdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrR : r ≤ R := Real.sqrt_le_sqrt hss
  have hRδ : R ≤ δ := by
    rw [hRdef]
    calc Real.sqrt sp ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt (min_le_left _ _)
      _ = δ := by rw [Real.sqrt_sq hδ]
  have hr2 : r ^ 2 = sm := Real.sq_sqrt hsm0
  have hR2 : R ^ 2 = sp := Real.sq_sqrt hsp0
  have hV : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)).toReal :=
    ENNReal.toReal_nonneg
  have hshell := measureReal_le_shell (p := k + 2)
    (A := {u : EuclideanSpace ℝ (Fin (k + 2)) | ‖u‖ ≤ δ ∧ |‖u‖ ^ 2 - a| ≤ ε})
    hr0 hrR ?_ ?_
  · have hpow := pow_sub_pow_le_mul_sq_sub_sq k hr0 hrR hRδ
    rw [hr2, hR2] at hpow
    have hkδ : (0:ℝ) ≤ ((k : ℝ) + 2) * δ ^ k := by positivity
    have hbound : R ^ (k + 2) - r ^ (k + 2) ≤ ((k : ℝ) + 2) * δ ^ k * (2 * ε) := by
      refine hpow.trans ?_
      exact mul_le_mul_of_nonneg_left hgap hkδ
    have := mul_le_mul_of_nonneg_right hbound hV
    refine hshell.trans (this.trans (le_of_eq ?_))
    push_cast
    ring
  · rintro u ⟨hu1, hu2⟩
    have habs := abs_le.mp hu2
    have h1 : ‖u‖ ^ 2 ≤ max 0 (a + ε) := le_max_of_le_right (by linarith [habs.2])
    have h2 : ‖u‖ ^ 2 ≤ δ ^ 2 := by nlinarith [norm_nonneg u]
    have h3 : ‖u‖ ^ 2 ≤ sp := le_min h2 h1
    calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
      _ ≤ Real.sqrt sp := Real.sqrt_le_sqrt h3
  · rintro u ⟨hu1, hu2⟩
    have habs := abs_le.mp hu2
    have h1 : max (0:ℝ) (a - ε) ≤ ‖u‖ ^ 2 :=
      max_le (sq_nonneg _) (by linarith [habs.1])
    have h3 : sm ≤ ‖u‖ ^ 2 := (min_le_right _ _).trans h1
    calc r = Real.sqrt sm := hrdef
      _ ≤ Real.sqrt (‖u‖ ^ 2) := Real.sqrt_le_sqrt h3
      _ = ‖u‖ := Real.sqrt_sq (norm_nonneg u)

/-- The ENNReal form of the slice estimate. -/
public theorem measure_sliceBand_le {p : ℕ} (hp : 2 ≤ p) {δ ε a : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume {u : EuclideanSpace ℝ (Fin p) | ‖u‖ ≤ δ ∧ |‖u‖ ^ 2 - a| ≤ ε}
      ≤ ENNReal.ofReal (2 * (p : ℝ) * δ ^ (p - 2) * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal) := by
  have hsub : {u : EuclideanSpace ℝ (Fin p) | ‖u‖ ≤ δ ∧ |‖u‖ ^ 2 - a| ≤ ε}
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) δ := by
    rintro u ⟨hu, -⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hu
  have htop : volume {u : EuclideanSpace ℝ (Fin p) | ‖u‖ ≤ δ ∧ |‖u‖ ^ 2 - a| ≤ ε} ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hsub)
  have hnn : (0:ℝ) ≤ 2 * (p : ℝ) * δ ^ (p - 2) * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal := by
    have : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal :=
      ENNReal.toReal_nonneg
    have hδk : (0:ℝ) ≤ δ ^ (p - 2) := pow_nonneg hδ _
    positivity
  rw [ENNReal.le_ofReal_iff_toReal_le htop hnn]
  exact measureReal_sliceBand_le hp hδ hε

/-! ## The shifted band -/

/-- The nondegenerate indefinite form `‖u‖² - ‖v‖²` of signature `(p, q)`, read
on the ambient space through the coordinate split.  `modelBandGerm` is its
absolute value; this module needs the signed form, because a band around a
nonzero level is not a sublevel set of the germ. -/
@[expose] public noncomputable def modelBandForm (p q : ℕ)
    (w : EuclideanSpace ℝ (Fin (p + q))) : ℝ :=
  ‖((splitLE p q).symm w).1‖ ^ 2 - ‖((splitLE p q).symm w).2‖ ^ 2

public theorem modelBandGerm_eq_abs_form (p q : ℕ) (w : EuclideanSpace ℝ (Fin (p + q))) :
    modelBandGerm p q w = |modelBandForm p q w| := rfl

/-- Evaluated on a split pair, the form is what it looks like. -/
public theorem modelBandForm_splitLE (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) :
    modelBandForm p q (splitLE p q (u, v)) = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  simp [modelBandForm]

/-- **The band of half-width `ε` around the level `c`**, inside the closed ball
of radius `δ` about the origin. -/
@[expose] public noncomputable def shiftedBandSet (p q : ℕ) (c δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin (p + q))) :=
  {w | ‖w‖ ≤ δ ∧ |modelBandForm p q w - c| ≤ ε}

public theorem continuous_modelBandForm (p q : ℕ) : Continuous (modelBandForm p q) := by
  have hc : Continuous (fun w : EuclideanSpace ℝ (Fin (p + q)) => (splitLE p q).symm w) :=
    LinearMap.continuous_of_finiteDimensional (splitLE p q).symm.toLinearMap
  exact ((continuous_fst.comp hc).norm.pow 2).sub ((continuous_snd.comp hc).norm.pow 2)

public theorem isClosed_shiftedBandSet (p q : ℕ) (c δ ε : ℝ) :
    IsClosed (shiftedBandSet p q c δ ε) :=
  (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le (((continuous_modelBandForm p q).sub continuous_const).abs) continuous_const)

public theorem measurableSet_shiftedBandSet (p q : ℕ) (c δ ε : ℝ) :
    MeasurableSet (shiftedBandSet p q c δ ε) :=
  (isClosed_shiftedBandSet p q c δ ε).measurableSet

/-- The band read in split coordinates and enlarged from the Euclidean ball to
the product window `‖u‖ ≤ δ`, `‖v‖ ≤ δ`.  The enlargement costs a constant and
buys a set Fubini can slice. -/
@[expose] public noncomputable def bandWindow (p q : ℕ) (c δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
  {z | ‖z.1‖ ≤ δ ∧ ‖z.2‖ ≤ δ ∧ |‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 - c| ≤ ε}

public theorem measurableSet_bandWindow (p q : ℕ) (c δ ε : ℝ) :
    MeasurableSet (bandWindow p q c δ ε) := by
  refine IsClosed.measurableSet ?_
  refine (isClosed_le (continuous_fst.norm) continuous_const).inter ?_
  refine (isClosed_le (continuous_snd.norm) continuous_const).inter ?_
  exact isClosed_le
    ((((continuous_fst.norm).pow 2).sub ((continuous_snd.norm).pow 2)).sub
      continuous_const).abs continuous_const

/-- In split coordinates the Euclidean band sits inside the product window. -/
public theorem preimage_shiftedBandSet_subset (p q : ℕ) (c δ ε : ℝ) :
    (⇑(splitLE p q)) ⁻¹' (shiftedBandSet p q c δ ε) ⊆ bandWindow p q c δ ε := by
  rintro ⟨u, v⟩ ⟨hz1, hz2⟩
  have hn := norm_sq_splitLE p q u v
  have hsq : ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ δ ^ 2 := by
    rw [← hn]; nlinarith [norm_nonneg (splitLE p q (u, v))]
  rw [modelBandForm_splitLE] at hz2
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hz1
  refine ⟨?_, ?_, hz2⟩
  · show ‖u‖ ≤ δ
    nlinarith [norm_nonneg u, norm_nonneg v]
  · show ‖v‖ ≤ δ
    nlinarith [norm_nonneg u, norm_nonneg v]

/-- **The level-uniform band estimate, in split coordinates.**  Fubini in the
`p`-block, with the slice estimate applied at the level `c + ‖v‖²`. -/
public theorem measure_bandWindow_le (p q : ℕ) (hp : 2 ≤ p) (c : ℝ) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume (bandWindow p q c δ ε)
      ≤ ENNReal.ofReal (2 * (p : ℝ) * δ ^ (p - 2) * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal)
        * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin q)) δ) := by
  have hfub : volume (bandWindow p q c δ ε)
      = ∫⁻ v : EuclideanSpace ℝ (Fin q),
          volume ((fun u => (u, v)) ⁻¹' bandWindow p q c δ ε) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_apply_symm (measurableSet_bandWindow p q c δ ε)
  have hslice : ∀ v : EuclideanSpace ℝ (Fin q),
      volume ((fun u => (u, v)) ⁻¹' bandWindow p q c δ ε)
        ≤ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin q)) δ).indicator
            (fun _ => ENNReal.ofReal (2 * (p : ℝ) * δ ^ (p - 2) * ε *
              (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal)) v := by
    intro v
    by_cases hv : ‖v‖ ≤ δ
    · have hmem : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin q)) δ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hv
      rw [Set.indicator_of_mem hmem]
      refine le_trans (measure_mono ?_)
        (measure_sliceBand_le (p := p) hp (a := c + ‖v‖ ^ 2) hδ hε)
      rintro u ⟨hu1, -, hu3⟩
      refine ⟨hu1, ?_⟩
      have hrw : ‖u‖ ^ 2 - (c + ‖v‖ ^ 2) = ‖u‖ ^ 2 - ‖v‖ ^ 2 - c := by ring
      rw [hrw]
      exact hu3
    · have hempty : ((fun u => (u, v)) ⁻¹' bandWindow p q c δ ε) = ∅ := by
        ext u
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, hv', -⟩
        exact hv hv'
      rw [hempty]
      simp
  calc volume (bandWindow p q c δ ε)
      = ∫⁻ v : EuclideanSpace ℝ (Fin q),
          volume ((fun u => (u, v)) ⁻¹' bandWindow p q c δ ε) := hfub
    _ ≤ ∫⁻ _v : EuclideanSpace ℝ (Fin q),
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin q)) δ).indicator
            (fun _ => ENNReal.ofReal (2 * (p : ℝ) * δ ^ (p - 2) * ε *
              (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal)) _v :=
        lintegral_mono hslice
    _ = _ := lintegral_indicator_const measurableSet_closedBall _

/-- The closed ball's volume in one block, in real form. -/
public theorem measureReal_closedBall_eq (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)).toReal
      = δ ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  rw [Measure.addHaar_closedBall volume (0 : EuclideanSpace ℝ (Fin n)) hδ,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hδ n)]

/-- **The level-uniform band estimate on the ambient space.** -/
public theorem measure_shiftedBandSet_le (p q : ℕ) (hp : 2 ≤ p) (c : ℝ) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume (shiftedBandSet p q c δ ε)
      ≤ ENNReal.ofReal (2 * (p : ℝ) * δ ^ (p - 2) * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal)
        * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin q)) δ) := by
  have hpre := (measurePreserving_splitLE p q).measure_preimage
    (measurableSet_shiftedBandSet p q c δ ε).nullMeasurableSet
  rw [← hpre]
  exact le_trans (measure_mono (preimage_shiftedBandSet_subset p q c δ ε))
    (measure_bandWindow_le p q hp c hδ hε)

/-- The level-uniform upper constant of signature `(p, q)` at radius `δ`.  It
depends on the radius and on the two block dimensions, and on nothing else — in
particular not on the level `c`, which is the whole point. -/
@[expose] public noncomputable def shiftedBandConst (p q : ℕ) (δ : ℝ) : ℝ :=
  2 * (p : ℝ) * δ ^ (p - 2) * δ ^ q *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal

/-- The real-valued volume of the band of half-width `ε` around the level `c`,
inside the closed ball of radius `δ` about the origin. -/
@[expose] public noncomputable def shiftedBandVolume (p q : ℕ) (c δ ε : ℝ) : ℝ :=
  (volume (shiftedBandSet p q c δ ε)).toReal

public theorem shiftedBandConst_nonneg (p q : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ shiftedBandConst p q δ := by
  have h1 : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal :=
    ENNReal.toReal_nonneg
  have h2 : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal :=
    ENNReal.toReal_nonneg
  have h3 : (0:ℝ) ≤ δ ^ (p - 2) := pow_nonneg hδ _
  have h4 : (0:ℝ) ≤ δ ^ q := pow_nonneg hδ _
  rw [shiftedBandConst]
  positivity

public theorem shiftedBandConst_pos (p q : ℕ) [NeZero p] {δ : ℝ} (hδ : 0 < δ) :
    0 < shiftedBandConst p q δ := by
  have h1 : (0:ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal := by
    have := unitBallReal_pos p
    rwa [measureReal_def] at this
  have h2 : (0:ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal := by
    have := unitBallReal_pos q
    rwa [measureReal_def] at this
  have h3 : (0:ℝ) < δ ^ (p - 2) := pow_pos hδ _
  have h4 : (0:ℝ) < δ ^ q := pow_pos hδ _
  have hp : (0:ℝ) < (p : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [shiftedBandConst]
  positivity

/-- **The level-uniform upper bound.**  With the first block of dimension at
least two, the band of half-width `ε` around *any* level `c` has volume at most
`shiftedBandConst p q δ * ε`.  The constant is free of `c`: that is what makes
the bound level-uniform rather than a family of bounds indexed by the level. -/
public theorem shiftedBandVolume_le (p q : ℕ) (hp : 2 ≤ p) (c : ℝ) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    shiftedBandVolume p q c δ ε ≤ shiftedBandConst p q δ * ε := by
  have hVp : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal :=
    ENNReal.toReal_nonneg
  have hnn : (0:ℝ) ≤ 2 * (p : ℝ) * δ ^ (p - 2) * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal := by
    have h3 : (0:ℝ) ≤ δ ^ (p - 2) := pow_nonneg hδ _
    positivity
  have hle := measure_shiftedBandSet_le p q hp c hδ hε
  have hfin : ENNReal.ofReal (2 * (p : ℝ) * δ ^ (p - 2) * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal)
      * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin q)) δ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have hmono := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn,
    measureReal_closedBall_eq q hδ] at hmono
  refine hmono.trans (le_of_eq ?_)
  rw [shiftedBandConst]
  ring

/-! ## The block swap, and the `p = 1` case -/

public theorem norm_euclideanSwap (p q : ℕ) (w : EuclideanSpace ℝ (Fin (p + q))) :
    ‖euclideanSwap p q w‖ = ‖w‖ := by
  have h := (isometry_euclideanSwap p q).dist_eq w 0
  rwa [euclideanSwap_zero, dist_zero_right, dist_zero_right] at h

public theorem modelBandForm_euclideanSwap (p q : ℕ) (w : EuclideanSpace ℝ (Fin (p + q))) :
    modelBandForm q p (euclideanSwap p q w) = -modelBandForm p q w := by
  obtain ⟨⟨u, v⟩, rfl⟩ := (euclideanProdEquiv p q).surjective w
  rw [euclideanSwap_apply, ← coe_splitLE, ← coe_splitLE, modelBandForm_splitLE,
    modelBandForm_splitLE]
  ring

/-- The band around `c` of signature `(p, q)` is the band around `-c` of
signature `(q, p)`, read through the block swap. -/
public theorem preimage_shiftedBandSet_euclideanSwap (p q : ℕ) (c δ ε : ℝ) :
    (⇑(euclideanSwap p q)) ⁻¹' (shiftedBandSet q p (-c) δ ε) = shiftedBandSet p q c δ ε := by
  ext w
  simp only [Set.mem_preimage, shiftedBandSet, Set.mem_ofPred_eq, norm_euclideanSwap,
    modelBandForm_euclideanSwap]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : -modelBandForm p q w - -c = -(modelBandForm p q w - c) := by ring
    rwa [this, abs_neg] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : -modelBandForm p q w - -c = -(modelBandForm p q w - c) := by ring
    rwa [this, abs_neg]

public theorem shiftedBandVolume_swap (p q : ℕ) (c δ ε : ℝ) :
    shiftedBandVolume p q c δ ε = shiftedBandVolume q p (-c) δ ε := by
  rw [shiftedBandVolume, shiftedBandVolume, ← preimage_shiftedBandSet_euclideanSwap p q c δ ε,
    (measurePreserving_euclideanSwap p q).measure_preimage
      (measurableSet_shiftedBandSet q p (-c) δ ε).nullMeasurableSet]

/-- **The level-uniform upper bound, every signature off the two-dimensional
boundary.**  Both blocks nonempty and `3 ≤ p + q` forces one block to have
dimension at least two, and the form is antisymmetric under exchanging the
blocks, so the estimate can always be run with the larger block outside.  This
is the same block swap `hasLocalVolumeOrder_modelBandGerm_of_three_le` uses at
level zero. -/
public theorem shiftedBandVolume_le_of_three_le (p q : ℕ) [NeZero p] [NeZero q]
    (hpq : 3 ≤ p + q) (c : ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    shiftedBandVolume p q c δ ε ≤ (shiftedBandConst p q δ + shiftedBandConst q p δ) * ε := by
  have hpq0 : (0:ℝ) ≤ shiftedBandConst p q δ := shiftedBandConst_nonneg p q hδ
  have hqp0 : (0:ℝ) ≤ shiftedBandConst q p δ := shiftedBandConst_nonneg q p hδ
  rcases Nat.lt_or_ge p 2 with hp | hp
  · have hq2 : 2 ≤ q := by
      have := Nat.pos_of_ne_zero (NeZero.ne p); omega
    rw [shiftedBandVolume_swap p q c δ ε]
    refine (shiftedBandVolume_le q p hq2 (-c) hδ hε).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hε
  · refine (shiftedBandVolume_le p q hp c hδ hε).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hε

public theorem shiftedBandConst_mono (p q : ℕ) {δ δ' : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ δ') :
    shiftedBandConst p q δ ≤ shiftedBandConst p q δ' := by
  have h1 : δ ^ (p - 2) ≤ δ' ^ (p - 2) := pow_le_pow_left₀ hδ h _
  have h2 : δ ^ q ≤ δ' ^ q := pow_le_pow_left₀ hδ h _
  have h3 : (0:ℝ) ≤ δ ^ (p - 2) := pow_nonneg hδ _
  have h4 : (0:ℝ) ≤ δ ^ q := pow_nonneg hδ _
  have h5 : (0:ℝ) ≤ δ' ^ (p - 2) := pow_nonneg (hδ.trans h) _
  have hVp : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal :=
    ENNReal.toReal_nonneg
  have hVq : (0:ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal :=
    ENNReal.toReal_nonneg
  rw [shiftedBandConst, shiftedBandConst]
  gcongr

/-- **The level-uniform upper bound, packaged.**  One constant serves every
level `c` and every radius up to `δ₀`. -/
public theorem exists_shiftedBandVolume_upper (p q : ℕ) [NeZero p] [NeZero q]
    (hpq : 3 ≤ p + q) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ ε : ℝ, 0 ≤ ε →
      shiftedBandVolume p q c δ ε ≤ C * ε := by
  refine ⟨shiftedBandConst p q δ₀ + shiftedBandConst q p δ₀, ?_, ?_⟩
  · have h1 := shiftedBandConst_pos p q hδ₀
    have h2 := shiftedBandConst_pos q p hδ₀
    linarith
  · intro c δ hδ hδ₀' ε hε
    refine (shiftedBandVolume_le_of_three_le p q hpq c hδ.le hε).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hε
    exact add_le_add (shiftedBandConst_mono p q hδ.le hδ₀')
      (shiftedBandConst_mono q p hδ.le hδ₀')

/-! ## The matching lower bound

The upper bound is the half the level-uniformity is about, and it holds for
every level.  A lower bound cannot: at a level the form does not attain inside
the ball the band is empty.  The statement below therefore restricts the level
to `|c| ≤ δ²/32`, which is enough room to place a whole annulus of the second
block inside the window, and asks `ε ≤ δ²/4` so that the shell it sweeps in the
first block still fits.
-/

/-- **The volume of a spherical shell.**  A concentric annulus has exactly the
volume the two ball formulas predict. -/
public theorem measure_annulus {n : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin n))] {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    volume {u : EuclideanSpace ℝ (Fin n) | r ≤ ‖u‖ ∧ ‖u‖ ≤ R}
      = ENNReal.ofReal (R ^ n - r ^ n)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hR : (0:ℝ) ≤ R := hr.trans hrR
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hcover : {u : EuclideanSpace ℝ (Fin n) | r ≤ ‖u‖ ∧ ‖u‖ ≤ R}
      ∪ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
      = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    ext u
    simp only [Set.mem_union, Set.mem_ofPred_eq, Metric.mem_ball, Metric.mem_closedBall,
      dist_zero_right]
    constructor
    · rintro (⟨-, h2⟩ | h)
      · exact h2
      · exact h.le.trans hrR
    · intro h
      rcases le_or_gt r ‖u‖ with h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact Or.inr h'
  have hdisj : Disjoint {u : EuclideanSpace ℝ (Fin n) | r ≤ ‖u‖ ∧ ‖u‖ ≤ R}
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    rw [Set.disjoint_left]
    rintro u ⟨h1, -⟩ h2
    have : ‖u‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using h2
    exact absurd h1 (not_le.mpr this)
  have hsplit : volume {u : EuclideanSpace ℝ (Fin n) | r ≤ ‖u‖ ∧ ‖u‖ ≤ R}
      + volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := by
    rw [← hcover, measure_union hdisj measurableSet_ball]
  rw [Measure.addHaar_closedBall volume (0 : EuclideanSpace ℝ (Fin n)) hR,
    finrank_euclideanSpace_fin] at hsplit
  rw [Measure.addHaar_ball volume (0 : EuclideanSpace ℝ (Fin n)) hr,
    finrank_euclideanSpace_fin] at hsplit
  have hpow : r ^ n ≤ R ^ n := pow_le_pow_left₀ hr hrR n
  have hofReal : ENNReal.ofReal (R ^ n)
      = ENNReal.ofReal (R ^ n - r ^ n) + ENNReal.ofReal (r ^ n) := by
    rw [← ENNReal.ofReal_add (by linarith) (pow_nonneg hr n)]
    congr 1
    ring
  rw [hofReal, add_mul] at hsplit
  exact (ENNReal.add_left_inj
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop)).mp hsplit

/-- One term of the difference-of-powers expansion, kept as a lower bound. -/
public theorem pow_succ_sub_pow_succ_ge (m : ℕ) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    y ^ m * (x - y) ≤ x ^ (m + 1) - y ^ (m + 1) := by
  have hx : 0 ≤ x := hy.trans hyx
  have h1 : y ^ m ≤ x ^ m := pow_le_pow_left₀ hy hyx m
  have h2 : x * y ^ m ≤ x * x ^ m := mul_le_mul_of_nonneg_left h1 hx
  have e1 : x ^ (m + 1) = x * x ^ m := by ring
  have e2 : y ^ (m + 1) = y * y ^ m := by ring
  rw [e1, e2]
  nlinarith [h2]

/-- **The shell swept in the first block.**  For a level `a` bounded away from
zero and a shell that still fits in the ball of radius `δ`, the set where `‖u‖²`
runs over `[a, a + ε]` has volume at least a fixed multiple of `ε`. -/
public theorem measure_shell_ge {p : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin p))] (hp : 1 ≤ p)
    {a δ ε : ℝ} (hδ : 0 < δ) (ha : δ ^ 2 / 36 ≤ a) (haε : a + ε ≤ δ ^ 2) (hε : 0 ≤ ε) :
    ENNReal.ofReal ((δ / 6) ^ (p - 1) * (ε / (2 * δ)))
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)
      ≤ volume {u : EuclideanSpace ℝ (Fin p) | a ≤ ‖u‖ ^ 2 ∧ ‖u‖ ^ 2 ≤ a + ε} := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hδ2 : (0:ℝ) < δ ^ 2 := by positivity
  have ha0 : 0 < a := by linarith
  have haε0 : (0:ℝ) ≤ a + ε := by linarith
  set r : ℝ := Real.sqrt a with hrdef
  set R : ℝ := Real.sqrt (a + ε) with hRdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrR : r ≤ R := Real.sqrt_le_sqrt (by linarith)
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha0.le
  have hR2 : R ^ 2 = a + ε := Real.sq_sqrt haε0
  have hRδ : R ≤ δ := by
    rw [hRdef]
    calc Real.sqrt (a + ε) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt haε
      _ = δ := Real.sqrt_sq hδ.le
  have hr6 : δ / 6 ≤ r := by
    have h1 : (δ / 6) ^ 2 ≤ a := by nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hset : {u : EuclideanSpace ℝ (Fin (m + 1)) | a ≤ ‖u‖ ^ 2 ∧ ‖u‖ ^ 2 ≤ a + ε}
      = {u : EuclideanSpace ℝ (Fin (m + 1)) | r ≤ ‖u‖ ∧ ‖u‖ ≤ R} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have h3 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (norm_nonneg u)] at h3
      · have h3 := Real.sqrt_le_sqrt h2
        rwa [Real.sqrt_sq (norm_nonneg u)] at h3
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [norm_nonneg u], by nlinarith [norm_nonneg u]⟩
  rw [hset, measure_annulus hr0 hrR]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have hsum : R + r ≤ 2 * δ := by linarith
  have hpos : (0:ℝ) < R + r := by linarith
  have hRr : (R - r) * (R + r) = ε := by
    have e : (R - r) * (R + r) = R ^ 2 - r ^ 2 := by ring
    rw [e, hR2, hr2]; ring
  have hdiff : ε / (2 * δ) ≤ R - r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sub_nonneg.mpr hrR]
  have hkey : r ^ m * (R - r) ≤ R ^ (m + 1) - r ^ (m + 1) :=
    pow_succ_sub_pow_succ_ge m hr0 hrR
  have h6 : (δ / 6) ^ m ≤ r ^ m := pow_le_pow_left₀ (by positivity) hr6 m
  have hεd : (0:ℝ) ≤ ε / (2 * δ) := by positivity
  simp only [Nat.add_sub_cancel]
  calc (δ / 6) ^ m * (ε / (2 * δ))
      ≤ r ^ m * (ε / (2 * δ)) := mul_le_mul_of_nonneg_right h6 hεd
    _ ≤ r ^ m * (R - r) := mul_le_mul_of_nonneg_left hdiff (pow_nonneg hr0 m)
    _ ≤ R ^ (m + 1) - r ^ (m + 1) := hkey

public theorem nontrivial_euclideanSpace {n : ℕ} (hn : 0 < n) :
    Nontrivial (EuclideanSpace ℝ (Fin n)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  infer_instance

/-- The subset of the band that the lower bound sweeps: the second block runs
over the annulus `δ/4 ≤ ‖v‖ ≤ δ/2`, and for each such `v` the first block runs
over the shell `‖u‖² ∈ [c + ‖v‖², c + ‖v‖² + ε]`. -/
@[expose] public noncomputable def bandCore (p q : ℕ) (c δ ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
  {z | δ / 4 ≤ ‖z.2‖ ∧ ‖z.2‖ ≤ δ / 2 ∧
    c + ‖z.2‖ ^ 2 ≤ ‖z.1‖ ^ 2 ∧ ‖z.1‖ ^ 2 ≤ c + ‖z.2‖ ^ 2 + ε}

public theorem measurableSet_bandCore (p q : ℕ) (c δ ε : ℝ) :
    MeasurableSet (bandCore p q c δ ε) := by
  refine IsClosed.measurableSet ?_
  refine (isClosed_le continuous_const (continuous_snd.norm)).inter ?_
  refine (isClosed_le (continuous_snd.norm) continuous_const).inter ?_
  exact (isClosed_le (continuous_const.add ((continuous_snd.norm).pow 2))
      ((continuous_fst.norm).pow 2)).inter
    (isClosed_le ((continuous_fst.norm).pow 2)
      ((continuous_const.add ((continuous_snd.norm).pow 2)).add continuous_const))

/-- The core sits inside the band: the annulus and the shell are chosen so that
the Euclidean radius stays below `δ` and the form stays within `ε` of `c`. -/
public theorem bandCore_subset (p q : ℕ) {c δ ε : ℝ} (hδ : 0 < δ)
    (hc : |c| ≤ δ ^ 2 / 32) (hε0 : 0 ≤ ε) (hε : ε ≤ δ ^ 2 / 4) :
    bandCore p q c δ ε ⊆ (⇑(splitLE p q)) ⁻¹' (shiftedBandSet p q c δ ε) := by
  rintro ⟨u, v⟩ ⟨hv1, hv2, hu1, hu2⟩
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hv0 : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
  have hvsq : ‖v‖ ^ 2 ≤ δ ^ 2 / 4 := by nlinarith
  have husq : ‖u‖ ^ 2 ≤ δ ^ 2 / 32 + δ ^ 2 / 4 + δ ^ 2 / 4 := by
    nlinarith
  have hn := norm_sq_splitLE p q u v
  have hnorm : ‖splitLE p q (u, v)‖ ≤ δ := by
    have h1 : ‖splitLE p q (u, v)‖ ^ 2 ≤ δ ^ 2 := by
      rw [hn]
      nlinarith
    nlinarith [norm_nonneg (splitLE p q (u, v))]
  refine ⟨hnorm, ?_⟩
  rw [modelBandForm_splitLE]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Fubini for the core.**  The annulus in the second block, times the shell
estimate in the first. -/
public theorem measure_bandCore_ge (p q : ℕ) [NeZero q] (hp : 2 ≤ p) {c δ ε : ℝ}
    (hδ : 0 < δ) (hc : |c| ≤ δ ^ 2 / 32) (hε0 : 0 ≤ ε) (hε : ε ≤ δ ^ 2 / 4) :
    ENNReal.ofReal ((δ / 6) ^ (p - 1) * (ε / (2 * δ)))
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)
        * (ENNReal.ofReal ((δ / 2) ^ q - (δ / 4) ^ q)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1))
      ≤ volume (bandCore p q c δ ε) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin p)) := nontrivial_euclideanSpace (by omega)
  have : Nontrivial (EuclideanSpace ℝ (Fin q)) :=
    nontrivial_euclideanSpace (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hann : MeasurableSet {v : EuclideanSpace ℝ (Fin q) | δ / 4 ≤ ‖v‖ ∧ ‖v‖ ≤ δ / 2} :=
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet
  have hfub : volume (bandCore p q c δ ε)
      = ∫⁻ v : EuclideanSpace ℝ (Fin q),
          volume ((fun u => (u, v)) ⁻¹' bandCore p q c δ ε) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_apply_symm (measurableSet_bandCore p q c δ ε)
  have hslice : ∀ v : EuclideanSpace ℝ (Fin q),
      {v : EuclideanSpace ℝ (Fin q) | δ / 4 ≤ ‖v‖ ∧ ‖v‖ ≤ δ / 2}.indicator
          (fun _ => ENNReal.ofReal ((δ / 6) ^ (p - 1) * (ε / (2 * δ)))
            * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)) v
        ≤ volume ((fun u => (u, v)) ⁻¹' bandCore p q c δ ε) := by
    intro v
    by_cases hv : v ∈ {v : EuclideanSpace ℝ (Fin q) | δ / 4 ≤ ‖v‖ ∧ ‖v‖ ≤ δ / 2}
    · obtain ⟨hv1, hv2⟩ := hv
      rw [Set.indicator_of_mem (by exact ⟨hv1, hv2⟩)]
      have heq : ((fun u => (u, v)) ⁻¹' bandCore p q c δ ε)
          = {u : EuclideanSpace ℝ (Fin p) |
              c + ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 ∧ ‖u‖ ^ 2 ≤ c + ‖v‖ ^ 2 + ε} := by
        ext u
        simp only [Set.mem_preimage, bandCore, Set.mem_ofPred_eq]
        exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hv1, hv2, h.1, h.2⟩⟩
      rw [heq]
      have hv0 : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
      refine measure_shell_ge (by omega) hδ ?_ ?_ hε0
      · nlinarith
      · nlinarith
    · have hempty : ((fun u => (u, v)) ⁻¹' bandCore p q c δ ε) = ∅ := by
        ext u
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, bandCore,
          Set.mem_ofPred_eq]
        rintro ⟨h1, h2, -, -⟩
        exact hv ⟨h1, h2⟩
      rw [Set.indicator_of_notMem hv]
      exact zero_le
  calc ENNReal.ofReal ((δ / 6) ^ (p - 1) * (ε / (2 * δ)))
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)
        * (ENNReal.ofReal ((δ / 2) ^ q - (δ / 4) ^ q)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1))
      = ENNReal.ofReal ((δ / 6) ^ (p - 1) * (ε / (2 * δ)))
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)
        * volume {v : EuclideanSpace ℝ (Fin q) | δ / 4 ≤ ‖v‖ ∧ ‖v‖ ≤ δ / 2} := by
        rw [measure_annulus (by positivity) (by linarith)]
    _ = ∫⁻ _v : EuclideanSpace ℝ (Fin q),
          {v : EuclideanSpace ℝ (Fin q) | δ / 4 ≤ ‖v‖ ∧ ‖v‖ ≤ δ / 2}.indicator
            (fun _ => ENNReal.ofReal ((δ / 6) ^ (p - 1) * (ε / (2 * δ)))
              * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)) _v :=
        (lintegral_indicator_const hann _).symm
    _ ≤ ∫⁻ v : EuclideanSpace ℝ (Fin q),
          volume ((fun u => (u, v)) ⁻¹' bandCore p q c δ ε) := lintegral_mono hslice
    _ = volume (bandCore p q c δ ε) := hfub.symm

/-- The level-uniform lower constant: the annulus in the second block times the
shell in the first. -/
@[expose] public noncomputable def shiftedBandLowerConst (p q : ℕ) (δ : ℝ) : ℝ :=
  (δ / 6) ^ (p - 1) / (2 * δ) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal *
    (((δ / 2) ^ q - (δ / 4) ^ q) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal)

public theorem shiftedBandSet_subset_closedBall (p q : ℕ) (c δ ε : ℝ) :
    shiftedBandSet p q c δ ε ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (p + q))) δ := by
  rintro w ⟨hw, -⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using hw

public theorem measure_shiftedBandSet_ne_top (p q : ℕ) (c δ ε : ℝ) :
    volume (shiftedBandSet p q c δ ε) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_closedBall_lt_top.ne
    (measure_mono (shiftedBandSet_subset_closedBall p q c δ ε))

/-- **The matching lower bound.**  For a level close enough to zero relative to
the radius, and a half-width small enough that the swept shell still fits, the
band has volume at least `shiftedBandLowerConst p q δ * ε`.

Unlike the upper bound this cannot hold for every `c`: at a level the form does
not attain inside the ball the band is empty, so a lower bound has to restrict
the level.  `|c| ≤ δ²/32` is one such restriction, chosen so that a whole
annulus of the second block stays inside the window. -/
public theorem shiftedBandVolume_ge (p q : ℕ) [NeZero q] (hp : 2 ≤ p) {c δ ε : ℝ}
    (hδ : 0 < δ) (hc : |c| ≤ δ ^ 2 / 32) (hε0 : 0 ≤ ε) (hε : ε ≤ δ ^ 2 / 4) :
    shiftedBandLowerConst p q δ * ε ≤ shiftedBandVolume p q c δ ε := by
  have hpre := (measurePreserving_splitLE p q).measure_preimage
    (measurableSet_shiftedBandSet p q c δ ε).nullMeasurableSet
  have hle : ENNReal.ofReal ((δ / 6) ^ (p - 1) * (ε / (2 * δ)))
      * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)
      * (ENNReal.ofReal ((δ / 2) ^ q - (δ / 4) ^ q)
        * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1))
      ≤ volume (shiftedBandSet p q c δ ε) := by
    refine (measure_bandCore_ge p q hp hδ hc hε0 hε).trans ?_
    rw [← hpre]
    exact measure_mono (bandCore_subset p q hδ hc hε0 hε)
  have hA : (0:ℝ) ≤ (δ / 6) ^ (p - 1) * (ε / (2 * δ)) := by positivity
  have hB : (0:ℝ) ≤ (δ / 2) ^ q - (δ / 4) ^ q := by
    have : (δ / 4) ^ q ≤ (δ / 2) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
    linarith
  have hmono := ENNReal.toReal_mono (measure_shiftedBandSet_ne_top p q c δ ε) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB] at hmono
  refine le_trans (le_of_eq ?_) hmono
  rw [shiftedBandLowerConst]
  ring

public theorem shiftedBandLowerConst_pos (p q : ℕ) [NeZero q] {δ : ℝ} (hδ : 0 < δ) :
    0 < shiftedBandLowerConst p q δ := by
  have h1 : (0:ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal := by
    have := unitBallReal_pos p
    rwa [measureReal_def] at this
  have h2 : (0:ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal := by
    have := unitBallReal_pos q
    rwa [measureReal_def] at this
  have h3 : (0:ℝ) < (δ / 6) ^ (p - 1) := by positivity
  have h4 : (δ / 4) ^ q < (δ / 2) ^ q :=
    pow_lt_pow_left₀ (by linarith) (by positivity) (NeZero.ne q)
  rw [shiftedBandLowerConst]
  have h5 : (0:ℝ) < (δ / 2) ^ q - (δ / 4) ^ q := by linarith
  have h6 : (0:ℝ) < 2 * δ := by linarith
  positivity

/-- The two constants are ordered, as a pair of two-sided bounds must be.  The
proof is the only one available: run both bounds at a level and a half-width the
lower bound admits, and divide. -/
public theorem shiftedBandLowerConst_le (p q : ℕ) [NeZero q] (hp : 2 ≤ p) {δ : ℝ}
    (hδ : 0 < δ) : shiftedBandLowerConst p q δ ≤ shiftedBandConst p q δ := by
  have hεpos : (0:ℝ) < δ ^ 2 / 4 := by positivity
  have hc : |(0:ℝ)| ≤ δ ^ 2 / 32 := by
    rw [abs_zero]; positivity
  have h1 := shiftedBandVolume_ge p q hp (c := 0) (δ := δ) (ε := δ ^ 2 / 4)
    hδ hc hεpos.le le_rfl
  have h2 := shiftedBandVolume_le p q hp 0 (δ := δ) (ε := δ ^ 2 / 4) hδ.le hεpos.le
  exact le_of_mul_le_mul_right (h1.trans h2) hεpos

/-- **The two-sided level-uniform statement.**  One pair of constants
`0 < c₁ ≤ c₂` and one radius bound: the upper bound holds at every level and
every radius below `δ₀`, and the lower bound holds at every level the band can
be nonempty for. -/
public theorem exists_shiftedBand_bounds (p q : ℕ) [NeZero p] [NeZero q] (hp : 2 ≤ p)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      (∀ c : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ ε : ℝ, 0 ≤ ε →
        shiftedBandVolume p q c δ ε ≤ c₂ * ε) ∧
      (∀ c : ℝ, |c| ≤ δ₀ ^ 2 / 32 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ₀ ^ 2 / 4 →
        c₁ * ε ≤ shiftedBandVolume p q c δ₀ ε) := by
  refine ⟨shiftedBandLowerConst p q δ₀, shiftedBandConst p q δ₀ + shiftedBandConst q p δ₀,
    shiftedBandLowerConst_pos p q hδ₀, ?_, ?_, ?_⟩
  · have h1 := shiftedBandLowerConst_le p q hp hδ₀
    have h2 := shiftedBandConst_nonneg q p hδ₀.le
    linarith
  · intro c δ hδ hδle ε hε
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    refine (shiftedBandVolume_le_of_three_le p q (by omega) c hδ.le hε).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hε
    exact add_le_add (shiftedBandConst_mono p q hδ.le hδle)
      (shiftedBandConst_mono q p hδ.le hδle)
  · intro c hc ε hε0 hε
    exact shiftedBandVolume_ge p q hp hδ₀ hc hε0 hε

end AISafetyAtlas.SingularLearning
