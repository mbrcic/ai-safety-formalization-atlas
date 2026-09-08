module

public import AISafetyAtlas.SingularLearning.FreeBlockBand
public import AISafetyAtlas.SingularLearning.PairTransfer

/-!
# The free block, read as a local pair

`FreeBlockBand.lean` proves the two-sided `Θ(ε)` band estimate for
`Q(ξ) + g(ζ)`, but on the **product** space `EuclideanSpace ℝ (Fin (p+q)) ×
EuclideanSpace ℝ (Fin s)` and inside a **product box** `‖ξ‖ ≤ δ ∧ ‖ζ‖ ≤ δ`.
`HasLocalVolumeOrder` of `LocalPair.lean` lives on a single
`EuclideanSpace ℝ (Fin n)` and measures Euclidean balls.  This module is exactly
that transfer.

## The sandwich

`euclideanProdEquiv (p+q) s` is a coordinate reindexing, so it carries Lebesgue
measure to Lebesgue measure.  Pulled back through it, the Euclidean ball of
radius `δ` about the origin is `{(ξ,ζ) | ‖ξ‖² + ‖ζ‖² < δ²}`, and that set is
squeezed between two product boxes:

* `box (δ/2) ⊆ ball δ`, because `2·(δ/2)² = δ²/2 < δ²`;
* `ball δ ⊆ box δ`, because each of `‖ξ‖²`, `‖ζ‖²` is at most their sum.

So the sublevel volume of the germ inside the Euclidean ball of radius `δ` is
bounded below by the band volume in the box of radius `δ/2` and above by the band
volume in the box of radius `δ`.  `exists_freeBlockBand_bounds` supplies a
`Θ(ε)` estimate at each of the two radii, and the two estimates close the
sandwich.

## What the constants are, and the one cosmetic adjustment

The lower constant comes from the band estimate at radius `δ/2` and the upper one
from the band estimate at radius `δ`.  These are produced by two independent
invocations of `exists_freeBlockBand_bounds`, so nothing forces `cLower ≤ cUpper`
on the nose.  `HasLocalVolumeOrder` demands that ordering, so the upper constant
is taken to be `max cLower cUpper`, which still upper-bounds the sublevel volume
and is trivially at least the lower one.  This weakens no estimate: it only
enlarges a constant that the definition already quantifies existentially.

## The radius quantifier

`HasLocalVolumeOrder` quantifies `δ` over `Ioo 0 δ₀` for a `δ₀` the witness
chooses.  No upper restriction on `δ` is needed here — the sandwich and both band
estimates hold at every positive radius — so `δ₀ = 1` is taken, and the statement
would be equally true with any positive `δ₀`.

## The pair

The pair is `(λ, m) = (1, 1)`: the band `|Q(ξ) + g(ζ)| ≤ ε` has volume linear in
`ε` with no logarithmic factor, and `volumeScale 1 1 ε = ε`.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

/-! ## The scale at the pair `(1, 1)` -/

/-- At `(λ, m) = (1, 1)` the asymptotic scale is the identity: `ε ^ (1:ℝ) = ε` and
the logarithmic factor has exponent `m - 1 = 0`. -/
public theorem volumeScale_one_one (ε : ℝ) : volumeScale 1 1 ε = ε := by
  simp [volumeScale]

/-! ## The germ on a single Euclidean space -/

/-- The band germ of `Q(ξ) + g(ζ)` read on a single Euclidean space.

The split coordinates are recovered by `euclideanProdEquiv (p+q) s`, which is a
permutation of coordinates and nothing more, so this is the same function as the
one `FreeBlockBand.lean` studies on the product — only its domain is written as
`EuclideanSpace ℝ (Fin (p + q + s))`. -/
@[expose] public noncomputable def freeBlockGerm (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (w : EuclideanSpace ℝ (Fin (p + q + s))) : ℝ :=
  |modelBandForm p q ((euclideanProdEquiv (p + q) s).symm w).1
    + g (((euclideanProdEquiv (p + q) s).symm w).2)|

/-- In split coordinates the germ is the printed `|Q(ξ) + g(ζ)|`. -/
public theorem freeBlockGerm_euclideanProdEquiv (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (ξ : EuclideanSpace ℝ (Fin (p + q)))
    (ζ : EuclideanSpace ℝ (Fin s)) :
    freeBlockGerm p q s g (euclideanProdEquiv (p + q) s (ξ, ζ))
      = |modelBandForm p q ξ + g ζ| := by
  simp [freeBlockGerm]

/-- The germ is nonnegative: it is an absolute value. -/
public theorem freeBlockGerm_nonneg (p q s : ℕ) (g : EuclideanSpace ℝ (Fin s) → ℝ)
    (w : EuclideanSpace ℝ (Fin (p + q + s))) : 0 ≤ freeBlockGerm p q s g w :=
  abs_nonneg _

/-! ## The geometric sandwich: box `δ/2` ⊆ ball `δ` ⊆ box `δ` -/

/-- **Half box into ball.**  A point of the product box of radius `δ/2` lands in
the Euclidean ball of radius `δ`: `‖ξ‖² + ‖ζ‖² ≤ δ²/2 < δ²`. -/
public theorem euclideanProdEquiv_mem_ball_zero (p q s : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {ξ : EuclideanSpace ℝ (Fin (p + q))} {ζ : EuclideanSpace ℝ (Fin s)}
    (hξ : ‖ξ‖ ≤ δ / 2) (hζ : ‖ζ‖ ≤ δ / 2) :
    euclideanProdEquiv (p + q) s (ξ, ζ)
      ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (p + q + s))) δ := by
  have hsq := dist_sq_euclideanProdEquiv (p + q) s ξ 0 ζ 0
  rw [euclideanProdEquiv_zero, dist_zero_right, dist_zero_right, dist_zero_right] at hsq
  rw [Metric.mem_ball, dist_zero_right]
  have h0 : (0 : ℝ) ≤ ‖euclideanProdEquiv (p + q) s (ξ, ζ)‖ := norm_nonneg _
  have h1 : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖ζ‖ := norm_nonneg _
  nlinarith

/-- **Ball into box.**  Each block of a point of the Euclidean ball of radius `δ`
has norm below `δ`, since each squared norm is at most their sum. -/
public theorem norm_lt_of_mem_ball_zero (p q s : ℕ) {δ : ℝ}
    {ξ : EuclideanSpace ℝ (Fin (p + q))} {ζ : EuclideanSpace ℝ (Fin s)}
    (h : euclideanProdEquiv (p + q) s (ξ, ζ)
      ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (p + q + s))) δ) :
    ‖ξ‖ < δ ∧ ‖ζ‖ < δ := by
  have hball : euclideanProdEquiv (p + q) s (ξ, ζ)
      ∈ Metric.ball (euclideanProdEquiv (p + q) s (0, 0)) δ := by
    rwa [euclideanProdEquiv_zero]
  obtain ⟨hx, hy⟩ := dist_lt_of_euclideanProdEquiv_mem_ball hball
  rw [dist_zero_right] at hx hy
  exact ⟨hx, hy⟩

/-- The band in the box of radius `δ/2` sits inside the sublevel set of the germ
inside the Euclidean ball of radius `δ`, read in split coordinates. -/
public theorem freeBlockBandSet_subset_preimage (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) {δ : ℝ} (hδ : 0 < δ) (ε : ℝ) :
    freeBlockBandSet p q s g (δ / 2) ε
      ⊆ euclideanProdEquiv (p + q) s ⁻¹'
        {z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (p + q + s))) δ |
          freeBlockGerm p q s g z ≤ ε} := by
  rintro ⟨ξ, ζ⟩ ⟨h1, h2, h3⟩
  refine ⟨euclideanProdEquiv_mem_ball_zero p q s hδ h1 h2, ?_⟩
  rw [freeBlockGerm_euclideanProdEquiv]
  exact h3

/-- The sublevel set of the germ inside the Euclidean ball of radius `δ`, read in
split coordinates, sits inside the band in the box of radius `δ`. -/
public theorem preimage_subset_freeBlockBandSet (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ) :
    euclideanProdEquiv (p + q) s ⁻¹'
        {z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (p + q + s))) δ |
          freeBlockGerm p q s g z ≤ ε}
      ⊆ freeBlockBandSet p q s g δ ε := by
  rintro ⟨ξ, ζ⟩ ⟨h1, h2⟩
  rw [freeBlockGerm_euclideanProdEquiv] at h2
  obtain ⟨hx, hy⟩ := norm_lt_of_mem_ball_zero p q s h1
  exact ⟨hx.le, hy.le, h2⟩

/-- The reindexing preserves the volume of the sublevel set. -/
public theorem measure_preimage_sublevel (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ) :
    volume (euclideanProdEquiv (p + q) s ⁻¹'
        {z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (p + q + s))) δ |
          freeBlockGerm p q s g z ≤ ε})
      = volume {z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (p + q + s))) δ |
          freeBlockGerm p q s g z ≤ ε} :=
  (measurePreserving_euclideanProdEquiv (p + q) s).measure_preimage_emb
    (euclideanProdEquiv (p + q) s).measurableEmbedding _

/-! ## The sandwich in `sublevelVolume` form -/

/-- **Lower half of the sandwich.** -/
public theorem measure_freeBlockBandSet_half_le_sublevelVolume (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) {δ : ℝ} (hδ : 0 < δ) (ε : ℝ) :
    (volume (freeBlockBandSet p q s g (δ / 2) ε)).toReal
      ≤ sublevelVolume (freeBlockGerm p q s g) 0 δ ε := by
  rw [sublevelVolume]
  refine ENNReal.toReal_mono (sublevelVolume_ne_top (freeBlockGerm p q s g) 0 δ ε) ?_
  rw [← measure_preimage_sublevel p q s g δ ε]
  exact measure_mono (freeBlockBandSet_subset_preimage p q s g hδ ε)

/-- **Upper half of the sandwich.** -/
public theorem sublevelVolume_le_measure_freeBlockBandSet (p q s : ℕ)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (δ ε : ℝ) :
    sublevelVolume (freeBlockGerm p q s g) 0 δ ε
      ≤ (volume (freeBlockBandSet p q s g δ ε)).toReal := by
  rw [sublevelVolume]
  refine ENNReal.toReal_mono (measure_freeBlockBandSet_ne_top p q s g δ ε) ?_
  rw [← measure_preimage_sublevel p q s g δ ε]
  exact measure_mono (preimage_subset_freeBlockBandSet p q s g δ ε)

/-! ## The local pair -/

/-- **The free block has local pair `(1, 1)`.**  With a quadratic block of
signature `(p, q)`, `2 ≤ p` and `q ≠ 0`, and a free block carrying any continuous
shift vanishing at the origin, the germ `|Q(ξ) + g(ζ)|` has local volume order
`(λ, m) = (1, 1)` at the origin of `EuclideanSpace ℝ (Fin (p + q + s))`.

This is `exists_freeBlockBand_bounds` transported from the product box to the
Euclidean ball.  The lower constant is the one the band estimate gives at radius
`δ/2`, the upper constant the one it gives at radius `δ`; since the two come from
independent invocations, the upper constant is replaced by `max cLower cUpper` so
that `HasLocalVolumeOrder`'s `cLower ≤ cUpper` holds.  That enlarges a constant
the definition quantifies existentially and weakens no estimate.

The radius threshold is `δ₀ = 1` and could be any positive number: the sandwich
and both band estimates hold at every positive radius. -/
public theorem hasLocalVolumeOrder_freeBlockGerm (p q s : ℕ) [NeZero q] (hp : 2 ≤ p)
    (g : EuclideanSpace ℝ (Fin s) → ℝ) (hg : Continuous g) (hg0 : g 0 = 0) :
    HasLocalVolumeOrder (freeBlockGerm p q s g) 0 1 1 := by
  refine Or.inr ⟨one_pos, le_refl 1, 1, one_pos, ?_⟩
  rintro δ ⟨hδ0, -⟩
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨c₁, c₂, ε₀, hc₁, hc₁₂, hε₀, hband⟩ :=
    exists_freeBlockBand_bounds p q s hp g hg hg0 hhalf
  obtain ⟨d₁, d₂, η₀, hd₁, hd₁₂, hη₀, hband'⟩ :=
    exists_freeBlockBand_bounds p q s hp g hg hg0 hδ0
  refine ⟨c₁, max c₁ d₂, hc₁, le_max_left _ _, ?_⟩
  have hmem : Set.Ioc (0 : ℝ) (min ε₀ η₀) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioc_mem_nhdsGT (by simp [hε₀, hη₀])
  filter_upwards [hmem] with ε hε
  obtain ⟨hεpos, hεle⟩ := hε
  have hlow := (hband ε hεpos.le (hεle.trans (min_le_left _ _))).1
  have hup := (hband' ε hεpos.le (hεle.trans (min_le_right _ _))).2
  rw [volumeScale_one_one]
  refine ⟨hlow.trans (measure_freeBlockBandSet_half_le_sublevelVolume p q s g hδ0 ε), ?_⟩
  refine (sublevelVolume_le_measure_freeBlockBandSet p q s g δ ε).trans ?_
  exact hup.trans (by nlinarith [le_max_right c₁ d₂, hεpos.le])

end AISafetyAtlas.SingularLearning
