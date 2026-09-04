module

public import AISafetyAtlas.SingularLearning.LocalPair

/-!
# Worked models for the local-pair relations

`AISafetyAtlas/SingularLearning/LocalPair.lean` fixes two relations in which a
local-pair claim can be made — the source specification `HasExactLocalPair` and
the operational `HasLocalVolumeOrder` — and the bridge between them.

## What the bridge buys

An earlier plan listed three uniqueness obligations, each with its own
radius-picking argument. Only one needs a proof. `exactLocalPair_imp_volumeOrder`
is valid *at* the exceptional radii — where there is no exact premise at all —
because a countable set has dense complement, so any radius is squeezed between
two good ones, and the sublevel volume is monotone in the radius. Uniqueness for
the exact relation and the cross-interface comparison are then one-liners.

## Satisfiability

`hasExactLocalPair_sq` inhabits the non-degenerate branch `0 < lam`: the germ
`K(x) = x₀²` on `EuclideanSpace ℝ (Fin 1)` has local pair `(1/2, 1)`. Without it
the relations were inhabited only through the neutral `(0, 1)` convention for a
germ vanishing on a whole neighbourhood, so every theorem above held of a class
nothing had been shown to belong to.

## What is not here

Two of the transfer combinators now exist, in
`AISafetyAtlas/SingularLearning/PairTransfer.lean`: comparability of germs
(print's Lemma 6.2) and free coordinates (print's Lemma 6.4(ii)), applied to this
module's `hasLocalVolumeOrder_sq` in
`AISafetyAtlas/Examples/SingularLearning/PairTransfer.lean`. The rest of the
calculus — products of germs in disjoint variables, regular quadratic factors,
local diffeomorphisms — is still missing, as is print's Lemma 6.1, which is what
would supply a pair to transfer for a germ not already computed by hand. Those
remain real gaps and are recorded rather than papered over.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory Filter Topology

variable {n : ℕ}

/-- The source specification implies the operational interface, at every
sufficiently small radius. -/
example {K : EuclideanSpace ℝ (Fin n) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {lam : ℝ} {m : ℕ} (h : HasExactLocalPair K w lam m) :
    HasLocalVolumeOrder K w lam m :=
  exactLocalPair_imp_volumeOrder h

/-- Two-sided order bounds determine the pair. This is the obligation the whole
"the table is `f`" design rests on: without it, a computed pair need not be *the*
pair. -/
example {K : EuclideanSpace ℝ (Fin n) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {lam lam' : ℝ} {m m' : ℕ}
    (h : HasLocalVolumeOrder K w lam m) (h' : HasLocalVolumeOrder K w lam' m') :
    lam = lam' ∧ m = m' :=
  volumeOrder_unique h h'

/-- So does the source specification — a corollary, not a second argument. -/
example {K : EuclideanSpace ℝ (Fin n) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {lam lam' : ℝ} {m m' : ℕ}
    (h : HasExactLocalPair K w lam m) (h' : HasExactLocalPair K w lam' m') :
    lam = lam' ∧ m = m' :=
  exactLocalPair_unique h h'

/-- **The transport the conditional assembly needs.** Given a two-sided order
computation at a proposed pair, and the *value-free* hypothesis that some exact
pair exists for the germ, the exact pair is the computed one.

This is the shape of the trust boundary: the hypothesis says only that an exact
pair exists, never what it is. Assuming its value would assume the result. -/
example {K : EuclideanSpace ℝ (Fin n) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {lam : ℝ} {m : ℕ}
    (hex : ∃ lam' m', HasExactLocalPair K w lam' m')
    (h : HasLocalVolumeOrder K w lam m) :
    HasExactLocalPair K w lam m :=
  hasExactLocalPair_of_volumeOrder hex h

/-- The sublevel volume is finite, so the `ℝ`-valued relations are not comparing
`⊤` to `⊤`. -/
example (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ) :
    MeasureTheory.volume {x ∈ Metric.ball w δ | K x ≤ ε} ≠ ⊤ :=
  sublevelVolume_ne_top K w δ ε

/-- Monotone in the radius — the fact that makes the bridge work. -/
example (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    {δ₁ δ₂ ε : ℝ} (h : δ₁ ≤ δ₂) :
    sublevelVolume K w δ₁ ε ≤ sublevelVolume K w δ₂ ε :=
  sublevelVolume_mono K w h

/-- A countable set of radii cannot block the argument: good radii are dense. -/
example {E : Set ℝ} (hE : E.Countable) {x y : ℝ} (h : x < y) :
    ∃ z ∈ Set.Ioo x y, z ∉ E :=
  exists_notMem_of_countable hE h

/-! ## A witness: the one-dimensional quadratic germ

Until this section every occurrence of `HasExactLocalPair` and `HasLocalVolumeOrder`
in the repository was in hypothesis position, and the only germ known to satisfy
either relation was the degenerate one, through the neutral `(0, 1)` branch for a
`K` vanishing on a whole neighbourhood. So every theorem above was conditional on
something inhabiting the non-degenerate branch `0 < lam`. The germ `K(x) = x₀²`
inhabits it, which is what turns uniqueness and the bridge from true-but-possibly-
vacuous into statements about a nonempty relation.
-/

/-- The Lebesgue volume of the `ε`-sublevel set of `x ↦ x₀²` inside the ball of radius
`δ` about the origin of `EuclideanSpace ℝ (Fin 1)`, whenever the sublevel set is small
enough to sit strictly inside the ball.

This is the only genuinely measure-theoretic step. `EuclideanSpace ℝ (Fin 1)` is
`PiLp 2 (fun _ : Fin 1 => ℝ)`, so the computation is transported to `ℝ` along the
composite of `PiLp.volume_preserving_ofLp` (the `PiLp`-to-`ι → ℝ` collapse) and
`MeasureTheory.volume_preserving_funUnique` (the `Fin 1 → ℝ ≃ ℝ` collapse), under
which the set is the interval `Icc (-√ε) (√ε)`. -/
private theorem volume_sublevel_sq {δ ε : ℝ} (hε : 0 < ε) (hδ : Real.sqrt ε < δ) :
    volume {x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) δ | x 0 ^ 2 ≤ ε}
      = ENNReal.ofReal (2 * Real.sqrt ε) := by
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 1), ‖x‖ = |x 0| := fun x => by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 1) => x 0) volume volume :=
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).comp
      (PiLp.volume_preserving_ofLp (ι := Fin 1))
  have hset : {x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) δ | x 0 ^ 2 ≤ ε}
      = (fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹'
          Set.Icc (-Real.sqrt ε) (Real.sqrt ε) := by
    ext x
    have habs : x 0 ^ 2 ≤ ε ↔ |x 0| ≤ Real.sqrt ε := by
      rw [← Real.sqrt_sq_eq_abs, Real.sqrt_le_sqrt_iff (by positivity)]
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Metric.mem_ball, dist_zero_right,
      hnorm]
    constructor
    · rintro ⟨-, h2⟩
      exact abs_le.1 (habs.1 h2)
    · intro h
      have h' : |x 0| ≤ Real.sqrt ε := abs_le.2 h
      exact ⟨lt_of_le_of_lt h' hδ, habs.2 h'⟩
  rw [hset, hmp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  ring_nf

/-- **The one-dimensional quadratic germ `K(x) = x₀²` has local pair `(1/2, 1)`.**

This is the satisfiability witness for `HasExactLocalPair`. Before it, the relation
was inhabited only through its neutral first branch, the convention for a germ
vanishing on a whole neighbourhood of `w`; every theorem stated about the
non-degenerate branch `0 < lam` — uniqueness, the bridge, the transport — was
therefore conditional on the existence of something it had never been shown to
apply to. `x₀²` is the simplest germ with `lam = 1/2`, the scalar case of the
reduced-rank intuition that a single quadratic direction contributes `1/2` to the
learning coefficient.

The computation is exact and needs no exceptional set at all: with `δ₀ := 1` and
`Exceptional := ∅`, for every radius `δ ∈ Ioo 0 1` and every `ε < δ²` the sublevel
set is exactly the segment `|x₀| ≤ √ε`, of volume `2√ε`, so with `c := 2` the ratio
against `volumeScale (1/2) 1 ε = ε^(1/2)` — the logarithmic factor is literally `1`,
since `m - 1 = 0` in `ℕ` — is *identically* `1` on `(0, δ²)`. The countable
exceptional set that `HasExactLocalPair` permits is genuinely needed only for
harder germs; it costs this one nothing. -/
public theorem hasExactLocalPair_sq :
    HasExactLocalPair (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 (1/2) 1 := by
  refine Or.inr ⟨by norm_num, le_refl 1, 1, zero_lt_one, ∅, Set.countable_empty,
    fun δ hδ _ => ⟨2, by norm_num, Filter.Tendsto.congr' ?_ tendsto_const_nhds⟩⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ ^ 2 by nlinarith [hδ.1])] with ε hε
  have hε0 : (0 : ℝ) < ε := hε.1
  have hsq : Real.sqrt ε < δ := by
    have := Real.sqrt_lt_sqrt hε0.le hε.2
    rwa [Real.sqrt_sq hδ.1.le] at this
  have hs : Real.sqrt ε = ε ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow ε
  have hvol : sublevelVolume (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 δ ε
      = 2 * Real.sqrt ε := by
    rw [sublevelVolume, volume_sublevel_sq hε0 hsq, ENNReal.toReal_ofReal (by positivity)]
  have hne : (0 : ℝ) < ε ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hε0 _
  rw [hvol, volumeScale, hs, show (1 : ℕ) - 1 = 0 from rfl, pow_zero, mul_one, eq_comm,
    div_self (by positivity)]

/-- The same germ satisfies the operational two-sided relation, by the bridge. -/
public theorem hasLocalVolumeOrder_sq :
    HasLocalVolumeOrder (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 (1/2) 1 :=
  exactLocalPair_imp_volumeOrder hasExactLocalPair_sq

/-- The witness is the *only* pair for this germ: uniqueness plus inhabitation, so
the local pair of `x₀²` is determined and equal to `(1/2, 1)`. -/
public theorem eq_half_one_of_hasExactLocalPair_sq {lam : ℝ} {m : ℕ}
    (h : HasExactLocalPair (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 lam m) :
    lam = 1/2 ∧ m = 1 :=
  exactLocalPair_unique h hasExactLocalPair_sq

/-- The same, from the weaker operational side. -/
public theorem eq_half_one_of_hasLocalVolumeOrder_sq {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 lam m) :
    lam = 1/2 ∧ m = 1 :=
  volumeOrder_unique h hasLocalVolumeOrder_sq

end AISafetyAtlas.Examples.SingularLearning

