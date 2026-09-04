module

public import AISafetyAtlas.SingularLearning.LocalPair
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The transfer calculus for the local pair

`LocalPair.lean` can *state* a local pair, prove it unique, and bridge the exact
specification to the operational two-sided order. What it cannot do is *compute*
one. Nothing there lets a decomposition of a germ become a decomposition of its
pair, so nothing can be assembled from pieces.

This module supplies that missing calculus.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

variable {n : ℕ}


/-! ## Infrastructure: nesting of sublevel sets, and rescaling the scale -/

/-- Sublevel volumes are monotone under a pointwise implication *inside the ball*.
This is the only shape in which sublevel sets are compared below: comparability of
germs gives an implication `f x ≤ ε → g x ≤ ε'` on a neighbourhood, never a global
inequality of the germs. -/
public theorem sublevelVolume_le_sublevelVolume {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {δ ε ε' : ℝ}
    (h : ∀ x ∈ Metric.ball w δ, f x ≤ ε → g x ≤ ε') :
    sublevelVolume f w δ ε ≤ sublevelVolume g w δ ε' := by
  refine ENNReal.toReal_mono (sublevelVolume_ne_top g w δ ε') (measure_mono ?_)
  rintro x ⟨hx, hfx⟩
  exact ⟨hx, h x hx hfx⟩

/-- Dividing by a positive constant is a self-map of the punctured right filter at `0`.
This is what lets a two-sided bound stated at `ε` be read off at `ε / c`. -/
public theorem tendsto_div_const_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε : ℝ => ε / c) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun ε : ℝ => ε / c) (nhds 0) (nhds (0 / c)) :=
      (continuous_id.div_const c).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε using div_pos hε hc

/-- **The logarithmic step.** `log(c/ε)` is two-sided comparable to `log(1/ε)` as
`ε ↓ 0`, with the explicit constants `1/2` and `3/2` of print: once
`log(1/ε) ≥ 2|log c|`, the additive shift `log c` cannot move `log(1/ε)` by more
than half of itself.

This is the only place where the multiplicity — as opposed to the exponent — is at
risk, and it is the reason the multiplicity survives comparability: an additive
perturbation of the logarithm is a *multiplicative* perturbation by a constant, so
the power `m - 1` is untouched. The tool is `tendsto_log_one_div`. -/
public theorem eventually_log_div_comparable {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ Real.log (1 / ε) ∧
        1 / 2 * Real.log (1 / ε) ≤ Real.log (1 / (ε / c)) ∧
          Real.log (1 / (ε / c)) ≤ 3 / 2 * Real.log (1 / ε) := by
  filter_upwards [tendsto_log_one_div.eventually_ge_atTop (2 * |Real.log c|),
    self_mem_nhdsWithin] with ε hL hε
  have hε0 : (0 : ℝ) < ε := hε
  have hnn : 0 ≤ Real.log (1 / ε) := le_trans (by positivity) hL
  have hrw : Real.log (1 / (ε / c)) = Real.log c + Real.log (1 / ε) := by
    rw [one_div_div, Real.log_div hc.ne' hε0.ne', one_div, Real.log_inv]
    ring
  have habs : |Real.log c| ≤ Real.log (1 / ε) / 2 := by linarith
  obtain ⟨hlo, hhi⟩ := abs_le.1 habs
  exact ⟨hnn, by rw [hrw]; linarith, by rw [hrw]; linarith⟩

/-- **Rescaling the asymptotic scale.** `volumeScale lam m (ε / c)` is two-sided
comparable to `volumeScale lam m ε` near `0⁺`, for any fixed `c > 0`.

Both the exponent and the multiplicity are preserved: the factor `ε ^ lam` only
contributes the constant `c ^ (-lam)`, and by `eventually_log_div_comparable` the
logarithmic factor only contributes the constants `(1/2) ^ (m - 1)` and
`(3/2) ^ (m - 1)`. The constants are produced existentially because nothing
downstream needs their values. -/
public theorem exists_volumeScale_div_bounds (lam : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        a * volumeScale lam m ε ≤ volumeScale lam m (ε / c) ∧
          volumeScale lam m (ε / c) ≤ b * volumeScale lam m ε := by
  have hcl : (0 : ℝ) < c ^ lam := Real.rpow_pos_of_pos hc lam
  refine ⟨(1 / 2 : ℝ) ^ (m - 1) / c ^ lam, (3 / 2 : ℝ) ^ (m - 1) / c ^ lam, by positivity,
    by gcongr; norm_num, ?_⟩
  filter_upwards [eventually_log_div_comparable hc, self_mem_nhdsWithin] with ε hlog hε
  obtain ⟨hnn, hlo, hhi⟩ := hlog
  have hε0 : (0 : ℝ) < ε := hε
  have hεl : (0 : ℝ) < ε ^ lam := Real.rpow_pos_of_pos hε0 lam
  have hdiv : (ε / c) ^ lam = ε ^ lam / c ^ lam := Real.div_rpow hε0.le hc.le lam
  have hP : (0 : ℝ) ≤ ε ^ lam / c ^ lam := by positivity
  have h1 : (1 / 2 * Real.log (1 / ε)) ^ (m - 1) ≤ Real.log (1 / (ε / c)) ^ (m - 1) :=
    pow_le_pow_left₀ (by linarith) hlo _
  have h2 : Real.log (1 / (ε / c)) ^ (m - 1) ≤ (3 / 2 * Real.log (1 / ε)) ^ (m - 1) :=
    pow_le_pow_left₀ (by linarith) hhi _
  have e1 : (1 / 2 * Real.log (1 / ε)) ^ (m - 1)
      = (1 / 2 : ℝ) ^ (m - 1) * Real.log (1 / ε) ^ (m - 1) := mul_pow _ _ _
  have e2 : (3 / 2 * Real.log (1 / ε)) ^ (m - 1)
      = (3 / 2 : ℝ) ^ (m - 1) * Real.log (1 / ε) ^ (m - 1) := mul_pow _ _ _
  simp only [volumeScale, hdiv]
  constructor
  · calc (1 / 2 : ℝ) ^ (m - 1) / c ^ lam * (ε ^ lam * Real.log (1 / ε) ^ (m - 1))
        = ε ^ lam / c ^ lam * ((1 / 2 * Real.log (1 / ε)) ^ (m - 1)) := by rw [e1]; ring
      _ ≤ ε ^ lam / c ^ lam * Real.log (1 / (ε / c)) ^ (m - 1) := by gcongr
  · calc ε ^ lam / c ^ lam * Real.log (1 / (ε / c)) ^ (m - 1)
        ≤ ε ^ lam / c ^ lam * ((3 / 2 * Real.log (1 / ε)) ^ (m - 1)) := by gcongr
      _ = (3 / 2 : ℝ) ^ (m - 1) / c ^ lam * (ε ^ lam * Real.log (1 / ε) ^ (m - 1)) := by
          rw [e2]; ring

/-! ## Infrastructure: split coordinates and product windows

`HasLocalVolumeOrder` is quantified over *Euclidean balls*, while both remaining
transfer rules decompose the germ along a splitting of the coordinates, where the
natural window is a *product* of balls. The two are not equal, but they interleave:
a product of balls of radius `δ / 2` sits inside the Euclidean ball of radius `δ`,
which sits inside the product of balls of radius `δ`. Since `HasLocalVolumeOrder`
supplies bounds at *every* small radius, two different radii may be used on the two
sides, and the interleaving costs nothing but constants.

The splitting itself is a coordinate reindexing `Fin n ⊕ Fin k ≃ Fin (n + k)`, so it
carries Lebesgue measure to Lebesgue measure with no Jacobian factor; the chain of
Mathlib measure-preservation lemmas is the one used in `Coordinates.lean`. -/

/-- Split coordinates: `EuclideanSpace ℝ (Fin (n + k))` as a product, by the
reindexing `finSumFinEquiv`. A permutation of coordinates and nothing more. -/
@[expose] public noncomputable def euclideanProdEquiv (n k : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) ≃ᵐ EuclideanSpace ℝ (Fin (n + k)) :=
  ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.prodCongr
      (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm).trans <|
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ℝ)).symm.trans <|
      (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ)).trans
        (MeasurableEquiv.toLp 2 (Fin (n + k) → ℝ))

/-- The splitting writes the coordinates of `(x, y)` in the order given by
`finSumFinEquiv`. -/
public theorem euclideanProdEquiv_apply (n k : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin k)) (j : Fin (n + k)) :
    (euclideanProdEquiv n k (x, y)).ofLp j =
      Sum.elim x.ofLp y.ofLp (finSumFinEquiv.symm j) := rfl

/-- The splitting carries Lebesgue measure to Lebesgue measure: it is a reindexing,
so no Jacobian factor appears and no downstream asymptotic is rescaled. -/
public theorem measurePreserving_euclideanProdEquiv (n k : ℕ) :
    MeasurePreserving (euclideanProdEquiv n k) volume volume := by
  have h1 : MeasurePreserving
      (⇑((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.prodCongr
        (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm)) volume volume :=
    (PiLp.volume_preserving_ofLp (Fin n)).prod (PiLp.volume_preserving_ofLp (Fin k))
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin k => ℝ)
  have h3 := volume_preserving_arrowCongr' (finSumFinEquiv (m := n) (n := k))
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  have h4 := PiLp.volume_preserving_toLp (Fin (n + k))
  simp only [euclideanProdEquiv]
  exact h4.comp (h3.comp (h2.comp h1))

/-- Pythagoras in split coordinates. -/
public theorem dist_sq_euclideanProdEquiv (n k : ℕ) (x x' : EuclideanSpace ℝ (Fin n))
    (y y' : EuclideanSpace ℝ (Fin k)) :
    dist (euclideanProdEquiv n k (x, y)) (euclideanProdEquiv n k (x', y')) ^ 2
      = dist x x' ^ 2 + dist y y' ^ 2 := by
  have hnn : ∀ (ι : Type) [Fintype ι] (F : ι → ℝ), 0 ≤ ∑ i, F i ^ 2 :=
    fun ι _ F => Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq,
    Real.sq_sqrt (hnn _ _), Real.sq_sqrt (hnn _ _), Real.sq_sqrt (hnn _ _)]
  rw [← Fintype.sum_equiv (finSumFinEquiv (m := n) (n := k))
    (fun s => dist (Sum.elim x.ofLp y.ofLp s) (Sum.elim x'.ofLp y'.ofLp s) ^ 2)
    (fun j => dist ((euclideanProdEquiv n k (x, y)).ofLp j)
      ((euclideanProdEquiv n k (x', y')).ofLp j) ^ 2)
    (fun s => by rw [euclideanProdEquiv_apply, euclideanProdEquiv_apply,
      Equiv.symm_apply_apply])]
  exact Fintype.sum_sum_type _

/-- A product of balls of radius `δ / 2` sits inside the Euclidean ball of radius `δ`.
The factor `2` is not sharp (`√2` is), and nothing needs it to be. -/
public theorem euclideanProdEquiv_mem_ball {n k : ℕ} {x w : EuclideanSpace ℝ (Fin n)}
    {y v : EuclideanSpace ℝ (Fin k)} {δ : ℝ} (hδ : 0 < δ)
    (hx : dist x w < δ / 2) (hy : dist y v < δ / 2) :
    euclideanProdEquiv n k (x, y) ∈ Metric.ball (euclideanProdEquiv n k (w, v)) δ := by
  have hsq := dist_sq_euclideanProdEquiv n k x w y v
  have h1 : (0 : ℝ) ≤ dist x w := dist_nonneg
  have h2 : (0 : ℝ) ≤ dist y v := dist_nonneg
  have h3 : (0 : ℝ) ≤ dist (euclideanProdEquiv n k (x, y)) (euclideanProdEquiv n k (w, v)) :=
    dist_nonneg
  rw [Metric.mem_ball]
  nlinarith

/-- The Euclidean ball of radius `δ` sits inside the product of balls of radius `δ`. -/
public theorem dist_lt_of_euclideanProdEquiv_mem_ball {n k : ℕ}
    {x w : EuclideanSpace ℝ (Fin n)} {y v : EuclideanSpace ℝ (Fin k)} {δ : ℝ}
    (h : euclideanProdEquiv n k (x, y) ∈ Metric.ball (euclideanProdEquiv n k (w, v)) δ) :
    dist x w < δ ∧ dist y v < δ := by
  have hsq := dist_sq_euclideanProdEquiv n k x w y v
  rw [Metric.mem_ball] at h
  have h1 : (0 : ℝ) ≤ dist x w := dist_nonneg
  have h2 : (0 : ℝ) ≤ dist y v := dist_nonneg
  have h3 : (0 : ℝ) ≤ dist (euclideanProdEquiv n k (x, y)) (euclideanProdEquiv n k (w, v)) :=
    dist_nonneg
  exact ⟨by nlinarith, by nlinarith⟩

/-- Volume of a product set in split coordinates. -/
public theorem volume_prod_split {n k : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (B : Set (EuclideanSpace ℝ (Fin k))) :
    (volume : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k))) (A ×ˢ B)
      = volume A * volume B := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod_prod A B

/-- **Upper half of the product-window squeeze.** If every point of the sublevel set
inside the Euclidean ball lies in the product `A ×ˢ B` when read in split coordinates,
the sublevel volume is at most `vol A * vol B`. -/
public theorem sublevelVolume_le_prod {n k : ℕ} {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ}
    {W : EuclideanSpace ℝ (Fin (n + k))} {δ ε : ℝ} {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin k))} (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤)
    (h : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k),
      euclideanProdEquiv n k p ∈ Metric.ball W δ → F (euclideanProdEquiv n k p) ≤ ε →
        p.1 ∈ A ∧ p.2 ∈ B) :
    sublevelVolume F W δ ε ≤ (volume A).toReal * (volume B).toReal := by
  have hpre : volume (euclideanProdEquiv n k ⁻¹' {z ∈ Metric.ball W δ | F z ≤ ε})
      = volume {z ∈ Metric.ball W δ | F z ≤ ε} :=
    (measurePreserving_euclideanProdEquiv n k).measure_preimage_emb
      (euclideanProdEquiv n k).measurableEmbedding _
  have hmono : volume (euclideanProdEquiv n k ⁻¹' {z ∈ Metric.ball W δ | F z ≤ ε})
      ≤ volume (A ×ˢ B) := by
    refine measure_mono ?_
    rintro p ⟨hp1, hp2⟩
    exact h p hp1 hp2
  rw [volume_prod_split] at hmono
  rw [sublevelVolume, ← hpre, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hA hB) hmono

/-- **Lower half of the product-window squeeze.** If the product `A ×ˢ B` is contained
in the sublevel set inside the Euclidean ball, the sublevel volume is at least
`vol A * vol B`. -/
public theorem prod_le_sublevelVolume {n k : ℕ} {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ}
    {W : EuclideanSpace ℝ (Fin (n + k))} {δ ε : ℝ} {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin k))}
    (h : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k), p.1 ∈ A → p.2 ∈ B →
      euclideanProdEquiv n k p ∈ Metric.ball W δ ∧ F (euclideanProdEquiv n k p) ≤ ε) :
    (volume A).toReal * (volume B).toReal ≤ sublevelVolume F W δ ε := by
  have hpre : volume (euclideanProdEquiv n k ⁻¹' {z ∈ Metric.ball W δ | F z ≤ ε})
      = volume {z ∈ Metric.ball W δ | F z ≤ ε} :=
    (measurePreserving_euclideanProdEquiv n k).measure_preimage_emb
      (euclideanProdEquiv n k).measurableEmbedding _
  have hmono : volume (A ×ˢ B)
      ≤ volume (euclideanProdEquiv n k ⁻¹' {z ∈ Metric.ball W δ | F z ≤ ε}) := by
    refine measure_mono ?_
    rintro p ⟨hp1, hp2⟩
    exact h p hp1 hp2
  rw [volume_prod_split] at hmono
  rw [sublevelVolume, ← hpre, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (hpre ▸ sublevelVolume_ne_top F W δ ε) hmono

/-! ## Lemma 6.2: comparability transfers the pair -/

/-- **Lemma 6.2 (comparability transfers the pair), order form.** If
`c₁ * g ≤ f ≤ c₂ * g` on a neighbourhood of `w`, with `0 < c₁ ≤ c₂`, then any
two-sided local volume order of `g` at `w` is one of `f` at `w`. Print: *"the
multiplicity, not only the exponent, survives comparability."*

The proof is print's, with no analytic input: sublevel sets nest,
`{g ≤ ε/c₂} ⊆ {f ≤ ε} ⊆ {g ≤ ε/c₁}` inside the ball, so `V_f(ε)` is squeezed
between `V_g(ε/c₂)` and `V_g(ε/c₁)`; `exists_volumeScale_div_bounds` then converts
the scale at `ε/c` back into the scale at `ε` up to constants, which is exactly
where the multiplicity could have been lost and is not.

Applying it in both directions (`hasLocalVolumeOrder_comparable_iff`) gives the
statement print makes, that comparable germs have *the same* pair.

Deviation from print: print states the hypothesis for real-analytic `f, g ≥ 0`
vanishing at `w`. None of nonnegativity, analyticity or vanishing is used here,
and none is assumed: the transfer is a statement about sublevel volumes alone.
The premise is therefore weaker than print's, and the conclusion is print's for
the operational relation `HasLocalVolumeOrder`. Print's conclusion is about the
pair supplied by its Lemma 6.1, whose existence is not formalized in this
development; here the pair is a hypothesis, which is why the statement is an
implication rather than an equality of pairs. -/
public theorem hasLocalVolumeOrder_of_comparable {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam : ℝ} {m : ℕ} {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hcomp : ∀ᶠ x in nhds w, c₁ * g x ≤ f x ∧ f x ≤ c₂ * g x)
    (hg : HasLocalVolumeOrder g w lam m) :
    HasLocalVolumeOrder f w lam m := by
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  rcases hg with ⟨hz, hl, hm⟩ | ⟨hlam, hm, δ₀, hδ₀, hb⟩
  · refine Or.inl ⟨?_, hl, hm⟩
    filter_upwards [hz, hcomp] with x hgx hfx
    rw [hgx] at hfx
    linarith [hfx.1, hfx.2]
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hcomp
  obtain ⟨a₁, b₁, ha₁, hab₁, hsc₁⟩ := exists_volumeScale_div_bounds lam m hc₁
  obtain ⟨a₂, b₂, ha₂, hab₂, hsc₂⟩ := exists_volumeScale_div_bounds lam m hc₂
  refine Or.inr ⟨hlam, hm, min δ₀ r, lt_min hδ₀ hr, fun δ hδ => ?_⟩
  have hδδ₀ : δ < δ₀ := lt_of_lt_of_le hδ.2 (min_le_left _ _)
  have hδr : δ < r := lt_of_lt_of_le hδ.2 (min_le_right _ _)
  obtain ⟨a, A, ha, haA, hbd⟩ := hb δ ⟨hδ.1, hδδ₀⟩
  have hA : 0 < A := ha.trans_le haA
  refine ⟨a * a₂, max (a * a₂) (A * b₁), by positivity, le_max_left _ _, ?_⟩
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ volumeScale lam m ε := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    have h1 : 0 < ε ^ lam := Real.rpow_pos_of_pos hε.1 lam
    have h2 : (0 : ℝ) < Real.log (1 / ε) :=
      Real.log_pos (by rw [lt_div_iff₀ hε.1]; linarith [hε.2])
    exact le_of_lt (mul_pos h1 (pow_pos h2 _))
  filter_upwards [(tendsto_div_const_nhdsGT hc₁).eventually hbd,
    (tendsto_div_const_nhdsGT hc₂).eventually hbd, hsc₁, hsc₂, hpos]
    with ε hbd₁ hbd₂ hs₁ hs₂ hvs
  -- Nesting of the sublevel sets, inside the ball where comparability holds.
  have hnest_lo : sublevelVolume g w δ (ε / c₂) ≤ sublevelVolume f w δ ε := by
    refine sublevelVolume_le_sublevelVolume (fun x hx hgx => ?_)
    have hx' := hball (lt_trans (Metric.mem_ball.1 hx) hδr)
    calc f x ≤ c₂ * g x := hx'.2
      _ ≤ c₂ * (ε / c₂) := by gcongr
      _ = ε := by field_simp
  have hnest_hi : sublevelVolume f w δ ε ≤ sublevelVolume g w δ (ε / c₁) := by
    refine sublevelVolume_le_sublevelVolume (fun x hx hfx => ?_)
    have hx' := hball (lt_trans (Metric.mem_ball.1 hx) hδr)
    rw [le_div_iff₀ hc₁, mul_comm]
    exact le_trans hx'.1 hfx
  -- Transport the bounds for `g` at `ε / cᵢ` back to the scale at `ε`.
  have hlow : a * (a₂ * volumeScale lam m ε) ≤ sublevelVolume f w δ ε := by
    refine le_trans ?_ (le_trans hbd₂.1 hnest_lo)
    exact mul_le_mul_of_nonneg_left hs₂.1 ha.le
  have hhigh : sublevelVolume f w δ ε ≤ A * (b₁ * volumeScale lam m ε) := by
    refine le_trans (le_trans hnest_hi hbd₁.2) ?_
    exact mul_le_mul_of_nonneg_left hs₁.2 hA.le
  have hmax : A * b₁ * volumeScale lam m ε ≤ max (a * a₂) (A * b₁) * volumeScale lam m ε :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hvs
  constructor
  · calc a * a₂ * volumeScale lam m ε = a * (a₂ * volumeScale lam m ε) := by ring
      _ ≤ sublevelVolume f w δ ε := hlow
  · calc sublevelVolume f w δ ε ≤ A * (b₁ * volumeScale lam m ε) := hhigh
      _ = A * b₁ * volumeScale lam m ε := by ring
      _ ≤ max (a * a₂) (A * b₁) * volumeScale lam m ε := hmax

/-- Comparable germs have the *same* local volume order: print's Lemma 6.2 read as
an equivalence. The reverse direction is the forward one applied to
`c₂⁻¹ * f ≤ g ≤ c₁⁻¹ * f`. -/
public theorem hasLocalVolumeOrder_comparable_iff {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam : ℝ} {m : ℕ} {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hcomp : ∀ᶠ x in nhds w, c₁ * g x ≤ f x ∧ f x ≤ c₂ * g x) :
    HasLocalVolumeOrder f w lam m ↔ HasLocalVolumeOrder g w lam m := by
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  refine ⟨fun h => ?_, fun h => hasLocalVolumeOrder_of_comparable hc₁ hc₁₂ hcomp h⟩
  refine hasLocalVolumeOrder_of_comparable (c₁ := c₂⁻¹) (c₂ := c₁⁻¹) (by positivity)
    (by rw [inv_le_inv₀ hc₂ hc₁]; exact hc₁₂) ?_ h
  filter_upwards [hcomp] with x hx
  constructor
  · rw [inv_mul_le_iff₀ hc₂]
    exact hx.2
  · rw [le_inv_mul_iff₀ hc₁]
    exact hx.1


/-! ## Lemma 6.4(ii): free coordinates -/

/-- **Lemma 6.4(ii) (free coordinates), order form.** If `F` ignores the last `k`
coordinates — `F (x, y) = f x` in the split coordinates of `euclideanProdEquiv` —
then `F` at `(w, v)` has the local volume order that `f` has at `w`. Print: *"free
(gauge) coordinates change neither `λ` nor `m`"*, and *"free coordinates contribute
volume but no scaling in `ε`."*

The sublevel set of `F` is a product, so its volume is that of the sublevel set of
`f` times the volume of a ball in the free coordinates — a constant in `ε`, which
is absorbed into the two-sided constants and touches neither `lam` nor `m`.

The ambient dimension grows by `k` and the pair does not move.

Deviation from print: print takes the product window `B(w, δ) × B(v, ρ)` directly,
which its Lemma 6.1 permits. `HasLocalVolumeOrder` is quantified over Euclidean
balls only, so the product window is instead interleaved with Euclidean balls
(`euclideanProdEquiv_mem_ball`, `dist_lt_of_euclideanProdEquiv_mem_ball`) and the
two sides of the squeeze use the two radii `δ / 2` and `δ`. This is available
precisely because `HasLocalVolumeOrder` asserts its bounds at *every* small radius.
No hypothesis of print is dropped and none is added: `f` need not be nonnegative,
analytic, or vanishing at `w`. -/
public theorem hasLocalVolumeOrder_freeCoords {n k : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {v : EuclideanSpace ℝ (Fin k)} {lam : ℝ} {m : ℕ}
    (hF : ∀ x y, F (euclideanProdEquiv n k (x, y)) = f x)
    (hf : HasLocalVolumeOrder f w lam m) :
    HasLocalVolumeOrder F (euclideanProdEquiv n k (w, v)) lam m := by
  rcases hf with ⟨hz, hl, hm⟩ | ⟨hlam, hm, δ₀, hδ₀, hb⟩
  · refine Or.inl ⟨?_, hl, hm⟩
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hz
    refine Metric.eventually_nhds_iff.2 ⟨r, hr, fun z hzr => ?_⟩
    have hz' : euclideanProdEquiv n k ((euclideanProdEquiv n k).symm z) = z :=
      (euclideanProdEquiv n k).apply_symm_apply z
    have hmem : euclideanProdEquiv n k (((euclideanProdEquiv n k).symm z).1,
        ((euclideanProdEquiv n k).symm z).2) ∈
        Metric.ball (euclideanProdEquiv n k (w, v)) r := by
      rw [Prod.mk.eta, hz']
      exact Metric.mem_ball.2 hzr
    have h1 := (dist_lt_of_euclideanProdEquiv_mem_ball hmem).1
    calc F z = F (euclideanProdEquiv n k (((euclideanProdEquiv n k).symm z).1,
          ((euclideanProdEquiv n k).symm z).2)) := by rw [Prod.mk.eta, hz']
      _ = f ((euclideanProdEquiv n k).symm z).1 := hF _ _
      _ = 0 := hball h1
  refine Or.inr ⟨hlam, hm, δ₀, hδ₀, fun δ hδ => ?_⟩
  have hδ2 : 0 < δ / 2 := by linarith [hδ.1]
  obtain ⟨a, A, ha, -, hbd⟩ := hb (δ / 2) ⟨hδ2, by linarith [hδ.1, hδ.2]⟩
  obtain ⟨a', A', ha', ha'A', hbd'⟩ := hb δ hδ
  have hVlo : 0 < (volume (Metric.ball v (δ / 2))).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos volume v hδ2, measure_ball_lt_top⟩
  have hVhi : 0 ≤ (volume (Metric.ball v δ)).toReal := ENNReal.toReal_nonneg
  have hA' : 0 < A' := lt_of_lt_of_le ha' ha'A'
  refine ⟨a * (volume (Metric.ball v (δ / 2))).toReal,
    max (a * (volume (Metric.ball v (δ / 2))).toReal)
      (A' * (volume (Metric.ball v δ)).toReal), by positivity, le_max_left _ _, ?_⟩
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ volumeScale lam m ε := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    have h1 : 0 < ε ^ lam := Real.rpow_pos_of_pos hε.1 lam
    have h2 : (0 : ℝ) < Real.log (1 / ε) :=
      Real.log_pos (by rw [lt_div_iff₀ hε.1]; linarith [hε.2])
    exact le_of_lt (mul_pos h1 (pow_pos h2 _))
  filter_upwards [hbd, hbd', hpos] with ε hε hε' hvs
  -- The product window of radius `δ / 2` sits inside the Euclidean ball of radius `δ`.
  have hlow : sublevelVolume f w (δ / 2) ε * (volume (Metric.ball v (δ / 2))).toReal
      ≤ sublevelVolume F (euclideanProdEquiv n k (w, v)) δ ε := by
    refine prod_le_sublevelVolume (A := {x ∈ Metric.ball w (δ / 2) | f x ≤ ε})
      (B := Metric.ball v (δ / 2)) (fun p hp1 hp2 => ⟨?_, ?_⟩)
    · rw [← Prod.mk.eta (p := p)]
      exact euclideanProdEquiv_mem_ball (by linarith [hδ.1]) (Metric.mem_ball.1 hp1.1)
        (Metric.mem_ball.1 hp2)
    · rw [← Prod.mk.eta (p := p), hF]
      exact hp1.2
  -- The Euclidean ball of radius `δ` sits inside the product window of radius `δ`.
  have hhigh : sublevelVolume F (euclideanProdEquiv n k (w, v)) δ ε
      ≤ sublevelVolume f w δ ε * (volume (Metric.ball v δ)).toReal := by
    refine sublevelVolume_le_prod (A := {x ∈ Metric.ball w δ | f x ≤ ε}) (B := Metric.ball v δ)
      (sublevelVolume_ne_top f w δ ε) measure_ball_lt_top.ne (fun p hp1 hp2 => ?_)
    rw [← Prod.mk.eta (p := p)] at hp1 hp2
    obtain ⟨h1, h2⟩ := dist_lt_of_euclideanProdEquiv_mem_ball hp1
    rw [hF] at hp2
    exact ⟨⟨Metric.mem_ball.2 h1, hp2⟩, Metric.mem_ball.2 h2⟩
  constructor
  · calc a * (volume (Metric.ball v (δ / 2))).toReal * volumeScale lam m ε
        = a * volumeScale lam m ε * (volume (Metric.ball v (δ / 2))).toReal := by ring
      _ ≤ sublevelVolume f w (δ / 2) ε * (volume (Metric.ball v (δ / 2))).toReal :=
          mul_le_mul_of_nonneg_right hε.1 hVlo.le
      _ ≤ _ := hlow
  · calc sublevelVolume F (euclideanProdEquiv n k (w, v)) δ ε
        ≤ sublevelVolume f w δ ε * (volume (Metric.ball v δ)).toReal := hhigh
      _ ≤ A' * volumeScale lam m ε * (volume (Metric.ball v δ)).toReal :=
          mul_le_mul_of_nonneg_right hε'.2 hVhi
      _ = A' * (volume (Metric.ball v δ)).toReal * volumeScale lam m ε := by ring
      _ ≤ max (a * (volume (Metric.ball v (δ / 2))).toReal)
            (A' * (volume (Metric.ball v δ)).toReal) * volumeScale lam m ε := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hvs

/-! ## The `u`-block: the pair of a nondegenerate quadratic germ

The chart of Theorem 5.1 presents `2K` as comparable to `‖u‖² + ‖Y₀S_Z‖²_F`, with `u` ranging
over `ℝ^q`. The `u` half is a nondegenerate quadratic form, and its local pair is `(q/2, 1)` —
print's "each transverse direction contributes `1/2`", and the reason `λ` carries the `q/2` in
`λ = ½(q + min{…})`.

The computation is exact and needs no exceptional radii: inside a ball of radius `δ`, and for
`ε < δ²`, the sublevel set `{‖x‖² ≤ ε}` is exactly the closed ball of radius `√ε`, whose
volume is `ε^{q/2}` times the volume of the unit ball. So the ratio against
`volumeScale (q/2) 1 ε = ε^{q/2}` is *identically* the unit-ball volume — the logarithmic
factor is literally `1`, since `m − 1 = 0` in `ℕ`.

This generalizes `Examples/SingularLearning/LocalPair.lean`'s `hasExactLocalPair_sq`, which is
the case `q = 1`; there the constant came out as `2`, the length of `[−1, 1]`. -/

/-- The `q`-dimensional quadratic germ `x ↦ ‖x‖²`, print's `‖u‖²`. Written through
`EuclideanSpace.real_norm_sq_eq` as the sum of squares of the coordinates, which is the form the
chart produces. -/
@[expose] public noncomputable def quadraticGerm (q : ℕ) (x : EuclideanSpace ℝ (Fin q)) : ℝ :=
  ∑ i, x i ^ 2

public theorem quadraticGerm_eq_norm_sq {q : ℕ} (x : EuclideanSpace ℝ (Fin q)) :
    quadraticGerm q x = ‖x‖ ^ 2 := by
  rw [quadraticGerm, EuclideanSpace.real_norm_sq_eq]

public theorem quadraticGerm_nonneg {q : ℕ} (x : EuclideanSpace ℝ (Fin q)) :
    0 ≤ quadraticGerm q x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Inside a ball of radius `δ`, and for `0 < ε < δ²`, the sublevel set of `‖x‖²` is exactly
the closed ball of radius `√ε`. -/
public theorem sublevel_quadraticGerm_eq {q : ℕ} {δ ε : ℝ} (hε : 0 < ε) (hδ : √ε < δ) :
    {x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin q)) δ | quadraticGerm q x ≤ ε}
      = Metric.closedBall (0 : EuclideanSpace ℝ (Fin q)) (√ε) := by
  ext x
  simp only [Set.mem_ofPred_eq, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
    quadraticGerm_eq_norm_sq]
  constructor
  · rintro ⟨-, h2⟩
    rw [show ‖x‖ = √(‖x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg x)).symm]
    exact Real.sqrt_le_sqrt h2
  · intro h
    refine ⟨lt_of_le_of_lt h hδ, ?_⟩
    have h0 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    nlinarith [Real.sq_sqrt hε.le]

/-- The volume of the `ε`-sublevel set of `‖x‖²` in a ball of radius `δ`, for `0 < ε < δ²`:
`ε^{q/2}` times the volume of the unit ball. -/
public theorem sublevelVolume_quadraticGerm {q : ℕ} {δ ε : ℝ} (hε : 0 < ε) (hδ : √ε < δ) :
    sublevelVolume (quadraticGerm q) 0 δ ε
      = ε ^ ((q : ℝ) / 2) *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal := by
  rw [sublevelVolume, sublevel_quadraticGerm_eq hε hδ,
    MeasureTheory.Measure.addHaar_closedBall _ _ (Real.sqrt_nonneg ε),
    finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (ε ^ ((1:ℝ)/2)) q, ← Real.rpow_mul hε.le]
  ring_nf

/-- **The pair of the `u`-block.** The quadratic germ `‖x‖²` on `ℝ^q` has exact local pair
`(q/2, 1)` at the origin, for `q ≥ 1`. Print's transverse directions contribute `q/2` to `λ`
and nothing to the multiplicity. -/
public theorem hasExactLocalPair_quadraticGerm {q : ℕ} (hq : 0 < q) :
    HasExactLocalPair (quadraticGerm q) 0 ((q : ℝ) / 2) 1 := by
  have hvol : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin q)) 1)).toReal := by
    refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
    exact (Metric.measure_ball_pos volume 0 one_pos).ne'
  refine Or.inr ⟨by positivity, le_refl 1, 1, zero_lt_one, ∅, Set.countable_empty,
    fun δ hδ _ => ⟨_, hvol, Filter.Tendsto.congr' ?_ tendsto_const_nhds⟩⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < δ ^ 2 by nlinarith [hδ.1])] with ε hε
  have hε0 : (0:ℝ) < ε := hε.1
  have hsq : √ε < δ := by
    have h := Real.sqrt_lt_sqrt hε0.le hε.2
    rwa [Real.sqrt_sq hδ.1.le] at h
  have hpow : (0:ℝ) < ε ^ ((q : ℝ) / 2) := Real.rpow_pos_of_pos hε0 _
  rw [sublevelVolume_quadraticGerm hε0 hsq, volumeScale, show (1:ℕ) - 1 = 0 from rfl,
    pow_zero, mul_one, eq_comm, mul_comm (ε ^ ((q:ℝ)/2)), div_self (by positivity)]

/-- The same germ satisfies the operational relation, by the bridge — the form the transfer
combinators consume. -/
public theorem hasLocalVolumeOrder_quadraticGerm {q : ℕ} (hq : 0 < q) :
    HasLocalVolumeOrder (quadraticGerm q) 0 ((q : ℝ) / 2) 1 :=
  exactLocalPair_imp_volumeOrder (hasExactLocalPair_quadraticGerm hq)

/-- The pair is determined: `(q/2, 1)` is the only pair for the quadratic germ. -/
public theorem eq_of_hasLocalVolumeOrder_quadraticGerm {q : ℕ} (hq : 0 < q) {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder (quadraticGerm q) 0 lam m) : lam = (q : ℝ) / 2 ∧ m = 1 :=
  volumeOrder_unique h (hasLocalVolumeOrder_quadraticGerm hq)


/-! ## The product rule, when one factor has multiplicity one

Print's Section 6 combinator for germs in disjoint variables: the pair of
`(x, y) ↦ f x + g y`. In general the exponents add and the multiplicities combine as
`m = m₁ + m₂ − 1`, which needs a Mellin convolution of the two scales — the crude product
bound loses one logarithm and is not sharp.

**When one factor has multiplicity `1` the crude bound is already sharp.** With `m₁ = 1` the
rule reads `m = m₂`, and both inclusions

    {f ≤ ε/2} × {g ≤ ε/2} ⊆ {f + g ≤ ε} ⊆ {f ≤ ε} × {g ≤ ε}

give the scale `ε^{λ₁+λ₂}(log(1/ε))^{m₂−1}` up to constants — the first inclusion needing
nothing, the second needing only `f, g ≥ 0`. So no convolution is required, and this is
exactly the case the chart produces: the `u`-block's pair is `(q/2, 1)`
(`hasExactLocalPair_quadraticGerm`), so multiplying it into the residual block's pair moves
the exponent by `q/2` and leaves the multiplicity alone.

That is why print can write `λ = ½(q + min{…})` and `m = ` the residual multiplicity, with no
interaction term between the two blocks.

The general product rule, for two factors of arbitrary multiplicity, is **not** proved here.
-/

/-- `volumeScale` is multiplicative in the exponent when one multiplicity is `1`:
`ε^{λ₁} · ε^{λ₂}(log(1/ε))^{m−1} = ε^{λ₁+λ₂}(log(1/ε))^{m−1}`. This is the whole reason the
multiplicity-one case needs no convolution. -/
public theorem volumeScale_mul_one {lam₁ lam₂ : ℝ} {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    volumeScale lam₁ 1 ε * volumeScale lam₂ m ε = volumeScale (lam₁ + lam₂) m ε := by
  simp only [volumeScale, Nat.sub_self, pow_zero, mul_one]
  rw [Real.rpow_add hε]
  ring

/-- **The upper inclusion.** If `f, g ≥ 0` then `{f + g ≤ ε}` sits inside the product of the
two one-sided sublevel sets, so the product sublevel volume is at most the product of the
factors' sublevel volumes at the *same* radius and level. -/
public theorem sublevelVolume_add_le {n k : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin k) → ℝ} {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin k)} {δ ε : ℝ}
    (hF : ∀ x y, F (euclideanProdEquiv n k (x, y)) = f x + g y)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    sublevelVolume F (euclideanProdEquiv n k (w, v)) δ ε
      ≤ sublevelVolume f w δ ε * sublevelVolume g v δ ε := by
  refine sublevelVolume_le_prod (A := {x ∈ Metric.ball w δ | f x ≤ ε})
    (B := {y ∈ Metric.ball v δ | g y ≤ ε}) (sublevelVolume_ne_top f w δ ε)
    (sublevelVolume_ne_top g v δ ε) (fun p hp1 hp2 => ?_)
  rw [← Prod.mk.eta (p := p)] at hp1 hp2
  obtain ⟨h1, h2⟩ := dist_lt_of_euclideanProdEquiv_mem_ball hp1
  rw [hF] at hp2
  exact ⟨⟨Metric.mem_ball.2 h1, by linarith [hg0 p.2]⟩,
    ⟨Metric.mem_ball.2 h2, by linarith [hf0 p.1]⟩⟩

/-- **The lower inclusion.** Halving both the radius and the level puts a product window
inside the sublevel set, with no hypothesis on the signs. -/
public theorem le_sublevelVolume_add {n k : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin k) → ℝ} {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin k)} {δ ε : ℝ} (hδ : 0 < δ)
    (hF : ∀ x y, F (euclideanProdEquiv n k (x, y)) = f x + g y) :
    sublevelVolume f w (δ / 2) (ε / 2) * sublevelVolume g v (δ / 2) (ε / 2)
      ≤ sublevelVolume F (euclideanProdEquiv n k (w, v)) δ ε := by
  refine prod_le_sublevelVolume (A := {x ∈ Metric.ball w (δ / 2) | f x ≤ ε / 2})
    (B := {y ∈ Metric.ball v (δ / 2) | g y ≤ ε / 2}) (fun p hp1 hp2 => ⟨?_, ?_⟩)
  · rw [← Prod.mk.eta (p := p)]
    exact euclideanProdEquiv_mem_ball (by linarith) (Metric.mem_ball.1 hp1.1)
      (Metric.mem_ball.1 hp2.1)
  · rw [← Prod.mk.eta (p := p), hF]
    linarith [hp1.2, hp2.2]

/-- **The product rule, multiplicity-one case.** If `f` has pair `(λ₁, 1)`, `g` has pair
`(λ₂, m)`, both germs are nonnegative, and `F` is `f + g` in split coordinates, then `F` has
pair `(λ₁ + λ₂, m)`.

Both exponents are required positive: `HasLocalVolumeOrder`'s degenerate branch is reserved
for a germ vanishing on a whole neighbourhood, and a factor in that branch is handled by
`hasLocalVolumeOrder_freeCoords` instead — there `F` really does ignore its second argument. -/
public theorem hasLocalVolumeOrder_add {n k : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin k) → ℝ} {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin k)} {lam₁ lam₂ : ℝ} {m : ℕ}
    (hF : ∀ x y, F (euclideanProdEquiv n k (x, y)) = f x + g y)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hf : HasLocalVolumeOrder f w lam₁ 1) (hg : HasLocalVolumeOrder g v lam₂ m) :
    HasLocalVolumeOrder F (euclideanProdEquiv n k (w, v)) (lam₁ + lam₂) m := by
  rcases hf with ⟨-, hl1, -⟩ | ⟨-, -, δ₁, hδ₁, hb1⟩
  · exact absurd hl1 (ne_of_gt hlam₁)
  rcases hg with ⟨-, hl2, -⟩ | ⟨-, hm, δ₂, hδ₂, hb2⟩
  · exact absurd hl2 (ne_of_gt hlam₂)
  obtain ⟨s, S, hs, -, hsc⟩ := exists_volumeScale_div_bounds (lam₁ + lam₂) m two_pos
  refine Or.inr ⟨by linarith, hm, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ => ?_⟩
  have hδ1 : δ ∈ Set.Ioo 0 δ₁ := ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩
  have hδ2 : δ ∈ Set.Ioo 0 δ₂ := ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_right _ _)⟩
  have hδ1' : δ / 2 ∈ Set.Ioo 0 δ₁ := ⟨by linarith [hδ.1], by linarith [hδ1.2, hδ.1]⟩
  have hδ2' : δ / 2 ∈ Set.Ioo 0 δ₂ := ⟨by linarith [hδ.1], by linarith [hδ2.2, hδ.1]⟩
  obtain ⟨b₁, A₁, hb₁pos, hb₁le, hbd₁⟩ := hb1 δ hδ1
  obtain ⟨b₂, A₂, hb₂pos, hb₂le, hbd₂⟩ := hb2 δ hδ2
  obtain ⟨a₁, B₁, ha₁, ha₁le, hbd₁'⟩ := hb1 (δ / 2) hδ1'
  obtain ⟨a₂, B₂, ha₂, ha₂le, hbd₂'⟩ := hb2 (δ / 2) hδ2'
  refine ⟨a₁ * a₂ * s, max (A₁ * A₂) (a₁ * a₂ * s), by positivity, le_max_right _ _, ?_⟩
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ volumeScale (lam₁ + lam₂) m ε := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    have h1 : 0 < ε ^ (lam₁ + lam₂) := Real.rpow_pos_of_pos hε.1 _
    have h2 : (0 : ℝ) < Real.log (1 / ε) :=
      Real.log_pos (by rw [lt_div_iff₀ hε.1]; linarith [hε.2])
    exact le_of_lt (mul_pos h1 (pow_pos h2 _))
  filter_upwards [hbd₁, hbd₂, (tendsto_div_const_nhdsGT two_pos).eventually hbd₁',
    (tendsto_div_const_nhdsGT two_pos).eventually hbd₂', hsc, hpos,
    self_mem_nhdsWithin] with ε hε₁ hε₂ hε₁' hε₂' hεsc hεv hε0
  have hε0' : (0 : ℝ) < ε := hε0
  -- with `m₁ = 1` the first scale is just `(ε/2)^{λ₁}`, hence strictly positive
  have hvs1 : 0 < a₁ * volumeScale lam₁ 1 (ε / 2) := by
    have hv : volumeScale lam₁ 1 (ε / 2) = (ε / 2) ^ lam₁ := by simp [volumeScale]
    have hp : (0 : ℝ) < (ε / 2) ^ lam₁ := Real.rpow_pos_of_pos (by linarith) _
    rw [hv]
    positivity
  refine ⟨?_, ?_⟩
  · -- lower: halve both, then rescale the scale back to `ε`
    calc a₁ * a₂ * s * volumeScale (lam₁ + lam₂) m ε
        = a₁ * a₂ * (s * volumeScale (lam₁ + lam₂) m ε) := by ring
      _ ≤ a₁ * a₂ * volumeScale (lam₁ + lam₂) m (ε / 2) :=
          mul_le_mul_of_nonneg_left hεsc.1 (by positivity)
      _ = a₁ * volumeScale lam₁ 1 (ε / 2) * (a₂ * volumeScale lam₂ m (ε / 2)) := by
          rw [← volumeScale_mul_one (lam₁ := lam₁) (lam₂ := lam₂) (m := m) (by linarith)]
          ring
      _ ≤ a₁ * volumeScale lam₁ 1 (ε / 2) * sublevelVolume g v (δ / 2) (ε / 2) :=
          mul_le_mul_of_nonneg_left hε₂'.1 hvs1.le
      _ ≤ sublevelVolume f w (δ / 2) (ε / 2) * sublevelVolume g v (δ / 2) (ε / 2) :=
          mul_le_mul_of_nonneg_right hε₁'.1 ENNReal.toReal_nonneg
      _ ≤ _ := le_sublevelVolume_add hδ.1 hF
  · -- upper: the two one-sided sublevel sets, at the same radius and level
    calc sublevelVolume F (euclideanProdEquiv n k (w, v)) δ ε
        ≤ sublevelVolume f w δ ε * sublevelVolume g v δ ε := sublevelVolume_add_le hF hf0 hg0
      _ ≤ (A₁ * volumeScale lam₁ 1 ε) * (A₂ * volumeScale lam₂ m ε) :=
          mul_le_mul hε₁.2 hε₂.2 ENNReal.toReal_nonneg
            (le_trans ENNReal.toReal_nonneg hε₁.2)
      _ = A₁ * A₂ * volumeScale (lam₁ + lam₂) m ε := by
          rw [← volumeScale_mul_one (lam₁ := lam₁) (lam₂ := lam₂) (m := m) hε0']
          ring
      _ ≤ max (A₁ * A₂) (a₁ * a₂ * s) * volumeScale (lam₁ + lam₂) m ε :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hεv


/-! ### The product rule is consistent with the direct computation

The quadratic germ splits as a sum over any decomposition of its coordinates, so the product
rule applied to `‖x‖²` on `ℝ^n` and `‖y‖²` on `ℝ^k` must return the pair that
`hasExactLocalPair_quadraticGerm` computes directly on `ℝ^{n+k}`. It does: `n/2 + k/2` and
multiplicity `1` either way. This is the check that would catch an off-by-one in the
multiplicity rule, and it is the reason the multiplicity-one case can be trusted without the
convolution. -/

@[simp] public theorem euclideanProdEquiv_zero (n k : ℕ) :
    euclideanProdEquiv n k (0, 0) = 0 := by
  refine PiLp.ext fun j => ?_
  rw [euclideanProdEquiv_apply]
  rcases finSumFinEquiv.symm j with i | i <;> simp

/-- `‖·‖²` splits over the coordinate decomposition: the germ on `ℝ^{n+k}` is the sum of the
germs on the two factors. -/
public theorem quadraticGerm_add (n k : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin k)) :
    quadraticGerm (n + k) (euclideanProdEquiv n k (x, y))
      = quadraticGerm n x + quadraticGerm k y := by
  have hre : ∀ s : Fin n ⊕ Fin k,
      (euclideanProdEquiv n k (x, y)).ofLp (finSumFinEquiv s) = Sum.elim x.ofLp y.ofLp s := by
    intro s
    rw [euclideanProdEquiv_apply, finSumFinEquiv.symm_apply_apply]
  simp only [quadraticGerm]
  rw [← Fintype.sum_equiv (finSumFinEquiv (m := n) (n := k))
    (fun s => (euclideanProdEquiv n k (x, y)).ofLp (finSumFinEquiv s) ^ 2)
    (fun j => (euclideanProdEquiv n k (x, y)).ofLp j ^ 2) (fun _ => rfl)]
  rw [Fintype.sum_sum_type]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by rw [hre]; rfl

/-- **The two routes to the pair of `‖·‖²` on `ℝ^{n+k}` agree.** The product rule, fed the
two factors' pairs `(n/2, 1)` and `(k/2, 1)`, returns `(n/2 + k/2, 1)`; and
`hasLocalVolumeOrder_quadraticGerm` gives `((n+k)/2, 1)` directly. -/
public theorem hasLocalVolumeOrder_quadraticGerm_add {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    HasLocalVolumeOrder (quadraticGerm (n + k)) 0 ((n : ℝ) / 2 + (k : ℝ) / 2) 1 := by
  have h := hasLocalVolumeOrder_add (f := quadraticGerm n) (g := quadraticGerm k)
    (F := quadraticGerm (n + k)) (w := 0) (v := 0)
    (fun x y => quadraticGerm_add n k x y)
    (fun x => quadraticGerm_nonneg x) (fun y => quadraticGerm_nonneg y)
    (by positivity) (by positivity)
    (hasLocalVolumeOrder_quadraticGerm hn) (hasLocalVolumeOrder_quadraticGerm hk)
  rwa [euclideanProdEquiv_zero] at h

/-- And the exponents are literally equal, so the two routes give the same pair. -/
public theorem quadraticGerm_add_exponent (n k : ℕ) :
    ((n : ℝ) / 2 + (k : ℝ) / 2) = ((n + k : ℕ) : ℝ) / 2 := by
  push_cast
  ring


end AISafetyAtlas.SingularLearning
