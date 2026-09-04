module

public import AISafetyAtlas.SingularLearning.PairTransfer
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Exact coordinate changes: isometries, and the block swap

`PairTransfer.lean` reads a germ in *one* fixed coordinate layout: the free block last
(`hasLocalVolumeOrder_freeCoords`), the multiplicity-one summand first
(`hasLocalVolumeOrder_add`).  A germ that arrives in another layout has to be moved into that
one, and the elimination chart produces several — an empty `u` block, an empty gauge block, a
residual block packed `(X, Y)` where the chart lists `(Y, X)`.

Every such move is a *bijective isometry that preserves Lebesgue measure*.  Under such a map
sublevel volumes are not merely comparable but **equal**, at every radius and every level:
balls map to balls of the same radius, and the measure is carried across untouched.  So the
whole of `HasLocalVolumeOrder` transfers with the same `δ₀` and the same two constants, and
nothing has to be re-estimated.

This is the exact special case of print's Lemma 6.4(i) (`DiffeoTransfer.lean`), and it is
separated out because it costs nothing: no Lipschitz constant, no Jacobian, no Hausdorff
comparison.  Reaching for the general lemma where an isometry will do would import bounds that
are not tight and cannot be discharged.

The one derived combinator here is `hasLocalVolumeOrder_freeCoords_left`, print's Lemma 6.4(ii)
with the free block on the *other* side, obtained from the block swap rather than by repeating
the argument.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

/-! ## Transfer along a measure-preserving isometry -/

/-- **Sublevel volumes are literally equal across a measure-preserving isometry.** Not
comparable — equal, at every radius and every level. -/
public theorem sublevelVolume_comp_isometry {n₁ n₂ : ℕ}
    (e : EuclideanSpace ℝ (Fin n₁) ≃ᵐ EuclideanSpace ℝ (Fin n₂))
    (hmp : MeasurePreserving e volume volume) (hiso : Isometry (e : _ → _))
    (f : EuclideanSpace ℝ (Fin n₂) → ℝ) (w : EuclideanSpace ℝ (Fin n₁)) (δ ε : ℝ) :
    sublevelVolume (f ∘ e) w δ ε = sublevelVolume f (e w) δ ε := by
  have hset : {x ∈ Metric.ball w δ | (f ∘ e) x ≤ ε}
      = e ⁻¹' {y ∈ Metric.ball (e w) δ | f y ≤ ε} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, Function.comp_apply,
      hiso.dist_eq]
  rw [sublevelVolume, sublevelVolume, hset, ← MeasurableEquiv.map_apply, hmp.map_eq]

/-- **The pair transfers across a measure-preserving isometry**, with the same `δ₀` and the
same two constants at every radius. -/
public theorem hasLocalVolumeOrder_comp_isometry {n₁ n₂ : ℕ}
    (e : EuclideanSpace ℝ (Fin n₁) ≃ᵐ EuclideanSpace ℝ (Fin n₂))
    (hmp : MeasurePreserving e volume volume) (hiso : Isometry (e : _ → _))
    {f : EuclideanSpace ℝ (Fin n₂) → ℝ} {w : EuclideanSpace ℝ (Fin n₁)} {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder f (e w) lam m) :
    HasLocalVolumeOrder (f ∘ e) w lam m := by
  rcases h with ⟨hz, hl, hm⟩ | ⟨hlam, hm, δ₀, hδ₀, hb⟩
  · exact Or.inl ⟨(hiso.continuous.continuousAt).eventually hz, hl, hm⟩
  refine Or.inr ⟨hlam, hm, δ₀, hδ₀, fun δ hδ => ?_⟩
  obtain ⟨cL, cU, hcL, hcLU, hbd⟩ := hb δ hδ
  exact ⟨cL, cU, hcL, hcLU, by
    simpa only [sublevelVolume_comp_isometry e hmp hiso f w δ] using hbd⟩

/-- The bundled form: a linear isometry equivalence of Euclidean spaces carries the pair, with
measure preservation supplied by `LinearIsometryEquiv.measurePreserving`. -/
public theorem hasLocalVolumeOrder_comp_linearIsometryEquiv {n₁ n₂ : ℕ}
    (e : EuclideanSpace ℝ (Fin n₁) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n₂))
    {f : EuclideanSpace ℝ (Fin n₂) → ℝ} {w : EuclideanSpace ℝ (Fin n₁)} {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder f (e w) lam m) :
    HasLocalVolumeOrder (f ∘ e) w lam m :=
  hasLocalVolumeOrder_comp_isometry e.toMeasurableEquiv e.measurePreserving e.isometry h

/-! ## The block swap -/

/-- Exchanging the two coordinate blocks: `ℝ^{n+k} ≃ ℝ^{k+n}`. A permutation of coordinates,
packaged so that its measure preservation is a composition of three Mathlib lemmas. -/
@[expose] public noncomputable def euclideanSwap (n k : ℕ) :
    EuclideanSpace ℝ (Fin (n + k)) ≃ᵐ EuclideanSpace ℝ (Fin (k + n)) :=
  (euclideanProdEquiv n k).symm.trans
    (MeasurableEquiv.prodComm.trans (euclideanProdEquiv k n))

@[simp] public theorem euclideanSwap_apply (n k : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin k)) :
    euclideanSwap n k (euclideanProdEquiv n k (x, y)) = euclideanProdEquiv k n (y, x) := by
  simp only [euclideanSwap, MeasurableEquiv.trans_apply, MeasurableEquiv.symm_apply_apply]
  rfl

public theorem measurePreserving_euclideanSwap (n k : ℕ) :
    MeasurePreserving (euclideanSwap n k) volume volume := by
  have h1 : MeasurePreserving (⇑(euclideanProdEquiv n k).symm) volume volume :=
    (measurePreserving_euclideanProdEquiv n k).symm _
  have h2 : MeasurePreserving
      (⇑(MeasurableEquiv.prodComm :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) ≃ᵐ _)) volume volume := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.Measure.measurePreserving_swap
  exact ((measurePreserving_euclideanProdEquiv k n).comp h2).comp h1

public theorem isometry_euclideanSwap (n k : ℕ) : Isometry (euclideanSwap n k) := by
  refine Isometry.of_dist_eq fun z z' => ?_
  obtain ⟨⟨x, y⟩, rfl⟩ := (euclideanProdEquiv n k).surjective z
  obtain ⟨⟨x', y'⟩, rfl⟩ := (euclideanProdEquiv n k).surjective z'
  have hd : dist (euclideanSwap n k (euclideanProdEquiv n k (x, y)))
      (euclideanSwap n k (euclideanProdEquiv n k (x', y'))) ^ 2
      = dist (euclideanProdEquiv n k (x, y)) (euclideanProdEquiv n k (x', y')) ^ 2 := by
    rw [euclideanSwap_apply, euclideanSwap_apply, dist_sq_euclideanProdEquiv,
      dist_sq_euclideanProdEquiv]
    ring
  calc dist (euclideanSwap n k (euclideanProdEquiv n k (x, y)))
        (euclideanSwap n k (euclideanProdEquiv n k (x', y')))
      = √(dist (euclideanSwap n k (euclideanProdEquiv n k (x, y)))
          (euclideanSwap n k (euclideanProdEquiv n k (x', y'))) ^ 2) :=
        (Real.sqrt_sq dist_nonneg).symm
    _ = √(dist (euclideanProdEquiv n k (x, y)) (euclideanProdEquiv n k (x', y')) ^ 2) := by
        rw [hd]
    _ = dist (euclideanProdEquiv n k (x, y)) (euclideanProdEquiv n k (x', y')) :=
        Real.sqrt_sq dist_nonneg

/-! ## Lemma 6.4(ii) with the free block first -/

/-- **Free coordinates on the left.** If `F` ignores the *first* `n` coordinates, its pair at
`(w, v)` is `f`'s pair at `v`. Derived from `hasLocalVolumeOrder_freeCoords` by the block swap,
not by repeating its argument. -/
public theorem hasLocalVolumeOrder_freeCoords_left {n k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {v : EuclideanSpace ℝ (Fin k)} {lam : ℝ} {m : ℕ}
    (hF : ∀ x y, F (euclideanProdEquiv n k (x, y)) = f y)
    (hf : HasLocalVolumeOrder f v lam m) :
    HasLocalVolumeOrder F (euclideanProdEquiv n k (w, v)) lam m := by
  set G : EuclideanSpace ℝ (Fin (k + n)) → ℝ := F ∘ euclideanSwap k n with hG
  have hGapp : ∀ (y : EuclideanSpace ℝ (Fin k)) (x : EuclideanSpace ℝ (Fin n)),
      G (euclideanProdEquiv k n (y, x)) = f y := by
    intro y x
    rw [hG, Function.comp_apply, euclideanSwap_apply, hF]
  have hGpair : HasLocalVolumeOrder G (euclideanProdEquiv k n (v, w)) lam m :=
    hasLocalVolumeOrder_freeCoords hGapp hf
  have hbase : (euclideanSwap k n).symm (euclideanProdEquiv n k (w, v))
      = euclideanProdEquiv k n (v, w) := by
    rw [MeasurableEquiv.symm_apply_eq, euclideanSwap_apply]
  have hcomp : G ∘ ⇑(euclideanSwap k n).symm = F := by
    funext z
    rw [hG, Function.comp_apply, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  have hisosymm : Isometry (⇑(euclideanSwap k n).symm) := by
    refine Isometry.of_dist_eq fun z z' => ?_
    have hz := (isometry_euclideanSwap k n).dist_eq
      ((euclideanSwap k n).symm z) ((euclideanSwap k n).symm z')
    rw [MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply] at hz
    exact hz.symm
  have := hasLocalVolumeOrder_comp_isometry (euclideanSwap k n).symm
    ((measurePreserving_euclideanSwap k n).symm _) hisosymm
    (f := G) (w := euclideanProdEquiv n k (w, v)) (by rw [hbase]; exact hGpair)
  rwa [hcomp] at this

end AISafetyAtlas.SingularLearning
