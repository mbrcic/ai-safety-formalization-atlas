module

public import AISafetyAtlas.SingularLearning.DiffeoTransfer
public import AISafetyAtlas.SingularLearning.PairTransfer

/-!
# Worked models: Lemma 6.4(i)

The transfer is exercised on the one germ whose pair is known unconditionally, `‖x‖²`, along the
three shapes the O70 assembly uses: a dilation (nonlinear on the germ — it multiplies it by four),
a translation (which moves the base point), and a linear equivalence (print's orbit transfer).

A dilation is the sharpest of the three as a probe: `‖2x‖² = 4‖x‖²`, so the germ genuinely
changes, and only the *pair* is claimed to survive. The last example checks that against the
independent route through Lemma 6.2.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory Set
open scoped NNReal ENNReal

/-- **A dilation preserves the pair.** `x ↦ 2x` is its own kind of diffeomorphism of `ℝ^q`: entire,
with entire inverse `x ↦ x/2`. -/
example (q : ℕ) (hq : 0 < q) :
    HasLocalVolumeOrder (quadraticGerm q ∘ fun x => (2 : ℝ) • x) 0 ((q : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_comp_of_analytic (ψ := fun y => (2 : ℝ)⁻¹ • y) isOpen_univ isOpen_univ
    (mem_univ _) (mapsTo_univ _ _)
    ⟨fun x _ => by simp [smul_smul], fun y _ => by simp [smul_smul]⟩
    (analyticOnNhd_const.smul analyticOnNhd_id) (analyticOnNhd_const.smul analyticOnNhd_id)
    (by simpa using hasLocalVolumeOrder_quadraticGerm hq)

/-- And it does change the germ: the transferred germ is four times the original, not equal to it.
So the previous example is not the identity in disguise. -/
example (q : ℕ) (x : EuclideanSpace ℝ (Fin q)) :
    (quadraticGerm q ∘ fun y => (2 : ℝ) • y) x = 4 * quadraticGerm q x := by
  simp only [Function.comp_apply, quadraticGerm_eq_norm_sq, norm_smul, Real.norm_ofNat]
  ring

/-- **A translation moves the base point.** The pair of `x ↦ ‖x + b‖²` sits at `-b`. -/
example (q : ℕ) (hq : 0 < q) (b : EuclideanSpace ℝ (Fin q)) :
    HasLocalVolumeOrder (fun x => quadraticGerm q (x + b)) (-b) ((q : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_comp_add_const b (-b) (by simpa using hasLocalVolumeOrder_quadraticGerm hq)

/-- **The orbit transfer at the identity.** The linear corollary applies to any continuous linear
equivalence; `refl` is the degenerate check that it typechecks against the germ's own pair. -/
example (q : ℕ) (hq : 0 < q) :
    HasLocalVolumeOrder (quadraticGerm q ∘ ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin q)))
      0 ((q : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_comp_continuousLinearEquiv _
    (by simpa using hasLocalVolumeOrder_quadraticGerm hq)

/-- **The neutral branch transfers.** A germ vanishing on a neighbourhood of the image point pulls
back to one vanishing near the source point, and keeps the convention pair `(0, 1)`. -/
example (D : ℕ) (b w : EuclideanSpace ℝ (Fin D)) :
    HasLocalVolumeOrder (fun x => (fun _ : EuclideanSpace ℝ (Fin D) => (0 : ℝ)) (x + b)) w 0 1 :=
  hasLocalVolumeOrder_comp_add_const b w
    (Or.inl ⟨Filter.Eventually.of_forall fun _ => rfl, rfl, rfl⟩)

/-- **The volume bound at the identity.** A `1`-Lipschitz map moves no volume. -/
example {D : ℕ} (s : Set (EuclideanSpace ℝ (Fin D))) :
    volume ((fun x => x) '' s) ≤ (1 : ℝ≥0∞) ^ D * volume s :=
  measure_image_le_of_lipschitzOnWith (K := 1) (LipschitzWith.id.lipschitzOnWith)

/-- **The Hausdorff normalisation is nondegenerate.** The scalar relating `μH[D]` to Lebesgue
measure is strictly positive, which is what makes the two-sided sandwich two-sided. -/
example (D : ℕ) : ∃ c : ℝ≥0, 0 < c ∧
    (μH[(D : ℝ)] : Measure (EuclideanSpace ℝ (Fin D))) = c • volume :=
  exists_hausdorffMeasure_eq_smul_volume D

end AISafetyAtlas.Examples.SingularLearning
