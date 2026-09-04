module

public import AISafetyAtlas.SingularLearning.JacobianSandwich

/-!
# Worked models: the Jacobian sandwich

The measure-theoretic half of print's Lemma 6.4(i), on the maps where both sides can be
computed: a scaling, whose Jacobian is constant, and the identity, whose Jacobian is one.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory Set

/-- **The identity moves no volume.** Both bounds are equalities at `m = M = 1`. -/
example {D : ℕ} {s : Set (EuclideanSpace ℝ (Fin D))} (hs : MeasurableSet s)
    (hfin : volume s ≠ ⊤) :
    1 * (volume s).toReal ≤ (volume ((fun x => x) '' s)).toReal ∧
      (volume ((fun x => x) '' s)).toReal ≤ 1 * (volume s).toReal := by
  refine measureReal_image_sandwich (φ' := fun _ => ContinuousLinearMap.id ℝ _) hs hfin
    (fun x _ => (hasFDerivAt_id x).hasFDerivWithinAt) (Set.injOn_id s) zero_le_one
    (fun _ _ => ?_) (fun _ _ => ?_) <;>
  · rw [show (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin D))).det = 1 from by
      simp [ContinuousLinearMap.det], abs_one]

/-- **A `C¹` injection expands volume by at most `sup |det Dφ|`.** -/
example {D : ℕ}
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {φ' : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)}
    {s : Set (EuclideanSpace ℝ (Fin D))} (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hinj : Set.InjOn φ s)
    {M : ℝ} (hM : ∀ x ∈ s, |(φ' x).det| ≤ M) :
    volume (φ '' s) ≤ ENNReal.ofReal M * volume s :=
  measure_image_le_of_abs_det_le hs hφ' hinj hM

/-- And contracts it by at most `inf |det Dφ|`. -/
example {D : ℕ}
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {φ' : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)}
    {s : Set (EuclideanSpace ℝ (Fin D))} (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hinj : Set.InjOn φ s)
    {m : ℝ} (hm : ∀ x ∈ s, m ≤ |(φ' x).det|) :
    ENNReal.ofReal m * volume s ≤ volume (φ '' s) :=
  le_measure_image_of_le_abs_det hs hφ' hinj hm

/-- **The empty set is not a special case that had to be assumed away.** -/
example {D : ℕ}
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {φ' : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)}
    {m M : ℝ} (hm0 : 0 ≤ m) :
    m * (volume (∅ : Set (EuclideanSpace ℝ (Fin D)))).toReal
        ≤ (volume (φ '' ∅)).toReal ∧
      (volume (φ '' (∅ : Set (EuclideanSpace ℝ (Fin D))))).toReal
        ≤ M * (volume (∅ : Set (EuclideanSpace ℝ (Fin D)))).toReal :=
  measureReal_image_sandwich (φ' := φ') MeasurableSet.empty (by simp)
    (fun _ h => absurd h (Set.notMem_empty _)) (Set.injOn_empty φ) hm0
    (fun _ h => absurd h (Set.notMem_empty _)) (fun _ h => absurd h (Set.notMem_empty _))

end AISafetyAtlas.Examples.SingularLearning
