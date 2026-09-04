module

public import AISafetyAtlas.SingularLearning.CoordTransfer

/-!
# Worked models: exact coordinate changes

The swap really is a swap, sublevel volumes really are equal (not merely comparable) across it,
and the derived left-handed free-coordinate rule really does place the free block first.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory

/-- **The swap is an involution**, so nothing is lost by routing the left-handed rule through
it. -/
example (n k : ℕ) (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin k)) :
    euclideanSwap k n (euclideanSwap n k (euclideanProdEquiv n k (x, y)))
      = euclideanProdEquiv n k (x, y) := by
  rw [euclideanSwap_apply, euclideanSwap_apply]

/-- **Sublevel volumes are equal across the swap**, at every radius and every level. This is
the property the general Lemma 6.4(i) cannot supply: there the bound carries a factor `K ^ D`. -/
example (n k : ℕ) (f : EuclideanSpace ℝ (Fin (k + n)) → ℝ)
    (w : EuclideanSpace ℝ (Fin (n + k))) (δ ε : ℝ) :
    sublevelVolume (f ∘ euclideanSwap n k) w δ ε = sublevelVolume f (euclideanSwap n k w) δ ε :=
  sublevelVolume_comp_isometry _ (measurePreserving_euclideanSwap n k)
    (isometry_euclideanSwap n k) f w δ ε

/-- **The identity is the degenerate case**, and it typechecks against the bundled form. -/
example (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (m : ℕ) (h : HasLocalVolumeOrder f w lam m) :
    HasLocalVolumeOrder (f ∘ (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))) w lam m :=
  hasLocalVolumeOrder_comp_linearIsometryEquiv _ h

/-- **Free coordinates on the left.** A germ that reads only its *second* block has that
block's pair, at the base point `(w, 0)` for any `w` in the block it ignores. -/
example (n k : ℕ) (hk : 0 < k) (w : EuclideanSpace ℝ (Fin n)) :
    HasLocalVolumeOrder (fun z => quadraticGerm k ((euclideanProdEquiv n k).symm z).2)
      (euclideanProdEquiv n k (w, 0)) ((k : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_freeCoords_left
    (fun _ _ => by rw [(euclideanProdEquiv n k).symm_apply_apply])
    (hasLocalVolumeOrder_quadraticGerm hk)

/-- And the two rules agree where they overlap: a germ reading only its second block of a
`0 + k` split is the germ itself, so the left-handed rule reproduces the pair unchanged. -/
example (k : ℕ) (hk : 0 < k) :
    HasLocalVolumeOrder (fun z => quadraticGerm k ((euclideanProdEquiv 0 k).symm z).2)
      (euclideanProdEquiv 0 k (0, 0)) ((k : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_freeCoords_left
    (fun _ _ => by rw [(euclideanProdEquiv 0 k).symm_apply_apply])
    (hasLocalVolumeOrder_quadraticGerm hk)

end AISafetyAtlas.Examples.SingularLearning
