module

public import AISafetyAtlas.SingularLearning.FreeBlockPair

/-!
# Worked models for the free block read as a local pair

`FreeBlockPair.lean` transports the product-box band estimate of
`FreeBlockBand.lean` onto a single `EuclideanSpace ℝ (Fin (p + q + s))` with
Euclidean balls, and concludes `HasLocalVolumeOrder (freeBlockGerm p q s g) 0 1 1`.

The statement carries `2 ≤ p`, a `NeZero q` instance, and a shift `g` continuous
with `g 0 = 0`.  This file discharges all of it at the concrete shape
`(p, q, s) = (2, 1, 1)`, so the pair `(1, 1)` is asserted of something real
rather than of an empty hypothesis set.

Two shifts are exercised, matching `Examples/SingularLearning/FreeBlockBand.lean`:
`g ζ = ζ 0` (linear, the generic case) and `g ζ = ‖ζ‖²` (a degenerate direction
in the free block).  Both are continuous and vanish at the origin, and the pair
is `(1, 1)` either way — the free block contributes nothing to the exponent,
which is the whole content of the transfer.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning MeasureTheory

/-! ## The two shifts satisfy the printed hypotheses -/

/-- The linear shift is continuous. -/
example : Continuous (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) :=
  (EuclideanSpace.proj (0 : Fin 1)).continuous

/-- The linear shift vanishes at the origin. -/
example : (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) 0 = 0 := rfl

/-- The quadratic shift is continuous. -/
example : Continuous (fun ζ : EuclideanSpace ℝ (Fin 1) => ‖ζ‖ ^ 2) :=
  continuous_norm.pow 2

/-- The quadratic shift vanishes at the origin. -/
example : (fun ζ : EuclideanSpace ℝ (Fin 1) => ‖ζ‖ ^ 2) 0 = 0 := by simp

/-! ## The germ is the printed `|Q(ξ) + g(ζ)|` in split coordinates -/

/-- At the concrete shape the germ evaluates to what print writes: the absolute
value of the model form on the quadratic block plus the shift on the free one. -/
example (ξ : EuclideanSpace ℝ (Fin (2 + 1))) (ζ : EuclideanSpace ℝ (Fin 1)) :
    freeBlockGerm 2 1 1 (fun z : EuclideanSpace ℝ (Fin 1) => z 0)
        (euclideanProdEquiv (2 + 1) 1 (ξ, ζ))
      = |modelBandForm 2 1 ξ + ζ 0| :=
  freeBlockGerm_euclideanProdEquiv 2 1 1 _ ξ ζ

/-! ## The local pair at a concrete shape -/

/-- **Non-vacuity, linear shift.**  The germ `|(ξ₀² + ξ₁²) - ξ₂² + ζ₀|` on
`EuclideanSpace ℝ (Fin 4)` has local volume order `(1, 1)` at the origin. -/
example : HasLocalVolumeOrder
    (freeBlockGerm 2 1 1 (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0)) 0 1 1 :=
  hasLocalVolumeOrder_freeBlockGerm 2 1 1 (le_refl 2) _
    (EuclideanSpace.proj (0 : Fin 1)).continuous rfl

/-- **Non-vacuity, quadratic shift.**  The same shape with a shift that is
degenerate at the origin still has local volume order `(1, 1)`: the free block
does not move the exponent. -/
example : HasLocalVolumeOrder
    (freeBlockGerm 2 1 1 (fun ζ : EuclideanSpace ℝ (Fin 1) => ‖ζ‖ ^ 2)) 0 1 1 :=
  hasLocalVolumeOrder_freeBlockGerm 2 1 1 (le_refl 2) _ (continuous_norm.pow 2) (by simp)

/-- A larger free block changes nothing: the pair is `(1, 1)` at `(p, q, s) =
(2, 1, 3)` as well. -/
example : HasLocalVolumeOrder
    (freeBlockGerm 2 1 3 (fun ζ : EuclideanSpace ℝ (Fin 3) => ‖ζ‖ ^ 2)) 0 1 1 :=
  hasLocalVolumeOrder_freeBlockGerm 2 1 3 (le_refl 2) _ (continuous_norm.pow 2) (by simp)

/-- The scale at the pair `(1, 1)` is the identity, so the two-sided order the
witnesses assert really is linear in `ε`. -/
example (ε : ℝ) : volumeScale 1 1 ε = ε := volumeScale_one_one ε

end AISafetyAtlas.Examples.SingularLearning
