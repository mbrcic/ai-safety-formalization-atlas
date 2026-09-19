module

public import AISafetyAtlas.SingularLearning.FreeBlockBand

/-!
# Worked models for the band with a free shifted block

`FreeBlockBand.lean` adds a free `s`-dimensional block to the level-uniform band
of `ShiftedBand.lean`: the band is `|Q(ξ) + g(ζ)| ≤ ε` in a product box, and the
statements carry `2 ≤ p`, a `NeZero q` instance, and — for the lower bound — a
continuous shift vanishing at the origin.

This file discharges all of that at a concrete shape.  The signature is
`(p, q, s) = (2, 1, 1)`: three variables in the printed sense, an indefinite
nondegenerate quadratic form in the first two of them, and one free variable
carrying the shift.  Two shifts are exercised, `g ζ = ζ 0` (linear, the generic
case) and `g ζ = ‖ζ‖²` (the degenerate-direction case), and both satisfy the
printed hypotheses `g` continuous with `g 0 = 0`.

The point of the file is non-vacuity: the hypotheses are satisfiable at a real
shape, and the constants the packaged statement produces are positive, so
`Θ(ε)` is a genuine two-sided order rather than a bound against zero.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning MeasureTheory

/-- The linear shift is continuous and vanishes at the origin, which is exactly
what the printed Lemma 2 asks of `g`. -/
example : Continuous (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) := by
  exact (EuclideanSpace.proj (0 : Fin 1)).continuous

/-- The upper bound at `(2, 1, 1)` with the linear shift.  Nothing is asked of
the shift beyond measurability: the level-uniform constant does not see the
level `g ζ` moves the band to. -/
example {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume (freeBlockBandSet 2 1 1 (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) δ ε)
      ≤ ENNReal.ofReal (shiftedBandConst 2 1 δ * ε)
        * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) δ) :=
  measure_freeBlockBandSet_le 2 1 1 le_rfl _
    ((EuclideanSpace.proj (0 : Fin 1)).continuous.measurable) hδ hε

/-- The `ζ`-slice at an interior point is the level-`(-(g ζ))` band of
`ShiftedBand`.  That identity is the whole bridge between the two modules. -/
example (g : EuclideanSpace ℝ (Fin 1) → ℝ) (δ ε : ℝ)
    {ζ : EuclideanSpace ℝ (Fin 1)} (hζ : ‖ζ‖ ≤ δ) :
    (fun ξ => (ξ, ζ)) ⁻¹' freeBlockBandSet 2 1 1 g δ ε
      = shiftedBandSet 2 1 (-(g ζ)) δ ε :=
  freeBlockBandSet_slice 2 1 1 g δ ε hζ

/-- **Shrinking the ζ-box** at the quadratic shift `g ζ = ‖ζ‖²`: continuity and
`g 0 = 0` give a positive radius on which the shift stays inside the admissible
level window. -/
example {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ρ ≤ δ ∧ ∀ ζ : EuclideanSpace ℝ (Fin 1), ‖ζ‖ ≤ ρ → |‖ζ‖ ^ 2| ≤ δ ^ 2 / 32 :=
  exists_radius_of_continuousAt (g := fun ζ : EuclideanSpace ℝ (Fin 1) => ‖ζ‖ ^ 2)
    (continuous_norm.pow 2) (by simp) hδ

/-- **The printed Lemma 2 at `(p, q, s) = (2, 1, 1)` with the linear shift.**
Three variables, a nondegenerate indefinite form in two of them, one free
variable, and `Θ(ε)` with positive ordered constants below a positive
threshold. -/
public theorem freeBlockBand_theta_linear {δ : ℝ} (hδ : 0 < δ) :
    ∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        c₁ * ε
            ≤ (volume (freeBlockBandSet 2 1 1
                (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) δ ε)).toReal ∧
          (volume (freeBlockBandSet 2 1 1
                (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) δ ε)).toReal ≤ c₂ * ε :=
  exists_freeBlockBand_bounds 2 1 1 le_rfl _
    ((EuclideanSpace.proj (0 : Fin 1)).continuous) (by simp) hδ

/-- **The same at the quadratic shift `g ζ = ‖ζ‖²`.**  The shift is not linear
and is not monotone in `ζ`; the estimate does not care, because the only thing
it asks of `g` is that it be small on a small box. -/
public theorem freeBlockBand_theta_quadratic {δ : ℝ} (hδ : 0 < δ) :
    ∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        c₁ * ε
            ≤ (volume (freeBlockBandSet 2 1 1
                (fun ζ : EuclideanSpace ℝ (Fin 1) => ‖ζ‖ ^ 2) δ ε)).toReal ∧
          (volume (freeBlockBandSet 2 1 1
                (fun ζ : EuclideanSpace ℝ (Fin 1) => ‖ζ‖ ^ 2) δ ε)).toReal ≤ c₂ * ε :=
  exists_freeBlockBand_bounds 2 1 1 le_rfl _ (continuous_norm.pow 2) (by simp) hδ

/-- The packaged statement is not vacuous: at `δ = 1` it produces constants and
a threshold, and the threshold is positive, so the range of `ε` it speaks about
is nonempty. -/
example : ∃ c₁ c₂ ε₀ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      c₁ * ε
          ≤ (volume (freeBlockBandSet 2 1 1
              (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) 1 ε)).toReal ∧
        (volume (freeBlockBandSet 2 1 1
              (fun ζ : EuclideanSpace ℝ (Fin 1) => ζ 0) 1 ε)).toReal ≤ c₂ * ε :=
  freeBlockBand_theta_linear one_pos

/-- The band is a genuine subset of the product box, which is what makes its
volume finite without any dimension hypothesis. -/
example (g : EuclideanSpace ℝ (Fin 1) → ℝ) (δ ε : ℝ) :
    volume (freeBlockBandSet 2 1 1 g δ ε) ≠ ⊤ :=
  measure_freeBlockBandSet_ne_top 2 1 1 g δ ε

end AISafetyAtlas.Examples.SingularLearning
