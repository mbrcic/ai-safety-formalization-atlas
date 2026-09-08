module

public import AISafetyAtlas.SingularLearning.ShiftedBand

/-!
# Worked models for the level-uniform band

`ShiftedBand.lean` bounds the volume of the band `|Q(w) - c| ≤ ε` inside a ball
of radius `δ` by a constant multiple of `ε`, with the constant free of the level
`c`.  The statements there carry a dimension hypothesis and `NeZero` instances;
these instantiations are the cheapest check that they are satisfiable rather
than vacuous, and they exhibit the constant at a concrete signature.

The `(2,2)` shape is MAIS-O7's origin.  `(1,2)` is the smallest signature the
general form covers: its first block is one-dimensional, so the estimate has to
be run with the blocks exchanged.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning MeasureTheory

/-- The band around an arbitrary level, at O7's signature.  Every level `c` gets
the same constant. -/
example (c : ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    shiftedBandVolume 2 2 c δ ε ≤ shiftedBandConst 2 2 δ * ε :=
  shiftedBandVolume_le 2 2 le_rfl c hδ hε

/-- The constant is a genuine one: positive at every positive radius. -/
example {δ : ℝ} (hδ : 0 < δ) : 0 < shiftedBandConst 2 2 δ :=
  shiftedBandConst_pos 2 2 hδ

/-- The dimension hypothesis is not vacuous: `(3,1)` has a one-dimensional
second block and only the first carries the `2 ≤ p` requirement. -/
example (c : ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    shiftedBandVolume 3 1 c δ ε ≤ shiftedBandConst 3 1 δ * ε :=
  shiftedBandVolume_le 3 1 (by norm_num) c hδ hε

/-- **The general form, at the smallest signature it covers.**  `(1,2)` needs the
block exchange, which is what `shiftedBandVolume_le_of_three_le` performs. -/
example (c : ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    shiftedBandVolume 1 2 c δ ε
      ≤ (shiftedBandConst 1 2 δ + shiftedBandConst 2 1 δ) * ε :=
  shiftedBandVolume_le_of_three_le 1 2 (by norm_num) c hδ hε

/-- The packaged form: one constant for every level and every radius below a
fixed `δ₀`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε →
    shiftedBandVolume 2 2 c δ ε ≤ C * ε :=
  exists_shiftedBandVolume_upper 2 2 (by norm_num) one_pos

/-- The signed form is the germ's absolute value, so the level-zero band of
`ShiftedBand` is the sublevel set `IndefiniteBand` works with. -/
example (w : EuclideanSpace ℝ (Fin (2 + 2))) :
    modelBandGerm 2 2 w = |modelBandForm 2 2 w| :=
  modelBandGerm_eq_abs_form 2 2 w

/-- The matching lower bound at O7's signature, at the level and half-width the
statement admits. -/
example (c : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hc : |c| ≤ δ ^ 2 / 32) (hε0 : 0 ≤ ε)
    (hε : ε ≤ δ ^ 2 / 4) :
    shiftedBandLowerConst 2 2 δ * ε ≤ shiftedBandVolume 2 2 c δ ε :=
  shiftedBandVolume_ge 2 2 le_rfl hδ hc hε0 hε

/-- The lower constant is positive, so the lower bound is not the trivial one. -/
example {δ : ℝ} (hδ : 0 < δ) : 0 < shiftedBandLowerConst 2 2 δ :=
  shiftedBandLowerConst_pos 2 2 hδ

/-- The two constants are ordered, which a pair of two-sided bounds must be. -/
example {δ : ℝ} (hδ : 0 < δ) : shiftedBandLowerConst 2 2 δ ≤ shiftedBandConst 2 2 δ :=
  shiftedBandLowerConst_le 2 2 le_rfl hδ

/-- **The two-sided statement at O7's signature**, with one ordered pair of
constants covering every level for the upper bound and every admissible level
for the lower one. -/
example : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    (∀ c : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε →
      shiftedBandVolume 2 2 c δ ε ≤ c₂ * ε) ∧
    (∀ c : ℝ, |c| ≤ (1:ℝ) ^ 2 / 32 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1:ℝ) ^ 2 / 4 →
      c₁ * ε ≤ shiftedBandVolume 2 2 c 1 ε) :=
  exists_shiftedBand_bounds 2 2 le_rfl one_pos

end AISafetyAtlas.Examples.SingularLearning
