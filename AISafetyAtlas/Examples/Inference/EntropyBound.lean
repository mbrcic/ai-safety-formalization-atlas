module

public import AISafetyAtlas.Inference

/-!
# Worked model: the entropy bound fails

Proposition 12 is refuted rather than instantiated, so what an example can add is
the check that the countermodel is genuinely inside the proposition's scope and
that its two sides are the real numbers claimed.

`prop12_inside_scope` collects the printed hypotheses. `prop12_sides` records
both values. The rest is `prop12_refuted`.
-/

namespace AISafetyAtlas.Examples.Inference.EntropyBound

open AISafetyAtlas.Inference

/-- Every hypothesis Proposition 12 states, satisfied: a probability measure, a
target with finite image, and `D > Γ`. -/
theorem prop12_inside_scope :
    WeaklyInfers prop12Device prop12Gamma ∧ (rangeFinset prop12Gamma).card = 2 :=
  ⟨prop12_weaklyInfers, by rw [prop12_rangeFinset]; decide⟩

/-- Both sides, exactly. -/
theorem prop12_sides :
    inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
        prop12_weaklyInfers = 4 * Real.log 2 - Real.log 3 ∧
      entropyOn prop12Measure prop12X = 2 * Real.log 2 - 3 / 4 * Real.log 3 :=
  ⟨prop12_complexity, prop12_entropy⟩

/-- The two setup fibres carry `3/4` and `1/4`; the small one is what breaks the
printed proof's term-by-term comparison, which needs every fibre to carry at
least `1/|Γ|`. Here `1/|Γ| = 1/2` and one fibre carries `1/4`. -/
theorem prop12_small_fibre :
    massOn prop12Measure prop12X false = 1 / 4 ∧
      massOn prop12Measure prop12X false < 1 / (rangeFinset prop12Gamma).card := by
  refine ⟨prop12_mass_false, ?_⟩
  rw [prop12_mass_false, prop12_rangeFinset]
  norm_num

end AISafetyAtlas.Examples.Inference.EntropyBound
