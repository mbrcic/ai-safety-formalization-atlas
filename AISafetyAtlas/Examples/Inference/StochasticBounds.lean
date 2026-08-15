module

public import AISafetyAtlas.Inference

/-!
# Worked models: the covariance-accuracy lower bound

Proposition 8's bound factors into a cardinality term and a device term, and both
halves are exercised here on the Figure 6 devices, whose accuracy is known
exactly.

The binary case is the one with teeth. At two realized target values the
cardinality term is zero, so the bound reads `cov ≥ 0` — and
`fig6_respects_prop8` checks that against the exact accuracy `(1 − 6b)/(1 − 4b)`,
which is positive on the source's parameter range. Nothing in Definition 9's
shape forces an accuracy to be nonnegative; the bound is what does.
-/

namespace AISafetyAtlas.Examples.Inference.StochasticBounds

open AISafetyAtlas.Inference

/-- A `Bool`-valued target that is actually two-valued realizes both values, so
its `realizedValues` has two elements. -/
theorem realizedValues_fig6Y' : (realizedValues fig6Y').card = 2 := by decide

/-- Proposition 8 applies to the Figure 6 pair and gives `cov ≥ 0`. -/
theorem fig6_accuracy_nonneg {b : ℝ} (hb : 0 ≤ b) (hb6 : b ≤ 1 / 6) :
    0 ≤ inferenceAccuracy fig6Dev1 (fig6PMF b hb hb6) fig6Dev2.concl :=
  inferenceAccuracy_nonneg_of_card_eq_two fig6Dev1 (fig6PMF b hb hb6) fig6Dev2.concl
    realizedValues_fig6Y'

/-- The bound is consistent with the exact value, and strictly so: the accuracy
is `(1 − 6b)/(1 − 4b)`, which is strictly positive on the source's range while
the bound only asserts nonnegativity. -/
theorem fig6_respects_prop8 {b : ℝ} (hb : 0 < b) (hb6 : b < 1 / 6) :
    0 < inferenceAccuracy fig6Dev1 (fig6PMF b hb.le hb6.le) fig6Dev2.concl := by
  rw [fig6_accuracy_dev1 hb hb6]
  apply div_pos <;> linarith

/-- The general bound, instantiated. The `sup` term is the source's *inference
power* of the device, and at two target values it is multiplied by zero. -/
theorem fig6_prop8_instance {b : ℝ} (hb : 0 ≤ b) (hb6 : b ≤ 1 / 6) :
    ((2 - ((realizedValues fig6Dev2.concl).card : ℝ)) *
        (positiveMassSetups fig6Dev1 (fig6PMF b hb hb6)).sup'
          (positiveMassSetups_nonempty fig6Dev1 (fig6PMF b hb hb6))
          (fun x => condExpect (fig6PMF b hb hb6) fig6Dev1.setup x
            (fun u => boolPm (fig6Dev1.concl u)))) /
      ((realizedValues fig6Dev2.concl).card : ℝ)
      ≤ inferenceAccuracy fig6Dev1 (fig6PMF b hb hb6) fig6Dev2.concl :=
  inferenceAccuracy_ge fig6Dev1 (fig6PMF b hb hb6) fig6Dev2.concl

end AISafetyAtlas.Examples.Inference.StochasticBounds
