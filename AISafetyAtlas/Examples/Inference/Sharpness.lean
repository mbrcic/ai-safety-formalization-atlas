module

public import AISafetyAtlas.Inference

/-!
# Worked model: Example 6 does not attain the bound

The three numbers side by side. The point of stating them together is that all
three are true at once, which is what distinguishes "the bound fails" — it does
not — from "this construction fails to attain it".
-/

namespace AISafetyAtlas.Examples.Inference.Sharpness

open AISafetyAtlas.Inference

/-- The construction follows the source's recipe: `|Γ(U)| = 3` values, each cell
of the `X × Y` partition split into three equal-probability parts. -/
theorem ex6_shape : (realizedValues ex6Gamma).card = 3 := by
  rw [ex6_realizedValues]; decide

/-- The device's inference power is **not** constant across setups — the single
way this differs from Example 6, and the reason the maximum moves. -/
theorem ex6_power_varies :
    condExpect ex6PMF ex6X true (fun u => boolPm (ex6Y u)) = 0 ∧
      condExpect ex6PMF ex6X false (fun u => boolPm (ex6Y u)) = 1 / 3 :=
  ⟨ex6_condExpect_Y_true, ex6_condExpect_Y_false⟩

/-- Proposition 8 holds, and is not attained, on the same instance. -/
theorem ex6_summary :
    inferenceAccuracy ex6Device ex6PMF ex6Gamma = 0 ∧
      ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
          (positiveMassSetups ex6Device ex6PMF).sup'
            (positiveMassSetups_nonempty ex6Device ex6PMF)
            (fun x => condExpect ex6PMF ex6Device.setup x
              (fun u => boolPm (ex6Device.concl u)))) /
        ((realizedValues ex6Gamma).card : ℝ) = -(1 / 9) :=
  ⟨ex6_accuracy, ex6_prop8_bound⟩

end AISafetyAtlas.Examples.Inference.Sharpness
