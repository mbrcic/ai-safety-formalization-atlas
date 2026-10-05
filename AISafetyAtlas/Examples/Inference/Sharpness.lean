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

/-- **Proposition 8 holds here and is not attained**, which is the whole point
of Example 6 and which neither half states alone. The bound is `-1/9` and the
accuracy is `0`, so the inequality is comfortable and the claim of *sharpness*
for `|Γ(U)| ≥ 3` fails at this device.

Both halves existed in the library and neither had an application, so nothing in
the build connected the counterexample to the proposition it is a counterexample
about. -/
public theorem ex6_holds_and_is_slack :
    ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
        (positiveMassSetups ex6Device ex6PMF).sup'
          (positiveMassSetups_nonempty ex6Device ex6PMF)
          (fun x => condExpect ex6PMF ex6Device.setup x
            (fun u => boolPm (ex6Device.concl u)))) /
        ((realizedValues ex6Gamma).card : ℝ)
        ≤ inferenceAccuracy ex6Device ex6PMF ex6Gamma ∧
      ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
        (positiveMassSetups ex6Device ex6PMF).sup'
          (positiveMassSetups_nonempty ex6Device ex6PMF)
          (fun x => condExpect ex6PMF ex6Device.setup x
            (fun u => boolPm (ex6Device.concl u)))) /
        ((realizedValues ex6Gamma).card : ℝ)
        < inferenceAccuracy ex6Device ex6PMF ex6Gamma :=
  ⟨ex6_prop8_holds, ex6_bound_not_attained⟩

/-! ## The general apparatus, at the same distribution

Three statements underpinning the accuracy bounds had no application: that the
distinguishability index is a genuine index in `[0, 1]`, that mutual information
is non-negative, and that the joint push-forward marginalises correctly. Each
holds at every distribution and each is run here at Example 6's.
-/

/-- **The distinguishability index lands in `[0, 1]`.** It is called an index
and nothing had checked that it behaves like one. -/
public theorem ex6_miDistinguishability_index :
    0 ≤ miDistinguishability ex6Device ex6Device ex6PMF ∧
      miDistinguishability ex6Device ex6Device ex6PMF ≤ 1 :=
  miDistinguishability_mem_unit_interval ex6Device ex6Device ex6PMF

/-- **Mutual information is non-negative**, at the device's own setup and
conclusion — the inequality every bound in this cluster is built on. -/
public theorem ex6_mutualInfo_nonneg :
    0 ≤ mutualInfo ex6PMF ex6Device.setup ex6Device.concl :=
  mutualInfo_nonneg ex6PMF ex6Device.setup ex6Device.concl

/-- **And the joint marginalises to the margin.** Summing the pushed joint over
the second coordinate returns the pushed first, which is what makes the two
entropies in the index entropies of the same distribution. -/
public theorem ex6_pushOnImage_marginal (a : ex6Device.Setup) :
    (Finset.univ.image ex6Device.concl).sum
        (fun b => pushOnImage ex6PMF (fun u => (ex6Device.setup u, ex6Device.concl u)) (a, b))
      = pushOnImage ex6PMF ex6Device.setup a :=
  pushOnImage_marginal ex6PMF ex6Device.setup ex6Device.concl a

/-! ## The two arithmetic steps under the bounds

Neither needs a distribution: they are the inequalities the entropy arguments
reduce to, and both were proved and left unused.
-/

/-- **The Gibbs cell inequality**, at a cell where the joint is a quarter and
both margins a half — the balanced case, where the bound is closest to tight. -/
public theorem gibbs_cell_at_quarter :
    (if (1 / 4 : ℝ) = 0 then 0 else (1 / 4 : ℝ) * Real.log (1 / 2)) +
        (if (1 / 4 : ℝ) = 0 then 0 else (1 / 4 : ℝ) * Real.log (1 / 2)) -
        (if (1 / 4 : ℝ) = 0 then 0 else (1 / 4 : ℝ) * Real.log (1 / 4))
      ≤ (1 / 2 : ℝ) * (1 / 2) - 1 / 4 :=
  gibbs_cell (by norm_num) (by norm_num) (by norm_num)

/-- **And Proposition 6's expression at its maximiser is `1/4`.** The number the
proposition's bound is stated against, computed rather than quoted. -/
public theorem prop6_value_at_maximizer :
    prop6Expr (1 / 2) (1 / 2) prop6Maximizer = 1 / 4 :=
  prop6Expr_half_maximizer

end AISafetyAtlas.Examples.Inference.Sharpness
