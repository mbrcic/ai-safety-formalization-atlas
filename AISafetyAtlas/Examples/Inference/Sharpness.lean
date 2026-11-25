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
accuracy is `0`, so the inequality is comfortable and Example 6's construction
is slack at this device. The bound itself is still sharp at every `|Γ(U)|`
(`prop8_bound_sharp`); what fails here is only the demonstration of it.

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

/-! ## The repair, at concrete numbers

Example 6's split into three labelled parts, applied to the two-setup device with
inference power `e`. With constant `e = 1/2` the bound `(2 − 3) · (1/2) / 3 = −1/6`
is attained. With `e = (0, 1/3)` — the profile of `ex6Device` — the accuracy is
`(2 − 3) · min(0, 1/3) / 3 = 0`, not the bound `−1/9`.
-/

/-- Constant power `1/2` is an admissible profile. -/
public theorem halfProfile_le_one : ∀ x : Bool, |(fun _ : Bool => (1 / 2 : ℝ)) x| ≤ 1 := by
  intro _; norm_num [abs_of_pos]

/-- So is `ex6Device`'s profile, `0` at the first setup and `1/3` at the second. -/
public theorem ex6Profile_le_one :
    ∀ x : Bool, |(fun b : Bool => if b then (0 : ℝ) else 1 / 3) x| ≤ 1 := by
  intro x; cases x <;> norm_num [abs_of_pos]

/-- **Sharpness at `|Γ(U)| = 3`.** Constant inference power `1/2`: Example 6's
construction attains Proposition 8's bound, `−1/6`. -/
public theorem example6_attained_at_three :
    inferenceAccuracy (refineDevice powerDevice 3 (by norm_num))
        (refinePMF (powerPMF (fun _ => 1 / 2) halfProfile_le_one) 3 (by norm_num))
        (Prod.snd : (Bool × Bool) × Fin 3 → Fin 3) = -(1 / 6) := by
  rw [example6_power_accuracy _ _ 3 (by norm_num)]
  norm_num

/-- **The same instance through the general cell-uniform theorem**: Example 6's
split is cell-uniform and the power is constant, so the accuracy is Proposition
8's bound, computed in the split model's own terms. -/
public theorem example6_attained_at_three_cellUniform :
    inferenceAccuracy (refineDevice powerDevice 3 (by norm_num))
        (refinePMF (powerPMF (fun _ => 1 / 2) halfProfile_le_one) 3 (by norm_num))
        (Prod.snd : (Bool × Bool) × Fin 3 → Fin 3) =
      ((2 - ((realizedValues (Prod.snd : (Bool × Bool) × Fin 3 → Fin 3)).card : ℝ)) *
          (positiveMassSetups (refineDevice powerDevice 3 (by norm_num))
              (refinePMF (powerPMF (fun _ => 1 / 2) halfProfile_le_one) 3 (by norm_num))).sup'
            (positiveMassSetups_nonempty _ _)
            (fun x => condExpect
              (refinePMF (powerPMF (fun _ => 1 / 2) halfProfile_le_one) 3 (by norm_num))
              (refineDevice powerDevice 3 (by norm_num)).setup x
              (fun u => boolPm ((refineDevice powerDevice 3 (by norm_num)).concl u)))) /
        ((realizedValues (Prod.snd : (Bool × Bool) × Fin 3 → Fin 3)).card : ℝ) :=
  inferenceAccuracy_eq_prop8_bound_of_cellUniform _ _ _
    (refine_cellUniform powerDevice _ 3 (by norm_num))
    (fun x _ x' _ => by
      rw [refine_condExpect powerDevice _ 3 (by norm_num) x (fun u => boolPm (powerDevice.concl u)),
        refine_condExpect powerDevice _ 3 (by norm_num) x' (fun u => boolPm (powerDevice.concl u)),
        power_condExpect, power_condExpect])

/-- **Sharpness at `|Γ(U)| = 3`, `max_x E_P(Y ∣ x) = 1/2`, from the existence
theorem.** -/
example : ∃ (U : Type) (_ : Fintype U) (C : InferenceDevice.{0, 0} U)
    (_ : DecidableEq C.Setup) (p : FinPMF U) (Γ : U → Fin 3),
    (realizedValues Γ).card = 3 ∧ inferenceAccuracy C p Γ = -(1 / 6) := by
  obtain ⟨U, hU, C, hC, p, Γ, hcard, -, -, -, hacc⟩ :=
    prop8_bound_sharp 3 (by norm_num) (1 / 2) (by norm_num [abs_of_pos])
  exact ⟨U, hU, C, hC, p, Γ, hcard, by rw [hacc]; norm_num⟩

/-- **And the corrected value when the power varies.** Profile `(0, 1/3)`: the
accuracy is `0`, governed by the minimum. -/
public theorem example6_min_at_three :
    inferenceAccuracy (refineDevice powerDevice 3 (by norm_num))
        (refinePMF (powerPMF (fun b => if b then 0 else 1 / 3) ex6Profile_le_one) 3
          (by norm_num))
        (Prod.snd : (Bool × Bool) × Fin 3 → Fin 3) = 0 := by
  rw [example6_power_accuracy _ _ 3 (by norm_num)]
  norm_num

/-- **The hand-built instance agrees with the corrected formula**: `ex6Device` is
cell-uniform, so its accuracy is `(2 − 3) · min_x E_P(Y ∣ x) / 3`. -/
public theorem ex6_corrected_formula :
    inferenceAccuracy ex6Device ex6PMF ex6Gamma =
      ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
          (positiveMassSetups ex6Device ex6PMF).inf'
            (positiveMassSetups_nonempty ex6Device ex6PMF)
            (fun x => condExpect ex6PMF ex6Device.setup x
              (fun u => boolPm (ex6Device.concl u)))) /
        ((realizedValues ex6Gamma).card : ℝ) :=
  ex6_accuracy_via_min

/-- **Example 6's pointwise identity on the twelve-state instance.** The printed
identity `E_P(Yδ_γ(Γ) ∣ x) = (2 − |Γ(U)|)/|Γ(U)| · E_P(Y ∣ x)` holds at every setup
and every target value; the slip is only in the maximum taken after it. -/
public theorem ex6_probe_identity (x : ex6Device.Setup) (γ : Fin 3) :
    condExpect ex6PMF ex6Device.setup x
        (fun u => boolPm (ex6Device.concl u) * boolPm (probe γ (ex6Gamma u))) =
      (2 - ((realizedValues ex6Gamma).card : ℝ)) / ((realizedValues ex6Gamma).card : ℝ) *
        condExpect ex6PMF ex6Device.setup x (fun u => boolPm (ex6Device.concl u)) :=
  condExpect_probe_of_cellUniform ex6Device ex6PMF ex6Gamma ex6_cellUniform x
    (by rw [ex6_realizedValues]; exact Finset.mem_univ _)

end AISafetyAtlas.Examples.Inference.Sharpness
