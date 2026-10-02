module

public import AISafetyAtlas.Inference

/-!
# Worked models: approximate mutual inference

Proposition 10's accuracy is a real number one can read off, and reading it off
is what makes the collapse of Theorem 1 concrete rather than asymptotic.

At `b = 1/12` the two distinguishable devices infer each other with accuracy
exactly `3/4`. At `b = 1/102` the ratio `(1 − 6b)/(1 − 4b)` is `96/98 = 48/49`,
so each infers the other better than 97% of the time — while
`fig6_thm1_applies` confirms Theorem 1 still forbids the exact case for these
very devices. Both numbers are computed from the accuracy identities, not
asserted.

Proposition 9 is checked the same way: at `p = 9/10` the emulating device `D′`
strongly infers `D`, `D` infers `Γ` with accuracy `9/10`, and `D′` infers `Γ`
with accuracy `0`. The two are not close, and the gap does not shrink with `p`.
-/

namespace AISafetyAtlas.Examples.Inference.StochasticApproximation

open AISafetyAtlas.Inference

/-- At `b = 1/12` the accuracy is exactly `3/4`: `(1 − 1/2)/(1 − 1/3)`. -/
theorem fig6_accuracy_at_one_twelfth :
    inferenceAccuracy fig6Dev1
      (fig6PMF (1 / 12) (by norm_num) (by norm_num)) fig6Dev2.concl = 3 / 4 := by
  rw [fig6_accuracy_dev1 (by norm_num) (by norm_num)]
  norm_num

/-- At `b = 1/102` both accuracies are `48/49`. -/
theorem fig6_accuracy_at_one_hundred_second :
    inferenceAccuracy fig6Dev1
        (fig6PMF (1 / 102) (by norm_num) (by norm_num)) fig6Dev2.concl = 48 / 49 ∧
      inferenceAccuracy fig6Dev2
        (fig6PMF (1 / 102) (by norm_num) (by norm_num)) fig6Dev1.concl = 48 / 49 := by
  constructor
  · rw [fig6_accuracy_dev1 (by norm_num) (by norm_num)]; norm_num
  · rw [fig6_accuracy_dev2 (by norm_num) (by norm_num)]; norm_num

/-- Theorem 1 does apply to this pair, and denies *exact* mutual inference. The
two facts live together: approximate mutual inference to within any `ε`, exact
mutual inference impossible. -/
theorem fig6_thm1_applies :
    ¬ (InfersDevice fig6Dev1 fig6Dev2 ∧ InfersDevice fig6Dev2 fig6Dev1) :=
  fun h => not_infersDevice_both_of_distinguishable fig6_distinguishable h.1 h.2

/-! ## Proposition 9 -/

/-- At `p = 9/10`: `D` infers `Γ` with accuracy `9/10`, `D′` strongly infers `D`,
and `D′` infers `Γ` with accuracy `0`. Strong inference transmits none of it. -/
theorem fig5_gap_at_nine_tenths :
    StronglyInfers fig5Dev2 fig5Dev1 ∧
      inferenceAccuracy fig5Dev1
        (fig5PMF (9 / 10) (by norm_num) (by norm_num)) fig5Target.concl = 9 / 10 ∧
      inferenceAccuracy fig5Dev2
        (fig5PMF (9 / 10) (by norm_num) (by norm_num)) fig5Target.concl = 0 :=
  ⟨fig5_stronglyInfers, fig5_accuracy_dev1 (by norm_num) (by norm_num),
    fig5_accuracy_dev2 (by norm_num) (by norm_num)⟩

/-- The deterministic theorem that fails to survive: `D′ ≫ D` and `D > Γ` would
force `D′ > Γ`. Here `D′ ≫ D` holds, so `D` cannot infer `Γ` exactly — and it
does not, despite an accuracy of `9/10`. -/
theorem fig5_not_weaklyInfers : ¬ WeaklyInfers fig5Dev1 fig5Target.concl := by
  intro h
  have h' : WeaklyInfers fig5Dev2 fig5Target.concl :=
    weaklyInfers_of_stronglyInfers fig5_stronglyInfers h
  obtain ⟨x, -, hx⟩ := h' false (probe false) (isProbe_probe false) ⟨4, rfl⟩
  revert hx
  fin_cases x <;> decide

/-! ## The two approximation results, at a concrete tolerance

Both are stated for every `ε > 0`. Instantiating at one number is what turns
"can be made arbitrarily close" into a claim a reader can check, and neither
statement had been instantiated anywhere.
-/

/-- **Two distinguishable devices can each infer the other almost perfectly.**
At `ε = 1/10`: accuracy above `9/10` in both directions, while Theorem 1 forbids
*exact* mutual inference. The gap between "distinguishable" and "cannot infer"
is therefore a gap about exactness and not about accuracy. -/
public theorem mutual_accuracy_at_one_tenth :
    ∃ (D₁ D₂ : InferenceDevice.{0, 0} (Fin 16)) (i₁ : DecidableEq D₁.Setup)
      (i₂ : DecidableEq D₂.Setup) (p : FinPMF (Fin 16)),
      Distinguishable D₁ D₂ ∧
      1 - (1 / 10 : ℝ) < @inferenceAccuracy (Fin 16) _ D₁ i₁ Bool _ _ p D₂.concl ∧
      1 - (1 / 10 : ℝ) < @inferenceAccuracy (Fin 16) _ D₂ i₂ Bool _ _ p D₁.concl :=
  exists_distinguishable_accuracy_near_one (by norm_num)

/-- **And strong inference buys no accuracy at all.** At the same tolerance:
`fig5Dev2` strongly infers `fig5Dev1`, the weaker device scores above `9/10` on
the target, and the stronger one scores exactly `0`. Strength in the inference
order is not accuracy on a question. -/
public theorem fig5_gap_at_one_tenth :
    ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      StronglyInfers fig5Dev2 fig5Dev1 ∧
      1 - (1 / 10 : ℝ) < inferenceAccuracy fig5Dev1 (fig5PMF q h0 h1) fig5Target.concl ∧
      inferenceAccuracy fig5Dev2 (fig5PMF q h0 h1) fig5Target.concl = 0 :=
  fig5_accuracy_gap (by norm_num)

end AISafetyAtlas.Examples.Inference.StochasticApproximation
