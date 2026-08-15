module

public import AISafetyAtlas.Inference

/-!
# Worked model: complexity inverts under strong inference

The construction is checked at one concrete parameter, so the two complexities
are readable numbers rather than limits and the inversion is a comparison
between them.

**The inversion is not automatic in the parameter.** From the two identities,

`C(Γ; D) − C(Γ; D′) = −ln ε + ln(1 − ε) − 2 ln 2`,

which is positive exactly when `(1 − ε)/ε > 4`, that is `ε < 1/5`. At `ε = 1/4`
the emulating device is the *more* expensive one. At `ε = 1/10` the gap is
exactly `ln(9/4)` in the other direction, and `inv_strictly_cheaper` records it.
-/

namespace AISafetyAtlas.Examples.Inference.Inversion

open AISafetyAtlas.Inference

/-- Both source hypotheses hold: `D > Γ` and `D′ ≫ D`. -/
theorem inv_hypotheses :
    WeaklyInfers invDevice invGamma ∧ StronglyInfers invDevice' invDevice :=
  ⟨inv_weaklyInfers, inv_stronglyInfers⟩

/-- The two complexities at `ε = 1/10`, from the identities. -/
theorem inv_at_tenth :
    inferenceComplexityMeasure (invMeasure (1/10) (by norm_num) (by norm_num)) invDevice
        invGamma inv_weaklyInfers
      = -Real.log (1/10) - Real.log (1 - 1/10) ∧
    inferenceComplexityMeasure (invMeasure (1/10) (by norm_num) (by norm_num)) invDevice'
        invGamma (weaklyInfers_of_stronglyInfers inv_stronglyInfers inv_weaklyInfers)
      = 2 * Real.log 2 - 2 * Real.log (1 - 1/10) :=
  ⟨inv_complexity (by norm_num) (by norm_num), inv_complexity' (by norm_num) (by norm_num)⟩

/-- **The inversion, exactly.** At `ε = 1/10` the device that can emulate the
other is cheaper to use, by `ln 9 − ln 4`. -/
theorem inv_gap_at_tenth :
    inferenceComplexityMeasure (invMeasure (1/10) (by norm_num) (by norm_num)) invDevice
        invGamma inv_weaklyInfers
      - inferenceComplexityMeasure (invMeasure (1/10) (by norm_num) (by norm_num)) invDevice'
        invGamma (weaklyInfers_of_stronglyInfers inv_stronglyInfers inv_weaklyInfers)
      = Real.log 9 - Real.log 4 := by
  rw [inv_complexity (by norm_num) (by norm_num),
    inv_complexity' (by norm_num) (by norm_num)]
  have e1 : Real.log (1/10 : ℝ) = -Real.log 10 := by
    rw [show (1/10 : ℝ) = 10⁻¹ by norm_num, Real.log_inv]
  have e2 : (1 : ℝ) - 1/10 = 9/10 := by norm_num
  have e3 : Real.log (9/10 : ℝ) = Real.log 9 - Real.log 10 :=
    Real.log_div (by norm_num) (by norm_num)
  have e4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [e2, e1, e3, e4]
  ring

/-- The same fact as a strict inequality. -/
theorem inv_strictly_cheaper :
    inferenceComplexityMeasure (invMeasure (1/10) (by norm_num) (by norm_num)) invDevice'
        invGamma (weaklyInfers_of_stronglyInfers inv_stronglyInfers inv_weaklyInfers)
      < inferenceComplexityMeasure (invMeasure (1/10) (by norm_num) (by norm_num)) invDevice
        invGamma inv_weaklyInfers := by
  have hgap := inv_gap_at_tenth
  have h : Real.log (4 : ℝ) < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

end AISafetyAtlas.Examples.Inference.Inversion
