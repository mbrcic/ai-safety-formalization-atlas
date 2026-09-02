/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import Mathlib.Data.Real.Basic

@[expose] public section

-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-!
A few if utilities
-/

/-- ↑x ≤ ↑y ↔ y → x -/
lemma ite_le_ite_iff (x y : Prop) {dx : Decidable x} {dy : Decidable y} :
    (@ite _ x dx (1:ℝ) 0) ≤ (@ite _ y dy 1 0) ↔ x → y := by
  by_cases h : x
  repeat { by_cases l : y; repeat { simp only [h, l, ite_true, ite_false]; norm_num }}

lemma ite_one_zero_congr (x y : Prop) {dx : Decidable x} {dy : Decidable y} :
    @ite _ x dx (1:ℝ) 0 = @ite _ y dy (1:ℝ) 0 ↔ (x ↔ y) := by
  by_cases h : x
  repeat { by_cases l : y; repeat simp [h, l] }

lemma ite_one_zero_ne_zero (x : Prop) {dx : Decidable x} : @ite _ x dx (1:ℝ) 0 ≠ 0 ↔ x := by
  by_cases h : x; repeat { simp only [h, if_true, if_false]; norm_num }

lemma ite_and_one_zero (x y : Prop) {d : Decidable (x ∧ y)} :
    @ite _ (x ∧ y) d (1:ℝ) 0 =
      (@ite _ x (Classical.dec _) (1:ℝ) 0) * (@ite _ y (Classical.dec _) 1 0) := by
  rw [ite_zero_mul_ite_zero, one_mul]
  congr

lemma ite_one_zero_nonneg {x : Prop} {d : Decidable x} : 0 ≤ @ite _ x d (1:ℝ) 0 := by
  split_ifs; repeat norm_num
