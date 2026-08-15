module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

/-!
# The pointwise Gibbs step

Two facts about real numbers, with no probability in them at all: `log t ≤ t − 1`
gives the inequality behind `0 ≤ M`, and `log t < t − 1` for `t ≠ 1` gives the
equality case behind *`M = 0` implies independence* — the step Wolpert 2008's
Proposition 6 asserts without derivation.

They live in their own module because both the `FinPMF` layer and the general
measure layer need them and neither should depend on the other. Nothing here
knows what a device or a measure is.
-/

namespace AISafetyAtlas.Inference

/-- The pointwise Gibbs step: `q·log p₁ + q·log p₂ − q·log q ≤ p₁p₂ − q`. -/
public theorem gibbs_cell {q p1 p2 : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ p1) (hq2 : q ≤ p2) :
    (if q = 0 then 0 else q * Real.log p1) +
        (if q = 0 then 0 else q * Real.log p2) -
        (if q = 0 then 0 else q * Real.log q) ≤ p1 * p2 - q := by
  by_cases h : q = 0
  · rw [if_pos h, if_pos h, if_pos h, h]
    have hp1 : (0:ℝ) ≤ p1 := h ▸ hq1
    have hp2 : (0:ℝ) ≤ p2 := h ▸ hq2
    have hmul : (0:ℝ) ≤ p1 * p2 := mul_nonneg hp1 hp2
    linarith
  · simp only [h, if_false]
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm h)
    have hp1 : 0 < p1 := lt_of_lt_of_le hqpos hq1
    have hp2 : 0 < p2 := lt_of_lt_of_le hqpos hq2
    have hratio : 0 < p1 * p2 / q := div_pos (mul_pos hp1 hp2) hqpos
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hexp : Real.log (p1 * p2 / q) = Real.log p1 + Real.log p2 - Real.log q := by
      rw [Real.log_div (ne_of_gt (mul_pos hp1 hp2)) (ne_of_gt hqpos),
        Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2)]
    rw [hexp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hqpos)
    have hcancel : q * (p1 * p2 / q - 1) = p1 * p2 - q := by field_simp
    calc q * Real.log p1 + q * Real.log p2 - q * Real.log q
        = q * (Real.log p1 + Real.log p2 - Real.log q) := by ring
      _ ≤ q * (p1 * p2 / q - 1) := hmul
      _ = p1 * p2 - q := hcancel

/-- **Equality in the pointwise Gibbs step.** `log t ≤ t − 1` is tight exactly at
`t = 1`, so a cell contributes no slack exactly when it is independent. This is
the equality case Wolpert's Proposition 6 needs and `gibbs_cell` alone does not
give; `Real.log_lt_sub_one_of_pos` supplies the strictness. -/
public theorem gibbs_cell_eq_iff {q p1 p2 : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ p1) (hq2 : q ≤ p2) :
    ((if q = 0 then 0 else q * Real.log p1) +
        (if q = 0 then 0 else q * Real.log p2) -
        (if q = 0 then 0 else q * Real.log q) = p1 * p2 - q) ↔ q = p1 * p2 := by
  by_cases h : q = 0
  · subst h
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    constructor <;> intro heq <;> linarith
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm h)
    have hp1 : 0 < p1 := lt_of_lt_of_le hqpos hq1
    have hp2 : 0 < p2 := lt_of_lt_of_le hqpos hq2
    have hratio : 0 < p1 * p2 / q := div_pos (mul_pos hp1 hp2) hqpos
    have hexp : Real.log (p1 * p2 / q) = Real.log p1 + Real.log p2 - Real.log q := by
      rw [Real.log_div (ne_of_gt (mul_pos hp1 hp2)) (ne_of_gt hqpos),
        Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2)]
    have hcancel : q * (p1 * p2 / q - 1) = p1 * p2 - q := by field_simp
    rw [if_neg h, if_neg h, if_neg h]
    constructor
    · intro heq
      by_contra hne
      have hne1 : p1 * p2 / q ≠ 1 := by
        intro h1
        exact hne ((div_eq_one_iff_eq (ne_of_gt hqpos)).mp h1).symm
      have hlt := Real.log_lt_sub_one_of_pos hratio hne1
      have := mul_lt_mul_of_pos_left hlt hqpos
      rw [hexp, hcancel] at this
      nlinarith [this]
    · intro heq
      have h1 : p1 * p2 / q = 1 := by rw [← heq]; field_simp
      have hlog : Real.log p1 + Real.log p2 - Real.log q = 0 := by
        rw [← hexp, h1, Real.log_one]
      nlinarith [hlog]

end AISafetyAtlas.Inference
