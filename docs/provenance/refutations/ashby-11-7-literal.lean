import AISafetyAtlas.Control.VarietyCounting
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Ashby 11/7 as printed is false; the bound without attainment is the one that holds

W. Ross Ashby, *An Introduction to Cybernetics* (1956; second impression 1957), §11/7,
book pp. 206--207 (PDF p. 110; audit row S03-R04):

    11/7. If the varieties are measured logarithmically (as is almost
    always convenient), and if the same conditions hold, then the theorem takes a
    very simple form. Let V_D be the variety of D, V_R that of R, and
    V_O that of the outcome (all measured logarithmically).
    Then the previous section has proved that V_O cannot be less,
    numerically, than the value of V_D − V_R. Thus V_O's minimum is
    V_D − V_R.

(Transcribed from the page image in
`docs/provenance/printed-statements/ashby-1957-introduction-to-cybernetics.yaml`,
entry `ashby-11-7`, whose note reads: "Thus V_O's minimum is V_D − V_R" asserts
attainment as well as the bound.) "The same conditions" are §11/5's: "no column
contains a repeated outcome". Varieties in the logarithmic form are base 2
(§7/7, p. 126). `R`'s move is a single-valued transformation of `D`'s (§11/5).

The first sentence is true: it is `AISafetyAtlas.Control.ashby_logVariety_ge`. The
second is false. The number of outcomes is an integer, so `V_O` is the logarithm of
an integer, while `V_D − V_R = log₂ (|D| / |R|)` need not be. At `|D| = 3`,
`|R| = 2` every regulator leaves at least two outcomes
(`AISafetyAtlas.Control.two_le_card_admittedOutcomes`), so `V_O ≥ 1 > log₂ (3/2)`.
This file proves that for **every** column-injective table of that shape
(`no_regulator_attains`), so print fails whether "minimum" is read per table or
over all tables of the shape, and instantiates it at the table with columns
`(0, 1, 2)` and `(1, 2, 0)`.

Integrality is not the only way the per-table reading fails: at `T d r = d` the
columns are injective and every regulator admits every outcome, so `V_O = V_D`
even when `|R|` divides `|D|` (the library notes this table in the sharpness
section of `VarietyCounting`; not proved here). What is attainable is the integer
bound `⌈|D| / |R|⌉`, and only on some table of each shape
(`AISafetyAtlas.Control.ashby_variety_ge_isSharp`).

Why the repair is the necessary one and not a different theorem:

* it keeps the sentence print says §11/6 proved, `V_O ≥ V_D − V_R`, and drops only
  the attainment, which §11/6 does not prove and which fails;
* the law of Requisite Variety that §11/7 draws ("only variety in R can force down
  the variety due to D") is a statement about the bound and survives intact;
* the integer form `⌈|D| / |R|⌉ ≤ |outcomes|` is the sharp version of the same bound
  and is added because it costs one library lemma.

This is a different defect from §11/9's `log V_R` slip
(`docs/provenance/refutations/ashby-11-9-literal.lean`): that line has a
typographical second logarithm; this one overstates a correct bound as a minimum.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/ashby-11-7-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open AISafetyAtlas.Control

namespace AshbyElevenSevenLiteral

/-- §11/7 exactly as printed, varieties in bits: for every table with no repeated
outcome in a column (and at least one row and one column), `V_O ≥ V_D − V_R` for
every regulator, and some regulator attains `V_O = V_D − V_R`. -/
def LiteralPrint : Prop :=
  ∀ (D R E : Type) [Fintype D] [Fintype R] [DecidableEq R] [DecidableEq E]
    (T : D → R → E), (∀ r : R, Function.Injective fun d => T d r) →
    0 < Fintype.card D → 0 < Fintype.card R →
    (∀ ρ : D → R, Real.logb 2 (Fintype.card D) - Real.logb 2 (Fintype.card R)
        ≤ Real.logb 2 ((admittedOutcomes T ρ Finset.univ).card)) ∧
    ∃ ρ : D → R, Real.logb 2 ((admittedOutcomes T ρ Finset.univ).card)
        = Real.logb 2 (Fintype.card D) - Real.logb 2 (Fintype.card R)

/-- **No regulator attains `V_D − V_R` on any 3-by-2 table.** With three rows, two
columns and no repeat in a column, at least two outcomes occur, so `V_O ≥ 1`, while
`V_D − V_R = log₂ 3 − 1 < 1`. -/
theorem no_regulator_attains {D R E : Type} [Fintype D] [Fintype R] [DecidableEq R]
    [DecidableEq E] (T : D → R → E) (hcol : ∀ r : R, Function.Injective fun d => T d r)
    (hD : Fintype.card D = 3) (hR : Fintype.card R = 2) (ρ : D → R) :
    Real.logb 2 (Fintype.card D) - Real.logb 2 (Fintype.card R)
      < Real.logb 2 ((admittedOutcomes T ρ Finset.univ).card) := by
  have h2 : 2 ≤ (admittedOutcomes T ρ Finset.univ).card :=
    two_le_card_admittedOutcomes T ρ hcol (by omega)
  have hle : Real.logb 2 2 ≤ Real.logb 2 ((admittedOutcomes T ρ Finset.univ).card) :=
    Real.logb_le_logb_of_le one_lt_two (by norm_num) (by exact_mod_cast h2)
  have h34 : Real.logb 2 3 < Real.logb 2 4 :=
    Real.logb_lt_logb one_lt_two (by norm_num) (by norm_num)
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  rw [hD, hR]
  rw [Real.logb_self_eq_one one_lt_two] at hle
  push_cast
  rw [Real.logb_self_eq_one one_lt_two]
  linarith

/-- The table with columns `(0, 1, 2)` and `(1, 2, 0)`: three disturbances, two
responses, the second response shifting the outcome by one. -/
def table : Fin 3 → Bool → Fin 3 := fun d r => if r then d + 1 else d

theorem table_column_injective (r : Bool) : Function.Injective fun d => table d r := by
  cases r <;> decide

/-- **The printed line is false.** On the table above `V_D = log₂ 3`, `V_R = 1`, and
every regulator leaves `V_O ≥ 1 > log₂ 3 − 1`, so no regulator attains print's
minimum. -/
theorem not_literalPrint : ¬ LiteralPrint := by
  intro h
  obtain ⟨-, ρ, hρ⟩ := h (Fin 3) Bool (Fin 3) table table_column_injective
    (by decide) (by decide)
  exact (no_regulator_attains table table_column_injective (by decide) (by decide) ρ).ne'
    hρ

/-- **The repaired line holds in general**: on every table with no repeated outcome
in a column, every regulator leaves `V_O ≥ V_D − V_R` in bits, and in the integer
form at least `⌈|D| / |R|⌉` outcomes. -/
theorem repaired_holds (D R E : Type) [Fintype D] [Fintype R] [DecidableEq R]
    [DecidableEq E] (T : D → R → E) (hcol : ∀ r : R, Function.Injective fun d => T d r)
    (hD : 0 < Fintype.card D) (hR : 0 < Fintype.card R) (ρ : D → R) :
    Real.logb 2 (Fintype.card D) - Real.logb 2 (Fintype.card R)
        ≤ Real.logb 2 ((admittedOutcomes T ρ Finset.univ).card) ∧
      (Fintype.card D + Fintype.card R - 1) / Fintype.card R
        ≤ (admittedOutcomes T ρ Finset.univ).card := by
  refine ⟨?_, card_ceilDiv_le_admittedOutcomes T ρ hR hcol⟩
  unfold Real.logb
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (ashby_logVariety_ge T ρ hcol hD)
    (Real.log_nonneg one_le_two)

end AshbyElevenSevenLiteral
