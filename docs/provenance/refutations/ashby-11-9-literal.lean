import AISafetyAtlas.Control.VarietyCounting
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Ashby 11/9 as printed is false; the repaired bound is the one that holds

W. Ross Ashby, *An Introduction to Cybernetics* (1956; second impression 1957), §11/9, book p. 208:

    VO ≥ VD – log k – log VR ,
    in which the varieties are measured logarithmically.

(The scan sets ≥ as an underlined `>`, which text extraction reads as `>`;
the transcription from the page image is in
`docs/provenance/printed-statements/ashby-1957-introduction-to-cybernetics.yaml`.)

Varieties here are already logarithms (§7/7, p. 126: "the logarithm to the base 2 of the
number"; §11/7: "all measured logarithmically"), so `log VR` takes a second
logarithm of the regulator's variety. Read literally, the line is false. This file
proves that, on a table that satisfies every hypothesis Ashby states, and shows that
the same table satisfies the repaired bound `VO ≥ VD − log k − VR`, which the atlas
proves in general as `AISafetyAtlas.Control.ashby_logVariety_ge_mul`.

Why the repair is the necessary one and not a different theorem:

* it changes only the slip: `log VR` becomes `VR`, the regulator's variety in the
  unit §11/7 fixes for every other term of the line;
* Ashby's own entropy form of the same bound, two lines further on, is
  `H(D) – K – H(R)`, with no second logarithm on the regulator's term;
* for `k = 1` it is §11/7's `VO ≥ VD − VR`, which 11/9 says it modifies.

The counterexample is base 2, Ashby's unit. The literal line is not even stable in
the base: on this table it reads `0 ≥ log_b 2 − log_b (log_b 2)`, false exactly when
`log_b 2 < 2`, i.e. for every base above `√2` and true below it (not proved here), which
no statement about varieties can do.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/ashby-11-9-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open AISafetyAtlas.Control

namespace AshbyElevenNineLiteral

/-- §11/9 exactly as printed, varieties in bits: for every table whose entries
repeat at most `k` times per outcome-and-response pair,
`VO ≥ VD − log k − log VR`. -/
def LiteralPrint : Prop :=
  ∀ (D R E : Type) [Fintype D] [Fintype R] [DecidableEq R] [DecidableEq E]
    (T : D → R → E) (ρ : D → R) (k : ℕ),
    (∀ (e : E) (r : R),
      (Finset.univ.filter fun d => T d (ρ d) = e ∧ ρ d = r).card ≤ k) →
    0 < Fintype.card D →
    Real.logb 2 (Fintype.card D) - Real.logb 2 k
        - Real.logb 2 (Real.logb 2 (Fintype.card R))
      ≤ Real.logb 2 ((admittedOutcomes T ρ Finset.univ).card)

/-- Ashby's table `[[a, b], [b, a]]`: two disturbances, two responses, the outcome
is whether they differ. No outcome repeats in a column (§11/5's "once only"). -/
def table : Bool → Bool → Bool := fun d r => xor d r

/-- The regulator that answers each disturbance with itself, so the outcome is
always `false`. -/
def answer : Bool → Bool := id

theorem table_column_injective (r : Bool) : Function.Injective fun d => table d r := by
  intro a b h; cases a <;> cases b <;> cases r <;> simp_all [table]

/-- Multiplicity `k = 1`: the hypothesis of 11/9 at its smallest value. -/
theorem multiplicity_one (e r : Bool) :
    (Finset.univ.filter fun d => table d (answer d) = e ∧ answer d = r).card ≤ 1 := by
  cases e <;> cases r <;> decide

theorem one_outcome : (admittedOutcomes table answer Finset.univ).card = 1 := by
  decide

/-- **The printed line is false.** On the table above `VD = VR = 1` bit, `k = 1`
and `VO = 0`, so the printed bound reads `0 ≥ 1 − 0 − 0`. -/
theorem not_literalPrint : ¬ LiteralPrint := by
  intro h
  have := h Bool Bool Bool table answer 1 multiplicity_one (by decide)
  rw [one_outcome] at this
  simp [Fintype.card_bool, Real.logb_self_eq_one] at this
  norm_num at this

/-- **The repaired line holds on the same table**, as an instance of the atlas's
general theorem (natural logarithm; the bound is homogeneous in the base). -/
theorem repaired_holds :
    Real.log (Fintype.card Bool) - Real.log 1 - Real.log (Fintype.card Bool)
      ≤ Real.log ((admittedOutcomes table answer Finset.univ).card) := by
  exact_mod_cast ashby_logVariety_ge_mul table answer 1 multiplicity_one (by decide)

end AshbyElevenNineLiteral
