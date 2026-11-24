import AISafetyAtlas.Control.VarietyCounting

/-!
# Ashby 11/6 as printed is false; the ceiling form is the one that holds

W. Ross Ashby, *An Introduction to Cybernetics* (1956; second impression 1957), §11/6,
book p. 206 (PDF p. 110; audit row S03-R03):

    If next R uses, or has available, two moves, then the variety of the
    outcomes can be reduced to a half (but not lower). If R has three moves, it
    can be reduced to a third (but not lower); and so on.

(Transcribed from the page image in
`docs/provenance/printed-statements/ashby-1957-introduction-to-cybernetics.yaml`,
entry `ashby-11-6`, whose note reads: "can be reduced to a half" is an attainability
claim made without a construction.) The game is §11/5's, "still with the restriction
that no element may be repeated in a column"; variety is the number of distinct
elements (§7/7).

The "not lower" half is true: it is `AISafetyAtlas.Control.ashby_variety_ge`, and in
the integer form `AISafetyAtlas.Control.card_ceilDiv_le_admittedOutcomes`. The "can be
reduced to" half is false. The number of outcomes is an integer and `|D| / c` need not
be. At `|D| = 3` and two moves every strategy on every column-injective table leaves
at least two outcomes (`AISafetyAtlas.Control.two_le_card_admittedOutcomes`), and
`2 > 3/2`. This file proves that for **every** such table (`no_strategy_attains`), so
print fails whether "can" ranges over the strategies of one table or over all tables
of the shape (`not_literalPrint`, the weaker of the two readings). It fails at print's
own game: Table 11/5/1 has nine rows, so "reduced to a half" is `4.5`, never a count.
In bits the same instance fails: `log₂ n = log₂ 3 − 1` forces `n = 3/2`.

The per-table reading fails a second way, without integrality: on the table
`T d r = d` every column is injective and every strategy admits every outcome, so the
variety stays `|D|` even when `c` divides `|D|` (`diagonal_admits_all`). So "can"
must range over the tables of the shape.

Why the repair is the necessary one and not a different theorem:

* it keeps "but not lower", which §11/5's argument on the same page proves
  ("the variety in the selected set of outcomes cannot be fewer than `r/c`");
* it replaces "reduced to `|D| / c`" by "reduced to `⌈|D| / c⌉` on some table of the
  shape", the least integer not below `|D| / c`, so it lowers print's target by the
  rounding and by nothing else; §11/5's construction ("at the n-th row all the columns
  are used, so one of the columns must be used again for the next row, and a new
  outcome must be allowed into the set") is the block construction that attains it
  (`AISafetyAtlas.Control.ashby_variety_ge_isSharp`);
* "on some table" is forced by `diagonal_admits_all`, and is print's own
  "assuming that everything falls as favourably as possible" (§11/5);
* the law §11/6 draws from it ("only variety in R's moves can force down the variety
  in the outcomes") is a statement about the bound and survives intact.

This is the defect of §11/7 (`docs/provenance/refutations/ashby-11-7-literal.lean`,
accepted 2026-11-20) one section earlier: a correct bound stated as attained.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/ashby-11-6-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open AISafetyAtlas.Control

namespace AshbyElevenSixLiteral

/-- §11/6 exactly as printed, in its weaker reading: at every shape (`|D| > 0`
disturbances, `c > 0` moves for R) the outcomes are never fewer than `|D| / c`, and on
**some** table with no repeated outcome in a column some strategy reduces them to
exactly `|D| / c`. The per-table reading implies this one. -/
def LiteralPrint : Prop :=
  ∀ (D R : Type) [Fintype D] [Fintype R] [DecidableEq R],
    0 < Fintype.card D → 0 < Fintype.card R →
    (∀ (E : Type) [DecidableEq E] (T : D → R → E),
        (∀ r : R, Function.Injective fun d => T d r) →
        ∀ ρ : D → R, (Fintype.card D : ℚ) / Fintype.card R
          ≤ ((admittedOutcomes T ρ Finset.univ).card : ℚ)) ∧
    ∃ (E : Type) (_ : DecidableEq E) (T : D → R → E),
      (∀ r : R, Function.Injective fun d => T d r) ∧
      ∃ ρ : D → R, ((admittedOutcomes T ρ Finset.univ).card : ℚ)
        = (Fintype.card D : ℚ) / Fintype.card R

/-- **No strategy reduces a 3-by-2 game to a half.** With three rows, two columns and
no repeat in a column, at least two outcomes occur, and `2 > 3/2`. -/
theorem no_strategy_attains {D R E : Type} [Fintype D] [Fintype R] [DecidableEq R]
    [DecidableEq E] (T : D → R → E) (hcol : ∀ r : R, Function.Injective fun d => T d r)
    (hD : Fintype.card D = 3) (hR : Fintype.card R = 2) (ρ : D → R) :
    (Fintype.card D : ℚ) / Fintype.card R < ((admittedOutcomes T ρ Finset.univ).card : ℚ) := by
  have h2 : 2 ≤ (admittedOutcomes T ρ Finset.univ).card :=
    two_le_card_admittedOutcomes T ρ hcol (by omega)
  have h2' : (2 : ℚ) ≤ ((admittedOutcomes T ρ Finset.univ).card : ℚ) := by exact_mod_cast h2
  rw [hD, hR]
  push_cast
  linarith

/-- **The printed line is false.** At three disturbances and two moves no table and no
strategy reduces the outcomes to a half. -/
theorem not_literalPrint : ¬ LiteralPrint := by
  intro h
  obtain ⟨-, E, _, T, hcol, ρ, hρ⟩ := h (Fin 3) Bool (by decide) (by decide)
  exact (no_strategy_attains T hcol (by decide) (by decide) ρ).ne' hρ

/-- **The per-table reading fails without integrality.** On the table `T d r = d`
every column is injective and every strategy admits every disturbance as an outcome. -/
theorem diagonal_admits_all (D R : Type) [Fintype D] [DecidableEq D] [DecidableEq R]
    (ρ : D → R) :
    (∀ _r : R, Function.Injective fun d : D => d) ∧
      (admittedOutcomes (fun (d : D) (_ : R) => d) ρ Finset.univ).card = Fintype.card D := by
  refine ⟨fun _ => Function.injective_id, ?_⟩
  simp [admittedOutcomes]

/-- **The repaired line holds at every shape**: on every table with no repeated outcome
in a column every strategy leaves at least `|D| / c` outcomes, and at least `⌈|D| / c⌉`;
and on some table of the shape some strategy leaves exactly `⌈|D| / c⌉`. -/
theorem repaired_holds (r c : ℕ) [NeZero c] (hc : 0 < c) :
    (∀ (E : Type) [DecidableEq E] (T : Fin r → ZMod c → E),
        (∀ k, Function.Injective fun d => T d k) → ∀ ρ : Fin r → ZMod c,
        ((r : ℚ) / c ≤ ((admittedOutcomes T ρ Finset.univ).card : ℚ)) ∧
          (r + c - 1) / c ≤ (admittedOutcomes T ρ Finset.univ).card) ∧
      ((∀ k : ZMod c, Function.Injective fun d : Fin r => shiftTable r c hc d k) ∧
        (admittedOutcomes (shiftTable r c hc) (shiftStrategy r c) Finset.univ).card
          = (r + c - 1) / c) := by
  have hcard : Fintype.card (ZMod c) = c := ZMod.card c
  refine ⟨fun E _ T hcol ρ => ⟨?_, ?_⟩, ?_⟩
  · simpa [hcard] using ashby_variety_ge T ρ hcol
  · simpa [hcard] using card_ceilDiv_le_admittedOutcomes T ρ (by rw [hcard]; exact hc) hcol
  · simpa [hcard] using ashby_variety_ge_isSharp r c hc

end AshbyElevenSixLiteral
