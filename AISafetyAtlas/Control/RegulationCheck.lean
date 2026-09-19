module

public import AISafetyAtlas.Control.VarietyCounting
public import Mathlib.Data.Fintype.Card

/-!
# Deciding Ashby's counting law on a finite table

`Control.VarietyCounting.ashby_variety_ge` says that a regulator cannot hold the
outcome steadier than its own repertoire allows: with `r` disturbances, `c`
responses and no response column repeating an outcome, the strategy admits at
least `r / c` distinct outcomes. On a finite table every part of that is
decidable, and this module supplies the decision procedure together with the
theorem saying it agrees with the `Prop` — which is what `atlas-check` needs, and
`kind: "regulation"` is this checker.

## Why a runnable form of *this* statement

The counting law is not in doubt; the kernel settled it. What a runnable form
adds is a guard against a different failure, and it is the one this repository
has shipped six times: a compiling, axiom-clean, correctly-transcribed statement
about nothing. `ashby_variety_ge` takes a column-injectivity hypothesis, and
nothing in the build tests whether any table satisfies it — a theorem no model
satisfies is a valid proof.

So `columnsInjective` is doing double duty. It is the checker's precondition,
and a `true` verdict on a concrete table is a **satisfiability witness**: this
table is in the region the theorem quantifies over, exhibited rather than
asserted. `Examples.Control.RegulationCheck` carries the worked ones, and
`scripts/check_atlas_check.sh` asserts the executable agrees with them.

## What a `false` verdict is not

`columnsInjective` returning `false` means Ashby's hypothesis fails on this
table, so the law says nothing here. It does **not** mean regulation succeeds,
and `exists_columnsInjective_false_and_bound_fails` is the proof that the two
must not be confused: on a table with a repeated column the bound is not merely
unproved but false, so a reader who took `false` as a clearance would have the
conclusion backwards.

## Explicit non-claims

- **Not a decision procedure for good regulation.** It decides one counting
  obstruction on one table under one strategy. A regulator can fail for reasons
  this never looks at.
- **A `false` verdict is not a safety verdict.** It means the argument does not
  apply here.
- **Nothing about entropies.** The entropy forms of the law (11/8, 11/9) live in
  `Control.RequisiteVariety` over a measure, and nothing finite decides them; the
  checker covers the counting half only.
- **Not a proof term.** Like the rest of `atlas-check`, the executable returns a
  verdict and names the theorem that certifies it. The kernel has checked the
  theorem, not the instance.
- **Not a witness for the atlas widening, and the two must not be confused.**
  `scripts/check_scope_witnesses.py` asks a different question: Ashby's rows are
  graded `Wider` because the atlas takes a `Finset` of disturbances and an
  arbitrary outcome type where the chapter takes a finite table, and closing one
  of *those* rows needs an object living in the widened region that could not be
  stated at the printed hypotheses. Every table here is `Fin n → Fin m → Fin k`
  — Ashby's own finite case — so these witness that the hypothesis is
  satisfiable and say nothing about the widening. That report stood at 17 of 51
  rows witnessed before this module and stands there after it.
-/

namespace AISafetyAtlas.Control

open Function

/--
**Ashby's column condition, decided.** `true` when no response column repeats an
outcome — that is, when each response `r` distinguishes every pair of
disturbances.

A `true` verdict is also a satisfiability witness for `ashby_variety_ge`'s
hypothesis at this table.
-/
@[expose] public def columnsInjective {n m k : ℕ} (T : Fin n → Fin m → Fin k) : Bool :=
  decide (∀ r : Fin m, Injective fun d => T d r)

/--
The outcomes the strategy actually admits, counted. Ashby's *"set of outcomes
selected by R, one from each row"*.
-/
@[expose] public def achievedVariety {n m k : ℕ}
    (T : Fin n → Fin m → Fin k) (ρ : Fin n → Fin m) : ℕ :=
  (admittedOutcomes T ρ Finset.univ).card

/--
**The agreement theorem.** When the decision procedure says the column condition
holds, the admitted-outcome count is at least the number of disturbances divided
by the number of responses — Ashby 11/5, at this table, for every strategy.
-/
public theorem ashby_bound_of_columnsInjective {n m k : ℕ} {T : Fin n → Fin m → Fin k}
    (ρ : Fin n → Fin m) (h : columnsInjective T = true) :
    (n : ℚ) / m ≤ achievedVariety T ρ := by
  have hcol : ∀ r : Fin m, Injective fun d => T d r := of_decide_eq_true h
  have := ashby_variety_ge T ρ hcol
  simpa [achievedVariety, Fintype.card_fin] using this

/--
**A `false` verdict is not a clearance.** There is a table whose column condition
fails and on which the counting bound is *false*, so "the obstruction does not
apply" and "the regulator does better" are different claims.

Two disturbances, one response, one outcome: the single column repeats, the
strategy admits one outcome, and the bound would demand two.
-/
public theorem exists_columnsInjective_false_and_bound_fails :
    ∃ (T : Fin 2 → Fin 1 → Fin 1) (ρ : Fin 2 → Fin 1),
      columnsInjective T = false
        ∧ ¬ ((2 : ℚ) / 1 ≤ achievedVariety T ρ) := by
  refine ⟨fun _ _ => 0, fun _ => 0, by decide, ?_⟩
  have hone : achievedVariety (n := 2) (m := 1) (k := 1) (fun _ _ => 0) (fun _ => 0) = 1 := by
    decide
  rw [hone]
  norm_num

end AISafetyAtlas.Control
