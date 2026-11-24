import AISafetyAtlas.Goodhart.Regressional

/-!
# Manheim and Garrabrant's Regressional Goodhart, read without independence, is false

David Manheim and Scott Garrabrant, *Categorizing Variants of Goodhart's Law*,
arXiv:1803.04585v4 (24 Feb 2019), §1, p. 2 (PDF p. 2; audit row S17-R02):

    Regressional Goodhart - When selecting for a proxy measure, you select not only
    for the true goal, but also for the difference between the proxy and the goal.

with the setting of the same page (entry `mg-setup`): states `s ∈ S`, a goal
`G(s) → ℝ`, a proxy `M(s) → ℝ`, and "the regulator chooses some threshold `c` and the
permissible states are defined such that `s ∈ A` if `M(s) ≥ c`. This creates a
selection pressure". (Transcribed from the page image in
`docs/provenance/printed-statements/manheim-2018-goodhart-variants.yaml`, entries
`mg-regressional` and `mg-setup`.) The paper states no probability law on the states
and no independence of `G` and `M − G` (the yaml's `source.standing`: "no
probability space, no independence of G and the noise in (1)").

**The reading.** The sentence is explanatory, not a theorem, so a reading has to be
fixed before anything is refuted. "Selecting for" a quantity is read in its usual
sense: the selection raises it on average, i.e. the quantity's mean among the
permissible states is at least its mean among all states. In product form, so that
nothing divides by the selected mass (the form of the library's `gap_selection_ge`):
`E[X] · P(A) ≤ E[X ; A]`, for `X = G` and for `X = M − G`. That is the reading the
regrade's adjudication graded (row 254). It is stated here on a finite set of
states with nonnegative weights summing to one. A finite law is one of the laws any
wider reading (every law on `ℝ × ℝ`, every state space) quantifies over, so a failure
here is a failure there; and both witnesses use equal weights, so the reading that
counts each state once fails too. The threshold is print's `M(s) ≥ c`; both
witnesses put `c` strictly between values of `M`, so they also refute the strict
reading `M(s) > c` of the library's `selected` (not proved here).

The other reading, that threshold selection on `M = G + (M − G)` picks a superlevel
set of that sum, is true, and is what the library's definitions `goal`, `gap`,
`proxy` and `selected` render. It is not refuted here.

**How it fails.** Without independence, what selection does to each summand depends
on how the summands are coupled:

* the gap component fails when the gap moves against the goal: `M − G = −G/2`, i.e.
  `M = G/2`; selecting large `M` selects large `G` and so a small gap
  (`not_literalGap`, two states);
* the goal component fails when the proxy is driven by the gap: three equally
  weighted states `(M, G) = (−10, 0), (0, 10), (1, 0)` and `c = 1/2`; only the third
  state is selected, and its goal is below the mean (`not_literalGoal`).

In both witnesses the proxy is positively correlated with the goal (covariance
`1/2` and `10`; not proved here), so neither leaves print's notion of a proxy (`mg-goodhart-effect`:
a goal and "the proxy used for that goal", with a statistical relationship between
them).

Why the repair is the necessary one and not a different theorem:

* it adds one hypothesis print does not supply: the noise `M − G` is independent of
  `G` (and integrable). Eq. (1), the same section's *Simple Model*
  `M = G + normal(μ, σ²)`, is where the paper models the noise, but it prints nothing
  about how the noise relates to `G` (the yaml's note on `mg-eq-1`), so independence
  is added, not read off print. The two witnesses prove that some coupling
  hypothesis is necessary; independence is sufficient and is the one the library's
  product carrier encodes. Weaker sufficient conditions (positive association, say)
  are not ruled out, so minimality is not claimed;
* under it the gap component is the library's `gap_selection_ge`, on the product
  measure `μ.prod ν`, which is the independence; `repaired_holds` states it;
* the goal component under independence is not in the library (the library's own
  docstring says so); as in `pauly-thm-3-2-literal.lean`, this file proves no
  `repaired_holds` for it.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/regressional-gap-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open MeasureTheory AISafetyAtlas.Goodhart

namespace RegressionalGapLiteral

/-- "Selecting on `M ≥ c` selects for `X`", in product form, for every finite law on
the states: the weighted mean of `X` times the selected mass is at most the selected
mass of `X`. -/
def SelectsFor (X : ∀ {S : Type}, (S → ℝ) → (S → ℝ) → S → ℝ) : Prop :=
  ∀ (S : Type) [Fintype S] (w G M : S → ℝ), (∀ s, 0 ≤ w s) → ∑ s, w s = 1 → ∀ c : ℝ,
    (∑ s, w s * X G M s) * (∑ s, if c ≤ M s then w s else 0)
      ≤ ∑ s, if c ≤ M s then w s * X G M s else 0

/-- Print's goal component: selecting for the proxy selects for the goal `G`. -/
def LiteralGoal : Prop := SelectsFor fun G _ s => G s

/-- Print's gap component: selecting for the proxy selects for the difference
`M − G` between the proxy and the goal. -/
def LiteralGap : Prop := SelectsFor fun G M s => M s - G s

/-- The sentence as printed, both components, with no coupling hypothesis. -/
def LiteralPrint : Prop := LiteralGoal ∧ LiteralGap

/-- **The gap component is false.** Two equally likely states with goal `0` and `2`
and proxy `M = G/2`, so the gap `M − G = −G/2` is `0` and `−1`; at `c = 1/2` only the
second state is selected: `(−1/2) · (1/2) ≤ (1/2) · (−1)` fails. -/
theorem not_literalGap : ¬ LiteralGap := by
  intro h
  have := h Bool (fun _ => 1 / 2) (fun s => if s then 2 else 0)
    (fun s => if s then 1 else 0) (fun _ => by norm_num) (by norm_num) (1 / 2)
  norm_num at this

/-- **The goal component is false.** Three equally likely states
`(M, G) = (−10, 0), (0, 10), (1, 0)`; at `c = 1/2` only the third is selected:
`(10/3) · (1/3) ≤ 0` fails. -/
theorem not_literalGoal : ¬ LiteralGoal := by
  intro h
  have := h (Fin 3) (fun _ => 1 / 3) ![0, 10, 0] ![-10, 0, 1] (fun _ => by norm_num)
    (by norm_num) (1 / 2)
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two] at this

/-- **The printed sentence, read without independence, is false.** Either component
alone already fails (`not_literalGoal`, `not_literalGap`). -/
theorem not_literalPrint : ¬ LiteralPrint := fun h => not_literalGoal h.1

/-- **The repaired gap component holds**, as the library proves it: with the goal law
`μ` and an integrable noise law `ν` independent (the product measure), selecting on
the proxy raises the expected gap, in the same product form. -/
theorem repaired_holds (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ) :
    (∫ x, x ∂ν) * (μ.prod ν).real (selected c) ≤ ∫ p in selected c, gap p ∂(μ.prod ν) :=
  gap_selection_ge μ ν hν c

end RegressionalGapLiteral
