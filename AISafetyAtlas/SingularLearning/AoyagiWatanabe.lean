module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.MinMax
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The Aoyagi–Watanabe global pair for reduced-rank regression

Transcribed from `MAIS-A6.tex` Theorem `thm:aw` (lines 184–202), the four-case
global learning coefficient and multiplicity of the reduced-rank regression
model

    p(y | x, w) = (2π)^{-M/2} exp(-½‖y - BAx‖²),   w = (A, B),

with `A : ℝ^{H×N}`, `B : ℝ^{M×H}`, input `x ~ N(0, I_N)`, realizable truth of
rank `r`, and zero fiber `W₀ = {(A,B) : BA = B₀A₀}`.

**This module declares no theorem about the model.** It transcribes print's
arithmetic and the rank-feasibility vocabulary the O70 statement layer needs.
Whether `awLambda` really is the global learning coefficient is Aoyagi–Watanabe's
theorem, not a definition here — see `docs/` and the O70 conjecture module.

## Why everything is `ℤ`-valued underneath

Print's case split compares sums like `M + r` against `N + H`, and the balanced
numerator `2(H+r)(M+N) - (M-N)² - (H+r)²` contains a genuine difference `M - N`
whose sign is unconstrained. Formed in `ℕ`, truncated subtraction silently
replaces `M - N` by `0` whenever `M < N` and yields a different number. Every
difference below is therefore taken in `ℤ` and only the final value is cast.

The same trap has a second entrance: the residual density exponent `(d-k-1)/2`
of the candidate's spectral step is negative at `d = k`. That belongs to the
analysis layer, but the rule is identical and is stated once here.

## Print's own gloss

`thm:aw` adds, in the same sentence that states the case list:

> "Equivalently, `λ` is the minimum of `λ(w)` over `w ∈ W₀`, and `m` is the
> largest `m(w)` among the minimizers."

That gloss is what makes MAIS-O70's third clause — characterize the strata on
which `λ(w*)` attains this minimum — a statement about the factorization fiber
rather than an import of the published theorem. It is recorded here because the
O70 statement layer depends on it.
-/

namespace AISafetyAtlas.SingularLearning

/-- The balanced numerator of `thm:aw` case (1), before the parity correction:
`2(H+r)(M+N) - (M-N)² - (H+r)²`, formed in `ℤ`. -/
@[expose] public def awBalancedNumerator (M N H r : ℕ) : ℤ :=
  2 * ((H : ℤ) + r) * ((M : ℤ) + N) - ((M : ℤ) - N) ^ 2 - ((H : ℤ) + r) ^ 2

/-- Print's case (1) hypothesis: `M + r ≤ N + H`, `N + r ≤ M + H`, `H + r ≤ M + N`. -/
@[expose] public def AWBalanced (M N H r : ℕ) : Prop :=
  M + r ≤ N + H ∧ N + r ≤ M + H ∧ H + r ≤ M + N

public instance (M N H r : ℕ) : Decidable (AWBalanced M N H r) := by
  unfold AWBalanced; infer_instance

/-- The global learning coefficient of `thm:aw`, all four cases.

Case (1) is the balanced regime, with a parity split on `M + N + H + r`; cases
(2)–(4) are the three unbalanced regimes. The case list is exhaustive: if the
three balanced inequalities do not all hold, exactly one of the three strict
reverses does — see `awCases_exhaustive`. -/
@[expose] public def awLambda (M N H r : ℕ) : ℚ :=
  if AWBalanced M N H r then
    if (M + N + H + r) % 2 = 0 then (awBalancedNumerator M N H r : ℚ) / 8
    else ((awBalancedNumerator M N H r : ℚ) + 1) / 8
  else if N + H < M + r then ((H * N : ℤ) - H * r + M * r : ℤ) / 2
  else if M + H < N + r then ((H * M : ℤ) - H * r + N * r : ℤ) / 2
  else ((M * N : ℚ)) / 2

/-- The global multiplicity of `thm:aw`: `2` exactly in the odd balanced case. -/
@[expose] public def awMultiplicity (M N H r : ℕ) : ℕ :=
  if AWBalanced M N H r ∧ (M + N + H + r) % 2 = 1 then 2 else 1

/-- Print's global pair. -/
@[expose] public def awPair (M N H r : ℕ) : ℚ × ℕ := (awLambda M N H r, awMultiplicity M N H r)

/-- The four cases of `thm:aw` are exhaustive: when the balanced hypothesis
fails, one of the three unbalanced strict inequalities holds. -/
public theorem awCases_exhaustive (M N H r : ℕ) (h : ¬ AWBalanced M N H r) :
    N + H < M + r ∨ M + H < N + r ∨ M + N < H + r := by
  unfold AWBalanced at h
  omega

/-! ## Rank feasibility

The arithmetic constraints on a rank stratum `(a, b) = (rank A, rank B)` of the
fiber `W₀` over a truth of rank `r`. `r ≤ min a b` and the two shape bounds are
immediate; `a + b - r ≤ H` is Sylvester's rank inequality, which the O70 module
proves for actual factorizations. -/

/-- Arithmetic rank feasibility for a stratum `(a, b)` over a truth of rank `r`.

Deliberately *not* requiring positive dimensions: this is the arithmetic core
used by the candidate's formula, and the degenerate cases are real strata of a
degenerate model. Print-facing statements add positivity through
`AdmissibleRankData`. -/
@[expose] public def Feasible (M N H r a b : ℕ) : Prop :=
  r ≤ min a b ∧ a ≤ min H N ∧ b ≤ min H M ∧ a + b ≤ H + r

public instance (M N H r a b : ℕ) : Decidable (Feasible M N H r a b) := by
  unfold Feasible; infer_instance

/-- The one admissibility predicate every print-facing rank-stratum statement
uses. `rem:conventions` excludes the vacuous case `K ≡ 0`, which for reduced-rank
regression is exactly a zero ambient dimension. -/
@[expose] public def AdmissibleRankData (M N H r a b : ℕ) : Prop :=
  0 < M ∧ 0 < N ∧ 0 < H ∧ r ≤ min M (min N H) ∧ Feasible M N H r a b

public instance (M N H r a b : ℕ) : Decidable (AdmissibleRankData M N H r a b) := by
  unfold AdmissibleRankData; infer_instance

public theorem Feasible.rank_le (h : Feasible M N H r a b) : r ≤ min M (min N H) := by
  obtain ⟨hr, ha, hb, _⟩ := h
  simp only [le_min_iff] at *
  omega

/-- `(a, b) = (r, r)` is feasible whenever the truth rank is realizable. It is
the uniform attainment witness for the fiber minimum. -/
public theorem feasible_self (M N H r : ℕ) (h : r ≤ min M (min N H)) :
    Feasible M N H r r r := by
  simp only [le_min_iff] at h
  exact ⟨by simp, by simp only [le_min_iff]; omega,
    by simp only [le_min_iff]; omega, by omega⟩

/-! ## Transcription anchors

Print states one worked value for this table, and `MAIS-O70`'s own example
restates it. Pinning it as a theorem means a future edit to the case split
cannot silently change the transcribed arithmetic: these break loudly.

The four values below exercise all four cases of `thm:aw`, and the second
exercises the odd-parity branch that carries the `log log n` term. -/

/-- `prob:calibration`'s worked example: for `N = M = H = 2` and `r = 0`,
"the table gives `3/2`". -/
public theorem awLambda_two_two_two_zero : awLambda 2 2 2 0 = 3 / 2 := by
  norm_num [awLambda, awBalancedNumerator, AWBalanced]

/-- The scalar model. Parity `M+N+H+r = 3` is odd, so `thm:aw` case (1b) applies
and the multiplicity is `2`. This is the smallest witness for the support gap
recorded against `rem:conventions`. -/
public theorem awPair_one_one_one_zero : awPair 1 1 1 0 = (1 / 2, 2) := by
  norm_num [awPair, awLambda, awMultiplicity, awBalancedNumerator, AWBalanced]

/-- Case (2), `N + H < M + r`. -/
public theorem awLambda_case_two : awLambda 5 1 1 0 = 1 / 2 := by
  norm_num [awLambda, awBalancedNumerator, AWBalanced]

/-- Case (3), `M + H < N + r`. -/
public theorem awLambda_case_three : awLambda 1 5 1 0 = 1 / 2 := by
  norm_num [awLambda, awBalancedNumerator, AWBalanced]

/-- Case (4), `M + N < H + r`. -/
public theorem awLambda_case_four : awLambda 1 1 5 0 = 1 / 2 := by
  norm_num [awLambda, awBalancedNumerator, AWBalanced]

end AISafetyAtlas.SingularLearning
