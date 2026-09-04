module

public import AISafetyAtlas.Conjectures.MAIS.O70
public import AISafetyAtlas.Conjectures.MAIS.O70Proof
public import AISafetyAtlas.SingularLearning.RankRealization
public import AISafetyAtlas.SingularLearning.ReducedRank

/-!
# MAIS-O70: what the candidate table actually computes

`AISafetyAtlas/Conjectures/MAIS/O70.lean` transcribes the table submitted as
MAIS issue #3 and states what it would mean for it to be right. This module
evaluates it, at the one stratum where **print states the answer itself**.

## Print's own anchor

`prob:calibration` closes with:

> "For example, when `N = M = H = 2` and `r = 0`, a neighborhood of `(I₂, 0)` has
> local coefficient `2`, whereas the table gives `3/2`."

At `(A, B) = (I₂, 0)` the ranks are `(a, b) = (2, 0)`. The candidate table
returns `2` there, and the Aoyagi–Watanabe minimum over the fiber is `3/2` — so
both halves of print's sentence are reproduced below, and the *gap* between them
is the phenomenon O70 exists to explain: the local coefficient at a less
degenerate point exceeds the global one.

This is the arithmetic half of the semantic anchor. The other half — the two-sided
volume order of the actual loss germ at `(I₂, 0)`, against `sublevelVolume` on a
metric ball — is the last example in
`AISafetyAtlas/Examples/Conjectures/MAIS/O70Proof.lean`, and it carries
`EigenvalueLawStatement` as a visible hypothesis.

What is still **not** proved *unconditionally* is the *exact* claim: that the
local learning coefficient of that germ equals `2` in the sense of
`HasExactLocalPair`, with a constant and an asymptotic rather than two-sided
bounds. `isO70RankTable_o70Pair` delivers it, but it needs
`O70ExactLocalPairsExist` on top of the eigenvalue law, and neither frontier is
formalized.

## The support gap in the scalar model

`M = N = H = 1`, `r = 0`. All three feasible strata attain the threshold `1/2`,
and only the origin has multiplicity `2` — which is exactly why
`rem:conventions`'s "a neighborhood of *a* factorization attaining the minimum"
is too weak to deliver `thm:aw`'s "largest `m(w)` among the minimizers". The
three strata are tabulated below.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open AISafetyAtlas.Conjectures.MAIS

/-! ## Print's worked stratum -/

/-- Print's `(I₂, 0)`: ranks `(a, b) = (2, 0)` at `N = M = H = 2`, `r = 0`.
The candidate table gives local coefficient `2`, as print says. -/
example : o70Pair 2 2 2 0 2 0 = (2, 1) := by
  norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
    residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
    residualIndices]
  decide

/-- …"whereas the table gives `3/2`" — the fiber minimum at the same parameters. -/
example : awLambda 2 2 2 0 = 3 / 2 := awLambda_two_two_two_zero

/-- So `(I₂, 0)` is *not* a minimiser: print's example is a strict gap. -/
example : awLambda 2 2 2 0 < o70Lambda 2 2 2 0 2 0 := by
  norm_num [o70Lambda, o70Q, o70Shape, awLambda, awBalancedNumerator, AWBalanced,
    residualMinCost_eq_argmin, residualArgmin, residualCost, residualIndices]

/-! ## The scalar model's three strata -/

/-- The origin `A = B = 0`: multiplicity `2`, matching `thm:aw`'s global pair. -/
example : o70Pair 1 1 1 0 0 0 = (1 / 2, 2) := by
  norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
    residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
    residualIndices]
  decide

/-- `A = 0`, `B ≠ 0`: the same threshold `1/2`, but multiplicity `1`. A domain
that is a neighborhood of only this point satisfies `rem:conventions` and yields
the wrong global multiplicity. -/
example : o70Pair 1 1 1 0 0 1 = (1 / 2, 1) := by
  norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
    residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
    residualIndices]
  decide

/-- `A ≠ 0`, `B = 0`: likewise. The threshold is shared by all three strata; the
multiplicity is not. -/
example : o70Pair 1 1 1 0 1 0 = (1 / 2, 1) := by
  norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
    residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
    residualIndices]
  decide

/-! ## The residual minimisation

The candidate states its residual pair as a discrete minimisation. Closing it in
the atlas replaced that search with a closed-form minimiser, clamped by `ℕ`
arithmetic: the vertex `(h + n - p)/2` truncates to `0` when `p > h + n`, which
is the correct left endpoint. -/

example (p n h : ℕ) : residualMinCost p n h = residualCost p n h (residualArgmin p n h) :=
  residualMinCost_eq_argmin p n h

/-- The minimiser lies in the index range, so the closed form is usable. -/
example (p n h : ℕ) : residualArgmin p n h ∈ residualIndices n h :=
  residualArgmin_mem p n h

/-- Multiplicity is always at least one: the minimum is attained. -/
example (M N H r a b : ℕ) : 0 < o70Multiplicity M N H r a b :=
  o70Multiplicity_pos M N H r a b

/-! ## What the propositions grade

`o70Minimizers` satisfies `IsO70AWValueStratumTable` by construction — that half
is bookkeeping. The content is `IsO70FiberMinimumTable`, which is what makes the
printed value a *minimum* rather than merely a number that some strata hit.

The same set also satisfies `IsO70MinimizerCharacterization`, which quantifies
over the actual germs instead of the table; that one is not bookkeeping, and it
is proved in `O70Proof.lean` under both frontier hypotheses. -/

example : IsO70AWValueStratumTable o70Pair o70Minimizers :=
  o70_aw_value_strata_correct

/-! ## From arithmetic to actual factorizations

`o70_fiber_minimum_correct` is a statement about rank *strata*. Composing it with
the rank-feasibility bridge turns it into a statement about every actual
factorization of every truth matrix: no point of the zero fiber `W₀` carries a
candidate value below the number printed in `thm:aw`.

This is what P3's word "minimum" means once print's own gloss — "λ is the minimum
of λ(w) over w ∈ W₀" — is taken at face value. It is unconditional: no eigenvalue
law, no exact-local-pair existence, no Aoyagi–Watanabe hypothesis.

It is a claim about the *candidate table*, not about the model's actual local
learning coefficients. Identifying the two is the analytic layer;
`O70Proof.lean` does it, but only under the two frontier hypotheses, so nothing
unconditional here reaches the actual germs. -/

/-- Every factorization's candidate value is at least the printed Aoyagi–Watanabe value. The
theorem is `awLambda_le_of_factorization` in `O70Proof.lean`; restated here so that the worked
models below read against it. -/
example {M N H : ℕ} (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    awLambda M N H (B * A).rank
      ≤ o70Lambda M N H (B * A).rank A.rank B.rank :=
  awLambda_le_of_factorization hM hN hH A B

/-- And the bound is attained, so it really is a minimum and not merely a bound:
the stratum `(a, b) = (r, r)` is realised by an actual factorization whenever the
truth rank is realisable, and there the candidate value equals `awLambda`. -/
example (M N H r : ℕ) (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (hr : r ≤ min M (min N H)) :
    ∃ a b, AdmissibleRankData M N H r a b ∧ o70Lambda M N H r a b = awLambda M N H r :=
  ⟨r, r, admissible_self M N H r hM hN hH hr, o70Lambda_self M N H r hr⟩

/-! ## The minimum is attained by an actual factorization

`o70_fiber_minimum_correct` says the printed value is attained at the rank
stratum `(a,b) = (r,r)`. That is an arithmetic statement about a stratum. With
`exists_factorization_of_feasible` — every feasible stratum is realised by real
matrices — it becomes a statement about the fiber itself.

Together with `awLambda_le_of_factorization` this is the complete semantic
content of P3 at the level of matrices: over the zero fiber `W₀` of any
realizable truth, the candidate table's value is at least `awLambda`, and some
point of `W₀` attains it. Print's own gloss on `thm:aw` — "λ is the minimum of
λ(w) over W₀" — is then matched exactly, with no Aoyagi–Watanabe hypothesis.

It remains a statement about the candidate *table*. That the table is the
model's actual local coefficient is P1 and P2, and is not proved. -/

/-- The printed Aoyagi–Watanabe value is attained by an actual factorization of
any realizable truth matrix.

Positive dimensions are *not* needed here: attainment at `(a,b) = (r,r)` is a
closed-form identity that holds degenerately too. They are needed for the lower
bound, which is where `rem:conventions`'s exclusion of `K ≡ 0` bites. -/
theorem exists_factorization_attaining_awLambda {M N H : ℕ}
    (C : Matrix (Fin M) (Fin N) ℝ) (hC : C.rank ≤ H) :
    ∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = C.rank ∧ B.rank = C.rank ∧
        o70Lambda M N H C.rank A.rank B.rank = awLambda M N H C.rank := by
  have hr : C.rank ≤ min M (min N H) := by
    simp only [le_min_iff]
    exact ⟨Matrix.rank_le_height C, Matrix.rank_le_width C, hC⟩
  obtain ⟨A, B, hBA, hA, hB⟩ :=
    exists_factorization_of_feasible C (feasible_self M N H C.rank hr)
  exact ⟨A, B, hBA, hA, hB, by rw [hA, hB]; exact o70Lambda_self M N H C.rank hr⟩

/-- **P3 at the level of matrices.** Over the zero fiber of a realizable truth,
the candidate value is bounded below by the printed number, and the bound is
attained. Unconditional. -/
theorem awLambda_is_fiber_minimum {M N H : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (C : Matrix (Fin M) (Fin N) ℝ) (hC : C.rank ≤ H) :
    (∀ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
        awLambda M N H C.rank ≤ o70Lambda M N H C.rank A.rank B.rank) ∧
      ∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ), B * A = C ∧
        o70Lambda M N H C.rank A.rank B.rank = awLambda M N H C.rank := by
  refine ⟨fun A B hBA => ?_, ?_⟩
  · subst hBA
    exact awLambda_le_of_factorization hM hN hH A B
  · obtain ⟨A, B, hBA, -, -, hval⟩ :=
      exists_factorization_attaining_awLambda C hC
    exact ⟨A, B, hBA, hval⟩

end AISafetyAtlas.Examples.Conjectures.MAIS
