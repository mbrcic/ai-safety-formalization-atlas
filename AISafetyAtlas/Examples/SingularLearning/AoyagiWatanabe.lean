module

public import AISafetyAtlas.SingularLearning.AoyagiWatanabe

/-!
# Worked models for the Aoyagi–Watanabe transcription

`AISafetyAtlas/SingularLearning/AoyagiWatanabe.lean` transcribes `thm:aw`'s
four-case global pair. A transcription is worth nothing until someone can see it
run, so this module evaluates it where print states a value, and exhibits the
one place where print's own convention does not deliver what the theorem asserts.

## The scalar model, and a gap in `rem:conventions`

`M = N = H = 1`, `r = 0`: the model is `y = bax + noise` with two real
parameters and `K(a,b) = ½(ba)²`. Parity `M+N+H+r = 3` is odd, so `thm:aw` case
(1b) gives the global pair `(1/2, 2)` — the multiplicity `2` is what produces the
`log log n` term in the free energy.

`thm:aw` says `m` is "the largest `m(w)` among the minimizers", while
`rem:conventions` guarantees only that the parameter domain `W` "contains a
neighborhood of **a** factorization attaining the Aoyagi–Watanabe minimum". Those
do not match. In this model all three rank strata attain the threshold `1/2`,
but only the origin `A = B = 0` has local multiplicity `2`: near a point with
`B = b₀ ≠ 0` the loss is comparable to `a²` in one effective variable, giving
multiplicity `1`. A `W` that is a neighborhood of such a point satisfies
`rem:conventions` and yields the global pair `(1/2, 1)`, not `thm:aw`'s
`(1/2, 2)`.

The arithmetic half of that observation is `awPair_one_one_one_zero` below
together with the local table in `Examples/Conjectures/MAIS/O70.lean`; the
statement about the actual loss germ is not formalized here.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- Print's worked value: at `N = M = H = 2`, `r = 0`, "the table gives `3/2`". -/
example : awLambda 2 2 2 0 = 3 / 2 := awLambda_two_two_two_zero

/-- The scalar model's global pair, `thm:aw` case (1b). -/
example : awPair 1 1 1 0 = (1 / 2, 2) := awPair_one_one_one_zero

/-- The odd-parity branch really is the one that lifts the multiplicity: the
same dimensions with `r = 1` are even, and the multiplicity drops to `1`. -/
example : awMultiplicity 1 1 1 1 = 1 := by
  norm_num [awMultiplicity, AWBalanced]

/-- All four cases are reachable, so no branch of the transcription is dead. -/
example : awLambda 5 1 1 0 = 1 / 2 ∧ awLambda 1 5 1 0 = 1 / 2 ∧ awLambda 1 1 5 0 = 1 / 2 :=
  ⟨awLambda_case_two, awLambda_case_three, awLambda_case_four⟩

/-- The case list is total: outside the balanced regime one strict reverse holds. -/
example (M N H r : ℕ) (h : ¬ AWBalanced M N H r) :
    N + H < M + r ∨ M + H < N + r ∨ M + N < H + r :=
  awCases_exhaustive M N H r h

/-- The uniform attainment witness `(a,b) = (r,r)` is feasible whenever the truth
rank is realizable. This is what collapses P3's attainment obligation from a
search over the rank polytope to a single closed-form identity. -/
example (M N H r : ℕ) (h : r ≤ min M (min N H)) : Feasible M N H r r r :=
  feasible_self M N H r h

/-- Feasibility already pins the truth rank: no extra hypothesis is needed. -/
example (M N H r a b : ℕ) (h : Feasible M N H r a b) : r ≤ min M (min N H) :=
  h.rank_le

/-- `Feasible` alone admits a zero ambient dimension — which is why every
print-facing statement goes through `AdmissibleRankData` instead. `rem:conventions`
excludes the vacuous case `K ≡ 0`, and for reduced-rank regression that is
exactly a vanishing dimension. -/
example : Feasible 0 0 0 0 0 0 ∧ ¬ AdmissibleRankData 0 0 0 0 0 0 := by
  constructor
  · exact ⟨by simp, by simp, by simp, by simp⟩
  · rintro ⟨h, -, -, -, -⟩
    exact absurd h (by simp)

end AISafetyAtlas.Examples.SingularLearning
