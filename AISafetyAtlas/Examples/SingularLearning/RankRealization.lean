module

public import AISafetyAtlas.SingularLearning.RankRealization

/-!
# Worked models for rank-stratum realization

`AISafetyAtlas/SingularLearning/ReducedRank.lean` proves one direction: every
actual factorization has feasible ranks. This module exercises the converse —
every feasible stratum is realised by actual matrices.

**Why both directions are needed.** MAIS-O70's third clause is graded by a
proposition quantified over *rank strata*. If some feasible stratum were realised
by no pair of matrices, "every stratum" would say less than it appears to about
the zero fiber `W₀ = {(A,B) : B*A = C}`, and the fiber-minimum theorem would be
weaker than its name. With both directions the correspondence is exact:
`exists_factorization_iff_feasible`.

The pinned Mathlib has **no rectangular rank normal form** —
`Matrix.exists_rank_normal_form` is square-only and its two-sided transformation
mixes rows with columns, so it does not restrict — and no rank factorization
either. `exists_rank_normal_form` is built from adapted bases.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- Every feasible stratum is realised. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) {a b : ℕ}
    (hfeas : Feasible M N H C.rank a b) :
    ∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = a ∧ B.rank = b :=
  exists_factorization_of_feasible C hfeas

/-- **The exact correspondence.** Realised strata and feasible strata are the
same set — this is what makes a statement quantified over strata a statement
about the fiber. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) (a b : ℕ) :
    (∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = a ∧ B.rank = b) ↔ Feasible M N H C.rank a b :=
  exists_factorization_iff_feasible C a b

/-- The uniform witness `(a,b) = (r,r)` that the fiber-minimum theorem attains
its bound at. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) (hC : C.rank ≤ H) :
    ∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = C.rank ∧ B.rank = C.rank :=
  exists_factorization_rank_self C hC

end AISafetyAtlas.Examples.SingularLearning
