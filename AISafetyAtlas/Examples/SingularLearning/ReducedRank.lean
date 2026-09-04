module

public import AISafetyAtlas.SingularLearning.ReducedRank

/-!
# Worked models for the rank-feasibility bridge

`AISafetyAtlas/SingularLearning/ReducedRank.lean` proves that the ranks of any
actual factorization satisfy the arithmetic predicate `Feasible`. That is the
bridge without which a statement about rank strata says nothing about the zero
fiber `W₀ = {(A, B) : B * A = C}` of the reduced-rank model.

Three of its four conjuncts are Mathlib one-liners. The fourth, Sylvester's rank
inequality `rank A + rank B ≤ H + rank (B * A)`, is not in Mathlib in any form —
the pinned tree carries only *upper* bounds on the rank of a product
(`Matrix.rank_mul_le`, `rank_comp_le_left`, `rank_comp_le_right`). It is proved
there from rank–nullity.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- Every factorization lands in the arithmetic rank polytope. -/
example {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    Feasible M N H (B * A).rank A.rank B.rank :=
  ranks_feasible_of_mul_eq A B

/-- The zero-fiber reading: a point of `W₀` over a truth matrix `C`. -/
example {M N H : ℕ} {C : Matrix (Fin M) (Fin N) ℝ}
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) (hC : B * A = C) :
    Feasible M N H C.rank A.rank B.rank :=
  ranks_feasible_of_factorization A B hC

/-- Sylvester's inequality on its own. -/
example {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    A.rank + B.rank ≤ H + (B * A).rank :=
  rank_add_rank_le_of_mul A B

/-- With positive dimensions the stratum is admissible, which is the domain every
print-facing O70 statement quantifies over. -/
example {M N H : ℕ} (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    AdmissibleRankData M N H (B * A).rank A.rank B.rank :=
  admissible_of_mul_eq hM hN hH A B

end AISafetyAtlas.Examples.SingularLearning
