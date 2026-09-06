module

public import AISafetyAtlas.SingularLearning.HessianBlock

/-!
# Worked saddle Hessian block

The rung `k = 0` is the one MAIS-O7 computes: there `A` and `B` have rank zero,
so both are the zero matrix and the Hessian block degenerates to

    `[[0, -s I], [-s I, 0]]`.

The spectral condition is then `det (0 - s² I) = (-s²)^H`, nonzero for `s ≠ 0`,
so the block is nonsingular at the most degenerate rung — the case where the
diagonal blocks carry no information at all and the entire nondegeneracy comes
from the discarded mode.

This is the example worth having, because it is exactly where a Schur complement
against a diagonal block would fail.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning Matrix

/-- At the rank-zero rung both diagonal blocks vanish, and the Hessian block is
still nonsingular. -/
example {H : ℕ} {s : ℝ} (hs : s ≠ 0) :
    (fromBlocks (0 : Matrix (Fin H) (Fin H) ℝ) ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ))
      ((-s) • 1) 0).det ≠ 0 := by
  refine det_hessianBlock_ne_zero hs 0 0 ?_
  rw [Matrix.zero_mul, zero_sub, Matrix.det_neg, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (pow_ne_zero _ hs))

/-- The determinant identity itself, at the same rung. -/
example {H : ℕ} {s : ℝ} (hs : s ≠ 0) :
    (fromBlocks ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) (0 : Matrix (Fin H) (Fin H) ℝ)
        (0 : Matrix (Fin H) (Fin H) ℝ) ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ))).det
      = (-1 : ℝ) ^ H * ((0 : Matrix (Fin H) (Fin H) ℝ) * (0 : Matrix (Fin H) (Fin H) ℝ)
          - (s ^ 2) • (1 : Matrix (Fin H) (Fin H) ℝ)).det :=
  det_fromBlocks_offDiagonal hs 0 0


/-! ## A nonterminal rung, where the diagonal blocks are not zero

The rank-zero rung above is the extreme case.  The two examples below exercise
the general statements on a rung that is nonterminal for the ordinary reason: the
hidden width `H = 2` exceeds the bottleneck the factorization actually passes
through, so `rank (B A) < H` however `A` and `B` are chosen, and one Gram block
must have a kernel vector.  The second example then shows the block form taking
both signs with a diagonal block that is neither zero nor definite.
-/

/-- **Every factorization through a width-one bottleneck is nonterminal at
`H = 2`**, so one of its two Gram blocks always has a kernel vector.  No
genericity assumption on `A` or `B` is needed: the shape alone forces
`rank (B A) ≤ 1 < 2`. -/
example (A : Matrix (Fin 2) (Fin 1) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ) :
    ∃ z : Fin 2 → ℝ, z ≠ 0 ∧ ((Bᵀ * B) *ᵥ z = 0 ∨ (A * Aᵀ) *ᵥ z = 0) :=
  exists_mem_ker_gram A B
    (lt_of_le_of_lt (Matrix.rank_le_height (B * A)) (by norm_num))

/-- **The block form takes both signs at a rung whose blocks are not zero.**
`P = e₀ e₀ᵀ` is a rank-one projection and `R = 1` is the identity: both are
positive semidefinite, neither is zero, and `R` is even positive definite.  The
kernel vector `e₁` of `P` alone is enough, which is the point of the hypothesis
being a disjunction. -/
example {s : ℝ} (hs : 0 < s) :
    (∃ x y : Fin 2 → ℝ,
        x ⬝ᵥ (!![(1 : ℝ), 0; 0, 0] *ᵥ x)
          + y ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ y) - 2 * s * (x ⬝ᵥ y) < 0) ∧
      (∃ x y : Fin 2 → ℝ,
        0 < x ⬝ᵥ (!![(1 : ℝ), 0; 0, 0] *ᵥ x)
          + y ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ y) - 2 * s * (x ⬝ᵥ y)) := by
  refine hessianBlock_quadForm_indefinite hs (P := !![(1 : ℝ), 0; 0, 0]) (R := 1)
    (z := ![0, 1]) ?_ ?_ ?_ (Or.inl ?_)
  · intro x
    have hx : x ⬝ᵥ (!![(1 : ℝ), 0; 0, 0] *ᵥ x) = x 0 * x 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hx]
    exact mul_self_nonneg _
  · intro y
    rw [Matrix.one_mulVec, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  · intro h
    have h1 := congrFun h 1
    norm_num at h1
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end AISafetyAtlas.Examples.SingularLearning
