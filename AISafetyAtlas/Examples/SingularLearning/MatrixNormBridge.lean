module

public import AISafetyAtlas.SingularLearning.MatrixNormBridge

/-!
# Worked models for the instance-free matrix norms

`AISafetyAtlas/SingularLearning/EliminationChart.lean` states Theorem 5.1 and
proves its Step 7, but cannot construct the chart. The obstruction is not
mathematics: Lemmas 5.2 and 5.4 need **the ℓ² operator norm and the Frobenius
norm on `Matrix` at the same time**, and in Mathlib those are two incompatible
`NormedAddCommGroup` instances on one type, only one of which can be active.

This module removes it by stating both without instances — `frobeniusSq` as an
explicit double sum, `IsOpNormSqBound` as a quantified inequality over explicit
sums. Downstream code can then use them under either instance.

The same discipline is why `Loss.lean` keeps `rrrLoss_eq_sum_sq` as its primary
form: `Fin M → ℝ` carries the **supremum** norm in Mathlib, and a printed definition
rendered with `‖·‖` there states something other than print, and the difference
survives `#check`. These statements are written as sums on purpose; do not "simplify"
them back into `‖·‖`.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **Lemma 5.2, instance-free.** An operator bound on `G` gives a Frobenius
bound on `G * W` — the mixed inequality that no single norm instance can state. -/
example {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {G : Matrix ι κ ℝ} {c : ℝ} (hG : IsOpNormSqBound G c) (W : Matrix κ ν ℝ) :
    frobeniusSq (G * W) ≤ c * frobeniusSq W :=
  frobeniusSq_mul_le hG W

/-- Operator bounds compose, which is what the chart construction chains. -/
example {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {A : Matrix ι κ ℝ} {B : Matrix κ ν ℝ} {c d : ℝ}
    (hA : IsOpNormSqBound A c) (hB : IsOpNormSqBound B d) (hc : 0 ≤ c) :
    IsOpNormSqBound (A * B) (c * d) :=
  hA.mul hB hc

/-- `frobeniusSq` is a genuine norm-squared: it vanishes only at `0`. -/
example {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    frobeniusSq A = 0 ↔ A = 0 :=
  frobeniusSq_eq_zero_iff A


/-! ### Reindexing leaves the Frobenius square alone

The chart computes over `Sum` index types while `rrrLoss` is `Fin`-indexed, so
the transport needs relabelling to be metrically invisible. -/

/-- **Relabelling both axes.** -/
example {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (A : Matrix ι κ ℝ) (e : ι' ≃ ι) (f : κ' ≃ κ) :
    frobeniusSq (A.submatrix e f) = frobeniusSq A :=
  frobeniusSq_submatrix_equiv A e f

/-- The bundled `Matrix.reindex` form, which is what the transport applies. -/
example {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (A : Matrix ι κ ℝ) (e : ι ≃ ι') (f : κ ≃ κ') :
    frobeniusSq (Matrix.reindex e f A) = frobeniusSq A :=
  frobeniusSq_reindex A e f

/-- **The `Sum`-to-`Fin` relabelling the elimination chart actually performs.**
`finSumFinEquiv` is the concrete equivalence that turns a block-indexed matrix
into a `Fin`-indexed one, and the Frobenius square does not notice. -/
example {m n k : ℕ} (A : Matrix (Fin (m + n)) (Fin k) ℝ) :
    frobeniusSq (A.submatrix finSumFinEquiv id) = frobeniusSq A :=
  frobeniusSq_submatrix_row A finSumFinEquiv

/-- **Boundary: an empty axis.** Both sides are the empty sum, so the identity
is not vacuous by accident — it is the degenerate case stated on purpose. -/
example (A : Matrix (Fin 0) (Fin 3) ℝ) (f : Fin 3 ≃ Fin 3) :
    frobeniusSq (A.submatrix id f) = frobeniusSq A :=
  frobeniusSq_submatrix_col A f

/-- **A concrete permutation, evaluated.** Swapping the two rows of an explicit
matrix leaves `4 + 9 = 13`, computed rather than rewritten. -/
example :
    frobeniusSq ((Matrix.of ![![(2 : ℝ)], ![3]]).submatrix (Equiv.swap 0 1) id) = 13 := by
  simp [frobeniusSq, Fin.sum_univ_succ, Equiv.swap_apply_def]
  norm_num

end AISafetyAtlas.Examples.SingularLearning
