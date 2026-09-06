module

public import AISafetyAtlas.Conjectures.MAIS.O70Proof
public import AISafetyAtlas.Conjectures.MAIS.O77
public import AISafetyAtlas.SingularLearning.HessianBlock
public import AISafetyAtlas.SingularLearning.LossExpansion

/-!
# MAIS-O77(a) — conditional verification

This module proves the issue #12 fiber table by the exact reuse the candidate
claims: exchange the input and output dimension names and apply the O70
order-level theorem.  Centering at a factorization is proved to recover the
nonnegative loss, and the generic strict/weak bridge supplies A7's printed
strict band.  The only unproved binder is `EigenvalueLawStatement`.  Neither
`O70ExactLocalPairsExist` nor `O70ZetaPoleBridge` is used.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning

/-- **MAIS-O77(a), order-level verification.**  At every factorization of
every target of rank strictly below the hidden width, the submitted table is
the local two-sided volume order, conditional only on the inherited Wishart
eigenvalue law. -/
public theorem isO77FiberVolumeOrderTable_o77Pair (hEigen : EigenvalueLawStatement) :
    IsO77FiberVolumeOrderTable o77Pair := by
  intro M N H hM hN hH C _hr A B hC
  have hraw := isO70VolumeOrderTable_o70Pair hEigen N M H hN hM hH C A B hC
  have hz : o77LossCoords M N H C (matrixPairCoords A B) = 0 := by
    rw [o77LossCoords, rrrLossCoords, matrixPairCoords,
      LinearEquiv.symm_apply_apply, rrrLoss_eq_sum_sq, hC]
    simp
  have hfun : centeredBandGerm (o77LossCoords M N H C) (matrixPairCoords A B) =
      o77LossCoords M N H C := by
    funext w
    rw [centeredBandGerm, hz, sub_zero, abs_of_nonneg]
    exact rrrLoss_nonneg _ _ _
  have hweak : HasLocalVolumeOrder
      (centeredBandGerm (o77LossCoords M N H C) (matrixPairCoords A B))
      (matrixPairCoords A B)
      (((o77Pair M N H C.rank A.rank B.rank).1 : ℚ) : ℝ)
      (o77Pair M N H C.rank A.rank B.rank).2 := by
    rw [hfun]
    exact hraw
  exact ⟨hweak, hasStrictLocalVolumeOrder_of_hasLocalVolumeOrder hweak⟩

/-- The stronger target-uniform result specializes to the exact distinct-mode
class printed in MAIS-A7.  The frame contributes only `target_rank` here; no
spectral or saddle data are smuggled into the O77(a) proof. -/
public theorem isO77SourceFiberVolumeOrderTable_o77Pair
    (hEigen : EigenvalueLawStatement) :
    IsO77SourceFiberVolumeOrderTable o77Pair := by
  intro M N H r hM hN hrH frame A B hBA
  have hH : 0 < H := by omega
  have h := isO77FiberVolumeOrderTable_o77Pair hEigen M N H hM hN hH
    frame.target (by simpa [frame.target_rank] using hrH) A B hBA
  simpa only [frame.target_rank] using h

/-- Consequently, at the operational two-sided order, the fiber invariant
depends only on `(rank A, rank B)`. -/
public theorem o77FiberDependsOnRanksOnlyAtVolumeOrder
    (hEigen : EigenvalueLawStatement) : O77FiberDependsOnRanksOnlyAtVolumeOrder :=
  ⟨o77Pair, isO77FiberVolumeOrderTable_o77Pair hEigen⟩

/-- **MAIS-O77(a)'s minimal stratum, verified at the germs.**  The candidate's
stratum set is exactly the set on which the two-sided pair actually realized
over the fiber attains its least coefficient.

The only binder is `EigenvalueLawStatement`, the same one the table costs.  The
`←` direction needs a point of the fiber at the attaining stratum, and gets it
from `exists_factorization_of_feasible` together with the table itself; no
existence frontier is assumed, which is where this departs from
`isO70MinimizerCharacterization_o70Minimizers`.

`volumeOrder_unique` is what makes the hypothesis `HasO77FiberPairAt ... lam m`
usable: it is unconditional, so an arbitrary realized pair at a point is forced
to be the table's value there rather than merely bounded by it. -/
public theorem isO77MinimizerCharacterization_o77Minimizers
    (hEigen : EigenvalueLawStatement) :
    IsO77MinimizerCharacterization o77Minimizers := by
  intro M N H r hM hN hrH frame A B hBA lam m hpair
  have hH : 0 < H := Nat.lt_of_le_of_lt (Nat.zero_le r) hrH
  have hadm : AdmissibleRankData N M H r A.rank B.rank := by
    have h := admissible_of_mul_eq hN hM hH A B
    rw [hBA, frame.target_rank] at h
    exact h
  have hlam : lam = (((o77Pair M N H r A.rank B.rank).1 : ℚ) : ℝ) :=
    (volumeOrder_unique hpair.1
      (isO77SourceFiberVolumeOrderTable_o77Pair hEigen M N H r hM hN hrH frame A B hBA).1).1
  obtain ⟨hlb, a, b, habm, hattain⟩ :=
    o77_fiber_minimum_correct M N H r hM hN hH hadm.2.2.2.1
  constructor
  · rintro hmem A' B' hBA' lam' m' hpair'
    have hadm' : AdmissibleRankData N M H r A'.rank B'.rank := by
      have h := admissible_of_mul_eq hN hM hH A' B'
      rw [hBA', frame.target_rank] at h
      exact h
    have hlam' : lam' = (((o77Pair M N H r A'.rank B'.rank).1 : ℚ) : ℝ) :=
      (volumeOrder_unique hpair'.1
        (isO77SourceFiberVolumeOrderTable_o77Pair hEigen M N H r hM hN hrH
          frame A' B' hBA').1).1
    simp only [o77Minimizers, Set.mem_ofPred_eq, O77RankStratum.Admissible] at hmem
    rw [hlam, hlam', hmem.2]
    exact_mod_cast hlb A'.rank B'.rank hadm'
  · intro hmin
    simp only [o77Minimizers, Set.mem_ofPred_eq, O77RankStratum.Admissible]
    refine ⟨hadm, le_antisymm ?_ (hlb A.rank B.rank hadm)⟩
    obtain ⟨A', B', hBA', hA', hB'⟩ :=
      exists_factorization_of_feasible (H := H) frame.target
        (by rw [frame.target_rank]; exact habm.2.2.2.2)
    have hle := hmin A' B' hBA' _ _
      (isO77SourceFiberVolumeOrderTable_o77Pair hEigen M N H r hM hN hrH frame A' B' hBA')
    rw [hlam, hA', hB'] at hle
    rw [← hattain]
    exact_mod_cast hle

/-! ## Criticality of a rung point

O77(b) is not proved in this module; `O77Chart.lean` proves it, as
`o77AllSaddlesHavePairOne_holds`, and consumes this section.  What is proved
here is the one fact the full-space loss expansion needs from the source
predicate: a rung point is a critical point of the loss.

The two equations are the matrix form of "the residual is orthogonal to every
first-order motion of the product".  They are consequences of the annihilation
clauses already inside `IsO77SaddleRungPoint`, not extra hypotheses: at a rung
point the residual is supported on the discarded modes, and those are exactly
the directions `A` and `Bᵀ` kill.
-/

open AISafetyAtlas.SingularLearning Matrix

/-- The rank-one rows of the spectral expansion, at the matrix type. -/
@[expose] public noncomputable def O77SpectralFrame.row {M N r : ℕ}
    (frame : O77SpectralFrame M N r) (i : Fin r) : Matrix (Fin N) (Fin M) ℝ :=
  vecMulVec (frame.singularValue i • frame.leftMode i) (frame.rightMode i)

public theorem O77SpectralFrame.target_eq_sum_row {M N r : ℕ}
    (frame : O77SpectralFrame M N r) : frame.target = ∑ i, frame.row i := by
  rw [frame.target_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext x y
  simp [O77SpectralFrame.row, vecMulVec_apply, mul_assoc]

public theorem O77SpectralFrame.truncation_eq_sum_row {M N r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ) :
    frame.truncation k = ∑ i : Fin r, if (i : ℕ) < k then frame.row i else 0 := by
  rw [O77SpectralFrame.truncation]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext x y
  by_cases hi : (i : ℕ) < k <;>
    simp [hi, O77SpectralFrame.row, vecMulVec_apply, mul_assoc]

/-- `Bᵀ` kills a row built on a left mode it annihilates. -/
public theorem transpose_mul_row {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {B : Matrix (Fin N) (Fin H) ℝ} {i : Fin r} (hu : Bᵀ *ᵥ frame.leftMode i = 0) :
    Bᵀ * frame.row i = 0 := by
  rw [O77SpectralFrame.row, mul_vecMulVec, Matrix.mulVec_smul, hu, smul_zero]
  ext x y
  simp [vecMulVec_apply]

/-- `Aᵀ` kills a row built on a right mode `A` annihilates. -/
public theorem row_mul_transpose {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {A : Matrix (Fin H) (Fin M) ℝ} {i : Fin r} (hv : A *ᵥ frame.rightMode i = 0) :
    frame.row i * Aᵀ = 0 := by
  rw [O77SpectralFrame.row, vecMulVec_mul, Matrix.transpose_transpose, hv]
  ext x y
  simp [vecMulVec_apply]

/-! ### The residual is supported on the discarded modes

The two criticality equations are the case `C = B`, `Z = A` of a single fact:
*anything* that kills every discarded left mode annihilates the residual from
the left, and anything that kills every discarded right mode annihilates it from
the right.  Stating it that way is what lets the same lemma serve the Hessian's
null space below, where the annihilating matrices are a variation `(X, Y)` and
not the point itself.
-/

/-- **Left annihilation of the residual.**  At a rung point the residual is
supported on the discarded left modes, so any `C` killing all of them kills it. -/
public theorem transpose_mul_residual_eq_zero {M N H H' r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (hBA : B * A = frame.truncation k) {C : Matrix (Fin N) (Fin H') ℝ}
    (hC : ∀ i : Fin r, k ≤ (i : ℕ) → Cᵀ *ᵥ frame.leftMode i = 0) :
    Cᵀ * (B * A - frame.target) = 0 := by
  rw [Matrix.mul_sub, sub_eq_zero, hBA, frame.target_eq_sum_row,
    frame.truncation_eq_sum_row k, Matrix.mul_sum, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < k
  · rw [if_pos hi]
  · rw [if_neg hi, Matrix.mul_zero, transpose_mul_row (hC i (not_lt.1 hi))]

/-- **Right annihilation of the residual**, the mirror statement. -/
public theorem residual_mul_transpose_eq_zero {M N H M' r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (hBA : B * A = frame.truncation k) {Z : Matrix (Fin M') (Fin M) ℝ}
    (hZ : ∀ i : Fin r, k ≤ (i : ℕ) → Z *ᵥ frame.rightMode i = 0) :
    (B * A - frame.target) * Zᵀ = 0 := by
  rw [Matrix.sub_mul, sub_eq_zero, hBA, frame.target_eq_sum_row,
    frame.truncation_eq_sum_row k, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < k
  · rw [if_pos hi]
  · rw [if_neg hi, Matrix.zero_mul, row_mul_transpose (hZ i (not_lt.1 hi))]

/-- **Motions of `A` are orthogonal to the residual.**  The truncation and the
target agree on the kept modes and differ on the discarded ones, and `Bᵀ` kills
every discarded left mode, so the two products coincide term by term. -/
public theorem rung_transpose_mul_residual {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) :
    Bᵀ * (B * A - frame.target) = 0 :=
  transpose_mul_residual_eq_zero h.2.1 h.2.2.2

/-- **Motions of `B` are orthogonal to the residual**, by the mirror argument on
the right modes. -/
public theorem rung_residual_mul_transpose {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) :
    (B * A - frame.target) * Aᵀ = 0 :=
  residual_mul_transpose_eq_zero h.2.1 h.2.2.1

/-! ### The Hessian at a rung point, and its null space

The exact expansion leaves `frobeniusSq (BX + YA) + 2⟨R, YX⟩` as the quadratic
part.  Whether MAIS-O77(b) is a Morse–Bott statement or a genuine
Gromoll–Meyer splitting turns on one question about that form: is its null space
exactly the tangent space of the rung set `C_k`?

If it is, the degenerate directions are tangent to a manifold along which the
loss is *constant* — the loss sees `(A, B)` only through `B * A`, and `B * A` is
frozen on `C_k` — so they are free in the sense of print's Lemma 6.4(ii), and no
splitting is needed at all.  Numerical evidence at both special and generic rung
points says the two spaces coincide.  This section proves the inclusion that
holds unconditionally; the reverse inclusion is where the frame's orthonormality
and the distinctness of the singular values have to enter, and it is not proved
here.
-/

/-- The residual at a rung point, as a sum over the discarded modes only. -/
public theorem residual_eq_sum_row {M N H r : ℕ} {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (hBA : B * A = frame.truncation k) :
    B * A - frame.target
      = ∑ i : Fin r, if (i : ℕ) < k then 0 else -frame.row i := by
  rw [hBA, frame.target_eq_sum_row, frame.truncation_eq_sum_row k, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < k
  · rw [if_pos hi, if_pos hi, sub_self]
  · rw [if_neg hi, if_neg hi, zero_sub]

/-- A rank-one row applied to a vector reads off the pairing with its right factor. -/
public theorem row_mulVec {M N r : ℕ} (frame : O77SpectralFrame M N r) (i : Fin r)
    (c : Fin M → ℝ) :
    frame.row i *ᵥ c = (frame.rightMode i ⬝ᵥ c) • (frame.singularValue i • frame.leftMode i) := by
  funext x
  simp only [O77SpectralFrame.row, Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The transpose of a rank-one row, applied to a vector. -/
public theorem transpose_row_mulVec {M N r : ℕ} (frame : O77SpectralFrame M N r) (i : Fin r)
    (c : Fin N → ℝ) :
    (frame.row i)ᵀ *ᵥ c
      = (frame.singularValue i * (frame.leftMode i ⬝ᵥ c)) • frame.rightMode i := by
  funext y
  simp only [O77SpectralFrame.row, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **The residual reads off one discarded mode.**  This is where the frame's
orthonormality enters: every kept mode pairs to zero with a discarded right mode,
and the discarded ones pair to zero with each other. -/
public theorem residual_mulVec_rightMode {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (hBA : B * A = frame.truncation k) (j : Fin r) (hj : k ≤ (j : ℕ)) :
    (B * A - frame.target) *ᵥ frame.rightMode j
      = (-frame.singularValue j) • frame.leftMode j := by
  have hort : ∀ a b : Fin r, frame.rightMode a ⬝ᵥ frame.rightMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.right_orthonormal a b
  rw [residual_eq_sum_row hBA, Matrix.sum_mulVec]
  rw [Finset.sum_eq_single j]
  · rw [if_neg (not_lt.2 hj), Matrix.neg_mulVec, row_mulVec, hort j j,
      if_pos rfl, one_smul]
    funext x; simp
  · intro i _ hij
    by_cases hi : (i : ℕ) < k
    · simp [hi]
    · rw [if_neg hi, Matrix.neg_mulVec, row_mulVec, hort i j, if_neg hij]
      funext x; simp
  · intro hj'; exact absurd (Finset.mem_univ j) hj'

/-- The mirror statement on the left modes. -/
public theorem transpose_residual_mulVec_leftMode {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ}
    (hBA : B * A = frame.truncation k) (j : Fin r) (hj : k ≤ (j : ℕ)) :
    (B * A - frame.target)ᵀ *ᵥ frame.leftMode j
      = (-frame.singularValue j) • frame.rightMode j := by
  have hort : ∀ a b : Fin r, frame.leftMode a ⬝ᵥ frame.leftMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.left_orthonormal a b
  rw [residual_eq_sum_row hBA, Matrix.transpose_sum, Matrix.sum_mulVec]
  rw [Finset.sum_eq_single j]
  · rw [if_neg (not_lt.2 hj), Matrix.transpose_neg, Matrix.neg_mulVec, transpose_row_mulVec,
      hort j j, if_pos rfl, mul_one]
    funext x; simp
  · intro i _ hij
    by_cases hi : (i : ℕ) < k
    · simp [hi]
    · rw [if_neg hi, Matrix.transpose_neg, Matrix.neg_mulVec, transpose_row_mulVec,
        hort i j, if_neg hij, mul_zero]
      funext x; simp
  · intro hj'; exact absurd (Finset.mem_univ j) hj'

/-- **The Hessian quadratic form of the O77 loss at a point**: the second-order
part of `L(A + X, B + Y) - L(A, B)`, read off `frobeniusSq_full_variation_of_critical`.
The cubic `2⟨BX + YA, YX⟩` and quartic `‖YX‖²` are dropped; the term `2⟨R, YX⟩`
is kept because it is second order in the variation, and it is the term through
which the discarded modes enter. -/
@[expose] public noncomputable def o77HessianForm {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) : ℝ :=
  frobeniusSq (B * X + Y * A) + 2 * froIP (B * A - frame.target) (Y * X)

/-- The polar form of `o77HessianForm`.  Its diagonal is the quadratic form
(`o77HessianPolar_self`), which is what makes "null space" mean what it should. -/
@[expose] public noncomputable def o77HessianPolar {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) (X' : Matrix (Fin H) (Fin M) ℝ)
    (Y' : Matrix (Fin N) (Fin H) ℝ) : ℝ :=
  froIP (B * X + Y * A) (B * X' + Y' * A)
    + froIP (B * A - frame.target) (Y * X' + Y' * X)

public theorem o77HessianPolar_self {M N H r : ℕ} (frame : O77SpectralFrame M N r)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    o77HessianPolar frame A B X Y X Y = o77HessianForm frame A B X Y := by
  rw [o77HessianPolar, o77HessianForm, ← froIP_self (B * X + Y * A),
    froIP_add_right (B * A - frame.target) (Y * X) (Y * X)]
  ring

public theorem o77HessianPolar_symm {M N H r : ℕ} (frame : O77SpectralFrame M N r)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X X' : Matrix (Fin H) (Fin M) ℝ) (Y Y' : Matrix (Fin N) (Fin H) ℝ) :
    o77HessianPolar frame A B X Y X' Y' = o77HessianPolar frame A B X' Y' X Y := by
  rw [o77HessianPolar, o77HessianPolar, froIP_comm (B * X + Y * A), add_comm (Y' * X)]

/-- **The tangent space of the rung set `C_k` at a rung point.**  `C_k` is cut out
by `B * A = truncation k` together with the two annihilation clauses, so a
variation is tangent to it when it kills each defining equation to first order. -/
@[expose] public def IsO77RungTangent {M N H r : ℕ} (frame : O77SpectralFrame M N r)
    (k : ℕ) (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) : Prop :=
  B * X + Y * A = 0 ∧
    (∀ i : Fin r, k ≤ (i : ℕ) → X *ᵥ frame.rightMode i = 0) ∧
    (∀ i : Fin r, k ≤ (i : ℕ) → Yᵀ *ᵥ frame.leftMode i = 0)

/-- **Every direction tangent to the rung set is in the null space of the
Hessian.**  This is the Morse–Bott inclusion that holds for free: the first term
of the polar form dies because the product does not move, and the two residual terms die
because the residual is supported on exactly the modes a tangent variation
annihilates.

The converse — that the null space is no larger — is proved below as
`isO77RungTangent_of_null`. It does **not** make `C_k` a nondegenerate critical
manifold: `IsO77RungTangent` is the linearization of the rung conditions, and at
a rung point where the rung set is singular that linearization is strictly
larger than any manifold through the point. A witness is
`Examples.Conjectures.MAIS.loss_quartic_on_degenerateNull`. -/
public theorem o77HessianPolar_eq_zero_of_rungTangent {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (ht : IsO77RungTangent frame k A B X Y)
    (X' : Matrix (Fin H) (Fin M) ℝ) (Y' : Matrix (Fin N) (Fin H) ℝ) :
    o77HessianPolar frame A B X Y X' Y' = 0 := by
  obtain ⟨hP, hX, hY⟩ := ht
  have hYR : Yᵀ * (B * A - frame.target) = 0 := transpose_mul_residual_eq_zero h.2.1 hY
  have hRX : (B * A - frame.target) * Xᵀ = 0 := residual_mul_transpose_eq_zero h.2.1 hX
  rw [o77HessianPolar, hP,
    froIP_add_right (B * A - frame.target) (Y * X') (Y' * X),
    froIP_mul_left (B * A - frame.target) Y X', hYR,
    froIP_mul_right (B * A - frame.target) X Y', hRX]
  simp [froIP]

/-- The quadratic form itself vanishes on the tangent space, by the polar form. -/
public theorem o77HessianForm_eq_zero_of_rungTangent {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (ht : IsO77RungTangent frame k A B X Y) :
    o77HessianForm frame A B X Y = 0 := by
  rw [← o77HessianPolar_self]
  exact o77HessianPolar_eq_zero_of_rungTangent h ht X Y

/-! ### The converse inclusion

The null space is characterised by two matrix equations, one for each half of the
variation.  They are the statement that the derivative of the quadratic form
vanishes in the `X` and the `Y` directions separately, written without the test
matrix by nondegeneracy of the Frobenius pairing.
-/

/-- **The `X`-half of the null-space condition.** -/
public theorem transpose_mul_residual_add_of_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (hnull : ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0) :
    Bᵀ * (B * X + Y * A) + Yᵀ * (B * A - frame.target) = 0 := by
  refine eq_zero_of_forall_froIP_eq_zero _ fun Z => ?_
  have h := hnull Z 0
  rw [o77HessianPolar] at h
  simp only [Matrix.zero_mul, add_zero] at h
  rw [froIP_add_left, ← froIP_mul_left (B * X + Y * A) B Z,
    ← froIP_mul_left (B * A - frame.target) Y Z]
  exact h

/-- **The `Y`-half of the null-space condition.** -/
public theorem mul_transpose_residual_add_of_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (hnull : ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0) :
    (B * X + Y * A) * Aᵀ + (B * A - frame.target) * Xᵀ = 0 := by
  refine eq_zero_of_forall_froIP_eq_zero _ fun Z => ?_
  have h := hnull 0 Z
  rw [o77HessianPolar] at h
  simp only [Matrix.mul_zero, zero_add] at h
  rw [froIP_add_left, froIP_comm ((B * X + Y * A) * Aᵀ) Z,
    froIP_comm ((B * A - frame.target) * Xᵀ) Z,
    ← froIP_mul_right (B * X + Y * A) A Z, ← froIP_mul_right (B * A - frame.target) X Z]
  exact h

/-- **Contracting the `X`-half against a discarded right mode.**  Everything that
is not supported on that mode drops out: `A` annihilates it, and the residual
reads it off as a single left mode. -/
public theorem transpose_mul_mulVec_of_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    (hnull : ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0)
    (j : Fin r) (hj : k ≤ (j : ℕ)) :
    (Bᵀ * B) *ᵥ (X *ᵥ frame.rightMode j)
      = frame.singularValue j • (Yᵀ *ᵥ frame.leftMode j) := by
  have h1 := congrArg (fun Z : Matrix (Fin H) (Fin M) ℝ => Z *ᵥ frame.rightMode j)
    (transpose_mul_residual_add_of_null hnull)
  simp only [Matrix.add_mulVec, Matrix.zero_mulVec] at h1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h.2.2.1 j hj, Matrix.mulVec_zero, add_zero,
    residual_mulVec_rightMode h.2.1 j hj, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at h1
  have := add_eq_zero_iff_eq_neg.1 h1
  rw [this]
  funext z
  simp

/-- **Contracting the `Y`-half against a discarded left mode**, the mirror. -/
public theorem mul_transpose_mulVec_of_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    (hnull : ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0)
    (j : Fin r) (hj : k ≤ (j : ℕ)) :
    (A * Aᵀ) *ᵥ (Yᵀ *ᵥ frame.leftMode j)
      = frame.singularValue j • (X *ᵥ frame.rightMode j) := by
  have h1 := congrArg (fun Z : Matrix (Fin N) (Fin H) ℝ => Zᵀ *ᵥ frame.leftMode j)
    (mul_transpose_residual_add_of_null hnull)
  simp only [Matrix.transpose_add, Matrix.add_mulVec, Matrix.transpose_zero,
    Matrix.zero_mulVec] at h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h.2.2.2 j hj, Matrix.mulVec_zero, zero_add,
    transpose_residual_mulVec_leftMode h.2.1 j hj, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h1
  have := add_eq_zero_iff_eq_neg.1 h1
  rw [Matrix.mulVec_mulVec, this]
  funext z
  simp

/-! ### The spectral step

`(BA)ᵀ(BA)` at a rung point is the truncation's Gram matrix, whose only nonzero
eigenvalues are the *kept* squared singular values.  A discarded one is different
from all of them — that is what the printed strict decrease is for — so nothing
is an eigenvector for it.  The two lemmas below are that computation, and they
are where `singularValue_strict` finally does work.
-/

/-- The truncation applied to a vector, mode by mode. -/
public theorem truncation_mulVec {M N r : ℕ} (frame : O77SpectralFrame M N r) (k : ℕ)
    (w : Fin M → ℝ) :
    frame.truncation k *ᵥ w
      = ∑ i : Fin r, if (i : ℕ) < k then
          (frame.rightMode i ⬝ᵥ w) • (frame.singularValue i • frame.leftMode i) else 0 := by
  rw [frame.truncation_eq_sum_row k, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < k
  · rw [if_pos hi, if_pos hi, row_mulVec]
  · rw [if_neg hi, if_neg hi, Matrix.zero_mulVec]

/-- The transpose of the truncation applied to a vector, mode by mode. -/
public theorem transpose_truncation_mulVec {M N r : ℕ} (frame : O77SpectralFrame M N r)
    (k : ℕ) (z : Fin N → ℝ) :
    (frame.truncation k)ᵀ *ᵥ z
      = ∑ i : Fin r, if (i : ℕ) < k then
          (frame.singularValue i * (frame.leftMode i ⬝ᵥ z)) • frame.rightMode i else 0 := by
  rw [frame.truncation_eq_sum_row k, Matrix.transpose_sum, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < k
  · rw [if_pos hi, if_pos hi, transpose_row_mulVec]
  · rw [if_neg hi, if_neg hi, Matrix.transpose_zero, Matrix.zero_mulVec]

/-- Pairing a kept left mode against the truncation reads off one coefficient. -/
public theorem leftMode_dotProduct_truncation_mulVec {M N r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ) (w : Fin M → ℝ) {l : Fin r} (hl : (l : ℕ) < k) :
    frame.leftMode l ⬝ᵥ (frame.truncation k *ᵥ w)
      = frame.singularValue l * (frame.rightMode l ⬝ᵥ w) := by
  have hort : ∀ a b : Fin r, frame.leftMode a ⬝ᵥ frame.leftMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.left_orthonormal a b
  rw [truncation_mulVec, dotProduct_sum]
  rw [Finset.sum_eq_single l]
  · rw [if_pos hl, dotProduct_smul, dotProduct_smul, hort l l, if_pos rfl]
    simp [mul_comm]
  · intro i _ hil
    by_cases hi : (i : ℕ) < k
    · rw [if_pos hi, dotProduct_smul, dotProduct_smul, hort l i, if_neg (Ne.symm hil)]
      simp
    · rw [if_neg hi, dotProduct_zero]
  · intro hl'; exact absurd (Finset.mem_univ l) hl'

/-- Pairing a kept right mode against the transposed truncation. -/
public theorem rightMode_dotProduct_transpose_truncation_mulVec {M N r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ) (z : Fin N → ℝ) {l : Fin r} (hl : (l : ℕ) < k) :
    frame.rightMode l ⬝ᵥ ((frame.truncation k)ᵀ *ᵥ z)
      = frame.singularValue l * (frame.leftMode l ⬝ᵥ z) := by
  have hort : ∀ a b : Fin r, frame.rightMode a ⬝ᵥ frame.rightMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.right_orthonormal a b
  rw [transpose_truncation_mulVec, dotProduct_sum]
  rw [Finset.sum_eq_single l]
  · rw [if_pos hl, dotProduct_smul, hort l l, if_pos rfl]
    simp
  · intro i _ hil
    by_cases hi : (i : ℕ) < k
    · rw [if_pos hi, dotProduct_smul, hort l i, if_neg (Ne.symm hil)]
      simp
    · rw [if_neg hi, dotProduct_zero]
  · intro hl'; exact absurd (Finset.mem_univ l) hl'

/-- A discarded squared singular value is different from every kept one. -/
public theorem singularValue_sq_ne_of_lt {M N r : ℕ} (frame : O77SpectralFrame M N r)
    {l j : Fin r} (hlj : l < j) :
    frame.singularValue l ^ 2 ≠ frame.singularValue j ^ 2 := by
  have hs := frame.singularValue_strict l j hlj
  have hp := frame.singularValue_pos j
  nlinarith [frame.singularValue_pos l]

/-- **No discarded squared singular value is an eigenvalue of the truncation's
Gram matrix.**  Pairing the eigen-equation with a kept right mode forces that
coefficient to vanish, because the two squared singular values differ; with all
of them gone the left-hand side is zero, and the eigenvalue is not. -/
public theorem eq_zero_of_truncation_gram_eigen {M N r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ) {j : Fin r} (hj : k ≤ (j : ℕ))
    {w : Fin M → ℝ}
    (hw : (frame.truncation k)ᵀ *ᵥ (frame.truncation k *ᵥ w)
        = (frame.singularValue j ^ 2) • w) :
    w = 0 := by
  set z : Fin N → ℝ := frame.truncation k *ᵥ w with hz
  -- every kept coefficient of `w` vanishes
  have hcoef : ∀ l : Fin r, (l : ℕ) < k → frame.leftMode l ⬝ᵥ z = 0 := by
    intro l hl
    have hlj : l < j := by
      have : (l : ℕ) < (j : ℕ) := lt_of_lt_of_le hl hj
      exact this
    have h1 := congrArg (fun v => frame.rightMode l ⬝ᵥ v) hw
    rw [rightMode_dotProduct_transpose_truncation_mulVec frame k z hl, dotProduct_smul,
      smul_eq_mul] at h1
    have h2 : frame.leftMode l ⬝ᵥ z = frame.singularValue l * (frame.rightMode l ⬝ᵥ w) := by
      rw [hz]; exact leftMode_dotProduct_truncation_mulVec frame k w hl
    rw [h2] at h1
    have hne := singularValue_sq_ne_of_lt frame hlj
    have hzero : frame.rightMode l ⬝ᵥ w = 0 := by
      by_contra hc
      apply hne
      field_simp at h1 ⊢
      nlinarith [h1]
    rw [h2, hzero, mul_zero]
  -- so the transposed truncation kills `z`
  have hTz : (frame.truncation k)ᵀ *ᵥ z = 0 := by
    rw [transpose_truncation_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) < k
    · rw [if_pos hi, hcoef i hi, mul_zero, zero_smul]
    · rw [if_neg hi]
  rw [hTz] at hw
  have hs : frame.singularValue j ^ 2 ≠ 0 := by
    have := frame.singularValue_pos j; positivity
  funext x
  have := congrFun hw.symm x
  simpa [hs] using this

/-! ### The null space is no larger than the tangent space -/

/-- **A null direction annihilates every discarded right mode.**  The two
contractions make `X v_j` an eigenvector of `A Aᵀ Bᵀ B` for the discarded
eigenvalue `s_j²`; passing to `(BA)ᵀ(BA)`, which has the same nonzero spectrum,
the spectral step rules that out. -/
public theorem mulVec_rightMode_eq_zero_of_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    (hnull : ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0)
    (j : Fin r) (hj : k ≤ (j : ℕ)) :
    X *ᵥ frame.rightMode j = 0 := by
  have hI := transpose_mul_mulVec_of_null h hnull j hj
  have hII := mul_transpose_mulVec_of_null h hnull j hj
  set x := X *ᵥ frame.rightMode j with hx
  set w : Fin M → ℝ := Aᵀ *ᵥ ((Bᵀ * B) *ᵥ x) with hw
  have hAw : A *ᵥ w = (frame.singularValue j ^ 2) • x := by
    rw [hw, Matrix.mulVec_mulVec, hI, Matrix.mulVec_smul, hII, smul_smul, sq]
  have hgram : (frame.truncation k)ᵀ *ᵥ (frame.truncation k *ᵥ w)
      = (frame.singularValue j ^ 2) • w := by
    rw [← h.2.1, ← Matrix.mulVec_mulVec w B A, hAw, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.transpose_mul, ← Matrix.mulVec_mulVec (B *ᵥ x) Aᵀ Bᵀ,
      Matrix.mulVec_mulVec x Bᵀ B, hw]
  have hw0 : w = 0 := eq_zero_of_truncation_gram_eigen frame k hj hgram
  have hs : frame.singularValue j ^ 2 ≠ 0 := by
    have := frame.singularValue_pos j; positivity
  have : (frame.singularValue j ^ 2) • x = 0 := by rw [← hAw, hw0, Matrix.mulVec_zero]
  funext z
  have := congrFun this z
  simpa [hs] using this

/-- **A null direction annihilates every discarded left mode**, by the first
contraction once the right-mode part is known to vanish. -/
public theorem transpose_mulVec_leftMode_eq_zero_of_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    (hnull : ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0)
    (j : Fin r) (hj : k ≤ (j : ℕ)) :
    Yᵀ *ᵥ frame.leftMode j = 0 := by
  have hI := transpose_mul_mulVec_of_null h hnull j hj
  rw [mulVec_rightMode_eq_zero_of_null h hnull j hj, Matrix.mulVec_zero] at hI
  have hs : frame.singularValue j ≠ 0 := (frame.singularValue_pos j).ne'
  funext z
  have := congrFun hI.symm z
  simpa [hs] using this

/-- **The null space of the Hessian is exactly the tangent space of the rung
set.**  With both mode conditions in hand the residual drops out of the two
matrix equations, leaving `Bᵀ P = 0` and `P Aᵀ = 0`; pairing `P` with itself
through those gives `‖P‖² = 0`, so the product does not move either. -/
public theorem isO77RungTangent_of_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    (hnull : ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0) :
    IsO77RungTangent frame k A B X Y := by
  have hX : ∀ i : Fin r, k ≤ (i : ℕ) → X *ᵥ frame.rightMode i = 0 :=
    fun i hi => mulVec_rightMode_eq_zero_of_null h hnull i hi
  have hY : ∀ i : Fin r, k ≤ (i : ℕ) → Yᵀ *ᵥ frame.leftMode i = 0 :=
    fun i hi => transpose_mulVec_leftMode_eq_zero_of_null h hnull i hi
  have hYR : Yᵀ * (B * A - frame.target) = 0 := transpose_mul_residual_eq_zero h.2.1 hY
  have hRX : (B * A - frame.target) * Xᵀ = 0 := residual_mul_transpose_eq_zero h.2.1 hX
  have h1 : Bᵀ * (B * X + Y * A) = 0 := by
    have := transpose_mul_residual_add_of_null hnull
    rwa [hYR, add_zero] at this
  have h2 : (B * X + Y * A) * Aᵀ = 0 := by
    have := mul_transpose_residual_add_of_null hnull
    rwa [hRX, add_zero] at this
  refine ⟨?_, hX, hY⟩
  refine (frobeniusSq_eq_zero_iff _).1 ?_
  rw [← froIP_self]
  calc froIP (B * X + Y * A) (B * X + Y * A)
      = froIP (B * X + Y * A) (B * X) + froIP (B * X + Y * A) (Y * A) := froIP_add_right _ _ _
    _ = froIP (Bᵀ * (B * X + Y * A)) X + froIP Y ((B * X + Y * A) * Aᵀ) := by
        rw [froIP_mul_left, froIP_mul_right]
    _ = 0 := by rw [h1, h2]; simp [froIP]

/-- **The Hessian's null space is exactly the linearized rung set** at a rung
point.

This is the algebraic half of a Morse–Bott statement and no more. `IsO77RungTangent`
is the linearization of the three conditions cutting out `C_k`; it coincides with
the tangent space of `C_k` only where `C_k` is smooth of that dimension, and it does
not everywhere. At the rank-zero rung of `Examples.Conjectures.MAIS.wideFrame` both
factors vanish, the linearization is the whole annihilator of the discarded mode, and
`loss_quartic_on_degenerateNull` exhibits a direction in it along which the loss grows
like `t ^ 4`. So the loss is not constant on the null space, the rung set is not a
critical manifold there, and no Morse–Bott normal form exists at that point. -/
public theorem isO77RungTangent_iff_null {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ}
    {B : Matrix (Fin N) (Fin H) ℝ} {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) :
    IsO77RungTangent frame k A B X Y
      ↔ ∀ X' Y', o77HessianPolar frame A B X Y X' Y' = 0 :=
  ⟨fun ht X' Y' => o77HessianPolar_eq_zero_of_rungTangent h ht X' Y',
    isO77RungTangent_of_null h⟩

/-! ### The saddle direction

Pair `(1,1)` needs the transverse form to be *indefinite*: a definite
nondegenerate form in `D'` variables has pair `(D'/2, 1)`.  Nondegeneracy
transverse to `C_k` is what the Morse–Bott theorem above gives, so what is left is
that both signs occur.

There is a clean witness whenever some `c ≠ 0` is killed by `B` and by `Aᵀ`: the
variation `X = c v_kᵀ`, `Y = ± s_k u_k cᵀ` leaves the product fixed to first order
and picks up the first *discarded* mode at second order, so the whole Hessian is
the residual term and it is `∓ 2 s_k² ‖c‖²`.  That is the printed saddle
direction — descending it is exactly fitting one more singular mode.

At rung points where `ker B ∩ ker Aᵀ` is trivial, which numerically is the
generic case, this witness gives nothing. That case is settled by
`o77HessianForm_indefinite_of_rung` below, on a wider two-parameter block, and
needs no hypothesis print does not supply.
-/

/-- The saddle variation attached to a vector `c` and the first discarded mode. -/
@[expose] public noncomputable def saddleVariation {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ) (hk : k < r) (c : Fin H → ℝ) (t : ℝ) :
    Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ :=
  (vecMulVec c (frame.rightMode ⟨k, hk⟩),
    vecMulVec ((t * frame.singularValue ⟨k, hk⟩) • frame.leftMode ⟨k, hk⟩) c)

/-- **The Hessian on the saddle variation is the residual term alone.**  Both
first-order motions of the product vanish, by the hypothesis on `c`. -/
public theorem o77HessianForm_saddleVariation {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} (hk : k < r)
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    {c : Fin H → ℝ} (hBc : B *ᵥ c = 0) (hAc : Aᵀ *ᵥ c = 0) (t : ℝ) :
    o77HessianForm frame A B (saddleVariation frame k hk c t).1
        (saddleVariation frame k hk c t).2
      = -2 * t * frame.singularValue ⟨k, hk⟩ ^ 2 * (c ⬝ᵥ c) := by
  have hort : ∀ a b : Fin r, frame.leftMode a ⬝ᵥ frame.leftMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.left_orthonormal a b
  set j : Fin r := ⟨k, hk⟩ with hj
  have hBX : B * vecMulVec c (frame.rightMode j) = 0 := by
    rw [mul_vecMulVec, hBc]
    funext x y; simp [vecMulVec_apply]
  have hYA : vecMulVec ((t * frame.singularValue j) • frame.leftMode j) c * A = 0 := by
    rw [vecMulVec_mul, hAc]
    funext x y; simp [vecMulVec_apply]
  have hYX : vecMulVec ((t * frame.singularValue j) • frame.leftMode j) c
        * vecMulVec c (frame.rightMode j)
      = ((c ⬝ᵥ c) * t) • frame.row j := by
    rw [vecMulVec_mul_vecMulVec]
    funext x y
    simp only [O77SpectralFrame.row, vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hrow : froIP (B * A - frame.target) (frame.row j) = -(frame.singularValue j ^ 2) := by
    rw [O77SpectralFrame.row, froIP_vecMulVec,
      residual_mulVec_rightMode h.2.1 j (le_refl k),
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hort j j, if_pos rfl]
    ring
  rw [o77HessianForm, saddleVariation, hBX, hYA, add_zero, hYX, froIP_smul_right, hrow,
    frobeniusSq_zero]
  ring

/-- **The Hessian is indefinite at a rung point with a common kernel vector.**

Superseded by `o77HessianForm_indefinite_of_rung`, which needs no common kernel
vector and no hypothesis print does not supply. Kept because it is the one
statement that exhibits both signs on a *single* variation, moved along in
opposite directions, which the wider two-parameter block does not do.
Both signs are achieved on the same saddle variation, by moving along it and
against it: descending it fits one more singular mode, ascending it fits the
mode with the wrong sign.

This is the transverse indefiniteness that pair `(1,1)` needs — a definite
nondegenerate form in `D'` variables would give pair `(D'/2, 1)` instead. The
hypothesis on `c` is what makes both first-order motions of the product vanish;
it holds at the canonical rung points, and at rung points where
`ker B ∩ ker Aᵀ` is trivial the conclusion is still expected but needs a
different argument. -/
public theorem o77HessianForm_indefinite {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ} (hk : k < r)
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    {c : Fin H → ℝ} (hc : c ≠ 0) (hBc : B *ᵥ c = 0) (hAc : Aᵀ *ᵥ c = 0) :
    (∃ X Y, o77HessianForm frame A B X Y < 0)
      ∧ (∃ X Y, 0 < o77HessianForm frame A B X Y) := by
  have hnn : 0 ≤ c ⬝ᵥ c := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hcc : 0 < c ⬝ᵥ c :=
    lt_of_le_of_ne hnn (fun hz => hc (dotProduct_self_eq_zero.1 hz.symm))
  have hs : 0 < frame.singularValue ⟨k, hk⟩ := frame.singularValue_pos _
  constructor
  · refine ⟨(saddleVariation frame k hk c 1).1, (saddleVariation frame k hk c 1).2, ?_⟩
    rw [o77HessianForm_saddleVariation hk h hBc hAc 1]
    nlinarith [pow_pos hs 2, hcc]
  · refine ⟨(saddleVariation frame k hk c (-1)).1, (saddleVariation frame k hk c (-1)).2, ?_⟩
    rw [o77HessianForm_saddleVariation hk h hBc hAc (-1)]
    nlinarith [pow_pos hs 2, hcc]

/-- **The exact loss expansion at every rung point, over the whole parameter
space.**  This is `frobeniusSq_full_variation_of_critical` with the criticality
hypotheses discharged from the source predicate, so it holds at every point of
every nonterminal rung and for every variation of both factors — not only along
the rank-one slice that `frobeniusSq_rung_variation` expands.

It is a step towards §7.4 and is not §7.4: the splitting still has to exhibit
coordinates in which the quadratic part separates from a germ on the degenerate
complement.  Those coordinates are not produced here; they are produced in
`O77Chart.lean`, by `exists_o77_chart` and `exists_o77_block_matrix`, on top of
`SingularLearning.exists_gromoll_meyer_splitting`.
At some rung points no such coordinates exist at all — see
`isO77RungTangent_iff_null` for which ones and why. -/
public theorem frobeniusSq_rung_full_variation {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    frobeniusSq ((B + Y) * (A + X) - frame.target)
      = frobeniusSq (B * A - frame.target)
        + (2 * froIP (B * A - frame.target) (Y * X)
            + frobeniusSq (B * X + Y * A + Y * X)) :=
  frobeniusSq_full_variation_of_critical A B frame.target
    (rung_transpose_mul_residual h) (rung_residual_mul_transpose h) X Y



/-- **The truncation factors through the mode index**, so its rank is at most `r`.
The bound `k` would also hold, and is not needed: the rung condition supplies
`r < H`, which is what the kernel argument below consumes. Factoring through
`Fin r` rather than `Fin k` keeps both sums over the same index. -/
public theorem rank_truncation_le {M N r : ℕ} (frame : O77SpectralFrame M N r) (k : ℕ) :
    (frame.truncation k).rank ≤ r := by
  classical
  set P : Matrix (Fin N) (Fin r) ℝ := Matrix.of fun n i =>
    if (i : ℕ) < k then frame.singularValue i * frame.leftMode i n else 0 with hP
  set Q : Matrix (Fin r) (Fin M) ℝ := Matrix.of fun i m => frame.rightMode i m with hQ
  have hfac : frame.truncation k = P * Q := by
    ext n m
    simp only [O77SpectralFrame.truncation, Matrix.sum_apply, Matrix.mul_apply, hP, hQ,
      Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < k <;> simp [hi]
  rw [hfac]
  exact le_trans (Matrix.rank_mul_le_left P Q) (P.rank_le_width)

/-! ### Indefiniteness at every rung, unconditionally

The theorem above needs a vector killed by both `B` and `Aᵀ`, which is not
available at a general rung point. The candidate's own argument does not need
one, and this section transcribes it.

It works on the wider two-parameter block `Ẋ = x v_αᵀ`, `Ẏ = u_α yᵀ`, where the
earlier `saddleVariation` tied the two factors to one vector. On that block the
Hessian is `xᵀ(BᵀB)x + yᵀ(AAᵀ)y − 2 s_α ⟨x, y⟩`: both diagonal terms are Gram
forms, hence positive semidefinite, and the coupling carries the sign. The block
is positive at `(z, −z)` for every nonzero `z`. It is negative at `(z, t z)` for
small `t > 0` whenever `B z = 0`, and at `(t z, z)` whenever `Aᵀ z = 0` — and one
of those kernels is nonzero at every rung, because otherwise `rank (B * A)` would
be `H`, against `rank (B * A) = k < r < H`.
-/

/-- The two-parameter variation block attached to a discarded mode: `x` enters
through the right mode and `y` through the left, independently. -/
@[expose] public noncomputable def o77BlockVariation {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) (x y : Fin H → ℝ) :
    Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ :=
  (vecMulVec x (frame.rightMode α), vecMulVec (frame.leftMode α) y)

/-- **The Hessian on the two-parameter block is the candidate's `K_α` form.**
The cross term of the first-order product motion dies because the discarded left
mode annihilates `Bᵀ`, so the two diagonal Gram forms survive alone, and the
residual contributes exactly the coupling `−2 s_α ⟨x, y⟩`. -/
public theorem o77HessianForm_blockVariation {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (α : Fin r) (hα : k ≤ (α : ℕ))
    (x y : Fin H → ℝ) :
    o77HessianForm frame A B (o77BlockVariation frame α x y).1
        (o77BlockVariation frame α x y).2
      = x ⬝ᵥ ((Bᵀ * B) *ᵥ x) + y ⬝ᵥ ((A * Aᵀ) *ᵥ y)
        - 2 * frame.singularValue α * (x ⬝ᵥ y) := by
  have hlort : ∀ a b : Fin r, frame.leftMode a ⬝ᵥ frame.leftMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.left_orthonormal a b
  have hrort : ∀ a b : Fin r, frame.rightMode a ⬝ᵥ frame.rightMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.right_orthonormal a b
  have hBx : (B *ᵥ x) ⬝ᵥ frame.leftMode α = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h.2.2.2 α hα,
      zero_dotProduct]
  have hgramB : x ⬝ᵥ ((Bᵀ * B) *ᵥ x) = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hgramA : y ⬝ᵥ ((A * Aᵀ) *ᵥ y) = (Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [o77HessianForm, o77BlockVariation]
  rw [SingularLearning.mul_vecMulVec, vecMulVec_mul, vecMulVec_mul_vecMulVec,
    frobeniusSq_add, frobeniusSq_vecMulVec, frobeniusSq_vecMulVec,
    froIP_vecMulVec_vecMulVec, froIP_vecMulVec,
    residual_mulVec_rightMode h.2.1 α hα, hBx, hrort α α, hlort α α, if_pos rfl,
    hgramB, hgramA]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hlort α α, if_true,
    dotProduct_comm y x]
  ring

/-- **The Hessian is indefinite at every point of every nonterminal rung**, with
no hypothesis beyond the ones print supplies.

This is MAIS issue #12's own argument, transcribed. `o77HessianForm_indefinite`
above needs a vector killed by both `B` and `Aᵀ`, and at a general rung point
there is none; the argument here needs only a vector killed by **one** of them,
and produces it from the rank of the truncation.

The three ingredients are all print's: the diagonal blocks `Bᵀ B` and `A Aᵀ` are
Gram matrices and so positive semidefinite, the discarded singular value is
positive, and `rank (B * A) < H` because `B * A` is the rank-`k` truncation and
`k < r < H`. Sylvester's inequality then forbids both `B` and `Aᵀ` from being
injective, and on the kernel of whichever fails the coupling term dominates. -/
public theorem o77HessianForm_indefinite_of_rung {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (hrH : r < H)
    (α : Fin r) (hα : k ≤ (α : ℕ)) :
    (∃ X Y, o77HessianForm frame A B X Y < 0) ∧
      (∃ X Y, 0 < o77HessianForm frame A B X Y) := by
  have hself : ∀ {n : ℕ} (w : Fin n → ℝ), 0 ≤ w ⬝ᵥ w := by
    intro n w; rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hgramB : ∀ w : Fin H → ℝ, w ⬝ᵥ ((Bᵀ * B) *ᵥ w) = (B *ᵥ w) ⬝ᵥ (B *ᵥ w) := by
    intro w; rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hgramA : ∀ w : Fin H → ℝ, w ⬝ᵥ ((A * Aᵀ) *ᵥ w) = (Aᵀ *ᵥ w) ⬝ᵥ (Aᵀ *ᵥ w) := by
    intro w; rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hP : ∀ w : Fin H → ℝ, 0 ≤ w ⬝ᵥ ((Bᵀ * B) *ᵥ w) := fun w => (hgramB w) ▸ hself _
  have hR : ∀ w : Fin H → ℝ, 0 ≤ w ⬝ᵥ ((A * Aᵀ) *ᵥ w) := fun w => (hgramA w) ▸ hself _
  have hrank : (B * A).rank < H :=
    h.2.1 ▸ lt_of_le_of_lt (rank_truncation_le frame k) hrH
  obtain ⟨z, hz, hker⟩ := exists_mem_ker_gram A B hrank
  obtain ⟨⟨x, y, hneg⟩, ⟨x', y', hpos⟩⟩ :=
    hessianBlock_quadForm_indefinite (frame.singularValue_pos α) hP hR hz hker
  refine ⟨⟨(o77BlockVariation frame α x y).1, (o77BlockVariation frame α x y).2, ?_⟩,
    ⟨(o77BlockVariation frame α x' y').1, (o77BlockVariation frame α x' y').2, ?_⟩⟩
  · rw [o77HessianForm_blockVariation h α hα]; exact hneg
  · rw [o77HessianForm_blockVariation h α hα]; exact hpos

/-- **`H ≥ 2` and `2H ≥ 4` at every nonterminal rung.**

Print's own line, immediately after the indefiniteness argument: "Because
`k < r < H`, one has `H ≥ 2` and `2H ≥ 4`." Both are arithmetic from the two
facts already in hand — `k < r` is a clause of `IsO77SaddleRungPoint`, and
`r < H` is the nonterminality hypothesis `o77HessianForm_indefinite_of_rung`
already carries.

The bound is not decoration. The band lemma print invokes next asks for a
nondegenerate indefinite form in `n ≥ 3` variables, and the variation block
supplies `2H ≥ 4`. -/
public theorem o77_variation_block_dim_ge {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (hrH : r < H) :
    2 ≤ H ∧ 4 ≤ 2 * H := by
  have hk : k < r := h.1
  omega

/-- **The variation block really has dimension `2H`.**

Print introduces `Ȧ = x vα⊤`, `Ḃ = uα y⊤` as "the `2H`-dimensional variation
block". That phrase is a claim: the parametrisation by `(x, y) ∈ ℝ^H × ℝ^H` is
injective, so the block is a `2H`-dimensional subspace of the parameter space
rather than a `2H`-parameter family of lower rank. It holds because `vα` and
`uα` are unit vectors, hence nonzero.

Without this, `o77HessianForm_blockVariation` would compute the Hessian on a
possibly smaller block, and "nondegenerate indefinite in `2H` variables" would
not follow from the nonsingularity of `Kα`. -/
public theorem o77BlockVariation_injective {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    Function.Injective
      (fun p : (Fin H → ℝ) × (Fin H → ℝ) => o77BlockVariation frame α p.1 p.2) := by
  have hne : ∀ {n : ℕ} (v : Fin n → ℝ), v ⬝ᵥ v = 1 → ∃ j, v j ≠ 0 := by
    intro n v hv
    by_contra hall
    push Not at hall
    rw [dotProduct] at hv
    simp only [hall, mul_zero, Finset.sum_const_zero] at hv
    exact zero_ne_one hv
  have hr : frame.rightMode α ⬝ᵥ frame.rightMode α = 1 := by
    simpa [dotProduct] using frame.right_orthonormal α α
  have hl : frame.leftMode α ⬝ᵥ frame.leftMode α = 1 := by
    simpa [dotProduct] using frame.left_orthonormal α α
  obtain ⟨jr, hjr⟩ := hne _ hr
  obtain ⟨jl, hjl⟩ := hne _ hl
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  simp only [o77BlockVariation, Prod.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  have hx : x = x' := by
    funext i
    have hij := congrArg (fun P : Matrix (Fin H) (Fin M) ℝ => P i jr) h1
    simp only [vecMulVec_apply] at hij
    exact mul_right_cancel₀ hjr hij
  have hy : y = y' := by
    funext i
    have hij := congrArg (fun P : Matrix (Fin N) (Fin H) ℝ => P jl i) h2
    simp only [vecMulVec_apply] at hij
    exact mul_left_cancel₀ hjl hij
  simp [hx, hy]

/-- **The loss on the printed `2H` block, exactly.**

Print introduces the variation block `Ȧ = x vα⊤`, `Ḃ = uα y⊤` and asserts "the
Hessian of `L` restricted to this block is `Kα`". This theorem checks that
assertion against the loss itself rather than against `o77HessianForm`, and it
does so with no truncation: on the block the loss variation is the `Kα` form
**plus a single quartic term** `(x·y)²`, and nothing else. Every cubic
contribution cancels.

The three cancellations are all forced by the rung conditions. Writing
`u = uα`, `v = vα`, the products are `B Ȧ = (Bx) v⊤`, `Ḃ A = u (A⊤y)⊤` and
`Ḃ Ȧ = (y·x) u v⊤`, so the cross term `⟨B Ȧ + Ḃ A, Ḃ Ȧ⟩` splits into a multiple
of `(Bx)·u = x⊤B⊤u`, which vanishes because `B⊤uα = 0`, and a multiple of
`(A⊤y)·v = y·(Avα)`, which vanishes because `Avα = 0`. The surviving quartic is
`‖Ḃ Ȧ‖² = (x·y)²‖u‖²‖v‖² = (x·y)²`, the modes being unit vectors.

This is the sharpest statement the block admits, and it is what makes the
splitting step legitimate here: the restricted loss is a nondegenerate
indefinite quadratic form perturbed by a quartic, not a form whose higher-order
remainder is merely asserted to be negligible. -/
public theorem frobeniusSq_rung_blockVariation {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (α : Fin r) (hα : k ≤ (α : ℕ))
    (x y : Fin H → ℝ) :
    frobeniusSq ((B + (o77BlockVariation frame α x y).2)
          * (A + (o77BlockVariation frame α x y).1) - frame.target)
        - frobeniusSq (B * A - frame.target)
      = (x ⬝ᵥ ((Bᵀ * B) *ᵥ x) + y ⬝ᵥ ((A * Aᵀ) *ᵥ y)
          - 2 * frame.singularValue α * (x ⬝ᵥ y)) + (x ⬝ᵥ y) ^ 2 := by
  have hlort : frame.leftMode α ⬝ᵥ frame.leftMode α = 1 := by
    simpa [dotProduct] using frame.left_orthonormal α α
  have hrort : frame.rightMode α ⬝ᵥ frame.rightMode α = 1 := by
    simpa [dotProduct] using frame.right_orthonormal α α
  have hBx : (B *ᵥ x) ⬝ᵥ frame.leftMode α = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h.2.2.2 α hα,
      zero_dotProduct]
  have hAy : (Aᵀ *ᵥ y) ⬝ᵥ frame.rightMode α = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h.2.2.1 α hα,
      zero_dotProduct]
  have hXY : (o77BlockVariation frame α x y).2 * (o77BlockVariation frame α x y).1
      = vecMulVec ((y ⬝ᵥ x) • frame.leftMode α) (frame.rightMode α) := by
    simp only [o77BlockVariation]
    exact vecMulVec_mul_vecMulVec _ _ _ _
  have hBX : B * (o77BlockVariation frame α x y).1
      = vecMulVec (B *ᵥ x) (frame.rightMode α) := by
    simp only [o77BlockVariation]
    exact SingularLearning.mul_vecMulVec _ _ _
  have hYA : (o77BlockVariation frame α x y).2 * A
      = vecMulVec (frame.leftMode α) (Aᵀ *ᵥ y) := by
    simp only [o77BlockVariation]
    exact vecMulVec_mul _ _ _
  have hcross : froIP (B * (o77BlockVariation frame α x y).1
        + (o77BlockVariation frame α x y).2 * A)
      ((o77BlockVariation frame α x y).2 * (o77BlockVariation frame α x y).1) = 0 := by
    rw [froIP_add_left, hXY, hBX, hYA, froIP_vecMulVec_vecMulVec, froIP_vecMulVec_vecMulVec,
      dotProduct_smul, dotProduct_smul, hBx, hAy]
    ring
  have hquart : frobeniusSq ((o77BlockVariation frame α x y).2
      * (o77BlockVariation frame α x y).1) = (x ⬝ᵥ y) ^ 2 := by
    rw [hXY, frobeniusSq_vecMulVec, hrort, smul_dotProduct, dotProduct_smul, hlort,
      dotProduct_comm y x]
    ring
  have hsq : frobeniusSq (B * (o77BlockVariation frame α x y).1
        + (o77BlockVariation frame α x y).2 * A
        + (o77BlockVariation frame α x y).2 * (o77BlockVariation frame α x y).1)
      = frobeniusSq (B * (o77BlockVariation frame α x y).1
          + (o77BlockVariation frame α x y).2 * A) + (x ⬝ᵥ y) ^ 2 := by
    rw [frobeniusSq_add, hcross, hquart]
    ring
  have hfull := frobeniusSq_rung_full_variation h
    (o77BlockVariation frame α x y).1 (o77BlockVariation frame α x y).2
  have hH := o77HessianForm_blockVariation h α hα x y
  rw [o77HessianForm] at hH
  rw [hfull, hsq]
  linarith [hH]

/-! ## The loss as a smooth function, for the splitting step

Everything above is matrix algebra: exact identities in the entries, with no
derivative taken. The splitting print invokes next is a statement about a smooth
function and its Hessian, so it needs the loss presented that way. These two
lemmas are the whole bridge, and both are inherited: the O70 layer already
proved the reduced-rank loss real-analytic at every point of the coordinate
space, and O77's loss is that function with the two ambient dimensions
exchanged. -/

/-- **The O77 loss is real-analytic in Euclidean coordinates**, at every point.
`o77LossCoords M N H C` is `rrrLossCoords N M H C` by definition, so this is
`analyticAt_rrrLoss_symm_coords` read with the source's dimension names. -/
public theorem analyticAt_o77LossCoords {M N H : ℕ} (C : Matrix (Fin N) (Fin M) ℝ)
    (x : EuclideanSpace ℝ (Fin (H * M + N * H))) :
    AnalyticAt ℝ (o77LossCoords M N H C) x :=
  SingularLearning.analyticAt_rrrLoss_symm_coords (M := N) (N := M) (H := H) C x

open scoped ContDiff

/-- **The O77 loss is `C^∞`.** The splitting lemma is stated for `ContDiff ℝ ∞`
functions on a normed space; this discharges that hypothesis once and for all,
at every point of the parameter space and not only at rung points. -/
public theorem contDiff_o77LossCoords {M N H : ℕ} (C : Matrix (Fin N) (Fin M) ℝ) :
    ContDiff ℝ ∞ (o77LossCoords M N H C) :=
  contDiff_iff_contDiffAt.2 fun x => (analyticAt_o77LossCoords C x).contDiffAt

/-! ## The variation block as a subspace

Print calls `Adot = x v_α^T`, `Bdot = u_α y^T` "the `2H`-dimensional
variation block" and then treats it as the space the splitting's quadratic form
lives on. To be that, it has to be a subspace of the parameter space of
dimension `2H`. `o77BlockVariation_injective` is half of it; packaging the
parametrisation as a linear map supplies the rest. -/

/-- Print's variation block, as a linear map from `ℝ^H × ℝ^H` into the parameter
space. The map is linear because `vecMulVec` is linear in each argument
separately and each factor of the block varies only one of them. -/
@[expose] public noncomputable def o77BlockMap {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    ((Fin H → ℝ) × (Fin H → ℝ)) →ₗ[ℝ]
      (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) where
  toFun p := o77BlockVariation frame α p.1 p.2
  map_add' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩
    simp only [o77BlockVariation, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · ext i j; simp [Matrix.vecMulVec_apply, add_mul]
    · ext i j; simp [Matrix.vecMulVec_apply, mul_add]
  map_smul' := by
    rintro c ⟨x, y⟩
    simp only [o77BlockVariation, Prod.smul_mk, RingHom.id_apply, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · ext i j; simp [Matrix.vecMulVec_apply, mul_assoc]
    · ext i j; simp [Matrix.vecMulVec_apply]; ring

@[simp] public theorem o77BlockMap_apply {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) (x y : Fin H → ℝ) :
    o77BlockMap frame α (x, y) = o77BlockVariation frame α x y := rfl

public theorem o77BlockMap_injective {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    Function.Injective (o77BlockMap (H := H) frame α) :=
  o77BlockVariation_injective frame α

/-- **The block has dimension exactly `2H`**, print's own count.

This is what licenses reading `Q_α` as "nondegenerate indefinite in `2H`
variables": the form `K_α` computed by `o77HessianForm_blockVariation` lives
on `ℝ^H × ℝ^H`, and that space embeds in the parameter space without collapse,
so the subspace it spans carries the form faithfully. -/
public theorem finrank_range_o77BlockMap {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    Module.finrank ℝ (LinearMap.range (o77BlockMap (H := H) frame α)) = 2 * H := by
  rw [LinearMap.finrank_range_of_inj (o77BlockMap_injective frame α)]
  simp [Module.finrank_prod]
  ring

/-! ## Print's spectral condition, discharged

`SingularLearning.det_hessianBlock_ne_zero` proves `K_α` nonsingular *given*
`det (P R - s_α^2 I) ≠ 0`, and until now nothing in this tree supplied that
hypothesis anywhere except at the trivial rank-zero rung, where both diagonal
blocks vanish. Print supplies it in one sentence:

> The nonzero eigenvalues of `QP` are those of `A^T B^T B A = (BA)^T (BA)`,
> namely `s_1^2, ..., s_k^2`. Since the target singular values are distinct and
> `α > k`, `s_α^2` is neither zero nor one of these eigenvalues.

The transcription below takes that route and needs no spectral theorem. What is
used is only that `s_α^2` is not an eigenvalue of `(BA)^T (BA)`, and at a
rung point `BA` is the ordered truncation, whose Gram operator acts on the kept
right modes by `s_i^2` and annihilates everything orthogonal to them. Pairing
the eigenvector equation with one kept right mode gives
`(s_j^2 - s_α^2)(v_j . y) = 0` with `s_j > s_α > 0`, so every such
coordinate vanishes, so the truncation kills `y` outright, so `y` is zero. -/

/-- The truncation applied to a right mode: a kept mode comes back scaled by its
singular value, a discarded one is annihilated. -/
public theorem truncation_mulVec_rightMode {M N r : ℕ} (frame : O77SpectralFrame M N r)
    (k : ℕ) (j : Fin r) :
    frame.truncation k *ᵥ frame.rightMode j
      = if (j : ℕ) < k then frame.singularValue j • frame.leftMode j else 0 := by
  have hort : ∀ a b : Fin r, frame.rightMode a ⬝ᵥ frame.rightMode b = if a = b then 1 else 0 := by
    intro a b; simpa [dotProduct] using frame.right_orthonormal a b
  rw [frame.truncation_eq_sum_row k, Matrix.sum_mulVec, Finset.sum_eq_single j]
  · by_cases hj : (j : ℕ) < k
    · rw [if_pos hj, if_pos hj, row_mulVec, hort j j, if_pos rfl, one_smul]
    · rw [if_neg hj, if_neg hj, Matrix.zero_mulVec]
  · intro i _ hij
    by_cases hi : (i : ℕ) < k
    · rw [if_pos hi, row_mulVec, hort i j, if_neg hij, zero_smul]
    · rw [if_neg hi, Matrix.zero_mulVec]
  · intro hj'; exact absurd (Finset.mem_univ j) hj'

/-- **The Gram operator of the truncation has no eigenvector at a discarded
singular value.**  This is print's eigenvalue sentence, stated as the kernel
condition it is used for, and proved from orthonormality and the strict decrease
of the singular values alone. -/
public theorem truncation_gram_no_eigenvector {M N r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ) (α : Fin r) (hα : k ≤ (α : ℕ))
    {y : Fin M → ℝ}
    (hy : ((frame.truncation k)ᵀ * frame.truncation k) *ᵥ y
        = (frame.singularValue α ^ 2) • y) :
    y = 0 := by
  have hpair : ∀ j : Fin r, frame.rightMode j ⬝ᵥ
      (((frame.truncation k)ᵀ * frame.truncation k) *ᵥ y)
      = (frame.truncation k *ᵥ frame.rightMode j) ⬝ᵥ (frame.truncation k *ᵥ y) := by
    intro j
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hzero : ∀ j : Fin r, (j : ℕ) < k → frame.rightMode j ⬝ᵥ y = 0 := by
    intro j hj
    have hjα : j < α := Fin.lt_def.mpr (lt_of_lt_of_le hj hα)
    have hs : frame.singularValue α < frame.singularValue j :=
      frame.singularValue_strict j α hjα
    have hposα := frame.singularValue_pos α
    have h1 := hpair j
    rw [hy, truncation_mulVec_rightMode, if_pos hj, dotProduct_smul, smul_eq_mul,
      smul_dotProduct, smul_eq_mul,
      leftMode_dotProduct_truncation_mulVec frame k y hj] at h1
    have hfac : (frame.singularValue j * frame.singularValue j
        - frame.singularValue α ^ 2) * (frame.rightMode j ⬝ᵥ y) = 0 := by nlinarith [h1]
    have hne : frame.singularValue j * frame.singularValue j
        - frame.singularValue α ^ 2 ≠ 0 := by nlinarith
    exact (mul_eq_zero.mp hfac).resolve_left hne
  have hTy : frame.truncation k *ᵥ y = 0 := by
    rw [truncation_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) < k
    · rw [if_pos hi, hzero i hi, zero_smul]
    · rw [if_neg hi]
  have hsq : (frame.singularValue α ^ 2) • y = 0 := by
    rw [← hy, ← Matrix.mulVec_mulVec, hTy, Matrix.mulVec_zero]
  have hpos : (0 : ℝ) < frame.singularValue α ^ 2 := by
    have := frame.singularValue_pos α; positivity
  exact (smul_eq_zero.mp hsq).resolve_left (ne_of_gt hpos)

/-- **The saddle block is nonsingular at every point of every nonterminal rung.**

This is print's `det K_α ≠ 0` with the spectral hypothesis of
`det_hessianBlock_ne_zero` discharged rather than assumed. The reduction from
`P R` to the truncation's Gram operator is print's own
`A^T B^T B A = (BA)^T (BA)`, read as the standard fact that `U V` and `V U`
share their nonzero spectrum, here with `U = B^T B A` and `V = A^T`. -/
public theorem o77_saddle_spectral_det_ne_zero {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (α : Fin r) (hα : k ≤ (α : ℕ)) :
    ((Bᵀ * B) * (A * Aᵀ)
      - (frame.singularValue α ^ 2) • (1 : Matrix (Fin H) (Fin H) ℝ)).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨x, hx, hxeq⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hPR : ((Bᵀ * B) * (A * Aᵀ)) *ᵥ x = (frame.singularValue α ^ 2) • x := by
    have h0 := hxeq
    rw [Matrix.sub_mulVec, sub_eq_zero, smul_one_mulVec] at h0
    exact h0
  set y : Fin M → ℝ := Aᵀ *ᵥ x with hydef
  have hUy : ((Bᵀ * B) * A) *ᵥ y = (frame.singularValue α ^ 2) • x := by
    rw [hydef, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    exact hPR
  have hgram : (frame.truncation k)ᵀ * frame.truncation k = Aᵀ * ((Bᵀ * B) * A) := by
    rw [← h.2.1, Matrix.transpose_mul]
    simp [Matrix.mul_assoc]
  have hVU : ((frame.truncation k)ᵀ * frame.truncation k) *ᵥ y
      = (frame.singularValue α ^ 2) • y := by
    rw [hgram, ← Matrix.mulVec_mulVec, hUy, Matrix.mulVec_smul, ← hydef]
  have hy0 : y = 0 := truncation_gram_no_eigenvector frame k α hα hVU
  have hx0 : (frame.singularValue α ^ 2) • x = 0 := by
    rw [← hUy, hy0, Matrix.mulVec_zero]
  have hpos : (0 : ℝ) < frame.singularValue α ^ 2 := by
    have := frame.singularValue_pos α; positivity
  exact hx ((smul_eq_zero.mp hx0).resolve_left (ne_of_gt hpos))

/-- **`K_α` is nonsingular at every point of every nonterminal rung.**

Print's equation (8) names the block

    K_α = [[B^T B, -s_α I], [-s_α I, A A^T]]

and concludes it is nonsingular from the block determinant identity together
with the eigenvalue count. Both halves are now in place: the identity is
`SingularLearning.det_hessianBlock_ne_zero` and the count is
`o77_saddle_spectral_det_ne_zero`, so this corollary carries no hypothesis print
does not state. -/
public theorem det_o77SaddleBlock_ne_zero {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (α : Fin r) (hα : k ≤ (α : ℕ)) :
    (Matrix.fromBlocks (Bᵀ * B)
        ((-frame.singularValue α) • (1 : Matrix (Fin H) (Fin H) ℝ))
        ((-frame.singularValue α) • 1) (A * Aᵀ)).det ≠ 0 :=
  det_hessianBlock_ne_zero (ne_of_gt (frame.singularValue_pos α)) _ _
    (o77_saddle_spectral_det_ne_zero h α hα)

/-- **The Hessian on the block is the quadratic form of `K_α`.**

`o77HessianForm_blockVariation` computes the loss's Hessian on print's variation
block as `x^T (B^T B) x + y^T (A A^T) y - 2 s_α (x . y)`, and
`SingularLearning.hessianBlock_quadForm` computes the quadratic form of the
matrix (8) as the same expression. Identifying them is what lets a nonsingularity
statement about the matrix be used as a nondegeneracy statement about the form,
which is the only thing the splitting step consumes. -/
public theorem o77HessianForm_blockVariation_eq_matrixForm {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (α : Fin r) (hα : k ≤ (α : ℕ))
    (x y : Fin H → ℝ) :
    o77HessianForm frame A B (o77BlockVariation frame α x y).1
        (o77BlockVariation frame α x y).2
      = Sum.elim x y ⬝ᵥ (Matrix.fromBlocks (Bᵀ * B)
          ((-frame.singularValue α) • (1 : Matrix (Fin H) (Fin H) ℝ))
          ((-frame.singularValue α) • 1) (A * Aᵀ) *ᵥ Sum.elim x y) := by
  rw [o77HessianForm_blockVariation h α hα, hessianBlock_quadForm]

/-- **`K_α` is symmetric.**  Both diagonal blocks are Gram matrices and the
coupling block is a scalar multiple of the identity, so print's display (8) is a
symmetric matrix and its quadratic form determines it. -/
public theorem isSymm_o77SaddleBlock {M H : ℕ} {N : ℕ} (s : ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ) :
    (Matrix.fromBlocks (Bᵀ * B) ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ))
      ((-s) • 1) (A * Aᵀ)).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.fromBlocks_transpose]
  congr 1
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [Matrix.transpose_smul, Matrix.transpose_one]
  · rw [Matrix.transpose_smul, Matrix.transpose_one]
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **`K_α`'s quadratic form takes both signs**, at every point of every
nonterminal rung.

This is `o77HessianForm_indefinite_of_rung` read on the matrix rather than on
the loss: the same two witnesses, moved across
`SingularLearning.hessianBlock_quadForm`. Stating it here is what a
diagonalisation argument needs, since Sylvester's law consumes indefiniteness of
the form and not of any particular variation of the loss.

There is no `k ≤ alpha` hypothesis, and its absence is not an oversight. That
condition is what makes this matrix the Hessian on print's block
(`o77HessianForm_blockVariation`); indefiniteness of the matrix itself needs only
that both diagonal blocks are positive semidefinite Gram matrices, that
`s_α > 0`, and that `rank (BA) < H`. So the statement is strictly wider than
print's, which is the safe direction. -/
public theorem o77SaddleBlock_quadForm_indefinite {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (hrH : r < H) (α : Fin r) :
    (∃ z : Fin H ⊕ Fin H → ℝ, z ⬝ᵥ (Matrix.fromBlocks (Bᵀ * B)
        ((-frame.singularValue α) • (1 : Matrix (Fin H) (Fin H) ℝ))
        ((-frame.singularValue α) • 1) (A * Aᵀ) *ᵥ z) < 0) ∧
      (∃ z : Fin H ⊕ Fin H → ℝ, 0 < z ⬝ᵥ (Matrix.fromBlocks (Bᵀ * B)
        ((-frame.singularValue α) • (1 : Matrix (Fin H) (Fin H) ℝ))
        ((-frame.singularValue α) • 1) (A * Aᵀ) *ᵥ z)) := by
  have hself : ∀ {n : ℕ} (w : Fin n → ℝ), 0 ≤ w ⬝ᵥ w := by
    intro n w; rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hgramB : ∀ w : Fin H → ℝ, w ⬝ᵥ ((Bᵀ * B) *ᵥ w) = (B *ᵥ w) ⬝ᵥ (B *ᵥ w) := by
    intro w; rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hgramA : ∀ w : Fin H → ℝ, w ⬝ᵥ ((A * Aᵀ) *ᵥ w) = (Aᵀ *ᵥ w) ⬝ᵥ (Aᵀ *ᵥ w) := by
    intro w; rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hP : ∀ w : Fin H → ℝ, 0 ≤ w ⬝ᵥ ((Bᵀ * B) *ᵥ w) := fun w => (hgramB w) ▸ hself _
  have hR : ∀ w : Fin H → ℝ, 0 ≤ w ⬝ᵥ ((A * Aᵀ) *ᵥ w) := fun w => (hgramA w) ▸ hself _
  have hrank : (B * A).rank < H :=
    h.2.1 ▸ lt_of_le_of_lt (rank_truncation_le frame k) hrH
  obtain ⟨z, hz, hker⟩ := exists_mem_ker_gram A B hrank
  obtain ⟨⟨x, y, hneg⟩, ⟨x', y', hpos⟩⟩ :=
    hessianBlock_quadForm_indefinite (frame.singularValue_pos α) hP hR hz hker
  exact ⟨⟨Sum.elim x y, by rw [hessianBlock_quadForm]; exact hneg⟩,
    ⟨Sum.elim x' y', by rw [hessianBlock_quadForm]; exact hpos⟩⟩

/-- **The variation block sits isometrically in the parameter space.**

`o77BlockMap` is not merely injective: read in Euclidean coordinates it
preserves the norm, because `v_α` and `u_α` are unit vectors and the two
factors of the block land in the two different factors of the parameter space.

This is what lets the splitting be run with `W` an honest Euclidean space of
dimension `2H` rather than an abstract subspace with a distorted metric. A
volume order is a statement about balls, so a parametrisation that changed the
metric would change the constants and, on a non-linear chart, could change the
pair itself. -/
public theorem norm_sq_blockVariation_coords {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) (x y : Fin H → ℝ) :
    ‖matrixPairEquiv N M H (o77BlockVariation frame α x y)‖ ^ 2
      = (x ⬝ᵥ x) + (y ⬝ᵥ y) := by
  have hlort : frame.leftMode α ⬝ᵥ frame.leftMode α = 1 := by
    simpa [dotProduct] using frame.left_orthonormal α α
  have hrort : frame.rightMode α ⬝ᵥ frame.rightMode α = 1 := by
    simpa [dotProduct] using frame.right_orthonormal α α
  rw [show o77BlockVariation frame α x y
      = ((o77BlockVariation frame α x y).1, (o77BlockVariation frame α x y).2) from rfl,
    norm_sq_matrixPairEquiv]
  simp only [o77BlockVariation]
  rw [frobeniusSq_vecMulVec, frobeniusSq_vecMulVec, hrort, hlort]
  ring

/-- Print's variation block as a subspace of the **Euclidean** parameter space,
which is where the volume interface lives. -/
@[expose] public noncomputable def o77BlockSubspace {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (H * M + N * H))) :=
  LinearMap.range ((matrixPairEquiv N M H).toLinearMap.comp (o77BlockMap frame α))

public theorem o77BlockSubspace_injective {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    Function.Injective
      ((matrixPairEquiv N M H).toLinearMap.comp (o77BlockMap (H := H) frame α)) :=
  (matrixPairEquiv N M H).injective.comp (o77BlockMap_injective frame α)

/-- **The block is a `2H`-dimensional subspace of the parameter space.**  This is
`finrank_range_o77BlockMap` moved across the coordinate packing, which is a
linear equivalence and so changes no dimension. Stated separately because the
splitting is set up on the Euclidean side, and a dimension count that holds only
before the packing would be no use there. -/
public theorem finrank_o77BlockSubspace {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    Module.finrank ℝ (o77BlockSubspace (H := H) frame α) = 2 * H := by
  rw [o77BlockSubspace, LinearMap.finrank_range_of_inj (o77BlockSubspace_injective frame α)]
  simp [Module.finrank_prod]
  ring

/-- **`2H` fits inside the parameter space.**  Needed for the index arithmetic
of the splitting, which writes the parameter dimension as `2H + d` with `d` the
complement's dimension. It is not free arithmetic — for a frame with no modes
`M` or `N` could be zero — and the reason it holds is that the block is an
actual subspace, so its dimension is bounded by the ambient one. -/
public theorem two_mul_H_le_paramDim {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (α : Fin r) :
    2 * H ≤ H * M + N * H := by
  have hle := Submodule.finrank_le (o77BlockSubspace (H := H) frame α)
  rw [finrank_o77BlockSubspace] at hle
  simpa using hle

/-! ## The rung predicate is print's critical set, not a narrowing of it

Print fixes `w = (A, B) ∈ C_k` and then says "the defining criticality
conditions give `A v_α = 0`, `B^T u_α = 0`". The atlas's
`IsO77SaddleRungPoint` lists those two annihilation clauses among its
conjuncts rather than deriving them, and until now only the **forward**
direction was proved: `rung_transpose_mul_residual` and
`rung_residual_mul_transpose` show the clauses imply the two normal equations.

That left a scope question open in the direction that matters. If the clauses
were strictly stronger than criticality-plus-membership, then every theorem
quantified over `IsO77SaddleRungPoint` would range over a **subset** of print's
`C_k`, and an all-saddle claim proved of it would not be print's claim. The
converse below closes that: at a point where `B A` is the ordered truncation,
the two normal equations force the annihilation clauses, because the residual
reads off each discarded mode with a nonzero coefficient.
-/

/-- **Criticality gives the annihilation clauses.**  The converse of
`rung_transpose_mul_residual` and `rung_residual_mul_transpose`, and the reason
`IsO77SaddleRungPoint` is print's membership condition rather than a
strengthening of it. -/
public theorem isO77SaddleRungPoint_of_critical {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) {k : ℕ} (hk : k < r)
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (hBA : B * A = frame.truncation k)
    (h₁ : Bᵀ * (B * A - frame.target) = 0)
    (h₂ : (B * A - frame.target) * Aᵀ = 0) :
    IsO77SaddleRungPoint frame k A B := by
  refine ⟨hk, hBA, ?_, ?_⟩
  · intro i hi
    have hs : frame.singularValue i ≠ 0 := ne_of_gt (frame.singularValue_pos i)
    have hAt : A * (B * A - frame.target)ᵀ = 0 := by
      have := congrArg Matrix.transpose h₂
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this
    have h0 : A *ᵥ ((B * A - frame.target)ᵀ *ᵥ frame.leftMode i) = 0 := by
      rw [Matrix.mulVec_mulVec, hAt, Matrix.zero_mulVec]
    rw [transpose_residual_mulVec_leftMode hBA i hi, Matrix.mulVec_smul] at h0
    exact (smul_eq_zero.mp h0).resolve_left (neg_ne_zero.mpr hs)
  · intro i hi
    have hs : frame.singularValue i ≠ 0 := ne_of_gt (frame.singularValue_pos i)
    have h0 : Bᵀ *ᵥ ((B * A - frame.target) *ᵥ frame.rightMode i) = 0 := by
      rw [Matrix.mulVec_mulVec, h₁, Matrix.zero_mulVec]
    rw [residual_mulVec_rightMode hBA i hi, Matrix.mulVec_smul] at h0
    exact (smul_eq_zero.mp h0).resolve_left (neg_ne_zero.mpr hs)

/-- **The rung predicate is exactly print's `C_k` membership.**  Both directions
of the correspondence, so a theorem quantified over `IsO77SaddleRungPoint`
quantifies over print's critical set and no smaller class. -/
public theorem isO77SaddleRungPoint_iff_critical {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ} :
    IsO77SaddleRungPoint frame k A B ↔
      (k < r ∧ B * A = frame.truncation k ∧
        Bᵀ * (B * A - frame.target) = 0 ∧ (B * A - frame.target) * Aᵀ = 0) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, rung_transpose_mul_residual h, rung_residual_mul_transpose h⟩
  · rintro ⟨hk, hBA, h₁, h₂⟩
    exact isO77SaddleRungPoint_of_critical frame hk hBA h₁ h₂

/-- **Print's loss on print's block, with print's own factor of one half.**

MAIS-A7 states the loss as `L(A,B) = (1/2)‖BA − Φ‖²_F`, and the atlas keeps that
normalisation: `rrrLoss` carries the `1/2` (`rrrLoss_eq_frobeniusSq`). Every
identity above is stated for `frobeniusSq`, which is `2 L`, so this restates the
block variation for the loss print actually writes.

The normalisation is not cosmetic here, and getting it wrong would not have been
caught by any check. Taylor's theorem writes a second-order variation as
`(1/2) v^T Hess v`. The variation of `frobeniusSq` on the block has quadratic
part `o77HessianForm`, so the Hessian of `frobeniusSq` is `2 o77HessianForm` and
the Hessian of `L` is `o77HessianForm` itself — whose matrix on the block is
`Kα`, by `o77HessianForm_blockVariation_eq_matrixForm`. That is exactly print's
sentence "the Hessian of `L` restricted to this block is `Kα`". Had the `1/2`
been dropped, the same chain would have produced `2 Kα`, which is symmetric,
nonsingular and indefinite just as `Kα` is, so nothing downstream would have
failed and the error would have been silent. -/
public theorem rrrLoss_rung_blockVariation {M N H r : ℕ}
    {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (α : Fin r) (hα : k ≤ (α : ℕ))
    (x y : Fin H → ℝ) :
    rrrLoss frame.target (A + (o77BlockVariation frame α x y).1)
        (B + (o77BlockVariation frame α x y).2)
      - rrrLoss frame.target A B
      = (1 / 2) * ((x ⬝ᵥ ((Bᵀ * B) *ᵥ x) + y ⬝ᵥ ((A * Aᵀ) *ᵥ y)
          - 2 * frame.singularValue α * (x ⬝ᵥ y)) + (x ⬝ᵥ y) ^ 2) := by
  rw [rrrLoss_eq_frobeniusSq, rrrLoss_eq_frobeniusSq, ← mul_sub,
    frobeniusSq_rung_blockVariation h α hα x y]

end AISafetyAtlas.Conjectures.MAIS
