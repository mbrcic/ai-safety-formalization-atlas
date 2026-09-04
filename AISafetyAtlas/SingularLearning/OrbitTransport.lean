module

public import AISafetyAtlas.SingularLearning.ChartCoords
public import AISafetyAtlas.SingularLearning.DiffeoTransfer
public import AISafetyAtlas.SingularLearning.Loss
public import AISafetyAtlas.SingularLearning.OrbitNormalForm

/-!
# Print's step 1: from an arbitrary factorization to the canonical representative

Lemma 3.2 (`OrbitNormalForm.lean`) carries any pair `(A, B)` to the canonical representative of
its stratum by a triple of invertible matrices, `A ↦ S A Q⁻¹` and `B ↦ P B S⁻¹`. That action
also normalises the truth matrix, for free: it preserves the product, so `B* A* = P C Q⁻¹`, and
on a feasible stratum `B* A*` is the partial identity. One change of variables therefore does
both halves of the reduction.

## Why this is Lemma 6.2 and not Lemma 6.4(i)

The action is linear, so it is an analytic diffeomorphism and Lemma 6.4(i) applies to it. But
that is not enough on its own: the loss does not merely move, it *changes*, because

    ‖B'A' − C‖²_F   becomes   ‖P (B'A' − C) Q⁻¹‖²_F ,

and `P`, `Q⁻¹` are not orthogonal. The two are two-sidedly comparable, with constants that
depend only on `P` and `Q` — Cauchy–Schwarz through `isOpNormSqBound_frobeniusSq` gives the
upper bound in each direction, and the lower bound is the upper bound for the inverse pair. So
the transport is Lemma 6.4(i) at a linear map *followed by* Lemma 6.2, and neither step can be
dropped.

An orthogonal reduction would avoid the comparability step but cannot reach the partial
identity: the singular values survive an isometry. Print does not use one either.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology
open scoped Matrix

/-! ## Conjugation changes the Frobenius square by a bounded factor -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Undoing a two-sided multiplication by invertible matrices. -/
public theorem inv_mul_mul_mul_inv {S : Matrix ι ι ℝ} {Q : Matrix κ κ ℝ}
    (hS : IsUnit S.det) (hQ : IsUnit Q.det) (A : Matrix ι κ ℝ) :
    S⁻¹ * (S * A * Q⁻¹) * Q = A := by
  rw [Matrix.mul_assoc S A, ← Matrix.mul_assoc S⁻¹ S, Matrix.nonsing_inv_mul _ hS,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one]

/-- And the other direction. -/
public theorem mul_mul_inv_mul {S : Matrix ι ι ℝ} {Q : Matrix κ κ ℝ}
    (hS : IsUnit S.det) (hQ : IsUnit Q.det) (A : Matrix ι κ ℝ) :
    S * (S⁻¹ * A * Q) * Q⁻¹ = A := by
  rw [Matrix.mul_assoc S⁻¹ A, ← Matrix.mul_assoc S S⁻¹, Matrix.mul_nonsing_inv _ hS,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]

omit [DecidableEq ι] [DecidableEq κ] in
/-- One side of the sandwich: conjugating cannot inflate the Frobenius square by more than
`‖S‖²_F ‖Q‖²_F`. Both factors go through `isOpNormSqBound_frobeniusSq`, which is Cauchy–Schwarz
row by row, so no operator norm is ever computed. -/
public theorem frobeniusSq_conj_le (S : Matrix ι ι ℝ) (Q : Matrix κ κ ℝ)
    (A : Matrix ι κ ℝ) :
    frobeniusSq (S * A * Q) ≤ (frobeniusSq S * frobeniusSq Qᵀ) * frobeniusSq A := by
  have h1 : frobeniusSq (S * A * Q) ≤ frobeniusSq Qᵀ * frobeniusSq (S * A) :=
    frobeniusSq_mul_le_right (isOpNormSqBound_frobeniusSq Qᵀ) _
  have h2 : frobeniusSq (S * A) ≤ frobeniusSq S * frobeniusSq A :=
    frobeniusSq_mul_le (isOpNormSqBound_frobeniusSq S) _
  have h3 : (0 : ℝ) ≤ frobeniusSq Qᵀ := frobeniusSq_nonneg _
  calc frobeniusSq (S * A * Q) ≤ frobeniusSq Qᵀ * frobeniusSq (S * A) := h1
    _ ≤ frobeniusSq Qᵀ * (frobeniusSq S * frobeniusSq A) := by
        exact mul_le_mul_of_nonneg_left h2 h3
    _ = (frobeniusSq S * frobeniusSq Qᵀ) * frobeniusSq A := by ring

/-- **Conjugation by invertible matrices is a two-sided comparison of Frobenius squares.** The
constants depend on `S` and `Q` and not on the argument, which is what Lemma 6.2 consumes. -/
public theorem exists_frobeniusSq_conj_comparable {S : Matrix ι ι ℝ} {Q : Matrix κ κ ℝ}
    (hS : IsUnit S.det) (hQ : IsUnit Q.det) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ A : Matrix ι κ ℝ,
        c₁ * frobeniusSq A ≤ frobeniusSq (S * A * Q⁻¹) ∧
          frobeniusSq (S * A * Q⁻¹) ≤ c₂ * frobeniusSq A := by
  set K : ℝ := max (frobeniusSq S * frobeniusSq (Q⁻¹)ᵀ) 1 with hK
  set L : ℝ := max (frobeniusSq S⁻¹ * frobeniusSq Qᵀ) 1 with hL
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  have hL1 : (1 : ℝ) ≤ L := le_max_right _ _
  refine ⟨min (1 / L) K, K, lt_min (by positivity) (by linarith), min_le_right _ _, fun A => ?_⟩
  have hupper : frobeniusSq (S * A * Q⁻¹) ≤ K * frobeniusSq A :=
    (frobeniusSq_conj_le S Q⁻¹ A).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (frobeniusSq_nonneg A))
  have hback : frobeniusSq A ≤ L * frobeniusSq (S * A * Q⁻¹) := by
    have h := frobeniusSq_conj_le S⁻¹ Q (S * A * Q⁻¹)
    rw [inv_mul_mul_mul_inv hS hQ] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (frobeniusSq_nonneg (S * A * Q⁻¹)))
  refine ⟨?_, hupper⟩
  have hlow : 1 / L * frobeniusSq A ≤ frobeniusSq (S * A * Q⁻¹) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith [hback]
  exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (frobeniusSq_nonneg A)) hlow

/-! ## The action as a linear change of parameters -/

/-- The orbit action `(A, B) ↦ (S A Q⁻¹, P B S⁻¹)` as a linear automorphism of the parameter
space. -/
@[expose] public noncomputable def orbitParamEquiv {M N H : ℕ}
    {S : Matrix (Fin H) (Fin H) ℝ} {Q : Matrix (Fin N) (Fin N) ℝ} {P : Matrix (Fin M) (Fin M) ℝ}
    (hS : IsUnit S.det) (hQ : IsUnit Q.det) (hP : IsUnit P.det) :
    ParamSpace M N H ≃ₗ[ℝ] ParamSpace M N H where
  toFun w := (S * w.1 * Q⁻¹, P * w.2 * S⁻¹)
  invFun w := (S⁻¹ * w.1 * Q, P⁻¹ * w.2 * S)
  map_add' w w' := Prod.ext (by simp [Matrix.mul_add, Matrix.add_mul])
    (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' c w := Prod.ext (by simp [Matrix.mul_smul, Matrix.smul_mul])
    (by simp [Matrix.mul_smul, Matrix.smul_mul])
  left_inv w := Prod.ext (inv_mul_mul_mul_inv hS hQ w.1) (inv_mul_mul_mul_inv hP hS w.2)
  right_inv w := Prod.ext (mul_mul_inv_mul hS hQ w.1) (mul_mul_inv_mul hP hS w.2)

/-- The same action in Euclidean coordinates, as a continuous linear automorphism. -/
@[expose] public noncomputable def orbitCoordEquiv {M N H : ℕ}
    {S : Matrix (Fin H) (Fin H) ℝ} {Q : Matrix (Fin N) (Fin N) ℝ} {P : Matrix (Fin M) (Fin M) ℝ}
    (hS : IsUnit S.det) (hQ : IsUnit Q.det) (hP : IsUnit P.det) :
    EuclideanSpace ℝ (Fin (H * N + M * H)) ≃L[ℝ] EuclideanSpace ℝ (Fin (H * N + M * H)) :=
  ((paramCoords M N H).symm.trans (orbitParamEquiv hS hQ hP).toContinuousLinearEquiv).trans
    (paramCoords M N H)

public theorem orbitCoordEquiv_apply {M N H : ℕ}
    {S : Matrix (Fin H) (Fin H) ℝ} {Q : Matrix (Fin N) (Fin N) ℝ} {P : Matrix (Fin M) (Fin M) ℝ}
    (hS : IsUnit S.det) (hQ : IsUnit Q.det) (hP : IsUnit P.det)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    orbitCoordEquiv hS hQ hP (matrixPairCoords A B)
      = matrixPairCoords (S * A * Q⁻¹) (P * B * S⁻¹) := by
  show paramCoords M N H ((orbitParamEquiv hS hQ hP)
    ((paramCoords M N H).symm (matrixPairCoords A B))) = _
  rw [show (paramCoords M N H).symm (matrixPairCoords A B) = (A, B) from
    (paramCoords M N H).symm_apply_apply (A, B)]
  rfl

public theorem orbitCoordEquiv_symm_apply {M N H : ℕ}
    {S : Matrix (Fin H) (Fin H) ℝ} {Q : Matrix (Fin N) (Fin N) ℝ} {P : Matrix (Fin M) (Fin M) ℝ}
    (hS : IsUnit S.det) (hQ : IsUnit Q.det) (hP : IsUnit P.det)
    (x : EuclideanSpace ℝ (Fin (H * N + M * H))) :
    (matrixPairEquiv M N H).symm (orbitCoordEquiv hS hQ hP x)
      = (S * ((matrixPairEquiv M N H).symm x).1 * Q⁻¹,
          P * ((matrixPairEquiv M N H).symm x).2 * S⁻¹) := by
  show (matrixPairEquiv M N H).symm (paramCoords M N H ((orbitParamEquiv hS hQ hP)
    ((paramCoords M N H).symm x))) = _
  rw [show (matrixPairEquiv M N H).symm (paramCoords M N H
      ((orbitParamEquiv hS hQ hP) ((paramCoords M N H).symm x)))
      = (orbitParamEquiv hS hQ hP) ((paramCoords M N H).symm x) from
    (matrixPairEquiv M N H).symm_apply_apply _]
  rfl

/-! ## The reduction -/

/-- The loss as a Frobenius square, instance-free: `rrrLoss_eq_sum_sq` with the double sum
named. -/
public theorem rrrLoss_eq_frobeniusSq {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = (1 / 2) * frobeniusSq (B * A - C) :=
  rrrLoss_eq_sum_sq C A B

/-- **Print's step 1.** The local pair of the loss at an arbitrary factorization is the pair at
the canonical representative of its stratum.

The three rank hypotheses are print's feasibility inequalities read at the actual ranks. They are
not assumptions about the problem: `rank C ≤ rank A` and `rank C ≤ rank B` hold for any
factorization, and `rank A + rank B ≤ H + rank C` is Sylvester's inequality. They are hypotheses
here because this module does not prove them; `isO70VolumeOrderTable_o70Pair` discharges all
three, together with the two shape bounds its other half needs. -/
public theorem hasLocalVolumeOrder_rrrLoss_of_canonical {M N H : ℕ}
    {C : Matrix (Fin M) (Fin N) ℝ} {A : Matrix (Fin H) (Fin N) ℝ} {B : Matrix (Fin M) (Fin H) ℝ}
    (hC : B * A = C) (hra : C.rank ≤ A.rank) (hrb : C.rank ≤ B.rank)
    (hab : A.rank + B.rank ≤ H + C.rank) {lam : ℝ} {m : ℕ}
    (hcan : HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix M N C.rank) ((matrixPairEquiv M N H).symm x).1
        ((matrixPairEquiv M N H).symm x).2)
      (matrixPairCoords (canonicalA N H A.rank B.rank C.rank)
        (canonicalB M H B.rank C.rank)) lam m) :
    HasLocalVolumeOrder
      (fun x => rrrLoss C ((matrixPairEquiv M N H).symm x).1 ((matrixPairEquiv M N H).symm x).2)
      (matrixPairCoords A B) lam m := by
  obtain ⟨P, S, Q, hP, hS, hQ, hA, hB⟩ := exists_units_to_canonical A B
  rw [hC] at hA hB
  -- the canonical product is the conjugated truth matrix
  have hcanmul : canonicalB M H B.rank C.rank * canonicalA N H A.rank B.rank C.rank
      = partialIdMatrix M N C.rank :=
    canonicalB_mul_canonicalA hra hrb (by omega)
  have hPCQ : P * C * Q⁻¹ = partialIdMatrix M N C.rank := by
    rw [← hcanmul, ← hA, ← hB, ← hC]
    rw [Matrix.mul_assoc (P * B), Matrix.mul_assoc S A, ← Matrix.mul_assoc S⁻¹ S,
      Matrix.nonsing_inv_mul _ hS, Matrix.one_mul]
    simp [Matrix.mul_assoc]
  -- the change of variables
  set T := orbitCoordEquiv (M := M) (N := N) (H := H) hS hQ hP with hT
  have hTbase : T (matrixPairCoords A B)
      = matrixPairCoords (canonicalA N H A.rank B.rank C.rank) (canonicalB M H B.rank C.rank) := by
    rw [hT, orbitCoordEquiv_apply, hA, hB]
  have htrans := hasLocalVolumeOrder_comp_continuousLinearEquiv T (by rw [hTbase]; exact hcan)
  -- the transported germ is the conjugated loss
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hcomp⟩ := exists_frobeniusSq_conj_comparable hP hQ
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  have hval : ∀ x : EuclideanSpace ℝ (Fin (H * N + M * H)),
      rrrLoss (partialIdMatrix M N C.rank) ((matrixPairEquiv M N H).symm (T x)).1
          ((matrixPairEquiv M N H).symm (T x)).2
        = (1 / 2) * frobeniusSq (P * (((matrixPairEquiv M N H).symm x).2
            * ((matrixPairEquiv M N H).symm x).1 - C) * Q⁻¹) := by
    intro x
    set A' := ((matrixPairEquiv M N H).symm x).1 with hA'
    set B' := ((matrixPairEquiv M N H).symm x).2 with hB'
    rw [show (matrixPairEquiv M N H).symm (T x)
        = (S * A' * Q⁻¹, P * B' * S⁻¹) from orbitCoordEquiv_symm_apply hS hQ hP x]
    dsimp only
    rw [rrrLoss_eq_frobeniusSq]
    congr 2
    rw [← hPCQ]
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [Matrix.mul_assoc (P * B'), Matrix.mul_assoc S A', ← Matrix.mul_assoc S⁻¹ S,
      Matrix.nonsing_inv_mul _ hS, Matrix.one_mul]
    simp [Matrix.mul_assoc]
  refine hasLocalVolumeOrder_of_comparable (c₁ := 1 / c₂) (c₂ := 1 / c₁)
    (div_pos one_pos hc₂) (one_div_le_one_div_of_le hc₁ hc₁₂)
    (Filter.Eventually.of_forall fun x => ?_)
    htrans
  set X := ((matrixPairEquiv M N H).symm x).2 * ((matrixPairEquiv M N H).symm x).1 - C with hX
  have hb := hcomp X
  simp only [Function.comp_apply]
  rw [hval x, ← hX, rrrLoss_eq_frobeniusSq, ← hX]
  refine ⟨?_, ?_⟩
  · rw [show (1 : ℝ) / c₂ * (1 / 2 * frobeniusSq (P * X * Q⁻¹))
      = frobeniusSq (P * X * Q⁻¹) / (2 * c₂) from by ring, div_le_iff₀ (by linarith)]
    nlinarith [hb.2]
  · rw [show (1 : ℝ) / c₁ * (1 / 2 * frobeniusSq (P * X * Q⁻¹))
      = frobeniusSq (P * X * Q⁻¹) / (2 * c₁) from by ring, le_div_iff₀ (by linarith)]
    nlinarith [hb.1]

end AISafetyAtlas.SingularLearning
