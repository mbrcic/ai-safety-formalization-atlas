module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.SingularLearning.ReducedRank

/-!
# The saddle Hessian block

MAIS-O77(b) computes the two-sided local pair at a nonterminal critical point by
splitting the loss along a discarded singular mode.  The quadratic part of that
splitting is the `2H`-dimensional block

    `K = [[BᵀB, -s I], [-s I, A Aᵀ]]`,

and the argument needs it to be nonsingular.  That is the step this module
settles, and only that step: no Morse lemma, no volume statement, no claim about
`O77AllSaddlesHavePairOne`.

**Why this is not a direct Schur complement.**  At a rung point both diagonal
blocks are singular — `A` and `B` have rank `k < H` there — so neither of
Mathlib's two Schur-complement determinant lemmas applies as written.  What *is*
invertible is the off-diagonal block `-s I`, for `s ≠ 0`.  Exchanging the two
block rows moves it into the corner the Schur complement wants, at the cost of a
sign that is a unit and therefore invisible to the nonsingularity question.

The identity obtained is

    `det [[-s I, R], [P, -s I]] = (-1)^H det (P R - s² I)`,

which is the printed `det K = (-1)^H det (s² I - P R)` up to the sign
`det (s² I - X) = (-1)^H det (X - s² I)`.  Only the vanishing matters below, so
the sign is carried rather than fought.
-/

namespace AISafetyAtlas.SingularLearning

open Matrix

/-- **The block determinant with the invertible corner first.**  For `s ≠ 0` the
off-diagonal block is invertible, which is what makes the Schur complement
available even when both diagonal blocks are singular. -/
public theorem det_fromBlocks_offDiagonal {H : ℕ} {s : ℝ} (hs : s ≠ 0)
    (P R : Matrix (Fin H) (Fin H) ℝ) :
    (fromBlocks ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) R P ((-s) • 1)).det
      = (-1 : ℝ) ^ H * (P * R - (s ^ 2) • (1 : Matrix (Fin H) (Fin H) ℝ)).det := by
  have hns : (-s) ≠ 0 := neg_ne_zero.mpr hs
  have hinvertible : Invertible ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) := by
    refine Matrix.invertibleOfIsUnitDet _ ?_
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact IsUnit.pow _ (isUnit_iff_ne_zero.mpr hns)
  rw [Matrix.det_fromBlocks₁₁]
  have hinv : (⅟((-s) • (1 : Matrix (Fin H) (Fin H) ℝ))) = (-s)⁻¹ • 1 := by
    apply invOf_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hns, one_smul]
  rw [hinv]
  have hstep : ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) - P * ((-s)⁻¹ • 1) * R
      = s⁻¹ • (P * R - (s ^ 2) • 1) := by
    have h1 : P * ((-s)⁻¹ • (1 : Matrix (Fin H) (Fin H) ℝ)) * R = (-s)⁻¹ • (P * R) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have h2 : (-s)⁻¹ = -s⁻¹ := by field_simp
    have h3 : s⁻¹ * s ^ 2 = s := by field_simp
    rw [h1, smul_sub, smul_smul, h2, h3, neg_smul, neg_smul]
    abel
  rw [hstep, Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [← mul_assoc, ← mul_pow]
  congr 2
  field_simp

/-- Exchanging the two block rows is a `submatrix` by `Equiv.sumComm`. -/
public theorem fromBlocks_submatrix_sumComm {H : ℕ}
    (P R X : Matrix (Fin H) (Fin H) ℝ) :
    (fromBlocks P X X R).submatrix (Equiv.sumComm (Fin H) (Fin H)) (Equiv.refl _)
      = fromBlocks X R P X := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.submatrix]

/-- **The saddle Hessian block is nonsingular when the printed spectral condition
holds.**  This is MAIS-O77(b)'s §7.3 obligation, and nothing more: it says the
`2H`-dimensional block is nondegenerate, not that any volume order follows.

The sign lost in the block-row exchange is a unit, so it cannot affect whether
the determinant vanishes — which is why the exchange is free here and would not
be if the sign itself were being claimed. -/
public theorem det_hessianBlock_ne_zero {H : ℕ} {s : ℝ} (hs : s ≠ 0)
    (P R : Matrix (Fin H) (Fin H) ℝ)
    (hspec : (P * R - (s ^ 2) • (1 : Matrix (Fin H) (Fin H) ℝ)).det ≠ 0) :
    (fromBlocks P ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) ((-s) • 1) R).det ≠ 0 := by
  set σ : Equiv.Perm (Fin H ⊕ Fin H) := Equiv.sumComm (Fin H) (Fin H) with hσ
  have hswap := fromBlocks_submatrix_sumComm P R ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ))
  have hperm := Matrix.det_permute σ (fromBlocks P ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ))
    ((-s) • 1) R)
  rw [hσ] at hperm
  rw [show (Equiv.refl (Fin H ⊕ Fin H) : Fin H ⊕ Fin H → Fin H ⊕ Fin H) = id from rfl] at hswap
  rw [hswap] at hperm
  have hne : (fromBlocks ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) R P ((-s) • 1)).det ≠ 0 := by
    rw [det_fromBlocks_offDiagonal hs]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hspec
  intro hzero
  rw [hzero, mul_zero] at hperm
  exact hne hperm

/-! ## The quadratic form

Nonsingularity is a statement about the matrix; the Morse splitting consumes the
*form*.  This is the bridge between them, and it is where the shape
`xᵀ P x + yᵀ R y - 2 s ⟨x, y⟩` — the sum of the two block energies minus the
coupling through the discarded mode — becomes visible.
-/

/-- Multiplying by a scalar multiple of the identity is scaling. -/
public theorem smul_one_mulVec {H : ℕ} (c : ℝ) (y : Fin H → ℝ) :
    (c • (1 : Matrix (Fin H) (Fin H) ℝ)) *ᵥ y = c • y := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- **The quadratic form of the saddle Hessian block.**  On a variation split as
`(x, y)` along the discarded mode, the block contributes the two diagonal
energies and a coupling term `-2 s ⟨x, y⟩`.

The coupling is the whole reason the form is indefinite: at a rung point the two
diagonal blocks are positive semidefinite, so any negative direction has to come
from the cross term, and that term is present exactly when `s ≠ 0` — that is,
exactly when the mode being discarded is one the target actually carries. -/
public theorem hessianBlock_quadForm {H : ℕ} (s : ℝ) (P R : Matrix (Fin H) (Fin H) ℝ)
    (x y : Fin H → ℝ) :
    Sum.elim x y ⬝ᵥ (fromBlocks P ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) ((-s) • 1) R
        *ᵥ Sum.elim x y)
      = x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (R *ᵥ y) - 2 * s * (x ⬝ᵥ y) := by
  rw [Matrix.fromBlocks_mulVec]
  have hl : (Sum.elim x y) ∘ Sum.inl = x := rfl
  have hr : (Sum.elim x y) ∘ Sum.inr = y := rfl
  rw [hl, hr, sumElim_dotProduct_sumElim, smul_one_mulVec, smul_one_mulVec,
    dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_comm y x]
  simp only [smul_eq_mul]
  ring

/-- **The form is genuinely indefinite at a rank-zero rung.**  With both diagonal
blocks zero the form is `-2 s ⟨x, y⟩`, which takes both signs as soon as
`s ≠ 0`: positive at `(x, -x)` and negative at `(x, x)`, for any `x ≠ 0`.

This is the concrete content of "the discarded mode supplies a negative
direction", and it is what a definite form would not do. -/
public theorem hessianBlock_indefinite_at_zero {H : ℕ} {s : ℝ} (hs : 0 < s)
    (x : Fin H → ℝ) (hx : x ⬝ᵥ x ≠ 0) :
    Sum.elim x x ⬝ᵥ (fromBlocks (0 : Matrix (Fin H) (Fin H) ℝ)
        ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) ((-s) • 1) 0 *ᵥ Sum.elim x x) < 0
      ∧ 0 < Sum.elim x (-x) ⬝ᵥ (fromBlocks (0 : Matrix (Fin H) (Fin H) ℝ)
        ((-s) • (1 : Matrix (Fin H) (Fin H) ℝ)) ((-s) • 1) 0 *ᵥ Sum.elim x (-x)) := by
  have hnn : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne hnn (Ne.symm hx)
  constructor
  · rw [hessianBlock_quadForm]
    simp only [Matrix.zero_mulVec, dotProduct_zero]
    nlinarith [hpos, hs]
  · rw [hessianBlock_quadForm]
    simp only [Matrix.zero_mulVec, dotProduct_zero, dotProduct_neg]
    nlinarith [hpos, hs]

/-! ## The germ as a block form with varying coupling

The exact loss expansion produces

    `G = ½[xᵀPx + yᵀRy - 2s⟨x,y⟩] + ½⟨x,y⟩²`,

and the quartic can be absorbed: `G` is the *same* block quadratic form with the
coupling `s` replaced by `s - ½⟨x,y⟩`.  At the origin the coupling is `s`, so the
Hessian is the block already studied above, and away from it the coupling varies
polynomially.

This is the shape a Morse argument consumes — `G(z) = ½ zᵀ H(z) z` with `H`
analytic and `H(0)` the nondegenerate Hessian — obtained here without any
Hadamard-type lemma, because the loss expansion terminated.
-/

/-- **The loss germ is the block form with a varying coupling.**  The quartic term
of the exact expansion is absorbed by replacing `s` with `s - ½⟨x,y⟩`.

Nothing is approximated: this is an identity, and the coupling's value at the
origin is exactly the `s` of the printed Hessian. -/
public theorem lossGerm_eq_quadForm {H : ℕ} (P R : Matrix (Fin H) (Fin H) ℝ) (s : ℝ)
    (x y : Fin H → ℝ) :
    x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (R *ᵥ y) - 2 * s * (x ⬝ᵥ y) + (x ⬝ᵥ y) ^ 2
      = Sum.elim x y ⬝ᵥ (fromBlocks P ((-(s - (x ⬝ᵥ y) / 2)) • (1 : Matrix (Fin H) (Fin H) ℝ))
          ((-(s - (x ⬝ᵥ y) / 2)) • 1) R *ᵥ Sum.elim x y) := by
  rw [hessianBlock_quadForm]
  ring

/-- The varying coupling agrees with the printed one at the origin, which is what
makes the Hessian at the rung point the block studied above. -/
public theorem lossGerm_coupling_at_zero {H : ℕ} (s : ℝ) (x y : Fin H → ℝ)
    (hxy : x ⬝ᵥ y = 0) :
    s - (x ⬝ᵥ y) / 2 = s := by
  rw [hxy]; ring

/-! ## Reducing the coordinate change to a matrix equation

The Morse step asks for analytic `A(z)` with `A(0) = I` and `A(z)ᵀ K A(z) = H(z)`,
where `K = H(0)` is the nondegenerate Hessian.  Writing `A = I + K⁻¹X` with `X`
symmetric turns that into a single matrix equation whose linear part is
invertible, which is what puts it inside the reach of an inverse function
theorem rather than needing a bespoke construction.

The two lemmas here are the algebra of that reduction.  They are unconditional
and carry no analysis; the analytic solvability of the resulting equation is the
part still to be done.
-/

/-- **The congruence expands with a quadratic remainder.**  For symmetric `X` and
a symmetric inverse `Kinv`, conjugating by `I + Kinv X` adds `2X` plus a term
quadratic in `X`. -/
public theorem congruence_expand {n : Type*} [Fintype n] [DecidableEq n]
    (K Kinv X : Matrix n n ℝ) (hKK : K * Kinv = 1) (hKK' : Kinv * K = 1)
    (hKinv : Kinvᵀ = Kinv) (hX : Xᵀ = X) :
    (1 + Kinv * X)ᵀ * K * (1 + Kinv * X) = K + (2 : ℝ) • X + X * Kinv * X := by
  have hAt : (1 + Kinv * X)ᵀ = 1 + X * Kinv := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hKinv, hX]
  rw [hAt]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc X Kinv K, hKK', Matrix.mul_one]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_one]
  rw [← Matrix.mul_assoc K Kinv X, hKK, Matrix.one_mul, Matrix.mul_assoc X Kinv X]
  rw [two_smul]
  abel

/-- **The reduction.**  Solving `2X + X Kinv X = H - K` produces the congruence
the Morse step wants.  The linear part of the left-hand side is `2X`, invertible,
so the equation is exactly the shape an inverse function theorem handles — that
is the remaining analytic obligation, and it is not discharged here. -/
public theorem congruence_of_solution {n : Type*} [Fintype n] [DecidableEq n]
    (K Kinv X Hz : Matrix n n ℝ) (hKK : K * Kinv = 1) (hKK' : Kinv * K = 1)
    (hKinv : Kinvᵀ = Kinv) (hX : Xᵀ = X)
    (hsol : (2 : ℝ) • X + X * Kinv * X = Hz - K) :
    (1 + Kinv * X)ᵀ * K * (1 + Kinv * X) = Hz := by
  rw [congruence_expand K Kinv X hKK hKK' hKinv hX, add_assoc, hsol]
  abel


/-! ## Indefiniteness at a general rung, and where the kernel vector comes from

`hessianBlock_indefinite_at_zero` settles the rank-zero rung, where both diagonal
blocks vanish outright.  At a general rung the diagonal blocks are the Gram
matrices `BᵀB` and `AAᵀ`, which are positive semidefinite but not zero.  The two
results below close that gap in the only way the argument needs: a *shared*
kernel direction is not required, one block having a kernel vector is enough, and
at a nonterminal rung one of them always does.

The two statements are deliberately independent of the `fromBlocks` packaging on
the one side and of the coupling `s` on the other, so that a caller already
holding the form in the shape `xᵀPx + yᵀRy - 2s⟨x,y⟩` — which is what
`hessianBlock_quadForm` produces — can consume the first directly.
-/

/-- Scaling a vector scales the quadratic form quadratically. -/
private theorem quadForm_smul {H : ℕ} (M : Matrix (Fin H) (Fin H) ℝ) (t : ℝ)
    (z : Fin H → ℝ) :
    (t • z) ⬝ᵥ (M *ᵥ (t • z)) = t ^ 2 * (z ⬝ᵥ (M *ᵥ z)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The block form is indefinite whenever one diagonal block has a kernel
vector.**  Both blocks are assumed positive semidefinite — which is what the Gram
matrices `BᵀB` and `AAᵀ` are — and `z` is a nonzero vector killed by one of them.

This generalizes `hessianBlock_indefinite_at_zero`, which is the case
`P = R = 0`, where every `z ≠ 0` is a kernel vector of both.

The positive direction needs neither kernel hypothesis: `(z, -z)` turns the
coupling into `+2 s ⟨z, z⟩`, and the two semidefinite terms cannot cancel it.
The negative direction is where the kernel enters.  With `P *ᵥ z = 0` the choice
`(z, t • z)` has value `t² (zᵀRz) - 2 s t ⟨z, z⟩`, and taking
`t = s ⟨z, z⟩ / (zᵀRz + 1)` makes the bracket negative; the `+ 1` in the
denominator is what lets the same `t` serve when `zᵀRz = 0`, so no case split on
the second block is needed.

Note what is *not* claimed: nothing here says the block is nonsingular.
Indefiniteness and nondegeneracy are separate, and the latter is
`det_hessianBlock_ne_zero`. -/
public theorem hessianBlock_quadForm_indefinite {H : ℕ} {s : ℝ} (hs : 0 < s)
    {P R : Matrix (Fin H) (Fin H) ℝ}
    (hP : ∀ x : Fin H → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x))
    (hR : ∀ y : Fin H → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y))
    {z : Fin H → ℝ} (hz : z ≠ 0) (hker : P *ᵥ z = 0 ∨ R *ᵥ z = 0) :
    (∃ x y : Fin H → ℝ, x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (R *ᵥ y) - 2 * s * (x ⬝ᵥ y) < 0) ∧
      (∃ x y : Fin H → ℝ, 0 < x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (R *ᵥ y) - 2 * s * (x ⬝ᵥ y)) := by
  have hn : 0 < z ⬝ᵥ z := by
    refine lt_of_le_of_ne ?_ (fun h => hz (dotProduct_self_eq_zero.mp h.symm))
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  set n := z ⬝ᵥ z with hndef
  constructor
  · rcases hker with hk | hk
    · refine ⟨z, (s * n / (z ⬝ᵥ (R *ᵥ z) + 1)) • z, ?_⟩
      set q := z ⬝ᵥ (R *ᵥ z) with hq
      have hq0 : 0 ≤ q := hR z
      have hq1 : 0 < q + 1 := by linarith
      set t := s * n / (q + 1) with ht
      have ht0 : 0 < t := by rw [ht]; positivity
      have htq : t * (q + 1) = s * n := by rw [ht]; field_simp
      rw [hk, dotProduct_zero, quadForm_smul, dotProduct_smul, smul_eq_mul]
      nlinarith [ht0, hn, hs, hq0]
    · refine ⟨(s * n / (z ⬝ᵥ (P *ᵥ z) + 1)) • z, z, ?_⟩
      set q := z ⬝ᵥ (P *ᵥ z) with hq
      have hq0 : 0 ≤ q := hP z
      have hq1 : 0 < q + 1 := by linarith
      set t := s * n / (q + 1) with ht
      have ht0 : 0 < t := by rw [ht]; positivity
      have htq : t * (q + 1) = s * n := by rw [ht]; field_simp
      rw [hk, dotProduct_zero, quadForm_smul, smul_dotProduct, smul_eq_mul]
      nlinarith [ht0, hn, hs, hq0]
  · refine ⟨z, -z, ?_⟩
    have h1 : (-z) ⬝ᵥ (R *ᵥ (-z)) = z ⬝ᵥ (R *ᵥ z) := by
      rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    have h2 : z ⬝ᵥ (-z) = -n := by rw [dotProduct_neg]
    rw [h1, h2]
    nlinarith [hP z, hR z, hn, hs]

/-- A matrix of rank below its width has a nonzero kernel vector.  This is
rank–nullity in the only direction used here, phrased so that the caller never
has to see `Module.finrank`. -/
private theorem exists_ker_of_rank_lt {K H : ℕ} (B : Matrix (Fin K) (Fin H) ℝ)
    (h : B.rank < H) :
    ∃ z : Fin H → ℝ, z ≠ 0 ∧ B *ᵥ z = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [show Module.finrank ℝ (Fin H → ℝ) = H by simp] at hrn
  rw [show Module.finrank ℝ (LinearMap.range B.mulVecLin) = B.rank from rfl] at hrn
  have hker : Module.finrank ℝ (LinearMap.ker B.mulVecLin) ≠ 0 := by omega
  have hne : LinearMap.ker B.mulVecLin ≠ ⊥ := fun hb => hker (by rw [hb]; simp)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨z, hz0, hz⟩

/-- **At a nonterminal factorization one Gram block has a kernel vector.**  For
`A : ℝ^{H×M}` and `B : ℝ^{N×H}` with `rank (B A) < H`, some nonzero `z ∈ ℝ^H` is
killed by `BᵀB` or by `A Aᵀ` — the two diagonal blocks of the saddle Hessian.

Which Gram goes with which factor is fixed by the shapes and matters: `BᵀB` acts
on `ℝ^H` with kernel `ker B`, and `A Aᵀ` acts on `ℝ^H` with kernel `ker Aᵀ`.

The argument is Sylvester's inequality and nothing else.  If both `A` and `Aᵀ`
were injective on `ℝ^H`, i.e. `rank A = rank B = H`, then
`rank_add_rank_le_of_mul` would give `H + H ≤ H + rank (B A)`, contradicting the
hypothesis.  So one of the two factors drops rank, and rank–nullity produces the
kernel vector; passing to the Gram matrix is then
`(BᵀB) z = Bᵀ (B z)` and `(A Aᵀ) z = A (Aᵀ z)`.

Composed with `hessianBlock_quadForm_indefinite`, this is what turns "the rung is
nonterminal" into "the block form takes both signs". -/
public theorem exists_mem_ker_gram {M N H : ℕ}
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (hrank : (B * A).rank < H) :
    ∃ z : Fin H → ℝ, z ≠ 0 ∧ ((Bᵀ * B) *ᵥ z = 0 ∨ (A * Aᵀ) *ᵥ z = 0) := by
  have hsyl := rank_add_rank_le_of_mul A B
  have hA : A.rank ≤ H := Matrix.rank_le_height A
  have hB : B.rank ≤ H := Matrix.rank_le_width B
  have hsplit : A.rank < H ∨ B.rank < H := by omega
  rcases hsplit with h | h
  · have hAt : Aᵀ.rank < H := by rwa [Matrix.rank_transpose]
    obtain ⟨z, hz, hzk⟩ := exists_ker_of_rank_lt Aᵀ hAt
    exact ⟨z, hz, Or.inr (by rw [← Matrix.mulVec_mulVec, hzk, Matrix.mulVec_zero])⟩
  · obtain ⟨z, hz, hzk⟩ := exists_ker_of_rank_lt B h
    exact ⟨z, hz, Or.inl (by rw [← Matrix.mulVec_mulVec, hzk, Matrix.mulVec_zero])⟩

end AISafetyAtlas.SingularLearning
