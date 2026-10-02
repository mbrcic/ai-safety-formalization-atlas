/-
Statements and proofs adapted from `AnandGokhale/LeanForControl`
(https://github.com/AnandGokhale/LeanForControl), file
`LeanForControl/LinearSystems/Hautus.lean` at commit `c5cedca`, licensed
Apache-2.0. The upstream file's SHA-256 is
`ae6bf9464b9602cf27ea9fd88ae9e38d5042e4953e8676cc14b5d974d8a573f9`.

Atlas changes: namespace `LinearSystems` -> `AISafetyAtlas.LinearSystems`;
the `module` marker and per-declaration `public` visibility; the `Architect`
dependency and its `blueprint` attributes removed; Mathlib v4.30.0-rc2 ->
v4.33.0 (`db584cd6d46c92f209a44c0f1c829460d327499d`), which cost one `haveI`
(style linter) and one rewritten `simpa` inside
`exists_eigenvector_of_unobservableSubspace_neBot`, marked at the site. The mathematics
is the upstream author's. Repository-level notice:
`AISafetyAtlas/Upstream/LICENSE-NOTICE`.
-/

module

public import AISafetyAtlas.LinearSystems.Controllability
public import AISafetyAtlas.LinearSystems.Observability
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Hautus observability lemma

For a finite-dimensional linear system over `ℂ`,

  `IsObservable A C ↔ ∀ μ ∈ ℂ, the block matrix `[μI - A; C]` has trivial kernel`.

This file proves both directions and packages them as the iff
`isObservable_iff_hautus`. The whole development is over `ℂ` (per the
project note: eigenvalues live in `ℂ`).

The structure is:

* `unobservableSubspace A C` — the `A`-invariant submodule of vectors that
  are killed by every `C * A^k`.
* Cayley-Hamilton helper: vectors in `unobservableSubspace` are killed by
  `C * A^n` too, not just `C * A^k` for `k < n`.
* `A`-invariance of `unobservableSubspace`.
* `hautusObservabilityMatrix A C μ` — the block-row matrix `[μI - A; C]`.
* Failure direction: `¬ IsObservable A C → ∃ μ, witness vector` via
  eigenvector extraction on `unobservableSubspace`.
* Converse: a Hautus-failure witness violates observability directly.
* Full iff packaged at the bottom.
-/

namespace AISafetyAtlas.LinearSystems

open Matrix

variable {n p : ℕ}

/-- The unobservable subspace of `(A, C)`: states that the output `C · A^k`
fails to distinguish from zero for every `k = 0, …, n-1`.

Defined as the intersection of the kernels of the linear maps
`(C · A^k).mulVecLin` for `k : Fin n`. By Cayley–Hamilton (see
`A_mulVec_mem_unobservableSubspace_of_mem`) this submodule is `A`-invariant. -/
@[expose] public noncomputable def unobservableSubspace
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    Submodule ℂ (Fin n → ℂ) :=
  ⨅ k : Fin n, LinearMap.ker (C * A ^ (k : ℕ)).mulVecLin

public lemma mem_unobservableSubspace_iff
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    (v : Fin n → ℂ) :
    v ∈ unobservableSubspace A C
      ↔ ∀ k : Fin n, (C * A ^ (k : ℕ)) *ᵥ v = 0 := by
  simp [unobservableSubspace, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The unobservable subspace is trivial exactly when the system is observable
in the textbook sense `IsObservable`. -/
public theorem unobservableSubspace_eq_bot_iff_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    unobservableSubspace A C = ⊥ ↔ IsObservable A C := by
  rw [Submodule.eq_bot_iff]
  unfold IsObservable
  refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · exact h v ((mem_unobservableSubspace_iff v).mpr hv)
  · exact h v ((mem_unobservableSubspace_iff v).mp hv)

/-- Cayley-Hamilton consequence: a vector in the unobservable subspace is
also annihilated by `C * A^n`, not just by `C * A^k` for `k < n`. The single
extra power closes the gap that `A`-invariance needs. -/
private lemma mulVec_aPowN_eq_zero_of_mem_unobservableSubspace
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    {v : Fin n → ℂ} (hv : v ∈ unobservableSubspace A C) :
    (C * A ^ n) *ᵥ v = 0 := by
  rw [mem_unobservableSubspace_iff] at hv
  -- Cayley-Hamilton in matrix form, multiplied on the left by `C` and
  -- evaluated at `v`.
  have hCH := Matrix.aeval_self_charpoly A
  have h_apply : (C * Polynomial.aeval A A.charpoly) *ᵥ v = 0 := by
    rw [hCH, Matrix.mul_zero, Matrix.zero_mulVec]
  -- Expand `aeval` as a finite sum and use the degree of `charpoly`.
  have hdeg : A.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ] at h_apply
  -- Isolate the leading `A^n` term using monicity of `charpoly`.
  have hmonic : A.charpoly.coeff n = 1 := by
    have hL := A.charpoly_monic
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hL
    exact hL
  rw [hmonic, one_smul, Matrix.mul_add, Matrix.add_mulVec] at h_apply
  -- The remaining sum vanishes term-by-term because each `(C * A^i) *ᵥ v = 0`.
  have hsum : (C * ∑ i ∈ Finset.range n, A.charpoly.coeff i • A ^ i) *ᵥ v = 0 := by
    rw [Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Matrix.mul_smul, Matrix.smul_mulVec, hv ⟨i, hi⟩, smul_zero]
  rw [hsum, zero_add] at h_apply
  exact h_apply

/-- The unobservable subspace is `A`-invariant: applying `A` to any
unobservable state keeps it unobservable. The proof for the boundary case
`k = n - 1` uses Cayley-Hamilton through
`mulVec_aPowN_eq_zero_of_mem_unobservableSubspace`. -/
public lemma A_mulVec_mem_unobservableSubspace_of_mem
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    {v : Fin n → ℂ} (hv : v ∈ unobservableSubspace A C) :
    A *ᵥ v ∈ unobservableSubspace A C := by
  rw [mem_unobservableSubspace_iff]
  intro k
  -- Bridge `(C * A^k.val) *ᵥ (A *ᵥ v) = (C * A^(k.val + 1)) *ᵥ v`.
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ]
  by_cases hk : k.val + 1 < n
  · exact (mem_unobservableSubspace_iff v).mp hv ⟨k.val + 1, hk⟩
  · -- `k.val + 1 = n`, so use the Cayley-Hamilton helper.
    push Not at hk
    have hk_lt : k.val < n := k.isLt
    have heq : k.val + 1 = n := by omega
    rw [heq]
    exact mulVec_aPowN_eq_zero_of_mem_unobservableSubspace hv

/-- **Every power, not just the first `n`.** Iterating `A`-invariance lifts the
`Fin n`-indexed definition of the unobservable subspace to all natural powers.

This is where Cayley-Hamilton is spent for the dynamic layer: `IsObservable` and
`unobservableSubspace` are stated at `k : Fin n` because the rank criterion is,
while anything that differentiates a trajectory produces one more power at each
step and needs them all. -/
public theorem mulVec_pow_mem_unobservableSubspace
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    {v : Fin n → ℂ} (hv : v ∈ unobservableSubspace A C) :
    ∀ k : ℕ, A ^ k *ᵥ v ∈ unobservableSubspace A C := by
  intro k
  induction k with
  | zero => simpa using hv
  | succ k ih =>
      have h := A_mulVec_mem_unobservableSubspace_of_mem ih
      rwa [Matrix.mulVec_mulVec, ← pow_succ'] at h

/-- The same fact read as the vanishing of every Kalman row. -/
public theorem mulVec_pow_eq_zero_of_mem_unobservableSubspace
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin p) (Fin n) ℂ}
    {v : Fin n → ℂ} (hv : v ∈ unobservableSubspace A C) :
    ∀ k : ℕ, (C * A ^ k) *ᵥ v = 0 := by
  intro k
  have h := mulVec_pow_mem_unobservableSubspace hv k
  rw [mem_unobservableSubspace_iff] at h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i
    simp [Matrix.mulVec, dotProduct]
  · have h0 := h ⟨0, hn⟩
    rw [← Matrix.mulVec_mulVec]
    simpa using h0

/-- If the unobservable subspace is non-trivial, it contains a nonzero
eigenvector of `A` (over `ℂ`). The eigenvector lifts to the ambient space
`Fin n → ℂ` and is automatically annihilated by `C` (membership at `k = 0`). -/
public theorem exists_eigenvector_of_unobservableSubspace_neBot
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (h : unobservableSubspace A C ≠ ⊥) :
    ∃ μ : ℂ, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v ∧ C *ᵥ v = 0 := by
  have hNontriv : Nontrivial (unobservableSubspace A C) :=
    (Submodule.nontrivial_iff_ne_bot).mpr h
  -- The ambient space `Fin n → ℂ` must itself be non-trivial, hence `0 < n`.
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      apply h
      subst hn
      rw [Submodule.eq_bot_iff]
      intro v _
      funext i
      exact i.elim0
    · exact hn
  -- Restrict `A.mulVecLin` to the (A-invariant) unobservable subspace.
  let A_res : Module.End ℂ (unobservableSubspace A C) :=
    A.mulVecLin.restrict
      (fun _ hw => A_mulVec_mem_unobservableSubspace_of_mem hw)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A_res
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, w.val, ?_, ?_, ?_⟩
  · -- The eigenvector is nonzero in the ambient space.
    intro hzero
    exact hw.2 (Subtype.ext hzero)
  · -- Lift the eigenvalue equation through `Submodule.subtype`.
    have heig : A_res w = μ • w := hw.apply_eq_smul
    have hval := congrArg Subtype.val heig
    -- Atlas change: at this Mathlib the `simpa` closing this goal upstream
    -- leaves `↑((A.mulVecLin.restrict _) w)` unreduced, and both
    -- `LinearMap.restrict_apply` and `Matrix.mulVecLin_apply` are then unused
    -- simp arguments. Unfolding the `let` and the subtype `smul` suffices.
    simp only [A_res, SetLike.val_smul] at hval
    exact hval
  · -- Membership at `k = 0` reads off `C *ᵥ w.val = 0`.
    have hmem : w.val ∈ unobservableSubspace A C := w.2
    rw [mem_unobservableSubspace_iff] at hmem
    have h0 := hmem ⟨0, hn_pos⟩
    rw [show ((⟨0, hn_pos⟩ : Fin n) : ℕ) = 0 from rfl,
        pow_zero, Matrix.mul_one] at h0
    exact h0

/-- The Hautus observability matrix at `μ`,
`[μ • 1 - A; C] : Matrix (Fin n ⊕ Fin p) (Fin n) ℂ`. -/
@[expose] public noncomputable def hautusObservabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) :
    Matrix (Fin n ⊕ Fin p) (Fin n) ℂ :=
  Matrix.fromRows (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) C

/-- A vector `v` is in the kernel of `H_{A, C}(μ) *ᵥ ·` iff `v` is an
eigenvector (or zero) of `A` with eigenvalue `μ` and is annihilated by `C`. -/
public lemma hautusObservabilityMatrix_mulVec_eq_zero_iff
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (μ : ℂ) (v : Fin n → ℂ) :
    hautusObservabilityMatrix A C μ *ᵥ v = 0
      ↔ A *ᵥ v = μ • v ∧ C *ᵥ v = 0 := by
  unfold hautusObservabilityMatrix
  rw [Matrix.fromRows_mulVec]
  -- Sum.elim a b = 0 ↔ a = 0 ∧ b = 0
  constructor
  · intro h
    have h1 : (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) *ᵥ v = 0 := by
      funext i
      simpa using congrFun h (Sum.inl i)
    have h2 : C *ᵥ v = 0 := by
      funext j
      simpa using congrFun h (Sum.inr j)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    exact ⟨(sub_eq_zero.mp h1).symm, h2⟩
  · rintro ⟨hAv, hCv⟩
    funext x
    cases x with
    | inl i =>
      simp only [Sum.elim_inl, Pi.zero_apply]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAv]
      simp
    | inr j =>
      simp only [Sum.elim_inr, Pi.zero_apply]
      simpa using congrFun hCv j

/-- **Failure direction of observability Hautus.** A non-observable system
admits a complex Hautus failure: some `μ ∈ ℂ` and a nonzero vector `v` such
that `[μ I - A; C] · v = 0`. -/
public theorem not_isObservable_implies_hautus_failure
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (h : ¬ IsObservable A C) :
    ∃ μ : ℂ, ∃ v : Fin n → ℂ,
      v ≠ 0 ∧ hautusObservabilityMatrix A C μ *ᵥ v = 0 := by
  have hN : unobservableSubspace A C ≠ ⊥ := fun hbot =>
    h ((unobservableSubspace_eq_bot_iff_isObservable A C).mp hbot)
  obtain ⟨μ, v, hne, hAv, hCv⟩ :=
    exists_eigenvector_of_unobservableSubspace_neBot A C hN
  refine ⟨μ, v, hne, ?_⟩
  rw [hautusObservabilityMatrix_mulVec_eq_zero_iff]
  exact ⟨hAv, hCv⟩

/-- **Converse direction of observability Hautus.** A Hautus failure at any
`μ ∈ ℂ` with witness `v ≠ 0` implies the system is not observable. -/
public theorem hautus_failure_implies_not_isObservable
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ)
    (μ : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (h : hautusObservabilityMatrix A C μ *ᵥ v = 0) :
    ¬ IsObservable A C := by
  rw [hautusObservabilityMatrix_mulVec_eq_zero_iff] at h
  obtain ⟨hAv, hCv⟩ := h
  have hpow : ∀ j : ℕ, A ^ j *ᵥ v = μ ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih,
          smul_smul]
      congr 1
      ring
  intro hObs
  apply hv
  apply hObs
  intro k
  rw [← Matrix.mulVec_mulVec, hpow, Matrix.mulVec_smul, hCv, smul_zero]

/-- **Observability Hautus lemma.** For a finite-dimensional linear system
over `ℂ`, the system is observable if and only if for every `μ ∈ ℂ`, the
Hautus block `[μ I - A; C]` has trivial kernel. -/
public theorem isObservable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) :
    IsObservable A C
      ↔ ∀ μ : ℂ,
          LinearMap.ker (hautusObservabilityMatrix A C μ).mulVecLin = ⊥ := by
  constructor
  · intro hObs μ
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro v hker
    by_contra hv
    exact hautus_failure_implies_not_isObservable A C μ v hv hker hObs
  · intro hHautus
    by_contra hNotObs
    obtain ⟨μ, v, hv, hker⟩ :=
      not_isObservable_implies_hautus_failure A C hNotObs
    have hμ := hHautus μ
    rw [Matrix.ker_mulVecLin_eq_bot_iff] at hμ
    exact hv (hμ v hker)

end AISafetyAtlas.LinearSystems

/-!
## Hautus controllability via duality

Controllability Hautus is the dual of observability Hautus. Rather than
mirror the entire eigenvector argument, we route through the bridge
`IsControllable A B ↔ IsObservable Aᵀ Bᵀ` and reuse the observability
results from above. The key matrix identity is
`(controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ`, which makes
the rank-form characterizations match across the duality. -/

namespace AISafetyAtlas.LinearSystems

open Matrix

variable {n m : ℕ}

/-- The transpose of the controllability matrix is the observability matrix
of the transposed system: `𝒞(A, B)ᵀ = 𝒪(Aᵀ, Bᵀ)`. -/
public lemma controllabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    (controllabilityMatrix A B)ᵀ = observabilityMatrix Aᵀ Bᵀ := by
  ext ki j
  obtain ⟨k, i⟩ := ki
  rw [Matrix.transpose_apply, controllabilityMatrix_apply,
      observabilityMatrix_apply,
      ← Matrix.transpose_pow,
      ← Matrix.transpose_mul,
      Matrix.transpose_apply]

/-- **Duality bridge.** A linear system `(A, B)` is controllable iff the
transposed system `(Aᵀ, Bᵀ)` is observable. -/
public theorem isControllable_iff_isObservable_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable A B ↔ IsObservable Aᵀ Bᵀ := by
  rw [isControllable_iff_controllabilityMatrix_rank_eq,
      isObservable_iff_observabilityMatrix_rank_eq Aᵀ Bᵀ,
      ← controllabilityMatrix_transpose,
      Matrix.rank_transpose]

/-- The Hautus controllability matrix at `μ`, `[μI - A | B]`. -/
@[expose] public noncomputable def hautusControllabilityMatrix
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    Matrix (Fin n) (Fin n ⊕ Fin m) ℂ :=
  Matrix.fromCols (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) B

/-- The transpose of the Hautus controllability matrix is the Hautus
observability matrix of the transposed system. -/
public lemma hautusControllabilityMatrix_transpose
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) :
    (hautusControllabilityMatrix A B μ)ᵀ = hautusObservabilityMatrix Aᵀ Bᵀ μ := by
  unfold hautusControllabilityMatrix hautusObservabilityMatrix
  rw [Matrix.transpose_fromCols, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one]

/-- **Controllability Hautus lemma.** A finite-dimensional linear system
`(A, B)` over `ℂ` is controllable if and only if for every `μ ∈ ℂ`, the
Hautus block `[μI - A | B]` has full row rank. -/
public theorem isControllable_iff_hautus
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    IsControllable A B
      ↔ ∀ μ : ℂ, Matrix.rank (hautusControllabilityMatrix A B μ) = n := by
  rw [isControllable_iff_isObservable_transpose, isObservable_iff_hautus]
  refine forall_congr' fun μ => ?_
  rw [Matrix.ker_mulVecLin_eq_bot_iff,
      AISafetyAtlas.LinearSystems.MatrixLemmas.mulVec_kernel_trivial_iff_rank_eq_card_cols,
      Fintype.card_fin,
      ← hautusControllabilityMatrix_transpose,
      Matrix.rank_transpose]

/-! ## Klamka's bound, the half the Hautus test gives

**Atlas-original, not from the upstream development.** Added 2026-09-11.

Klamka, *Uncontrollability and unobservability of multivariable systems*, IEEE
TAC 17(5):725-726 (1972), proves that a linear time-invariant system is
uncontrollable as soon as, for some eigenvalue, a count of Jordan blocks exceeds
the rank of the input matrix. The count is bounded below by the ceiling of the
algebraic multiplicity over the index, and *that* bound is print's contribution
and is not proved **in this module**. It is proved in
`AISafetyAtlas.LinearSystems.BlockBound`, added 2026-09-13, which also carries
print's numbered results at print's own antecedent; this header said the bound
was absent from the tree and that stopped being true that day.

What is proved here is the step from a block count to uncontrollability, through
the Hautus pencil rather than through print's Jordan-row criterion: the number of
Jordan blocks at an eigenvalue is the dimension of its eigenspace, so a pencil
whose two blocks cannot together reach rank `n` witnesses the failure. The
hypotheses below are therefore weaker than print's -- weaker in a way that does
not imply print's without the counting bound, which is why that bound lives in a
module of its own. See section 25 of `docs/provenance/source-coverage-audit.md`.
-/

section Klamka

variable {n m p : ℕ}

/-- If the pencil `[μ • 1 - A , B]` cannot reach rank `n` on ranks alone, the
system is uncontrollable. -/
public theorem not_isControllable_of_rank_add_lt
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ)
    (h : (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A).rank + B.rank < n) :
    ¬ IsControllable A B := by
  rw [isControllable_iff_hautus]
  intro hall
  have hμ := hall μ
  rw [hautusControllabilityMatrix] at hμ
  have hle := MatrixLemmas.rank_fromCols_le
    (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) B
  omega

/-- Rank-nullity for a square matrix acting by `*ᵥ`: kernel dimension and rank
sum to the side length. Used at `μ • 1 - A`, where the kernel is the eigenspace. -/
public lemma finrank_ker_add_rank_eq (M : Matrix (Fin n) (Fin n) ℂ) :
    Module.finrank ℂ (LinearMap.ker M.mulVecLin) + M.rank = n := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_pi, Fintype.card_fin] at h
  unfold Matrix.rank
  omega

/-- **Klamka's Theorem 1, at the eigenspace dimension.** If some eigenvalue's
eigenspace is larger than the rank of the input matrix, the system is
uncontrollable. Print's hypothesis is the ceiling of the algebraic multiplicity
over the index, which bounds this dimension below and is not proved here. -/
public theorem not_isControllable_of_finrank_ker_gt_rank
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ)
    (h : B.rank < Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVecLin)) :
    ¬ IsControllable A B := by
  refine not_isControllable_of_rank_add_lt A B μ ?_
  have := finrank_ker_add_rank_eq (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A)
  omega

/-- **Klamka's Corollary 1.** The same against the input dimension, which bounds
the rank of the input matrix. -/
public theorem not_isControllable_of_finrank_ker_gt_width
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ)
    (h : m < Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVecLin)) :
    ¬ IsControllable A B := by
  refine not_isControllable_of_finrank_ker_gt_rank A B μ ?_
  have hB := B.rank_le_card_width
  rw [Fintype.card_fin] at hB
  omega

/-- **Klamka's Theorem 2, at the eigenspace dimension**, and by the route print
takes: *"It follows by duality."* -/
public theorem not_isObservable_of_finrank_ker_gt_rank
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (h : C.rank < Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Aᵀ).mulVecLin)) :
    ¬ IsObservable A C := by
  intro hobs
  have hctrl : IsControllable Aᵀ Cᵀ := by
    rw [isControllable_iff_isObservable_transpose, Matrix.transpose_transpose,
      Matrix.transpose_transpose]
    exact hobs
  exact not_isControllable_of_finrank_ker_gt_rank Aᵀ Cᵀ μ
    (by rwa [Matrix.rank_transpose]) hctrl

/-- **Klamka's Corollary 2.** The observability twin of Corollary 1. -/
public theorem not_isObservable_of_finrank_ker_gt_height
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (h : p < Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Aᵀ).mulVecLin)) :
    ¬ IsObservable A C := by
  refine not_isObservable_of_finrank_ker_gt_rank A C μ ?_
  have hC := C.rank_le_card_height
  rw [Fintype.card_fin] at hC
  omega

/-- The eigenspace dimension is the same for a matrix and its transpose, so the
controllability and observability bounds can be stated against one quantity. -/
public lemma finrank_ker_transpose_eq
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Aᵀ).mulVecLin)
      = Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVecLin) := by
  have hT : (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Aᵀ)
      = (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rw [hT]
  have h₁ := finrank_ker_add_rank_eq
    ((μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A)ᵀ)
  have h₂ := finrank_ker_add_rank_eq (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A)
  rw [Matrix.rank_transpose] at h₁
  omega

/-- **Klamka's Corollary 3.** One eigenspace larger than both ranks makes the
system uncontrollable and unobservable at once. -/
public theorem not_isControllable_and_not_isObservable_of_finrank_ker_gt_ranks
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (h : max B.rank C.rank < Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVecLin)) :
    ¬ IsControllable A B ∧ ¬ IsObservable A C := by
  have hmaxB : B.rank ≤ max B.rank C.rank := le_max_left _ _
  have hmaxC : C.rank ≤ max B.rank C.rank := le_max_right _ _
  refine ⟨not_isControllable_of_finrank_ker_gt_rank A B μ (by omega), ?_⟩
  refine not_isObservable_of_finrank_ker_gt_rank A C μ ?_
  rw [finrank_ker_transpose_eq]
  omega

/-- **Klamka's Corollary 4.** The same against the two dimensions alone. -/
public theorem not_isControllable_and_not_isObservable_of_finrank_ker_gt_dims
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (h : max m p < Module.finrank ℂ
        (LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVecLin)) :
    ¬ IsControllable A B ∧ ¬ IsObservable A C := by
  have hB := B.rank_le_card_width
  have hC := C.rank_le_card_height
  rw [Fintype.card_fin] at hB hC
  refine not_isControllable_and_not_isObservable_of_finrank_ker_gt_ranks A B C μ ?_
  have h1 : max B.rank C.rank ≤ max m p := max_le_max hB hC
  omega

end Klamka

end AISafetyAtlas.LinearSystems
