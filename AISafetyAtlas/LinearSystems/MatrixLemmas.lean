/-
Statements and proofs adapted from `AnandGokhale/LeanForControl`
(https://github.com/AnandGokhale/LeanForControl), file
`LeanForControl/LinearSystems/MatrixLemmas.lean` at commit `c5cedca`, licensed
Apache-2.0. The upstream file's SHA-256 is
`f81d4451ac510da893cba905c25cf2d7590b2b8e5faa45132f7ecbfa3d13507b`.

Atlas changes: namespace `LinearSystems` -> `AISafetyAtlas.LinearSystems`;
the `module` marker and per-declaration `public` visibility; the `Architect`
dependency and its `blueprint` attributes removed; Mathlib v4.30.0-rc2 ->
v4.33.0 (`db584cd6d46c92f209a44c0f1c829460d327499d`). The mathematics
is the upstream author's. Repository-level notice:
`AISafetyAtlas/Upstream/LICENSE-NOTICE`.
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `LinearSystems.MatrixLemmas`

Reusable matrix-level facts that bridge

* the kernel-of-`*ᵥ` formulation,
* the linear-map-`ker = ⊥` formulation,
* and the `Matrix.rank` / full-column-rank formulation.

This file is project-internal plumbing for `LinearSystems.Observability` and
`LinearSystems.Controllability`. It carries no `` annotations and
intentionally exposes no LaTeX nodes — control-level statements belong in the
two `Observability` / `Controllability` files.

The file is Field-scoped: Mathlib's matrix rank requires a commutative ring, and the
column or row independence bridges to `rank = card ...` need `[Field 𝕜]`.
-/

namespace AISafetyAtlas.LinearSystems.MatrixLemmas

open Matrix

section Field

variable {𝕜 : Type*} [Field 𝕜]
variable {m n : Type*}

/-- Bridge between the kernel-of-`*ᵥ` form and the rank-equals-card-of-columns
form: a matrix `M : Matrix m n 𝕜` over a field has full column rank iff the
only `x` with `M *ᵥ x = 0` is the zero vector.

Proof chains `Matrix.ker_mulVecLin_eq_bot_iff` with rank-nullity. -/
public lemma mulVec_kernel_trivial_iff_rank_eq_card_cols [Fintype n] (M : Matrix m n 𝕜) :
    (∀ x : n → 𝕜, M *ᵥ x = 0 → x = 0) ↔ Matrix.rank M = Fintype.card n := by
  rw [← Matrix.ker_mulVecLin_eq_bot_iff]
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_pi] at hsum
  unfold Matrix.rank
  constructor
  · intro hker
    rw [hker, finrank_bot] at hsum
    omega
  · intro hrank
    have h0 : Module.finrank 𝕜 (LinearMap.ker M.mulVecLin) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h0

/-- Bridge between the surjectivity-of-`*ᵥ` form and the rank-equals-card-of-rows
form: a matrix `M : Matrix m n 𝕜` over a field has full row rank iff every `y`
in the codomain is in the range of `M *ᵥ ·`. -/
public lemma mulVec_range_top_iff_rank_eq_card_rows
    [Fintype m] [Fintype n] (M : Matrix m n 𝕜) :
    (∀ y : m → 𝕜, ∃ x : n → 𝕜, M *ᵥ x = y) ↔ Matrix.rank M = Fintype.card m := by
  have hsurj_iff :
      (∀ y : m → 𝕜, ∃ x : n → 𝕜, M *ᵥ x = y)
        ↔ LinearMap.range M.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    rfl
  rw [hsurj_iff]
  unfold Matrix.rank
  constructor
  · intro h
    rw [h, finrank_top, Module.finrank_pi]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [h, Module.finrank_pi]

end Field

/-! ## Rank of a block matrix

**Atlas-original, not from the upstream development.** Added 2026-09-11 for the
Klamka bound in `AISafetyAtlas.LinearSystems.Hautus`: a pencil `[μI - A , B]`
cannot have rank `n` once the two blocks together cannot reach that far.
-/

section BlockRank

variable {𝕜 : Type*} [Field 𝕜] {l n₁ n₂ : Type*} [Fintype l] [Fintype n₁] [Fintype n₂]

omit [Fintype l] in
/-- Stacking two matrices side by side cannot give more rank than they have
apart: the range of the block matrix lies in the join of the two ranges. -/
public lemma rank_fromCols_le (M : Matrix l n₁ 𝕜) (N : Matrix l n₂ 𝕜) :
    (Matrix.fromCols M N).rank ≤ M.rank + N.rank := by
  have hle : LinearMap.range (Matrix.fromCols M N).mulVecLin ≤
      LinearMap.range M.mulVecLin ⊔ LinearMap.range N.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
      funext i; cases i <;> rfl
    rw [Matrix.mulVecLin_apply, hx, Matrix.fromCols_mulVec_sumElim]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  calc (Matrix.fromCols M N).rank
      ≤ Module.finrank 𝕜
          (LinearMap.range M.mulVecLin ⊔ LinearMap.range N.mulVecLin :
            Submodule 𝕜 (l → 𝕜)) := Submodule.finrank_mono hle
    _ ≤ M.rank + N.rank := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- The row-stacked form of `rank_fromCols_le`, by transposing. -/
public lemma rank_fromRows_le (M : Matrix n₁ l 𝕜) (N : Matrix n₂ l 𝕜) :
    (Matrix.fromRows M N).rank ≤ M.rank + N.rank := by
  rw [← Matrix.rank_transpose, Matrix.transpose_fromRows, ← Matrix.rank_transpose M,
    ← Matrix.rank_transpose N]
  exact rank_fromCols_le _ _

end BlockRank

end AISafetyAtlas.LinearSystems.MatrixLemmas
