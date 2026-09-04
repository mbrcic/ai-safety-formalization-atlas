module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.SingularLearning.AoyagiWatanabe

/-!
# Ranks of an actual factorization are arithmetically feasible

`AoyagiWatanabe.lean` states rank feasibility as arithmetic: `Feasible M N H r a b`
is a predicate on six natural numbers, with no matrix anywhere in it. This module
supplies the missing bridge, so that an arithmetic statement about the rank
stratum `(a, b)` may be read as a statement about actual factorizations.

Concretely, fix a truth matrix `C : ℝ^{M×N}` and let

    W₀ = {(A, B) : A ∈ ℝ^{H×N}, B ∈ ℝ^{M×H}, B * A = C}

be the zero fiber of the reduced-rank regression model. The main theorem says
that the stratum map `(A, B) ↦ (rank A, rank B)` sends `W₀` into the arithmetic
feasibility set `{(a, b) : Feasible M N H (rank C) a b}`: every point of the
fiber does satisfy the four inequalities, so no arithmetic case of the candidate
formula is being evaluated at a stratum that cannot occur.

Three of the four conjuncts are Mathlib one-liners (`Matrix.rank_mul_le` and the
two shape bounds). The fourth, `rank A + rank B ≤ H + rank (B * A)`, is
**Sylvester's rank inequality**, which the pinned Mathlib does not have in any
form: `Mathlib/LinearAlgebra/Matrix/Rank.lean` and
`Mathlib/LinearAlgebra/Dimension/LinearMap.lean` carry only the *upper* bounds
`rank_mul_le` / `rank_comp_le`. It is proved here from rank–nullity, in the
linear-map form `sylvester_finrank_le`, and then transported to matrices.

**This module is pure linear algebra.** It says nothing about learning
coefficients, volume asymptotics, or which stratum minimizes anything; it only
certifies that the arithmetic predicate is not vacuous on real factorizations.
-/

namespace AISafetyAtlas.SingularLearning

open Module (finrank)

/-! ## Sylvester's rank inequality for linear maps -/

/-- **Sylvester's rank inequality**, linear-map form:

    rank f + rank g ≤ dim W + rank (g ∘ f)

for `f : V →ₗ W` and `g : W →ₗ U`.

The proof restricts `g` to the submodule `range f ⊆ W` and applies rank–nullity
twice: once to the restriction `g ∘ₗ (range f).subtype`, whose range is
`range (g ∘ₗ f)`, and once to `g` itself. The two kernels are compared by
`Submodule.finrank_mono`, using that the restriction's kernel embeds into
`ker g` along the injective inclusion of `range f`.

Mathlib (at the pinned revision) has only the upper bounds `LinearMap.rank_comp_le`
and friends; this lower bound has no counterpart there. -/
public theorem sylvester_finrank_le {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [FiniteDimensional K V] [FiniteDimensional K W] (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.range g)
      ≤ finrank K W + finrank K (LinearMap.range (g ∘ₗ f)) := by
  set p : Submodule K W := LinearMap.range f with hp
  set k : p →ₗ[K] U := g ∘ₗ p.subtype with hk
  -- The restriction of `g` to `range f` has range exactly `range (g ∘ₗ f)`.
  have hrange : LinearMap.range k = LinearMap.range (g ∘ₗ f) := by
    rw [hk, LinearMap.range_comp, Submodule.range_subtype, LinearMap.range_comp, hp]
  -- Rank–nullity for the restriction.
  have hres : finrank K (LinearMap.range k) + finrank K (LinearMap.ker k) = finrank K p :=
    LinearMap.finrank_range_add_finrank_ker k
  -- Rank–nullity for `g` on all of `W`.
  have hg : finrank K (LinearMap.range g) + finrank K (LinearMap.ker g) = finrank K W :=
    LinearMap.finrank_range_add_finrank_ker g
  -- The restriction's kernel is no bigger than `ker g`.
  have hker : finrank K (LinearMap.ker k) ≤ finrank K (LinearMap.ker g) := by
    have hle : (LinearMap.ker k).map p.subtype ≤ LinearMap.ker g := by
      rintro x ⟨y, hy, rfl⟩
      simpa [hk, LinearMap.mem_ker] using hy
    have he := Submodule.equivMapOfInjective p.subtype (Submodule.subtype_injective p)
      (LinearMap.ker k)
    calc finrank K (LinearMap.ker k) = finrank K ((LinearMap.ker k).map p.subtype) := he.finrank_eq
      _ ≤ finrank K (LinearMap.ker g) := Submodule.finrank_mono hle
  -- `finrank p` is the rank of `f`; assemble in ℕ without any subtraction.
  rw [hrange] at hres
  omega

/-! ## The matrix form -/

/-- Sylvester's rank inequality for matrices, in the subtraction-free form
`rank A + rank B ≤ H + rank (B * A)`.

Stated additively on purpose: the textbook form `rank A + rank B - H ≤ rank (B*A)`
is false as written in `ℕ`, where the left side is truncated at `0` whenever
`rank A + rank B < H`. -/
public theorem rank_add_rank_le_of_mul {M N H : ℕ}
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    A.rank + B.rank ≤ H + (B * A).rank := by
  have h := sylvester_finrank_le A.mulVecLin B.mulVecLin
  rw [← Matrix.mulVecLin_mul] at h
  simpa [Matrix.rank, Module.finrank_fin_fun] using h

/-- Any actual factorization has arithmetically feasible ranks: for `A : ℝ^{H×N}`
and `B : ℝ^{M×H}`, the triple `(rank (B*A), rank A, rank B)` satisfies `Feasible`.

The four conjuncts are: `Matrix.rank_mul_le`, the two shape bounds
`Matrix.rank_le_height` / `Matrix.rank_le_width`, and Sylvester's inequality
`rank_add_rank_le_of_mul`. -/
public theorem ranks_feasible_of_mul_eq {M N H : ℕ}
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    Feasible M N H (B * A).rank A.rank B.rank :=
  ⟨le_min (Matrix.rank_mul_le_right B A) (Matrix.rank_mul_le_left B A),
   le_min (Matrix.rank_le_height A) (Matrix.rank_le_width A),
   le_min (Matrix.rank_le_width B) (Matrix.rank_le_height B),
   rank_add_rank_le_of_mul A B⟩

/-- The zero-fiber reading: if `(A, B) ∈ W₀ = {(A,B) : B * A = C}`, then its rank
stratum `(rank A, rank B)` is feasible over the truth rank `rank C`. -/
public theorem ranks_feasible_of_factorization {M N H : ℕ} {C : Matrix (Fin M) (Fin N) ℝ}
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) (hC : B * A = C) :
    Feasible M N H C.rank A.rank B.rank :=
  hC ▸ ranks_feasible_of_mul_eq A B

/-- Feasibility of a factorization stratum passes to `AdmissibleRankData` once the
ambient dimensions are positive: the truth-rank bound `r ≤ min M (min N H)` is
already implied by the four inequalities. -/
public theorem admissible_of_mul_eq {M N H : ℕ} (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    AdmissibleRankData M N H (B * A).rank A.rank B.rank :=
  ⟨hM, hN, hH, (ranks_feasible_of_mul_eq A B).rank_le, ranks_feasible_of_mul_eq A B⟩

/-! ## Worked examples

Two endpoints of the Sylvester bound, so the module is not statement-only. -/

/-- The Sylvester bound is sharp: the identity factorization `A = B = 1` saturates
`a + b ≤ H + r` with `a = b = H = r = n`. -/
example (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ).rank + (1 : Matrix (Fin n) (Fin n) ℝ).rank
      = n + ((1 : Matrix (Fin n) (Fin n) ℝ) * 1).rank := by
  simp

/-- The degenerate endpoint: the zero factorization sits in the stratum `(0, 0)`
over truth rank `0`, which is feasible for every shape. -/
example (M N H : ℕ) :
    Feasible M N H ((0 : Matrix (Fin M) (Fin H) ℝ) * (0 : Matrix (Fin H) (Fin N) ℝ)).rank
      (0 : Matrix (Fin H) (Fin N) ℝ).rank (0 : Matrix (Fin M) (Fin H) ℝ).rank :=
  ranks_feasible_of_mul_eq _ _

/-- A rank-deficient middle layer really does force the product to drop rank: with
`H = 1` the product of two `2 × 1` and `1 × 2` blocks has rank at most `1`, which
is what the `a + b ≤ H + r` conjunct records at `a = b = 1`. -/
example (A : Matrix (Fin 1) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 1) ℝ) :
    (B * A).rank ≤ 1 :=
  le_trans (Matrix.rank_mul_le B A) (le_trans (min_le_right _ _) (Matrix.rank_le_height A))

end AISafetyAtlas.SingularLearning
