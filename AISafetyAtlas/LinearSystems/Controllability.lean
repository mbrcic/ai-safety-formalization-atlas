/-
Statements and proofs adapted from `AnandGokhale/LeanForControl`
(https://github.com/AnandGokhale/LeanForControl), file
`LeanForControl/LinearSystems/Controllability.lean` at commit `c5cedca`, licensed
Apache-2.0. The upstream file's SHA-256 is
`2baaa99502889e476d1fa9eb737e413cfcc6ae953a8eeb3165c3fb334ea88760`.

Atlas changes: namespace `LinearSystems` -> `AISafetyAtlas.LinearSystems`;
the `module` marker and per-declaration `public` visibility; the `Architect`
dependency and its `blueprint` attributes removed; Mathlib v4.30.0-rc2 ->
v4.33.0 (`db584cd6d46c92f209a44c0f1c829460d327499d`);
`isControllable_iff_controllabilityMatrix_mulVec_surjective` made public,
unchanged in statement and proof, because
`AISafetyAtlas.Sovereignty.Disturbance` consumes it. The mathematics
is the upstream author's. Repository-level notice:
`AISafetyAtlas/Upstream/LICENSE-NOTICE`.
-/

module

public import AISafetyAtlas.LinearSystems.MatrixLemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Controllability of a finite-dimensional linear system

For a linear system

  ẋ = A x + B u

with `A : Matrix (Fin n) (Fin n) 𝕜` and `B : Matrix (Fin n) (Fin m) 𝕜`, this
file defines the (finite-horizon) controllability matrix

  𝒞(A, B) = [ B   A·B   A²·B   ⋯   Aⁿ⁻¹·B ] .

We index columns by `Fin n × Fin m` so that `A ^ (k : ℕ)` is available without
casting `k : Fin n` through `Fin.val`.

This file deliberately stays at the *definition + shape lemma* level: the
controllability characterizations (reachable subspace = span of columns,
controllable iff full column rank) are second-milestone work. -/

namespace AISafetyAtlas.LinearSystems

open Matrix

variable {𝕜 : Type*} [Semiring 𝕜]
variable {n m : ℕ}

/-- The controllability matrix of `(A, B)`.

The `(k, j)`-th column is the `j`-th column of `Aᵏ · B`, where `k : Fin n`
ranges over `0, 1, …, n-1`. -/
@[expose] public def controllabilityMatrix
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin n) (Fin n × Fin m) 𝕜 :=
  Matrix.of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

/-- Block-column shape lemma: the entry at row `i`, column `(k, j)` of the
controllability matrix is the `(i, j)` entry of `Aᵏ · B`. Holds
definitionally. -/
@[simp]
public lemma controllabilityMatrix_apply
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (i : Fin n) (k : Fin n) (j : Fin m) :
    controllabilityMatrix A B i (k, j) = (A ^ (k : ℕ) * B) i j :=
  rfl

/-- The textbook controllability predicate (existential reachability):
every state can be reached from the origin in `n` steps via some sequence
of inputs. Phrased in matrix-power language so the bridge theorem
`isControllable_iff_controllabilityMatrix_rank_eq` has real content. -/
@[expose] public def IsControllable
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) : Prop :=
  ∀ x : Fin n → 𝕜, ∃ u : Fin n → (Fin m → 𝕜),
    x = ∑ k : Fin n, (A ^ (k : ℕ) * B) *ᵥ u k

end AISafetyAtlas.LinearSystems

/-!
## Rank-form characterization

Reopened namespace over `[Field 𝕜]` only, breaking the typeclass diamond
between the outer `[Semiring 𝕜]` and the rank-side `[Field 𝕜]`. -/

namespace AISafetyAtlas.LinearSystems

open Matrix

variable {𝕜 : Type*} [Field 𝕜] {n m : ℕ}

/-- The matrix-vector product of the controllability matrix with a vector
indexed by `Fin n × Fin m` rewrites as a sum of per-power matrix-vector
products with curried inputs. Bridge between the assembled-matrix form and
the matrix-power-sum form of `IsControllable`. -/
private lemma controllabilityMatrix_mulVec_eq_sum
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (u : Fin n × Fin m → 𝕜) :
    controllabilityMatrix A B *ᵥ u
      = ∑ k : Fin n, (A ^ (k : ℕ) * B) *ᵥ (fun j => u (k, j)) := by
  funext i
  rw [Finset.sum_apply]
  change ∑ kj : Fin n × Fin m, controllabilityMatrix A B i kj * u kj
        = ∑ k : Fin n, ((A ^ (k : ℕ) * B) *ᵥ (fun j => u (k, j))) i
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [controllabilityMatrix_apply, Matrix.mulVec, dotProduct]

/-- `IsControllable` reformulated in the assembled-matrix form: the
controllability matrix's `*ᵥ` action is surjective onto the state space. -/
public lemma isControllable_iff_controllabilityMatrix_mulVec_surjective
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    IsControllable A B
      ↔ ∀ x : Fin n → 𝕜, ∃ u : Fin n × Fin m → 𝕜,
          controllabilityMatrix A B *ᵥ u = x := by
  unfold IsControllable
  constructor
  · intro h x
    obtain ⟨u', hu'⟩ := h x
    refine ⟨fun kj => u' kj.1 kj.2, ?_⟩
    rw [controllabilityMatrix_mulVec_eq_sum]
    exact hu'.symm
  · intro h x
    obtain ⟨u, hu⟩ := h x
    refine ⟨fun k j => u (k, j), ?_⟩
    rw [← hu, controllabilityMatrix_mulVec_eq_sum]

/-- Rank-form characterization: controllability is equivalent to the
controllability matrix having full row rank. -/
public theorem isControllable_iff_controllabilityMatrix_rank_eq
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    IsControllable A B ↔ Matrix.rank (controllabilityMatrix A B) = n := by
  refine (isControllable_iff_controllabilityMatrix_mulVec_surjective A B).trans ?_
  refine (AISafetyAtlas.LinearSystems.MatrixLemmas.mulVec_range_top_iff_rank_eq_card_rows
    (controllabilityMatrix A B)).trans ?_
  rw [Fintype.card_fin]

end AISafetyAtlas.LinearSystems
