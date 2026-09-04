module

public import AISafetyAtlas.SingularLearning.EliminationChart
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Transporting the elimination chart into `Fin`-indexed coordinates

`EliminationChart.lean` proves Steps 1–5 of the candidate's Theorem 5.1 over `Sum` index
types. That is the right place to prove them — print's `a − r`, `b − r`, `H − a`, `N − a`,
`M − b` and `H + r − a − b` all appear as *summands* there rather than as truncated
subtractions, so no `ℕ` subtraction is ever formed inside an identity. But
`HasEliminationChartAt` quantifies over `ParamSpace M N H` and `ChartSpace q p h n g`, which
are `Fin`-indexed. This module is the bridge.

## What is here

* **The index splittings.** `finSplit` is `Fin n ≃ Fin k ⊕ Fin (n − k)` for `k ≤ n`, and
  `elimHiddenEquiv`, `elimInputEquiv`, `elimOutputEquiv` are print's three splittings
  assembled from it:

      Fin H ≃ (Fin r ⊕ Fin (a−r)) ⊕ (Fin (b−r) ⊕ Fin h)
      Fin N ≃ (Fin r ⊕ Fin (a−r)) ⊕ Fin n
      Fin M ≃ (Fin r ⊕ Fin (b−r)) ⊕ Fin p

  So the six index types of Step 5 instantiate as `ρ = Fin r`, `σ = Fin (a−r)`,
  `τ = Fin (b−r)`, `η = Fin h`, `ν = Fin n`, `π = Fin p`, and Step 5's `ElimCoords` becomes a
  tuple of `Fin`-indexed matrices. The arithmetic that makes this work —
  `(b−r) + h = H − a`, `r + (b−r) = b` and so on — holds exactly on a feasible stratum and is
  discharged by `omega` from the feasibility hypotheses.

* **The coordinate packings.** `matrixEuclEquiv` identifies `EuclideanSpace ℝ (Fin (m*n))` with
  `Matrix (Fin m) (Fin n) ℝ`, and `euclSplitEquiv` splits `EuclideanSpace ℝ (Fin (k₁+k₂))` as a
  product. Both are `ContinuousLinearEquiv`s, which is the point: analyticity of anything built
  from them is then `ContinuousLinearMap.analyticAt` and composition, with no estimate to prove.

## Why continuous *linear* equivalences

The `AnalyticOnNhd` clauses of `HasEliminationChartAt` are the only place the norms matter, and
they matter only up to equivalence — every linear map between finite-dimensional real spaces is
continuous, and every continuous linear map is analytic. Bundling each reindexing as a
`ContinuousLinearEquiv` therefore discharges its share of the analyticity obligation for free,
and leaves only the genuinely nonlinear parts of `Ψ` — the two matrix inverses — to
`MatrixAnalytic.lean`.

## What is *not* here

This module builds the bridge; it does not drive `Ψ` across it. That composition --
instantiating Step 5's `elimPsi`/`elimPhi` at the six `Fin` types above, packing the nine
blocks of `ElimCoords` into `ChartSpace`, and assembling the analyticity of the composite --
is `ChartAssembly.lean`, and it ends at `isEliminationChart_of_feasible`, which inhabits
`IsEliminationChart` at every feasible stratum, not merely at the degenerate
`isEliminationChart_zero`.
-/

namespace AISafetyAtlas.SingularLearning

open scoped Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-! ## The index splittings -/

/-- `Fin n ≃ Fin k ⊕ Fin (n − k)` for `k ≤ n`: the reindexing that turns print's truncated
subtraction into a summand. The subtraction `n − k` is still formed, but only as a *type
index*, never inside an identity — and `Nat.add_sub_cancel'` is what makes it exact. -/
@[expose] public def finSplit {k n : ℕ} (h : k ≤ n) : Fin n ≃ Fin k ⊕ Fin (n - k) :=
  (finCongr (Nat.add_sub_cancel' h).symm).trans finSumFinEquiv.symm

/-- Print's hidden splitting `ℝ^H = (ℝ^r ⊕ ℝ^{a−r}) ⊕ (ℝ^{b−r} ⊕ ℝ^h)`, the one Step 5's
`ElimCoords` is indexed by. The two arithmetic facts it needs are `b − r ≤ H − a` and
`(H − a) − (b − r) = h`; both hold exactly on a feasible stratum. -/
@[expose] public def elimHiddenEquiv {H r a b : ℕ} (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) :
    Fin H ≃ (Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b)) :=
  (finSplit haH).trans <|
    Equiv.sumCongr (finSplit hra) <|
      (finSplit (show b - r ≤ H - a by omega)).trans <|
        Equiv.sumCongr (Equiv.refl _)
          (finCongr (show H - a - (b - r) = elimH H r a b by unfold elimH; omega))

/-- Print's input splitting `ℝ^N = (ℝ^r ⊕ ℝ^{a−r}) ⊕ ℝ^n`. -/
@[expose] public def elimInputEquiv {N r a : ℕ} (haN : a ≤ N) (hra : r ≤ a) :
    Fin N ≃ (Fin r ⊕ Fin (a - r)) ⊕ Fin (elimN N a) :=
  (finSplit haN).trans <|
    Equiv.sumCongr (finSplit hra) (finCongr (show N - a = elimN N a from rfl))

/-- Print's output splitting `ℝ^M = (ℝ^r ⊕ ℝ^{b−r}) ⊕ ℝ^p`. -/
@[expose] public def elimOutputEquiv {M r b : ℕ} (hbM : b ≤ M) (hrb : r ≤ b) :
    Fin M ≃ (Fin r ⊕ Fin (b - r)) ⊕ Fin (elimP M b) :=
  (finSplit hbM).trans <|
    Equiv.sumCongr (finSplit hrb) (finCongr (show M - b = elimP M b from rfl))

/-- The hidden index splits into `a` and `H − a` before it splits further; recorded because it
is the shape Step 1's gauge `L(A)` is stated in. -/
@[expose] public def elimHiddenCoarseEquiv {H a : ℕ} (haH : a ≤ H) :
    Fin H ≃ Fin a ⊕ Fin (H - a) := finSplit haH

/-! ### The two counts that make the packing work

`q = Ma + bn` and `g = a² + (H−a)a + (a−r)n + M(b−r) + bh` are print's own expressions, but
`elimQ` is written `a(M−b) + bN` and `elimGauge` in terms of `elimN`/`elimH`. The two forms of
`q` agree on a feasible stratum; the gauge one is definitional. -/

/-- `q = Ma + bn`, the form in which the `u`-block is packed: `Ma` entries of `U` followed by
`bn` entries of `T′`. Print writes `q = Ma + bN − ab`; `elimQ` writes `a(M−b) + bN`; on a
feasible stratum all three are the same natural number. -/
public theorem elimQ_eq_add {M N a b : ℕ} (hbM : b ≤ M) (haN : a ≤ N) :
    elimQ M N a b = M * a + b * elimN N a := by
  have hZ : ((elimQ M N a b : ℕ) : ℤ) = ((M * a + b * elimN N a : ℕ) : ℤ) := by
    rw [elimQ_cast hbM]
    have hn : ((elimN N a : ℕ) : ℤ) = (N : ℤ) - a := by unfold elimN; omega
    push_cast [hn]
    ring
  exact Nat.cast_injective hZ

/-- `g` as the sum of the five gauge blocks' entry counts, in print's order:
`A₁₁` is `a × a`, `A₂₁` is `(H−a) × a`, `X_P` is `(a−r) × n`, `D` is `M × (b−r)` and `Y₁` is
`b × h`. This is `elimGauge` unfolded, and is what the gauge packing consumes. -/
public theorem elimGauge_eq_add (M N H r a b : ℕ) :
    elimGauge M N H r a b =
      a * a + (H - a) * a + (a - r) * elimN N a + M * (b - r) + b * elimH H r a b := rfl

/-! ## The coordinate packings

Each is a `ContinuousLinearEquiv`, so every analyticity obligation it contributes is
`ContinuousLinearMap.analyticAt`. -/

/-- `(Fin (m*n) → ℝ)` is the space of `m × n` matrices, linearly: the reindexing
`finProdFinEquiv` and nothing more. -/
@[expose] public def matrixFunLinearEquiv (m n : ℕ) :
    (Fin (m * n) → ℝ) ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun x := Matrix.of fun i j => x (finProdFinEquiv (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun A := fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv x := by
    funext k
    show x (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = x k
    rw [Prod.mk.eta, finProdFinEquiv.apply_symm_apply]
  right_inv A := by
    ext i j
    show A (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = A i j
    rw [finProdFinEquiv.symm_apply_apply]

/-- **The matrix packing.** `EuclideanSpace ℝ (Fin (m*n)) ≃L[ℝ] Matrix (Fin m) (Fin n) ℝ`. -/
@[expose] public noncomputable def matrixEuclEquiv (m n : ℕ) :
    EuclideanSpace ℝ (Fin (m * n)) ≃L[ℝ] Matrix (Fin m) (Fin n) ℝ :=
  (EuclideanSpace.equiv (Fin (m * n)) ℝ).trans
    (matrixFunLinearEquiv m n).toContinuousLinearEquiv

/-- `(Fin (k₁ + k₂) → ℝ)` splits as a product, linearly. -/
@[expose] public def sumFunLinearEquiv (k₁ k₂ : ℕ) :
    (Fin (k₁ + k₂) → ℝ) ≃ₗ[ℝ] (Fin k₁ → ℝ) × (Fin k₂ → ℝ) where
  toFun x := (fun i => x (finSumFinEquiv (Sum.inl i)), fun i => x (finSumFinEquiv (Sum.inr i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := fun k => Sum.elim p.1 p.2 (finSumFinEquiv.symm k)
  left_inv x := by
    funext k
    rcases h : finSumFinEquiv.symm k with i | i <;>
      simp only [h, Sum.elim_inl, Sum.elim_inr] <;>
      rw [← h, finSumFinEquiv.apply_symm_apply]
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> funext i <;> simp

/-- **The block packing.** `EuclideanSpace ℝ (Fin (k₁+k₂))` splits as a product of Euclidean
spaces, as a continuous linear equivalence. Iterating it is how the `u`-block's two matrices
and the gauge block's five are packed into single coordinates. -/
@[expose] public noncomputable def euclSplitEquiv (k₁ k₂ : ℕ) :
    EuclideanSpace ℝ (Fin (k₁ + k₂)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂) :=
  (EuclideanSpace.equiv (Fin (k₁ + k₂)) ℝ).trans <|
    (sumFunLinearEquiv k₁ k₂).toContinuousLinearEquiv.trans <|
      ((EuclideanSpace.equiv (Fin k₁) ℝ).prodCongr (EuclideanSpace.equiv (Fin k₂) ℝ)).symm

/-- Reindexing a matrix along two index equivalences, as a continuous linear equivalence. This
is what carries Step 5's `Sum`-indexed matrices to `Fin`-indexed ones. -/
@[expose] public noncomputable def matrixReindexEquiv {m n m' n' : Type*} [Fintype m]
    [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m] [DecidableEq n] [DecidableEq m']
    [DecidableEq n'] (em : m ≃ m') (en : n ≃ n') :
    Matrix m n ℝ ≃L[ℝ] Matrix m' n' ℝ :=
  (Matrix.reindexLinearEquiv ℝ ℝ em en).toContinuousLinearEquiv

/-! ## Analyticity comes for free

Each packing above is a continuous linear equivalence, so it and its inverse are analytic
everywhere. These are the lemmas the assembly of `Ψ` will consume; they are stated once here
rather than re-derived at each of the nine blocks. -/

public theorem analyticOnNhd_matrixEuclEquiv (m n : ℕ)
    (s : Set (EuclideanSpace ℝ (Fin (m * n)))) :
    AnalyticOnNhd ℝ (matrixEuclEquiv m n) s :=
  fun x _ => (matrixEuclEquiv m n).toContinuousLinearMap.analyticAt x

public theorem analyticOnNhd_matrixEuclEquiv_symm (m n : ℕ)
    (s : Set (Matrix (Fin m) (Fin n) ℝ)) :
    AnalyticOnNhd ℝ (matrixEuclEquiv m n).symm s :=
  fun x _ => (matrixEuclEquiv m n).symm.toContinuousLinearMap.analyticAt x

public theorem analyticOnNhd_euclSplitEquiv (k₁ k₂ : ℕ)
    (s : Set (EuclideanSpace ℝ (Fin (k₁ + k₂)))) :
    AnalyticOnNhd ℝ (euclSplitEquiv k₁ k₂) s :=
  fun x _ => (euclSplitEquiv k₁ k₂).toContinuousLinearMap.analyticAt x

public theorem analyticOnNhd_euclSplitEquiv_symm (k₁ k₂ : ℕ)
    (s : Set (EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂))) :
    AnalyticOnNhd ℝ (euclSplitEquiv k₁ k₂).symm s :=
  fun x _ => (euclSplitEquiv k₁ k₂).symm.toContinuousLinearMap.analyticAt x

public theorem analyticOnNhd_matrixReindexEquiv {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n']
    (em : m ≃ m') (en : n ≃ n') (s : Set (Matrix m n ℝ)) :
    AnalyticOnNhd ℝ (matrixReindexEquiv em en) s :=
  fun x _ => (matrixReindexEquiv em en).toContinuousLinearMap.analyticAt x

/-! ## The packings are bijections onto the whole space

Trivial, but worth having as the form `Set.BijOn` that `HasEliminationChartAt` asks for: a
continuous linear equivalence is a bijection of any set onto its image, and of `univ` onto
`univ`. -/

public theorem bijOn_matrixEuclEquiv (m n : ℕ) :
    Set.BijOn (matrixEuclEquiv m n) Set.univ Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, Set.injOn_of_injective (matrixEuclEquiv m n).injective, ?_⟩
  intro A _
  exact ⟨(matrixEuclEquiv m n).symm A, Set.mem_univ _,
    (matrixEuclEquiv m n).apply_symm_apply A⟩

/-! ## The parameter-space equivalence

The first of the two equivalences `chart_transport` consumes. `ParamSpace M N H` is
`Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ`, and Step 5's `PairSpace` is the same
pair over the `Sum` index types; the three splittings above turn one into the other, and
`matrixReindexEquiv` makes each a continuous linear equivalence.

The six index types are instantiated once and for all here:

    ρ = Fin r,  σ = Fin (a − r),  τ = Fin (b − r),
    η = Fin h,  ν = Fin n,        π = Fin p

with `h = elimH H r a b`, `n = elimN N a`, `p = elimP M b`. -/

section ParamEquiv

variable {M N H r a b : ℕ}

/-- `EuclideanSpace ℝ (Fin k)` transported along an equality of dimensions. Needed because
`q` and `g` are given by `elimQ`/`elimGauge` but packed as sums of block sizes. -/
@[expose] public noncomputable def euclCongr {k k' : ℕ} (h : k = k') :
    EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k') :=
  (EuclideanSpace.equiv (Fin k) ℝ).trans <|
    (LinearEquiv.funCongrLeft ℝ ℝ (finCongr h.symm)).toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin k') ℝ).symm

public theorem analyticOnNhd_euclCongr {k k' : ℕ} (h : k = k')
    (s : Set (EuclideanSpace ℝ (Fin k))) : AnalyticOnNhd ℝ (euclCongr h) s :=
  fun x _ => (euclCongr h).toContinuousLinearMap.analyticAt x

/-- **The hidden-index equivalence, in the shape `PairSpace` uses.** -/
@[expose] public def elimHiddenIdx (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) :
    ((Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b))) ≃ Fin H :=
  (elimHiddenEquiv haH hra hrb hab).symm

/-- **The input-index equivalence.** -/
@[expose] public def elimInputIdx (haN : a ≤ N) (hra : r ≤ a) :
    ((Fin r ⊕ Fin (a - r)) ⊕ Fin (elimN N a)) ≃ Fin N :=
  (elimInputEquiv haN hra).symm

/-- **The output-index equivalence.** -/
@[expose] public def elimOutputIdx (hbM : b ≤ M) (hrb : r ≤ b) :
    ((Fin r ⊕ Fin (b - r)) ⊕ Fin (elimP M b)) ≃ Fin M :=
  (elimOutputEquiv hbM hrb).symm

/-- **The parameter-space equivalence.** `PairSpace` at the six `Fin` index types is
`ParamSpace M N H`, as a continuous linear equivalence — so `chart_transport` applies to it and
every clause proved over `Sum` types moves across.

This is the first of the two equivalences `IsEliminationChart` needs. The second, into
`ChartSpace q p h n g`, additionally has to pack the nine coordinate blocks into the four
components of `ChartSpace`, using `elimQ_eq_add` and `elimGauge_eq_add`; it is not built
here. -/
@[expose] public noncomputable def elimParamEquiv (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M) :
    (Matrix ((Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b)))
        ((Fin r ⊕ Fin (a - r)) ⊕ Fin (elimN N a)) ℝ ×
      Matrix ((Fin r ⊕ Fin (b - r)) ⊕ Fin (elimP M b))
        ((Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b))) ℝ) ≃L[ℝ]
      (Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ) :=
  (matrixReindexEquiv (elimHiddenIdx haH hra hrb hab) (elimInputIdx haN hra)).prodCongr
    (matrixReindexEquiv (elimOutputIdx hbM hrb) (elimHiddenIdx haH hra hrb hab))

public theorem analyticOnNhd_elimParamEquiv (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (s : Set (Matrix ((Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b)))
        ((Fin r ⊕ Fin (a - r)) ⊕ Fin (elimN N a)) ℝ ×
      Matrix ((Fin r ⊕ Fin (b - r)) ⊕ Fin (elimP M b))
        ((Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b))) ℝ)) :
    AnalyticOnNhd ℝ (elimParamEquiv haH hra hrb hab haN hbM) s :=
  fun x _ => (elimParamEquiv haH hra hrb hab haN hbM).toContinuousLinearMap.analyticAt x

end ParamEquiv


/-! ## Packing matrices into a single Euclidean coordinate

`ChartSpace` holds the `u`-block and the gauge block as `EuclideanSpace ℝ (Fin q)` and
`EuclideanSpace ℝ (Fin g)`, while the chart produces them as two and five matrices
respectively. These are the packings, each a continuous linear equivalence, so they cost
nothing in the analyticity clauses. -/

section Packing

/-- Two matrices as one Euclidean coordinate of the summed dimension. This is the `u`-block:
`U` of shape `M × a` followed by `T′` of shape `b × n`, into `ℝ^{Ma + bn}`. -/
@[expose] public noncomputable def matrixPairEucl (m₁ n₁ m₂ n₂ : ℕ) :
    (Matrix (Fin m₁) (Fin n₁) ℝ × Matrix (Fin m₂) (Fin n₂) ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m₁ * n₁ + m₂ * n₂)) :=
  (((matrixEuclEquiv m₁ n₁).symm).prodCongr ((matrixEuclEquiv m₂ n₂).symm)).trans
    (euclSplitEquiv (m₁ * n₁) (m₂ * n₂)).symm

/-- Three matrices as one Euclidean coordinate. -/
@[expose] public noncomputable def matrixTripleEucl (m₁ n₁ m₂ n₂ m₃ n₃ : ℕ) :
    (Matrix (Fin m₁) (Fin n₁) ℝ × Matrix (Fin m₂) (Fin n₂) ℝ ×
        Matrix (Fin m₃) (Fin n₃) ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m₁ * n₁ + (m₂ * n₂ + m₃ * n₃))) :=
  (ContinuousLinearEquiv.refl ℝ (Matrix (Fin m₁) (Fin n₁) ℝ)).prodCongr
      (matrixPairEucl m₂ n₂ m₃ n₃) |>.trans <|
    (((matrixEuclEquiv m₁ n₁).symm).prodCongr
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (m₂ * n₂ + m₃ * n₃))))).trans
        (euclSplitEquiv (m₁ * n₁) (m₂ * n₂ + m₃ * n₃)).symm

/-- Four matrices as one Euclidean coordinate. -/
@[expose] public noncomputable def matrixQuadEucl (m₁ n₁ m₂ n₂ m₃ n₃ m₄ n₄ : ℕ) :
    (Matrix (Fin m₁) (Fin n₁) ℝ × Matrix (Fin m₂) (Fin n₂) ℝ ×
        Matrix (Fin m₃) (Fin n₃) ℝ × Matrix (Fin m₄) (Fin n₄) ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m₁ * n₁ + (m₂ * n₂ + (m₃ * n₃ + m₄ * n₄)))) :=
  (ContinuousLinearEquiv.refl ℝ (Matrix (Fin m₁) (Fin n₁) ℝ)).prodCongr
      (matrixTripleEucl m₂ n₂ m₃ n₃ m₄ n₄) |>.trans <|
    (((matrixEuclEquiv m₁ n₁).symm).prodCongr
      (ContinuousLinearEquiv.refl ℝ
        (EuclideanSpace ℝ (Fin (m₂ * n₂ + (m₃ * n₃ + m₄ * n₄)))))).trans
      (euclSplitEquiv (m₁ * n₁) (m₂ * n₂ + (m₃ * n₃ + m₄ * n₄))).symm

/-- **Five matrices as one Euclidean coordinate**: the gauge block. Print's `g` is the sum of
the five block sizes `a²`, `(H−a)a`, `(a−r)n`, `M(b−r)` and `bh`, in that order. -/
@[expose] public noncomputable def matrixQuintEucl (m₁ n₁ m₂ n₂ m₃ n₃ m₄ n₄ m₅ n₅ : ℕ) :
    (Matrix (Fin m₁) (Fin n₁) ℝ × Matrix (Fin m₂) (Fin n₂) ℝ ×
        Matrix (Fin m₃) (Fin n₃) ℝ × Matrix (Fin m₄) (Fin n₄) ℝ ×
        Matrix (Fin m₅) (Fin n₅) ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m₁ * n₁ + (m₂ * n₂ + (m₃ * n₃ + (m₄ * n₄ + m₅ * n₅))))) :=
  (ContinuousLinearEquiv.refl ℝ (Matrix (Fin m₁) (Fin n₁) ℝ)).prodCongr
      (matrixQuadEucl m₂ n₂ m₃ n₃ m₄ n₄ m₅ n₅) |>.trans <|
    (((matrixEuclEquiv m₁ n₁).symm).prodCongr
      (ContinuousLinearEquiv.refl ℝ
        (EuclideanSpace ℝ (Fin (m₂ * n₂ + (m₃ * n₃ + (m₄ * n₄ + m₅ * n₅))))))).trans
      (euclSplitEquiv (m₁ * n₁) (m₂ * n₂ + (m₃ * n₃ + (m₄ * n₄ + m₅ * n₅)))).symm

public theorem analyticOnNhd_matrixPairEucl (m₁ n₁ m₂ n₂ : ℕ)
    (s : Set (Matrix (Fin m₁) (Fin n₁) ℝ × Matrix (Fin m₂) (Fin n₂) ℝ)) :
    AnalyticOnNhd ℝ (matrixPairEucl m₁ n₁ m₂ n₂) s :=
  fun x _ => (matrixPairEucl m₁ n₁ m₂ n₂).toContinuousLinearMap.analyticAt x

public theorem analyticOnNhd_matrixQuintEucl (m₁ n₁ m₂ n₂ m₃ n₃ m₄ n₄ m₅ n₅ : ℕ)
    (s : Set (Matrix (Fin m₁) (Fin n₁) ℝ × Matrix (Fin m₂) (Fin n₂) ℝ ×
      Matrix (Fin m₃) (Fin n₃) ℝ × Matrix (Fin m₄) (Fin n₄) ℝ ×
      Matrix (Fin m₅) (Fin n₅) ℝ)) :
    AnalyticOnNhd ℝ (matrixQuintEucl m₁ n₁ m₂ n₂ m₃ n₃ m₄ n₄ m₅ n₅) s :=
  fun x _ =>
    (matrixQuintEucl m₁ n₁ m₂ n₂ m₃ n₃ m₄ n₄ m₅ n₅).toContinuousLinearMap.analyticAt x

end Packing


/-! ## The coordinate equivalence

The second of the two equivalences `chart_transport` consumes. Unlike the parameter side it is
not a plain reindexing: `ChartSpace q p h n g` groups the nine blocks as

    (u-block : ℝ^q) × (Y₀ : p × h) × (S_Z : h × n) × (gauge : ℝ^g),

so the nine-fold product has to be regrouped, each block reindexed to `Fin`-shaped matrices,
and the two Euclidean groups packed. The counts `q = Ma + bn` and `g = a² + (H−a)a + (a−r)n +
M(b−r) + bh` are `elimQ_eq_add` and `elimGauge_eq_add`, transported by `euclCongr`. -/

section CoordEquiv

variable {M N H r a b : ℕ}

/-- `Fin r ⊕ Fin (a − r) ≃ Fin a`. -/
@[expose] public def elimAIdx (hra : r ≤ a) : (Fin r ⊕ Fin (a - r)) ≃ Fin a :=
  (finSplit hra).symm

/-- `Fin r ⊕ Fin (b − r) ≃ Fin b`. -/
@[expose] public def elimBIdx (hrb : r ≤ b) : (Fin r ⊕ Fin (b - r)) ≃ Fin b :=
  (finSplit hrb).symm

/-- `Fin (b − r) ⊕ Fin h ≃ Fin (H − a)`, the lower half of the hidden splitting. -/
@[expose] public def elimHTailIdx (haH : a ≤ H) (hrb : r ≤ b) (hab : a + b ≤ H + r) :
    (Fin (b - r) ⊕ Fin (elimH H r a b)) ≃ Fin (H - a) :=
  ((finSplit (show b - r ≤ H - a by omega)).trans
    (Equiv.sumCongr (Equiv.refl _)
      (finCongr (show H - a - (b - r) = elimH H r a b by unfold elimH; omega)))).symm

/-- `g` as the right-associated sum of the five gauge block sizes, the shape
`matrixQuintEucl` produces. -/
public theorem elimGauge_eq_add' (M N H r a b : ℕ) :
    elimGauge M N H r a b =
      a * a + ((H - a) * a + ((a - r) * elimN N a + (M * (b - r) + b * elimH H r a b))) := by
  rw [elimGauge_eq_add]
  omega

/-- Regrouping a nine-fold product as `(A × B) × C × D × (E × F × G × H × I)`, the shape
`ChartSpace` asks for. Purely structural: both directions are `rfl` on components. -/
@[expose] public def prodRegroup9 (A B C D E F G I K : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [AddCommGroup F] [AddCommGroup G] [AddCommGroup I] [AddCommGroup K]
    [Module ℝ A] [Module ℝ B] [Module ℝ C] [Module ℝ D] [Module ℝ E] [Module ℝ F]
    [Module ℝ G] [Module ℝ I] [Module ℝ K]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace I]
    [TopologicalSpace K] :
    (A × B × C × D × E × F × G × I × K) ≃L[ℝ] ((A × B) × C × D × (E × F × G × I × K)) where
  toFun x := ((x.1, x.2.1), x.2.2.1, x.2.2.2.1,
    (x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2))
  invFun y := (y.1.1, y.1.2, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1,
    y.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end CoordEquiv


/-! ## The packings are isometries

`comparisonGerm` is `‖u‖² + ‖Y₀S_Z‖²_F`, with `u` the *packed* `u`-block, while Step 7's `NF`
is `‖U‖²_F + ‖T′‖²_F + ‖Y₀S_Z‖²_F`. The two agree only because the packing preserves the sum of
squares — it is a reindexing of coordinates, so it does. That is not automatic from the
packings being linear equivalences, and it is what these lemmas supply.

Without them the comparability clause of `HasEliminationChartAt` could not be read off Step 7:
`chart_transport` moves the *shape* of a chart across an equivalence, but the germ is measured
by a norm, and only an isometry leaves that alone. -/

section Isometry

/-- **The matrix packing preserves the sum of squares.** `‖·‖²` on
`EuclideanSpace ℝ (Fin (m*n))` is the Frobenius square of the matrix it packs. -/
public theorem norm_sq_matrixEuclEquiv_symm (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(matrixEuclEquiv m n).symm A‖ ^ 2 = frobeniusSq A := by
  rw [EuclideanSpace.real_norm_sq_eq, frobeniusSq]
  have hcoord : ∀ k : Fin (m * n),
      ((matrixEuclEquiv m n).symm A) k
        = A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := fun _ => rfl
  calc ∑ k : Fin (m * n), ((matrixEuclEquiv m n).symm A) k ^ 2
      = ∑ k : Fin (m * n),
          A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 ^ 2 := by
        exact Finset.sum_congr rfl fun k _ => by rw [hcoord k]
    _ = ∑ p : Fin m × Fin n, A p.1 p.2 ^ 2 := by
        refine (Fintype.sum_equiv finProdFinEquiv _ _ fun p => ?_).symm
        rw [finProdFinEquiv.symm_apply_apply]
    _ = ∑ i, ∑ j, A i j ^ 2 := by
        rw [← Finset.sum_product']
        rfl

/-- **The block packing preserves the sum of squares**, so splitting a Euclidean coordinate in
two adds the squared norms. -/
public theorem norm_sq_euclSplitEquiv_symm (k₁ k₂ : ℕ) (x : EuclideanSpace ℝ (Fin k₁))
    (y : EuclideanSpace ℝ (Fin k₂)) :
    ‖(euclSplitEquiv k₁ k₂).symm (x, y)‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  have hcoord : ∀ k : Fin (k₁ + k₂),
      ((euclSplitEquiv k₁ k₂).symm (x, y)) k
        = Sum.elim (fun i => x i) (fun i => y i) (finSumFinEquiv.symm k) := fun _ => rfl
  calc ∑ k : Fin (k₁ + k₂), ((euclSplitEquiv k₁ k₂).symm (x, y)) k ^ 2
      = ∑ k : Fin (k₁ + k₂),
          Sum.elim (fun i => x i) (fun i => y i) (finSumFinEquiv.symm k) ^ 2 :=
        Finset.sum_congr rfl fun k _ => by rw [hcoord k]
    _ = ∑ s : Fin k₁ ⊕ Fin k₂,
          Sum.elim (fun i => x i) (fun i => y i) s ^ 2 := by
        refine (Fintype.sum_equiv finSumFinEquiv _ _ fun s => ?_).symm
        rw [finSumFinEquiv.symm_apply_apply]
    _ = (∑ i, x i ^ 2) + ∑ i, y i ^ 2 := by rw [Fintype.sum_sum_type]; rfl

/-- **The `u`-block packing is an isometry.** `‖u‖² = ‖U‖²_F + ‖T′‖²_F`, which is exactly the
first two terms of print's `NF`. This is the identity that lets Step 7's conclusion be read as
a statement about `comparisonGerm`. -/
public theorem norm_sq_matrixPairEucl (m₁ n₁ m₂ n₂ : ℕ) (A : Matrix (Fin m₁) (Fin n₁) ℝ)
    (B : Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖matrixPairEucl m₁ n₁ m₂ n₂ (A, B)‖ ^ 2 = frobeniusSq A + frobeniusSq B := by
  show ‖(euclSplitEquiv (m₁ * n₁) (m₂ * n₂)).symm
      ((matrixEuclEquiv m₁ n₁).symm A, (matrixEuclEquiv m₂ n₂).symm B)‖ ^ 2 = _
  rw [norm_sq_euclSplitEquiv_symm, norm_sq_matrixEuclEquiv_symm,
    norm_sq_matrixEuclEquiv_symm]

/-- `euclCongr` is an isometry too, so transporting the dimension does not move the germ. -/
public theorem norm_sq_euclCongr {k k' : ℕ} (h : k = k') (x : EuclideanSpace ℝ (Fin k)) :
    ‖euclCongr h x‖ ^ 2 = ‖x‖ ^ 2 := by
  subst h
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl fun i _ => by rfl

end Isometry


end AISafetyAtlas.SingularLearning
