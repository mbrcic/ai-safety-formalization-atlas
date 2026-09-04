module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.SingularLearning.AoyagiWatanabe
public import AISafetyAtlas.SingularLearning.ReducedRank

/-!
# Every feasible rank stratum is realised by an actual factorization

`ReducedRank.lean` proves one direction of the rank correspondence for the reduced-rank
regression fiber

    W₀ = {(A, B) : A ∈ ℝ^{H×N}, B ∈ ℝ^{M×H}, B * A = C} :

every actual factorization has arithmetically feasible ranks, the hard conjunct being
Sylvester's inequality. This module proves the **converse**, which is the direction that keeps
the O70 statement layer from being weaker than it looks.

## Why the converse matters

`IsO70FiberMinimumTable` and its neighbours quantify over admissible rank strata
`(M, N, H, r, a, b)`. Feasibility is pure arithmetic — `Feasible` mentions no matrix at all — so
a universally quantified statement about strata is only as strong as the supply of strata that
actually occur. If some feasible `(a, b)` were realised by no pair `(A, B)` with `B * A = C`,
then "for every feasible stratum …" would be quantifying partly over ghosts, and a claim about
the minimum of `λ(w)` over the *strata* would not be a claim about the minimum over the
*fiber*. `exists_factorization_of_feasible` removes that gap: over a fixed truth matrix `C` of
rank `r`, every feasible `(a, b)` is the rank pair of an actual point of `W₀`. Combined with
`ranks_feasible_of_factorization` this gives the exact image characterization
`exists_factorization_iff_feasible`.

Note that the realisation is **pointwise in `C`**, not merely "over some matrix of rank `r`":
the fiber-minimum statements are about one fixed truth, so a witness built over an auxiliary
matrix of the same rank would not close the gap.

## What had to be built

The pinned Mathlib has no rectangular rank normal form: `Matrix.exists_rank_normal_form` is for
square matrices, and its two-sided transformation mixes rows with columns, so it does not
restrict. `exists_rank_normal_form` here supplies `C = P * partialIdMatrix M N r * Q` with `P`,
`Q` invertible, from bases of `Fin N → ℝ` and `Fin M → ℝ` adapted to `ker` and `range` of the
associated linear map (`Module.Basis.sumQuot`, then the change-of-basis identity
`basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`).

Given the normal form the construction is explicit, and it is exactly the arithmetic of the
feasibility conjuncts. Write `c = b - r`. The factor `A` uses the middle coordinates
`[c, c + a)`: its rows `[c, c + r)` carry the row space of `C` and its rows `[c + r, c + a)` are
`a - r` further independent rows. The factor `B` uses the middle coordinates `[0, b)`: its
columns `[c, b)` carry the column space of `C` and its columns `[0, c)` are `b - r` further
independent columns. The overlap is precisely the `r` coordinates `[c, b)` that transmit `C`;
`B` annihilates `A`'s padding rows and `A` contributes nothing along `B`'s padding columns.
The two blocks fit inside the `H` middle coordinates exactly when `a + b ≤ H + r`, and each
padding fits its own shape exactly when `a ≤ min H N` and `b ≤ min H M`. That is why those are
the feasibility conditions.

**This module is pure linear algebra.** It says nothing about learning coefficients or which
stratum minimizes anything; it certifies that the strata quantified over are inhabited.
-/

namespace AISafetyAtlas.SingularLearning

open Module (finrank)

/-! ## Two counting utilities -/

/-- The `M × N` matrix with `1` in the first `r` diagonal positions and `0` elsewhere: the
right-hand side of the rank normal form below. -/
@[expose] public def partialIdMatrix (M N r : ℕ) : Matrix (Fin M) (Fin N) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then 1 else 0

/-- An initial segment of `Fin n` has the expected cardinality. Both padding blocks below have
a support of this shape, which is why their layout was chosen contiguous. -/
public theorem card_subtype_val_lt {n k : ℕ} (h : k ≤ n) :
    Fintype.card {j : Fin n // (j : ℕ) < k} = k := by
  have e : {j : Fin n // (j : ℕ) < k} ≃ Fin k :=
    { toFun := fun j => ⟨(j.1 : ℕ), j.2⟩
      invFun := fun i => ⟨⟨(i : ℕ), lt_of_lt_of_le i.2 h⟩, i.2⟩
      left_inv := fun j => by ext; rfl
      right_inv := fun i => by ext; rfl }
  simpa using Fintype.card_congr e

/-- Reading a rank off an orthogonality identity: if `Xᵀ * X` is diagonal then the rank of `X`
is the number of nonzero diagonal entries. Over `ℝ` this is `Matrix.rank_transpose_mul_self`
followed by `Matrix.rank_diagonal`, and it is how every padding block below is counted. -/
public theorem rank_eq_card_of_transpose_mul_self {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (h : X.transpose * X = Matrix.diagonal v) :
    X.rank = Fintype.card {j // v j ≠ 0} := by
  classical
  rw [← Matrix.rank_transpose_mul_self X, h, Matrix.rank_diagonal]

/-! ## Column-selection matrices -/

/-- The column-selection matrix `selCols m n g`: its `j`-th column is the standard basis vector
`e (g j)` when `g j < m`, and the zero column otherwise. Every padding factor below is of this
shape, so the rank count and the product rule are proved once here. -/
@[expose] public def selCols (m n : ℕ) (g : ℕ → ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = g (j : ℕ) then 1 else 0

public theorem selCols_ext {m n : ℕ} {g g' : ℕ → ℕ} (h : ∀ j : Fin n, g (j : ℕ) = g' (j : ℕ)) :
    selCols m n g = selCols m n g' := by
  ext i j
  simp [selCols, h j]

/-- `Xᵀ * X` for a column-selection matrix is diagonal: distinct nonzero columns are distinct
standard basis vectors, hence orthonormal. -/
public theorem transpose_mul_self_selCols {m n : ℕ} (g : ℕ → ℕ)
    (hinj : ∀ j j' : Fin n, g (j : ℕ) < m → g (j : ℕ) = g (j' : ℕ) → (j : ℕ) = (j' : ℕ)) :
    (selCols m n g).transpose * selCols m n g
      = Matrix.diagonal (fun j : Fin n => if g (j : ℕ) < m then (1 : ℝ) else 0) := by
  ext j j'
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [selCols, Matrix.transpose_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  by_cases hjm : g (j : ℕ) < m
  · have hcond : ∀ i : Fin m, ((i : ℕ) = g (j : ℕ)) = (i = ⟨g (j : ℕ), hjm⟩) := by
      intro i
      simp [Fin.ext_iff]
    simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hjj : j = j'
    · subst hjj
      simp [hjm]
    · rw [if_neg hjj, if_neg]
      exact fun h => hjj (Fin.ext (hinj j j' hjm h))
  · have hzero : ∀ i : Fin m, ¬ ((i : ℕ) = g (j : ℕ)) := fun i h => hjm (h ▸ i.2)
    simp only [hzero, if_false, Finset.sum_const_zero]
    simp [hjm]

/-- The rank of a column-selection matrix is the number of columns it does not kill. -/
public theorem rank_selCols {m n : ℕ} (g : ℕ → ℕ) (k : ℕ) (hk : k ≤ n)
    (hsupp : ∀ j : Fin n, g (j : ℕ) < m ↔ (j : ℕ) < k)
    (hinj : ∀ j j' : Fin n, g (j : ℕ) < m → g (j : ℕ) = g (j' : ℕ) → (j : ℕ) = (j' : ℕ)) :
    (selCols m n g).rank = k := by
  classical
  rw [rank_eq_card_of_transpose_mul_self _ _ (transpose_mul_self_selCols g hinj)]
  rw [← card_subtype_val_lt hk]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (by intro j; simp [← hsupp j]))

/-- Column-selection matrices compose: selecting columns twice selects the composite. -/
public theorem selCols_mul_selCols {m p n : ℕ} (gB gA : ℕ → ℕ) :
    selCols m p gB * selCols p n gA
      = selCols m n (fun j => if gA j < p then gB (gA j) else m) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [selCols, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  by_cases hA : gA (j : ℕ) < p
  · have hcond : ∀ x : Fin p, ((x : ℕ) = gA (j : ℕ)) = (x = ⟨gA (j : ℕ), hA⟩) := by
      intro x
      simp [Fin.ext_iff]
    simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_pos hA]
  · have hzero : ∀ x : Fin p, ¬ ((x : ℕ) = gA (j : ℕ)) := fun x h => hA (h ▸ x.2)
    simp only [hzero, if_false, Finset.sum_const_zero, if_neg hA]
    exact (if_neg (by omega)).symm

/-! ## The rectangular rank normal form -/

/-- **Rank normal form for a rectangular matrix.** Every `M × N` real matrix `C` of rank `r`
factors as `C = P * partialIdMatrix M N r * Q` with `P`, `Q` invertible square matrices.

Mathlib's `Matrix.exists_rank_normal_form` covers only square matrices, and its two-sided
transformation mixes rows and columns, so it does not restrict to the rectangular case. The
proof here is the textbook one: pick a basis of `Fin N → ℝ` adapted to `ker f` and a basis of
`Fin M → ℝ` adapted to `range f` (both via `Module.Basis.sumQuot`), in which the matrix of
`f = C.toLin` is the partial identity, and read off the two change-of-basis matrices. -/
public theorem exists_rank_normal_form {M N : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) :
    ∃ (P : Matrix (Fin M) (Fin M) ℝ) (Q : Matrix (Fin N) (Fin N) ℝ),
      IsUnit P.det ∧ IsUnit Q.det ∧ C = P * partialIdMatrix M N C.rank * Q := by
  classical
  set eN : Module.Basis (Fin N) ℝ (Fin N → ℝ) := Pi.basisFun ℝ (Fin N) with heN
  set eM : Module.Basis (Fin M) ℝ (Fin M → ℝ) := Pi.basisFun ℝ (Fin M) with heM
  set f : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ) := Matrix.toLin eN eM C with hf
  set r := C.rank with hrdef
  have hrange : finrank ℝ (LinearMap.range f) = r :=
    (Matrix.rank_eq_finrank_range_toLin C eM eN).symm
  have hdimN : finrank ℝ (Fin N → ℝ) = N := by simp
  have hdimM : finrank ℝ (Fin M → ℝ) = M := by simp
  have hnull : finrank ℝ (LinearMap.range f) + finrank ℝ (LinearMap.ker f) = N := by
    rw [LinearMap.finrank_range_add_finrank_ker f, hdimN]
  have hrN : r ≤ N := by omega
  have hrM : r ≤ M := by
    have := Submodule.finrank_le (LinearMap.range f)
    omega
  have hker : finrank ℝ (LinearMap.ker f) = N - r := by omega
  have hquotN : finrank ℝ ((Fin N → ℝ) ⧸ LinearMap.ker f) = r := by
    have := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
    omega
  have hquotM : finrank ℝ ((Fin M → ℝ) ⧸ LinearMap.range f) = M - r := by
    have := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
    omega
  -- Adapted bases: `bN` splits `Fin N → ℝ` as `ker f` plus a lift of the quotient, and `bM`
  -- splits `Fin M → ℝ` as `range f` plus a complement.
  set bK : Module.Basis (Fin (N - r)) ℝ (LinearMap.ker f) :=
    Module.finBasisOfFinrankEq ℝ _ hker with hbK
  set bQN : Module.Basis (Fin r) ℝ ((Fin N → ℝ) ⧸ LinearMap.ker f) :=
    Module.finBasisOfFinrankEq ℝ _ hquotN with hbQN
  set bW : Module.Basis (Fin r) ℝ (LinearMap.range f) := bQN.map f.quotKerEquivRange with hbW
  set bQM : Module.Basis (Fin (M - r)) ℝ ((Fin M → ℝ) ⧸ LinearMap.range f) :=
    Module.finBasisOfFinrankEq ℝ _ hquotM with hbQM
  set bN0 : Module.Basis (Fin (N - r) ⊕ Fin r) ℝ (Fin N → ℝ) :=
    Module.Basis.sumQuot bK bQN with hbN0
  set bM0 : Module.Basis (Fin r ⊕ Fin (M - r)) ℝ (Fin M → ℝ) :=
    Module.Basis.sumQuot bW bQM with hbM0
  set eqN : Fin (N - r) ⊕ Fin r ≃ Fin N :=
    (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega))) with heqN
  set eqM : Fin r ⊕ Fin (M - r) ≃ Fin M :=
    finSumFinEquiv.trans (finCongr (by omega)) with heqM
  set bN : Module.Basis (Fin N) ℝ (Fin N → ℝ) := bN0.reindex eqN with hbN
  set bM : Module.Basis (Fin M) ℝ (Fin M → ℝ) := bM0.reindex eqM with hbM
  have hD : LinearMap.toMatrix bN bM f = partialIdMatrix M N r := by
    ext i j
    rw [LinearMap.toMatrix_apply, partialIdMatrix, Matrix.of_apply, hbN,
      Module.Basis.reindex_apply]
    rcases lt_or_ge (j : ℕ) r with hj | hj
    · have hjr : eqN.symm j = Sum.inr ⟨(j : ℕ), hj⟩ := by
        rw [Equiv.symm_apply_eq]
        ext
        simp [heqN]
      have hfb : f (bN0 (Sum.inr ⟨(j : ℕ), hj⟩)) = (bW ⟨(j : ℕ), hj⟩ : Fin M → ℝ) := by
        rw [hbW, Module.Basis.map_apply, ← Module.Basis.sumQuot_inr bK bQN,
          LinearMap.quotKerEquivRange_apply_mk]
      rw [hjr, hfb, hbM, Module.Basis.repr_reindex_apply, hbM0,
        Module.Basis.sumQuot_repr_left, Finsupp.single_apply]
      have hiff : (Sum.inl (⟨(j : ℕ), hj⟩ : Fin r) = eqM.symm i) ↔ ((i : ℕ) = (j : ℕ)) := by
        rw [eq_comm, Equiv.symm_apply_eq]
        constructor
        · rintro rfl; simp [heqM]
        · intro h; ext; simp [heqM, h]
      by_cases h : (i : ℕ) = (j : ℕ)
      · rw [if_pos (hiff.mpr h), if_pos ⟨h, h ▸ hj⟩]
      · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg (fun hc => h hc.1)]
    · have hjr : eqN.symm j = Sum.inl ⟨(j : ℕ) - r, by omega⟩ := by
        rw [Equiv.symm_apply_eq]
        ext
        simp [heqN]
        omega
      rw [hjr, hbN0, Module.Basis.sumQuot_inl]
      have : f (bK ⟨(j : ℕ) - r, by omega⟩ : Fin N → ℝ) = 0 :=
        (bK ⟨(j : ℕ) - r, by omega⟩).2
      rw [this, map_zero, Finsupp.coe_zero, Pi.zero_apply, if_neg]
      rintro ⟨h1, h2⟩
      omega
  refine ⟨eM.toMatrix bM, bN.toMatrix eN, ?_, ?_, ?_⟩
  · have : Invertible (eM.toMatrix bM) := Module.Basis.invertibleToMatrix eM bM
    exact Matrix.isUnit_det_of_invertible _
  · have : Invertible (bN.toMatrix eN) := Module.Basis.invertibleToMatrix bN eN
    exact Matrix.isUnit_det_of_invertible _
  · rw [← hD, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix, hf,
      LinearMap.toMatrix_toLin]

/-! ## Realising a feasible stratum -/

/-- The partial identity is a column-selection matrix: it keeps column `j` as `e j` for `j < r`
and kills the rest. This is the bridge between the normal form and the explicit factors. -/
public theorem partialIdMatrix_eq_selCols (M N r : ℕ) :
    partialIdMatrix M N r = selCols M N (fun j => if j < r then j else M) := by
  ext i j
  simp only [partialIdMatrix, selCols, Matrix.of_apply]
  split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)

/-- **Every feasible rank stratum is realised.** Over a fixed truth matrix `C` of rank `r`, and
for any `(a, b)` satisfying the arithmetic feasibility predicate, there is an actual point
`(A, B)` of the zero fiber `W₀ = {(A, B) : B * A = C}` with `rank A = a` and `rank B = b`.

Together with `ranks_feasible_of_factorization` (the converse, in `ReducedRank.lean`) this
identifies the image of `W₀` under `(A, B) ↦ (rank A, rank B)` with the feasibility set. -/
public theorem exists_factorization_of_feasible {M N H : ℕ}
    (C : Matrix (Fin M) (Fin N) ℝ) {a b : ℕ}
    (hfeas : Feasible M N H C.rank a b) :
    ∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = a ∧ B.rank = b := by
  obtain ⟨h1, h2, h3, h4⟩ := hfeas
  simp only [le_min_iff] at h1 h2 h3
  obtain ⟨hra, hrb⟩ := h1
  obtain ⟨haH, haN⟩ := h2
  obtain ⟨hbH, hbM⟩ := h3
  obtain ⟨P, Q, hP, hQ, hC⟩ := exists_rank_normal_form C
  set r := C.rank with hrdef
  set c := b - r with hcdef
  -- `A` carries the row space of `C` in its rows `[c, c + r)` and `a - r` further independent
  -- rows in `[c + r, c + a)`; `B` carries the column space in its columns `[c, b)` and `b - r`
  -- further independent columns in `[0, c)`. The `a + b ≤ H + r` conjunct is exactly what makes
  -- the two blocks fit inside the `H` middle coordinates.
  set gA : ℕ → ℕ := fun j => if j < a then j + c else H with hgA
  set gB : ℕ → ℕ := fun j => if j < c then j + r else if j < b then j - c else M with hgB
  have hmid : selCols M H gB * selCols H N gA = partialIdMatrix M N r := by
    rw [selCols_mul_selCols, partialIdMatrix_eq_selCols]
    refine selCols_ext ?_
    intro j
    simp only [hgA, hgB]
    split_ifs <;> omega
  refine ⟨selCols H N gA * Q, P * selCols M H gB, ?_, ?_, ?_⟩
  · rw [hC, ← hmid]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det Q _ hQ]
    refine rank_selCols gA a haN (fun j => ?_) (fun j j' hj hjj => ?_)
    · simp only [hgA]
      split_ifs <;> omega
    · simp only [hgA] at hj hjj
      split_ifs at hj hjj <;> omega
  · rw [Matrix.rank_mul_eq_right_of_isUnit_det P _ hP]
    refine rank_selCols gB b hbH (fun j => ?_) (fun j j' hj hjj => ?_)
    · simp only [hgB]
      split_ifs <;> omega
    · simp only [hgB] at hj hjj
      split_ifs at hj hjj <;> omega

/-- The image characterization of the stratum map: a rank pair `(a, b)` occurs on the zero fiber
`W₀ = {(A, B) : B * A = C}` if and only if it is arithmetically feasible over `rank C`.

The forward direction is `ranks_feasible_of_factorization` (`ReducedRank.lean`, Sylvester's
inequality); the backward direction is `exists_factorization_of_feasible`. -/
public theorem exists_factorization_iff_feasible {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (a b : ℕ) :
    (∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = a ∧ B.rank = b) ↔ Feasible M N H C.rank a b := by
  constructor
  · rintro ⟨A, B, hBA, rfl, rfl⟩
    exact ranks_feasible_of_factorization A B hBA
  · exact exists_factorization_of_feasible C

/-- The uniform witness the fiber-minimum statement uses: the stratum `(r, r)` is realised over
every truth matrix whose rank fits inside the hidden layer. -/
public theorem exists_factorization_rank_self {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (hH : C.rank ≤ H) :
    ∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = C.rank ∧ B.rank = C.rank :=
  exists_factorization_of_feasible C
    ⟨by simp, le_min hH (Matrix.rank_le_width C), le_min hH (Matrix.rank_le_height C), by omega⟩

/-- A stratum with `a > rank C`: as soon as one coordinate is left over in the hidden layer and
in the input, the fiber contains a point whose `A` carries a rank-raising padding row that `B`
annihilates. -/
public theorem exists_factorization_rank_succ {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (hH : C.rank + 1 ≤ H) (hN : C.rank + 1 ≤ N) :
    ∃ (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ),
      B * A = C ∧ A.rank = C.rank + 1 ∧ B.rank = C.rank :=
  exists_factorization_of_feasible C
    ⟨le_min (by omega) le_rfl, le_min hH hN,
      le_min (by omega) (Matrix.rank_le_height C), by omega⟩

/-! ## Worked examples -/

/-- The `(a, b) = (r, r)` witness, made explicit in the invertible case: for `C = 1` in
dimension `2`, `A = B = 1` is the realisation produced at the stratum `(2, 2) = (r, r)`. -/
example : ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1 = 1) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℝ).rank = (1 : Matrix (Fin 2) (Fin 2) ℝ).rank ∧
    (1 : Matrix (Fin 2) (Fin 2) ℝ).rank = 2 := by
  refine ⟨by simp, rfl, ?_⟩
  simp

/-- A stratum with `a > r`, explicitly: over the zero truth matrix (`r = 0`) the pair
`(A, B) = (1, 0)` sits in the stratum `(2, 0)`, which is feasible for `M = N = H = 2` because
`a + b = 2 ≤ H + r = 2`. The padding rows of `A` are exactly the rows `B` annihilates. -/
example : (0 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
    (1 : Matrix (Fin 2) (Fin 2) ℝ).rank = 2 ∧ (0 : Matrix (Fin 2) (Fin 2) ℝ).rank = 0 := by
  refine ⟨by simp, ?_, ?_⟩ <;> simp

/-- The same stratum obtained from the theorem rather than by hand, over the zero truth
matrix: `Feasible 2 2 2 0 2 0` holds, so the fiber over `C = 0` really does meet the stratum
`(a, b) = (2, 0)`. -/
example : ∃ (A B : Matrix (Fin 2) (Fin 2) ℝ),
    B * A = (0 : Matrix (Fin 2) (Fin 2) ℝ) ∧ A.rank = 2 ∧ B.rank = 0 := by
  refine exists_factorization_of_feasible (0 : Matrix (Fin 2) (Fin 2) ℝ) ?_
  rw [Matrix.rank_zero]
  exact ⟨by simp, by simp, by simp, by simp⟩

/-- A stratum with `b > r`, over a rank-deficient hidden layer: `H = 1` forces `a, b ≤ 1`, and
`(a, b) = (0, 1)` is feasible over the zero truth, realised inside a fiber whose products all
vanish. -/
example : ∃ (A : Matrix (Fin 1) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 1) ℝ),
    B * A = (0 : Matrix (Fin 2) (Fin 2) ℝ) ∧ A.rank = 0 ∧ B.rank = 1 := by
  refine exists_factorization_of_feasible (0 : Matrix (Fin 2) (Fin 2) ℝ) ?_
  rw [Matrix.rank_zero]
  exact ⟨by simp, by simp, by simp, by simp⟩


end AISafetyAtlas.SingularLearning
