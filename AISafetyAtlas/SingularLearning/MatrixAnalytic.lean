module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix inversion is analytic on the nonsingular locus

This module supplies the one analytic prerequisite that `EliminationChart.lean` is missing for
Step 5 of Theorem 5.1 of the MAIS issue #3 candidate. The chart `Ψ` of that step is a rational
map of the entries of `(A, B)` with exactly two denominators, `det A₁₁` and `det P_{top}`; every
other component is polynomial. So the whole of Step 5's `AnalyticOnNhd` obligation reduces to
"a matrix inverse is analytic where the determinant does not vanish", which is what
`analyticAt_inv`, `analyticOnNhd_inv` and their composite forms `analyticAt_inv_comp`,
`analyticOnNhd_inv_comp` provide here.

## What Mathlib already had, and what it did not

Worth recording, because a survey of this corner is easy to get backwards in either direction.

Mathlib **has**:

* `analyticAt_inverse` and `analyticOnNhd_inverse` (`Mathlib/Analysis/Analytic/Constructions`):
  `Ring.inverse` is analytic at every unit of a normed algebra `A` with `HasSummableGeomSeries A`;
* `contDiffAt_ringInverse` (`Mathlib/Analysis/Calculus/ContDiff/Operations`), the `C^n` version;
* `analyticAt_inv` / `analyticOnNhd_inv` for a normed division ring (the *scalar* `x ↦ x⁻¹`);
* `Matrix.inv_def : A⁻¹ = Ring.inverse A.det • A.adjugate` and `Matrix.adjugate_apply`, i.e.
  the Cramer description of the inverse;
* `Continuous.matrix_det`, `Continuous.matrix_adjugate`, `continuousAt_matrix_inv`
  (`Mathlib/Topology/Instances/Matrix`) — the *topological* statements only.

Mathlib **lacks**: any analyticity or differentiability statement for `Matrix.det`,
`Matrix.adjugate` or `Matrix.inv` as maps of the entries. `Continuous.matrix_det` is where that
chain stops: the pinned Mathlib carries no `ContDiff` or `AnalyticAt` counterpart of it, and no
`AnalyticOnNhd … Matrix.inv`.

## Why not the Banach-algebra route

`Matrix m n α` carries **no global** normed instance in Mathlib — `NormedAddCommGroup
(Matrix (Fin n) (Fin n) ℝ)` does not synthesise — so `analyticOnNhd_inverse` cannot be applied
to matrices without first fixing a scoped instance, and the `NormedRing` one that route needs
(`Matrix.frobeniusNormedRing`) is a different structure from the `NormedAddCommGroup` that
`EliminationChart.lean` installs. This file therefore takes the Cramer route: `det` and
`adjugate` are polynomial in the entries, and only the scalar `x ↦ x⁻¹` is inverted. No
operator-norm machinery is used, and the argument is insensitive to which norm is installed.

## Instances

`Matrix.frobeniusNormedAddCommGroup` and `Matrix.frobeniusNormedSpace` are local instances, the
same pair `EliminationChart.lean` installs for the whole of its file, so the statements proved
here are the ones that file can apply. Nothing below depends on the choice: analyticity is a
property of the topology, and all norms on a finite-dimensional real vector space are equivalent.
-/

namespace AISafetyAtlas.SingularLearning

open scoped Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Entries

A matrix-valued map is analytic exactly when each of its entries is, in both directions. The
forward direction is the entry functional, a linear map on a finite-dimensional space; the
backward direction expands the matrix in the single-entry basis. -/

section Entries

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Reading off the `(i, j)` entry is analytic: it is a linear functional on a
finite-dimensional space. -/
public theorem analyticAt_matrix_entry (i : m) (j : n) (A : Matrix m n ℝ) :
    AnalyticAt ℝ (fun B : Matrix m n ℝ => B i j) A :=
  ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).analyticAt A

/-- Every entry of an analytic matrix-valued map is analytic. -/
public theorem analyticAt_entry_comp {f : E → Matrix m n ℝ} {x : E} (hf : AnalyticAt ℝ f x)
    (i : m) (j : n) : AnalyticAt ℝ (fun y => f y i j) x :=
  (analyticAt_matrix_entry i j (f x)).comp hf

/-- A matrix-valued map with analytic entries is analytic. Expand in the single-entry basis:
`M y = ∑ i, ∑ j, (M y i j) • Matrix.single i j 1`. -/
public theorem analyticAt_matrix_of_entries [DecidableEq m] [DecidableEq n]
    {M : E → Matrix m n ℝ} {x : E} (h : ∀ i j, AnalyticAt ℝ (fun y => M y i j) x) :
    AnalyticAt ℝ M x := by
  have hM : M = fun y => ∑ i, ∑ j, (M y i j) • Matrix.single i j (1 : ℝ) := by
    funext y
    conv_lhs => rw [Matrix.matrix_eq_sum_single (M y)]
    simp [Matrix.smul_single]
  rw [hM]
  exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _
    fun j _ => (h i j).smul analyticAt_const

end Entries

/-! ## Determinant and adjugate

Both are polynomial in the entries: the determinant is the Leibniz sum of signed products, and
each adjugate entry is a determinant of a row update. -/

section Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of a matrix-valued map with analytic entries is analytic: it is the finite
Leibniz sum `∑ σ, sign σ * ∏ i, M (σ i) i` of finite products of entries. -/
public theorem analyticAt_det_of_entries {M : E → Matrix n n ℝ} {x : E}
    (h : ∀ i j, AnalyticAt ℝ (fun y => M y i j) x) :
    AnalyticAt ℝ (fun y => (M y).det) x := by
  have hd : (fun y => (M y).det)
      = fun y => ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * ∏ i, M y (σ i) i := by
    funext y; exact Matrix.det_apply' (M y)
  rw [hd]
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => h (σ i) i)

/-- The determinant of an analytic matrix-valued map is analytic. -/
public theorem analyticAt_det_comp {f : E → Matrix n n ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).det) x :=
  analyticAt_det_of_entries fun i j => analyticAt_entry_comp hf i j

/-- `Matrix.det` is analytic on the whole matrix space. -/
public theorem analyticAt_det (A : Matrix n n ℝ) :
    AnalyticAt ℝ (fun B : Matrix n n ℝ => B.det) A :=
  analyticAt_det_comp (analyticAt_id (𝕜 := ℝ) (z := A))

/-- Each adjugate entry of a matrix-valued map with analytic entries is analytic:
`adjugate M i j` is the determinant of `M` with row `j` replaced by a constant vector. -/
public theorem analyticAt_adjugate_entry_of_entries {M : E → Matrix n n ℝ} {x : E}
    (h : ∀ i j, AnalyticAt ℝ (fun y => M y i j) x) (i j : n) :
    AnalyticAt ℝ (fun y => (M y).adjugate i j) x := by
  have ha : (fun y => (M y).adjugate i j)
      = fun y => ((M y).updateRow j (Pi.single i 1)).det := by
    funext y; exact Matrix.adjugate_apply (M y) i j
  rw [ha]
  refine analyticAt_det_of_entries fun k l => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hk : k = j
  · simp only [hk]; exact analyticAt_const
  · simp only [if_neg hk]; exact h k l

/-- The adjugate of a matrix-valued map with analytic entries is analytic. -/
public theorem analyticAt_adjugate_of_entries {M : E → Matrix n n ℝ} {x : E}
    (h : ∀ i j, AnalyticAt ℝ (fun y => M y i j) x) :
    AnalyticAt ℝ (fun y => (M y).adjugate) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_adjugate_entry_of_entries h i j

/-- The adjugate of an analytic matrix-valued map is analytic. -/
public theorem analyticAt_adjugate_comp {f : E → Matrix n n ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).adjugate) x :=
  analyticAt_adjugate_of_entries fun i j => analyticAt_entry_comp hf i j

end Polynomial

/-! ## The inverse

`A⁻¹ = (det A)⁻¹ • adjugate A`, so the only non-polynomial ingredient is the scalar inverse. -/

section Inverse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Cramer's rule over a field, with `Ring.inverse` on the scalar unfolded to `⁻¹`. -/
public theorem matrix_inv_eq_smul_adjugate (A : Matrix n n ℝ) :
    A⁻¹ = (A.det)⁻¹ • A.adjugate := by
  rw [Matrix.inv_def, congrFun Ring.inverse_eq_inv' A.det]

/-- **Analyticity of the matrix inverse, composite form.** If `f` is analytic at `x` and
`f x` is nonsingular, then `y ↦ (f y)⁻¹` is analytic at `x`. This is the form the chart of
Theorem 5.1 Step 5 applies, its `f` being the submatrix maps `A ↦ A₁₁` and `A ↦ P_{top}`. -/
public theorem analyticAt_inv_comp {f : E → Matrix n n ℝ} {x : E} (hf : AnalyticAt ℝ f x)
    (hdet : (f x).det ≠ 0) : AnalyticAt ℝ (fun y => (f y)⁻¹) x := by
  have hfun : (fun y => (f y)⁻¹) = fun y => ((f y).det)⁻¹ • (f y).adjugate := by
    funext y; exact matrix_inv_eq_smul_adjugate (f y)
  rw [hfun]
  exact ((analyticAt_det_comp hf).inv hdet).smul (analyticAt_adjugate_comp hf)

/-- **Matrix inversion is analytic at every nonsingular matrix.** -/
public theorem analyticAt_inv {A : Matrix n n ℝ} (hA : A.det ≠ 0) :
    AnalyticAt ℝ (fun B : Matrix n n ℝ => B⁻¹) A :=
  analyticAt_inv_comp (analyticAt_id (𝕜 := ℝ) (z := A)) hA

/-- **Matrix inversion is analytic on the nonsingular locus.** -/
public theorem analyticOnNhd_inv :
    AnalyticOnNhd ℝ (fun A : Matrix n n ℝ => A⁻¹) {A : Matrix n n ℝ | A.det ≠ 0} :=
  fun _ hA => analyticAt_inv hA

/-- The literal Theorem 5.1 form of `analyticOnNhd_inv`, at index type `Fin n`. -/
public theorem analyticOnNhd_inv_fin {n : ℕ} :
    AnalyticOnNhd ℝ (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹)
      {A : Matrix (Fin n) (Fin n) ℝ | A.det ≠ 0} :=
  analyticOnNhd_inv

/-- **Analyticity of the matrix inverse on a set, composite form.** -/
public theorem analyticOnNhd_inv_comp {f : E → Matrix n n ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hdet : ∀ x ∈ s, (f x).det ≠ 0) :
    AnalyticOnNhd ℝ (fun y => (f y)⁻¹) s :=
  fun x hx => analyticAt_inv_comp (hf x hx) (hdet x hx)

/-- `Matrix.det` is analytic on the whole matrix space, set form. -/
public theorem analyticOnNhd_det (s : Set (Matrix n n ℝ)) :
    AnalyticOnNhd ℝ (fun B : Matrix n n ℝ => B.det) s :=
  fun A _ => analyticAt_det A

end Inverse

/-! ## Submatrices

The two denominators of the chart of Theorem 5.1 Step 5 are `det A₁₁` and `det P_{top}`, the
determinants of *submatrices* of the parameter, so this is the shape the chart applies. -/

section Submatrix

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι] [DecidableEq ι]

/-- Taking a submatrix is analytic: each of its entries is an entry of the argument. -/
public theorem analyticAt_submatrix (r : ι → m) (c : ι → n) (A : Matrix m n ℝ) :
    AnalyticAt ℝ (fun B : Matrix m n ℝ => B.submatrix r c) A :=
  analyticAt_matrix_of_entries fun i j => analyticAt_matrix_entry (r i) (c j) A

/-- The inverse of a square submatrix is analytic wherever that submatrix is nonsingular. -/
public theorem analyticAt_submatrix_inv (r : ι → m) (c : ι → n) {A : Matrix m n ℝ}
    (hA : (A.submatrix r c).det ≠ 0) :
    AnalyticAt ℝ (fun B : Matrix m n ℝ => (B.submatrix r c)⁻¹) A :=
  analyticAt_inv_comp (analyticAt_submatrix r c A) hA

/-- The inverse of a square submatrix is analytic on any set where that submatrix is
nonsingular. -/
public theorem analyticOnNhd_submatrix_inv (r : ι → m) (c : ι → n) {s : Set (Matrix m n ℝ)}
    (hs : ∀ A ∈ s, (A.submatrix r c).det ≠ 0) :
    AnalyticOnNhd ℝ (fun B : Matrix m n ℝ => (B.submatrix r c)⁻¹) s :=
  fun A hA => analyticAt_submatrix_inv r c (hs A hA)

end Submatrix

end AISafetyAtlas.SingularLearning
