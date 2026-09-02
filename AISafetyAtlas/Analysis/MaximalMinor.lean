module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A linearly independent family has a nonzero maximal minor

If `card ι` vectors in `ℝⁿ` are linearly independent, some `card ι` of the `n`
coordinates already separate them: the square submatrix on those rows is
invertible.

Mathlib has this only for **square** matrices — `Matrix.linearIndependent_cols_iff_isUnit`
and `Matrix.linearIndependent_cols_of_det_ne_zero` — where there is nothing to
choose. The rectangular statement, which is the one a genericity argument needs
because it turns *"these vectors are independent"* into *"this explicit
polynomial in the entries is nonzero"*, is absent.

## Primary surface

| declaration | says |
|---|---|
| `exists_det_ne_zero_of_linearIndependent` | an independent family has a row selection on which its determinant is nonzero |

## Why it is wanted

A parametrized genericity argument has to produce, from a subspace condition, a
*polynomial* witness in the parameters — a rational or chart-based witness costs
parameters, and there are none to spare. A maximal minor is such a witness: it is
a determinant in the entries, so polynomial, and it detects exactly the failure of
independence.

## Provenance

Written to be lifted upstream: the declarations are named as Mathlib would name
them and the proofs use no atlas definitions. The proof is the textbook one —
column rank equals row rank, so the rows span the coordinate space, and
`Module.Basis.ofSpan` extracts a basis from among them.
-/

namespace AISafetyAtlas.Analysis

open Matrix Module

/-- **An independent family has a nonzero maximal minor.**

`f` selects `card ι` of the `n` coordinates, and on those coordinates the family
is already a basis. No injectivity hypothesis on `f` is needed or stated: the
determinant being nonzero forces it. -/
public theorem exists_det_ne_zero_of_linearIndependent {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {v : ι → (Fin n → ℝ)} (h : LinearIndependent ℝ v) :
    ∃ f : ι → Fin n, (Matrix.of fun a b : ι => v b (f a)).det ≠ 0 := by
  classical
  -- column rank equals row rank, so the coordinate functionals span
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range fun i : Fin n => (fun a : ι => v a i)) := by
    have hrow : LinearIndependent ℝ (Matrix.of fun a i => v a i : Matrix ι (Fin n) ℝ).row := h
    have hrank := hrow.rank_matrix
    have hcols := (Matrix.of fun a i => v a i : Matrix ι (Fin n) ℝ).rank_eq_finrank_span_cols
    have hfin : finrank ℝ (Submodule.span ℝ
        (Set.range (Matrix.of fun a i => v a i : Matrix ι (Fin n) ℝ).col)) = Fintype.card ι := by
      rw [← hcols, hrank]
    have htop : Submodule.span ℝ
        (Set.range (Matrix.of fun a i => v a i : Matrix ι (Fin n) ℝ).col) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hfin]
      simp
    rw [show (Set.range fun i : Fin n => (fun a : ι => v a i))
        = Set.range (Matrix.of fun a i => v a i : Matrix ι (Fin n) ℝ).col from rfl, htop]
  -- extract a basis from among the coordinate functionals
  set b := Module.Basis.ofSpan hspan with hb
  let e := (Pi.basisFun ℝ ι).indexEquiv b
  have hsub := Module.Basis.ofSpan_subset hspan
  have hmem : ∀ a : ι, ∃ i : Fin n, (fun a' : ι => v a' i) = b (e a) := fun a =>
    hsub (Set.mem_range_self _)
  choose f hf using hmem
  refine ⟨f, ?_⟩
  have hind : LinearIndependent ℝ (Matrix.of fun a b' : ι => v b' (f a)).row := by
    have hr : (Matrix.of fun a b' : ι => v b' (f a)).row = fun a => b (e a) := by
      funext a
      exact hf a
    rw [hr]
    exact b.linearIndependent.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hind
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  exact isUnit_iff_ne_zero.1 hu

/-! ## The minor as a linear functional

A genericity argument needs a *linear functional* vanishing on a subspace, and it
needs that functional to be polynomial in whatever parameters the subspace
depends on. Bordering a family `u` with a test vector and taking a maximal minor
supplies exactly that: it is linear in the test vector, it vanishes when the test
vector is in the family's span, and by `exists_det_ne_zero_of_linearIndependent`
it is nonzero for some row selection whenever it is not. -/

section MinorFunctional

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The family `u`, bordered by a test vector `y`, read on the rows `f`. -/
@[expose] public def borderedMinor (u : ι → (Fin n → ℝ)) (f : Option ι → Fin n)
    (y : Fin n → ℝ) : ℝ :=
  (Matrix.of fun a b : Option ι => (Option.elim b y u) (f a)).det

/-- Determinants are linear in a single column. Mathlib has the `add` and `smul`
forms; this is the finite-sum form they give by induction. -/
private theorem det_updateCol_sum_smul {κ : Type*} [Fintype κ] [DecidableEq κ]
    {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J ℝ) (b₀ : J) (c : κ → ℝ) (v : κ → J → ℝ) :
    (M.updateCol b₀ (fun a => ∑ j, c j * v j a)).det
      = ∑ j, c j * (M.updateCol b₀ (v j)).det := by
  classical
  have key : ∀ s : Finset κ, (M.updateCol b₀ (fun a => ∑ j ∈ s, c j * v j a)).det
      = ∑ j ∈ s, c j * (M.updateCol b₀ (v j)).det := by
    intro s
    induction s using Finset.induction with
    | empty =>
      simp only [Finset.sum_empty]
      exact Matrix.det_eq_zero_of_column_eq_zero b₀ (fun i => by simp)
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [show (fun x : J => c a * v a x + ∑ j ∈ s, c j * v j x)
          = (fun x : J => c a * v a x) + (fun x : J => ∑ j ∈ s, c j * v j x) from rfl,
        Matrix.det_updateCol_add,
        show (fun x : J => c a * v a x) = c a • v a from rfl,
        Matrix.det_updateCol_smul, ih]
  exact key Finset.univ

private theorem borderedMinor_eq_updateCol (u : ι → (Fin n → ℝ)) (f : Option ι → Fin n)
    (y : Fin n → ℝ) :
    borderedMinor u f y
      = ((Matrix.of fun a b : Option ι => (Option.elim b 0 u) (f a)).updateCol none
          (fun a => y (f a))).det := by
  classical
  refine congrArg Matrix.det ?_
  ext a b
  cases b with
  | none => simp
  | some j => simp

/-- **The minor is linear in the test vector.** -/
public theorem borderedMinor_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (u : ι → (Fin n → ℝ)) (f : Option ι → Fin n) (c : κ → ℝ) (g : κ → (Fin n → ℝ)) :
    borderedMinor u f (fun i => ∑ j, c j * g j i)
      = ∑ j, c j * borderedMinor u f (g j) := by
  classical
  rw [borderedMinor_eq_updateCol]
  simp_rw [borderedMinor_eq_updateCol]
  exact det_updateCol_sum_smul _ none c (fun j a => g j (f a))

/-- **The minor vanishes on the family's span.** -/
public theorem borderedMinor_eq_zero_of_mem_span (u : ι → (Fin n → ℝ)) (f : Option ι → Fin n)
    {y : Fin n → ℝ} (hy : y ∈ Submodule.span ℝ (Set.range u)) :
    borderedMinor u f y = 0 := by
  classical
  refine Matrix.det_eq_zero_of_not_linearIndependent_cols (fun hind => ?_)
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hy
  have hzero : ∑ b : Option ι,
      (Option.elim b (1 : ℝ) (fun j => -lam j)) •
        (Matrix.of fun a b : Option ι => (Option.elim b y u) (f a)).transpose b = 0 := by
    funext a
    rw [Fintype.sum_option]
    simp only [Option.elim, Matrix.transpose_apply, Matrix.of_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, one_mul, Finset.sum_apply, Pi.zero_apply]
    rw [← hlam]
    simp [Finset.sum_apply, mul_comm]
  have := Fintype.linearIndependent_iff.1 hind _ hzero none
  simp at this

/-- A determinant whose entries are `C¹` in a parameter is `C¹` in that
parameter: the determinant is a polynomial in the entries. -/
public theorem contDiff_det {J : Type*} [Fintype J] [DecidableEq J] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {M : E → Matrix J J ℝ}
    (h : ∀ a b, ContDiff ℝ 1 fun x => M x a b) :
    ContDiff ℝ 1 fun x => (M x).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.mul contDiff_const ?_
  exact contDiff_prod fun i _ => h _ _

/-- **The minor is `C¹` in whatever the family and the test vector depend on.**
This is the property that lets it serve as a normal vector in a parametrized
genericity argument. -/
public theorem contDiff_borderedMinor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ι → (Fin n → ℝ)} {y : E → (Fin n → ℝ)} (f : Option ι → Fin n)
    (hu : ∀ (i : ι) (r : Fin n), ContDiff ℝ 1 fun x => u x i r)
    (hy : ∀ r : Fin n, ContDiff ℝ 1 fun x => y x r) :
    ContDiff ℝ 1 fun x => borderedMinor (u x) f (y x) := by
  refine contDiff_det (M := fun x => Matrix.of fun a b : Option ι => (Option.elim b (y x) (u x)) (f a))
    (fun a b => ?_)
  cases b with
  | none => exact hy (f a)
  | some i => exact hu i (f a)

/-- **A finite family contains an independent subfamily with the same span**,
listed as a tuple so that it can index a square minor.

This is what lets a bordered minor be built from a rank-deficient family: border
the subfamily, not the family, and the span condition the minor has to vanish on
is unchanged. -/
public theorem exists_independent_spanning_subfamily {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (u : ι' → (Fin n → ℝ)) :
    ∃ (r : ℕ) (σ : Fin r → ι'), r ≤ Fintype.card ι' ∧ LinearIndependent ℝ (u ∘ σ) ∧
      Submodule.span ℝ (Set.range (u ∘ σ)) = Submodule.span ℝ (Set.range u) := by
  classical
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ℝ (Set.range u)
  have : Fintype b := Set.Finite.fintype (Set.Finite.subset (Set.finite_range u) hbsub)
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card b) ≃ b) := ⟨(Fintype.equivFin b).symm⟩
  have hpre : ∀ x : b, ∃ i : ι', u i = (x : Fin n → ℝ) := fun x => hbsub x.2
  choose g hg using hpre
  refine ⟨Fintype.card b, fun i => g (e i), ?_, ?_, ?_⟩
  · have hinj : Function.Injective (fun x : b => g x) := by
      intro x y hxy
      have hux : (x : Fin n → ℝ) = (y : Fin n → ℝ) := by
        rw [← hg x, ← hg y]
        exact congrArg u hxy
      exact Subtype.ext hux
    simpa using Fintype.card_le_of_injective _ hinj
  · have hcomp : (u ∘ fun i => g (e i)) = fun i => ((e i : b) : Fin n → ℝ) := by
      funext i
      exact hg (e i)
    rw [hcomp]
    exact hbind.comp e e.injective
  · have hr : Set.range (u ∘ fun i => g (e i)) = b := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        simp only [Function.comp_apply, hg (e i)]
        exact (e i).2
      · intro hy
        exact ⟨e.symm ⟨y, hy⟩, by simp [hg]⟩
    rw [hr, hbspan]

/-- **A bordered family that stays independent has a nonzero minor.** -/
public theorem exists_borderedMinor_ne_zero (u : ι → (Fin n → ℝ)) {y : Fin n → ℝ}
    (h : LinearIndependent ℝ (fun b : Option ι => Option.elim b y u)) :
    ∃ f : Option ι → Fin n, borderedMinor u f y ≠ 0 :=
  exists_det_ne_zero_of_linearIndependent h

end MinorFunctional

end AISafetyAtlas.Analysis
