module

public import AISafetyAtlas.SingularLearning.IndefiniteBand
public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Sylvester's law of inertia, wired to the band pair

`hasLocalVolumeOrder_abs_of_diagonal` computes the local band pair
of a germ *already presented* as the absolute value of a `±1`-weighted sum of
squares: its caller must supply the weight vector `w`, the coordinate equivalence
`f`, and the sign-sorting bijection `τ`.  Its docstring calls that "the interface
Sylvester's law of inertia feeds", and `QuadraticSplit`'s header records that
Mathlib has the law.  Neither module ever invoked it, so every caller was still
producing those three objects by hand.

This module invokes it.  What a caller actually holds is a symmetric matrix `K`
with `K.det ≠ 0` together with two vectors on which the form takes opposite
signs; the theorems here turn exactly that into the pair `(1,1)`.

The route is four steps, each a separate declaration so that a failure is
attributable:

* `associated_toQuadraticForm'` — for a **symmetric** `K`, the bilinear form
  `QuadraticMap.associated` recovers from `K`'s quadratic form is `K`'s own
  bilinear form.  Symmetry is needed and is not decoration: `associated` is the
  polarisation `(Q (x + y) - Q x - Q y) / 2`, which returns the *symmetrisation*
  of `K`, and only a symmetric `K` is its own symmetrisation.
* `separatingLeft_of_det_ne_zero` — nondegeneracy in the shape Mathlib's
  Sylvester lemma demands, discharged from `K.det ≠ 0` through
  `Matrix.separatingLeft_iff_det_ne_zero`.
* `exists_diagonal_coords` — Mathlib's
  `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`, repackaged from an
  isometric equivalence onto `weightedSumSquares` into the plain `(w, f)` pair
  the atlas interface reads.
* `hasLocalVolumeOrder_abs_of_diagonal_indefinite` — the counting step.  Both
  signs occur in `w` exactly because the form takes both signs, and that is what
  supplies the `NeZero p`, `NeZero q` instances the band estimate needs.

Indefiniteness is stated as *two witnesses*, not as a negation.  A germ only one
sign reaches is a definite form, whose sublevel sets are ellipsoids and whose
pair is not `(1,1)`; asking for the witnesses rather than for `¬ definite` keeps
the hypothesis constructive and keeps the examples file honest, since it must
exhibit both vectors.
-/

namespace AISafetyAtlas.SingularLearning

open QuadraticMap
open scoped Matrix

/-! ## Sylvester's law of inertia in atlas coordinates

Mathlib returns a `QuadraticMap.IsometryEquiv` onto `weightedSumSquares`; the
atlas interface reads a bare linear equivalence and a bare weight vector.  The
repackaging is the whole content of this section.
-/

/-- **Sylvester's law of inertia, in coordinates.**  A nondegenerate real
quadratic form on an `n`-dimensional space becomes a `±1`-weighted sum of squares
in some linear coordinates.

This is `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` with the
isometric equivalence unfolded into the `(w, f)` pair that
`hasLocalVolumeOrder_abs_of_diagonal` consumes, and with the dimension read as a
supplied `n` rather than as `Module.finrank ℝ M`. -/
public theorem exists_diagonal_coords {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (hdim : Module.finrank ℝ M = n)
    (Q : QuadraticForm ℝ M) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    ∃ (w : Fin n → ℝ) (f : M ≃ₗ[ℝ] (Fin n → ℝ)),
      (∀ i, w i = -1 ∨ w i = 1) ∧ ∀ x, Q x = ∑ i, w i * (f x i * f x i) := by
  subst hdim
  obtain ⟨w, hw, ⟨g⟩⟩ := Q.equivalent_one_neg_one_weighted_sum_squared hQ
  refine ⟨w, g.toLinearEquiv, hw, fun x => ?_⟩
  have h := g.map_app x
  rw [QuadraticMap.weightedSumSquares_apply] at h
  simp only [smul_eq_mul] at h
  exact h.symm

/-! ## The counting step

Sylvester alone does not give the band pair: a definite form is diagonalised too,
with all weights of one sign, and its germ has a different pair.  What rules that
out is that the form takes both signs, and the translation from "takes both
signs" to "both blocks are nonempty" is this lemma.
-/

/-- **A diagonalised form that takes both signs has band pair `(1,1)`.**

The two sign witnesses are what produce `NeZero p` and `NeZero q`: with `p = 0`
the sorted sum is `0 - ∑ (…)²`, nonpositive everywhere and so not positive at
`hpos`'s witness, and symmetrically for `q = 0`.  Nothing here needs the
witnesses to be near the origin — the germ is homogeneous, so one witness
anywhere fixes the sign along a whole ray. -/
public theorem hasLocalVolumeOrder_abs_of_diagonal_indefinite {n : ℕ} (h3 : 3 ≤ n)
    {Q : EuclideanSpace ℝ (Fin n) → ℝ} (w : Fin n → ℝ)
    (f : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ))
    (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hQ : ∀ x, Q x = ∑ i, w i * (f x i * f x i))
    (hpos : ∃ x, 0 < Q x) (hneg : ∃ x, Q x < 0) :
    HasLocalVolumeOrder (fun x => |Q x|) 0 1 1 := by
  classical
  obtain ⟨p, q, hpq, τ, hp1, hq1⟩ := exists_sign_split w hw
  have hsplit : ∀ x, Q x
      = (∑ a : Fin p, (f x (τ (Sum.inl a))) ^ 2)
        - ∑ b : Fin q, (f x (τ (Sum.inr b))) ^ 2 := by
    intro x
    rw [hQ x, sum_weighted_sq_eq_split w τ hp1 hq1 (f x)]
  have hpne : p ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hpos
    rw [hsplit x] at hx
    have hnn : (0:ℝ) ≤ ∑ b : Fin q, (f x (τ (Sum.inr b))) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_sub] at hx
    linarith
  have hqne : q ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hneg
    rw [hsplit x] at hx
    have hnn : (0:ℝ) ≤ ∑ a : Fin p, (f x (τ (Sum.inl a))) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at hx
    linarith
  have : NeZero p := ⟨hpne⟩
  have : NeZero q := ⟨hqne⟩
  exact hasLocalVolumeOrder_abs_of_diagonal hpq h3 w f τ hp1 hq1 hQ

/-! ## The matrix interface

The form a Stage 3 caller actually holds arrives as an explicit symmetric matrix,
so this is the interface the programme consumes.  Nondegeneracy arrives as
`K.det ≠ 0`, which is the form a caller can check by computation.
-/

/-- The quadratic form of a symmetric matrix, read on Euclidean space. -/
@[expose] public noncomputable def matrixQuadForm {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (fun i => z i) ⬝ᵥ (K *ᵥ (fun i => z i))

/-- `Matrix.toQuadraticForm'` evaluated, which Mathlib states only through the
bilinear map it is built from. -/
public theorem toQuadraticForm'_apply {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    Matrix.toQuadraticForm' K y = y ⬝ᵥ (K *ᵥ y) := by
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

/-- `matrixQuadForm` is `Matrix.toQuadraticForm'` read through the `ℓ²`
repackaging of the coordinate space. -/
public theorem matrixQuadForm_eq {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    matrixQuadForm K z
      = Matrix.toQuadraticForm' K (WithLp.linearEquiv 2 ℝ (Fin n → ℝ) z) := by
  rw [toQuadraticForm'_apply]
  rfl

/-- **The polarisation of a symmetric matrix form is the matrix form.**

`QuadraticMap.associated` returns the symmetrisation `(K + Kᵀ) / 2`, so this is
where `K.IsSymm` is spent: without it the nondegeneracy fed to Sylvester would be
that of the symmetrisation, which `K.det ≠ 0` does not imply. -/
public theorem associated_toQuadraticForm' {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : K.IsSymm) :
    QuadraticMap.associated (R := ℝ) (Matrix.toQuadraticForm' K)
      = Matrix.toLinearMap₂' ℝ K := by
  refine QuadraticMap.associated_left_inverse (S := ℝ) (fun x y => ?_)
  rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply']
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm.eq, dotProduct_comm]

/-- **Nondegeneracy in the shape Sylvester wants.**  `K.det ≠ 0` is the form a
caller can check; `SeparatingLeft` of the associated bilinear form is the form
`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` demands. -/
public theorem separatingLeft_of_det_ne_zero {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : K.IsSymm) (hdet : K.det ≠ 0) :
    (QuadraticMap.associated (R := ℝ) (Matrix.toQuadraticForm' K)).SeparatingLeft := by
  rw [associated_toQuadraticForm' K hsymm]
  exact (Matrix.separatingLeft_iff_det_ne_zero.mpr hdet).toLinearMap₂'

/-- **A nondegenerate indefinite quadratic form has band pair `(1,1)`** in
dimension at least three.

This is the theorem the Stage 3 programme needs, and the one that closes the gap
between `QuadraticSplit`'s header note and the tree: a caller supplies a
symmetric `K`, its nonvanishing determinant, and one vector of each sign, and
nothing else.  The weight vector, the coordinates and the sign-sorting bijection
`hasLocalVolumeOrder_abs_of_diagonal` reads are all produced here. -/
public theorem hasLocalVolumeOrder_abs_matrixQuadForm {n : ℕ} (h3 : 3 ≤ n)
    (K : Matrix (Fin n) (Fin n) ℝ) (hsymm : K.IsSymm) (hdet : K.det ≠ 0)
    (hpos : ∃ z, 0 < matrixQuadForm K z) (hneg : ∃ z, matrixQuadForm K z < 0) :
    HasLocalVolumeOrder (fun z => |matrixQuadForm K z|) 0 1 1 := by
  obtain ⟨w, g, hw, hgQ⟩ :=
    exists_diagonal_coords (M := Fin n → ℝ) (Module.finrank_fin_fun ℝ)
      (Matrix.toQuadraticForm' K) (separatingLeft_of_det_ne_zero K hsymm hdet)
  refine hasLocalVolumeOrder_abs_of_diagonal_indefinite h3 w
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans g) hw (fun z => ?_) hpos hneg
  rw [matrixQuadForm_eq K z, hgQ]
  rfl

/-! ## The bilinear-form interface

A caller holding the form as a symmetric bilinear map rather than as a matrix
reaches the same conclusion with no matrix in sight.  Nondegeneracy is stated
here in its own terms — every nonzero vector is separated by some other vector —
because that is `LinearMap.SeparatingLeft` unfolded, and a caller in this shape
has no determinant to appeal to.
-/

/-- **A nondegenerate indefinite symmetric bilinear form has band pair `(1,1)`**
in dimension at least three.

`hnd` is `LinearMap.SeparatingLeft B` written out.  Symmetry is spent recovering
`B` from the polarisation of `x ↦ B x x`, exactly as in the matrix case. -/
public theorem hasLocalVolumeOrder_abs_of_nondegenerate_indefinite {n : ℕ} (h3 : 3 ≤ n)
    (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hpos : ∃ x, 0 < B x x) (hneg : ∃ x, B x x < 0) :
    HasLocalVolumeOrder (fun x => |B x x|) 0 1 1 := by
  have hassoc : QuadraticMap.associated (R := ℝ)
      (LinearMap.BilinMap.toQuadraticMap B) = B :=
    QuadraticMap.associated_left_inverse (S := ℝ) hsymm
  have hsep : (QuadraticMap.associated (R := ℝ)
      (LinearMap.BilinMap.toQuadraticMap B)).SeparatingLeft := by
    rw [hassoc]; exact hnd
  obtain ⟨w, f, hw, hfQ⟩ :=
    exists_diagonal_coords (M := EuclideanSpace ℝ (Fin n)) finrank_euclideanSpace_fin
      (LinearMap.BilinMap.toQuadraticMap B) hsep
  exact hasLocalVolumeOrder_abs_of_diagonal_indefinite h3 w f hw hfQ hpos hneg

end AISafetyAtlas.SingularLearning
