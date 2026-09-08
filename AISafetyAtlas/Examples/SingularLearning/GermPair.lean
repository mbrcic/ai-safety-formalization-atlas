module

public import AISafetyAtlas.SingularLearning.GermPair
public import AISafetyAtlas.Examples.SingularLearning.SylvesterPair

/-!
# Worked models for the indefinite form plus a free-block germ

`hasLocalVolumeOrder_abs_matrixQuadForm_add_germ` carries seven hypotheses — a
symmetric matrix, a nonvanishing determinant, one vector of each sign, and a
continuous germ vanishing at the origin — and a theorem whose hypotheses no model
satisfies is a valid theorem about nothing.  This file exhibits models.

Three things are checked here that the general statement cannot check for itself:

* **The germ is genuinely arbitrary.**  Two germs are instantiated on the same
  quadratic block, one even (`ζ ↦ ‖ζ‖²`) and one odd (`ζ ↦ ζ 0`).  The odd one
  matters: it takes both signs arbitrarily close to the origin, so the band
  `|Q(ξ) + g(ζ)| ≤ ε` is not a perturbation of a sublevel set of `|Q|`.
* **The congruence does real work.**  `hyperbolic4` is not diagonal, so the
  linear change of coordinates `exists_model_congruence` produces is not the
  identity and not a permutation.  A statement proved only at diagonal matrices
  would be a statement about `modelBandForm` with extra notation.
* **Both branches of the congruence are reachable.**  `minkowski4` has signature
  `(3,1)` and is carried by the first branch; `negMinkowski4` is its negation,
  signature `(1,3)`, and is carried by the second.  That the second is *forced*
  there is Sylvester's inertia argument in `GermPair`'s module header, which is
  prose rather than a checked declaration; what this file checks is that the
  route through the second branch closes.

`minkowski4`, its symmetry, its determinant and its two sign witnesses are reused
from `Examples.SingularLearning.SylvesterPair` rather than restated.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open scoped Matrix

/-! ## The two germs on the free block

`s = 1`, so the free block is a line.  Both germs are continuous and vanish at
the origin, which is everything the theorem asks of them.
-/

/-- The even germ `ζ ↦ ‖ζ‖²`. -/
@[expose] public noncomputable def evenGerm (ζ : EuclideanSpace ℝ (Fin 1)) : ℝ := ‖ζ‖ ^ 2

/-- The odd germ `ζ ↦ ζ 0`.  Unlike `evenGerm` this changes sign in every
neighbourhood of the origin, so the band it produces is not a deformation of a
sublevel set of the quadratic part alone. -/
@[expose] public noncomputable def oddGerm (ζ : EuclideanSpace ℝ (Fin 1)) : ℝ := ζ 0

public theorem continuous_evenGerm : Continuous evenGerm := by
  unfold evenGerm
  exact continuous_norm.pow 2

public theorem evenGerm_zero : evenGerm 0 = 0 := by simp [evenGerm]

public theorem continuous_oddGerm : Continuous oddGerm := by
  unfold oddGerm
  exact (EuclideanSpace.proj (0 : Fin 1)).continuous

public theorem oddGerm_zero : oddGerm 0 = 0 := by simp [oddGerm]

/-! ## The diagonal model: signature `(3,1)` in dimension four -/

/-- **The `(3,1)` form plus an even germ on a line.**  Every hypothesis of
`hasLocalVolumeOrder_abs_matrixQuadForm_add_germ` is discharged at an explicit
matrix and an explicit germ. -/
public theorem hasLocalVolumeOrder_minkowski4_add_evenGerm :
    HasLocalVolumeOrder
      (fun w : EuclideanSpace ℝ (Fin (4 + 1)) =>
        |matrixQuadForm minkowski4 ((euclideanProdEquiv 4 1).symm w).1
          + evenGerm (((euclideanProdEquiv 4 1).symm w).2)|)
      0 1 1 :=
  hasLocalVolumeOrder_abs_matrixQuadForm_add_germ (by norm_num) minkowski4 minkowski4_isSymm
    (by rw [minkowski4_det]; norm_num)
    ⟨spaceWitness, by rw [matrixQuadForm_spaceWitness]; norm_num⟩
    ⟨timeWitness, by rw [matrixQuadForm_timeWitness]; norm_num⟩
    evenGerm continuous_evenGerm evenGerm_zero

/-- **The `(3,1)` form plus an odd germ on a line.**  Same quadratic block, a
germ that takes both signs arbitrarily close to the origin. -/
public theorem hasLocalVolumeOrder_minkowski4_add_oddGerm :
    HasLocalVolumeOrder
      (fun w : EuclideanSpace ℝ (Fin (4 + 1)) =>
        |matrixQuadForm minkowski4 ((euclideanProdEquiv 4 1).symm w).1
          + oddGerm (((euclideanProdEquiv 4 1).symm w).2)|)
      0 1 1 :=
  hasLocalVolumeOrder_abs_matrixQuadForm_add_germ (by norm_num) minkowski4 minkowski4_isSymm
    (by rw [minkowski4_det]; norm_num)
    ⟨spaceWitness, by rw [matrixQuadForm_spaceWitness]; norm_num⟩
    ⟨timeWitness, by rw [matrixQuadForm_timeWitness]; norm_num⟩
    oddGerm continuous_oddGerm oddGerm_zero

/-! ## The negated model: signature `(1,3)`

Nothing about the conclusion changes, but the route through
`exists_model_congruence` does: with only one positive square, the block that the
band estimate needs to be two-dimensional is the negative one, so this instance is
carried by the second disjunct rather than the first.
-/

/-- The signature-`(1,3)` diagonal form in dimension four. -/
@[expose] public noncomputable def negMinkowski4 : Matrix (Fin 4) (Fin 4) ℝ := -minkowski4

public theorem negMinkowski4_isSymm : negMinkowski4.IsSymm := minkowski4_isSymm.neg

public theorem negMinkowski4_det : negMinkowski4.det = -1 := by
  rw [negMinkowski4, Matrix.det_neg, minkowski4_det]
  norm_num

public theorem matrixQuadForm_negMinkowski4 (z : EuclideanSpace ℝ (Fin 4)) :
    matrixQuadForm negMinkowski4 z = -matrixQuadForm minkowski4 z := by
  simp [matrixQuadForm, negMinkowski4, Matrix.neg_mulVec]

/-- **The `(1,3)` form plus an even germ on a line.**  The block with dimension at
least two is the negative one here, so this instance is carried by the second
disjunct of `exists_model_congruence`. -/
public theorem hasLocalVolumeOrder_negMinkowski4_add_evenGerm :
    HasLocalVolumeOrder
      (fun w : EuclideanSpace ℝ (Fin (4 + 1)) =>
        |matrixQuadForm negMinkowski4 ((euclideanProdEquiv 4 1).symm w).1
          + evenGerm (((euclideanProdEquiv 4 1).symm w).2)|)
      0 1 1 :=
  hasLocalVolumeOrder_abs_matrixQuadForm_add_germ (by norm_num) negMinkowski4
    negMinkowski4_isSymm (by rw [negMinkowski4_det]; norm_num)
    ⟨timeWitness, by rw [matrixQuadForm_negMinkowski4, matrixQuadForm_timeWitness]; norm_num⟩
    ⟨spaceWitness, by rw [matrixQuadForm_negMinkowski4, matrixQuadForm_spaceWitness]; norm_num⟩
    evenGerm continuous_evenGerm evenGerm_zero

/-! ## A model whose matrix is not diagonal

`hyperbolic4` is `2 ξ₀ ξ₁ + ξ₂² + ξ₃²`.  Its diagonal entries in the first block
are zero, so no rescaling of coordinates diagonalises it: the congruence produced
by `exists_model_congruence` mixes `ξ₀` and `ξ₁`.  Its signature is `(3,1)`,
which the two witnesses below exhibit.
-/

/-- A nondiagonal nondegenerate indefinite form: `2 ξ₀ ξ₁ + ξ₂² + ξ₃²`. -/
@[expose] public noncomputable def hyperbolic4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

public theorem hyperbolic4_isSymm : hyperbolic4.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolic4]

public theorem hyperbolic4_det : hyperbolic4.det = -1 := by
  simp [hyperbolic4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- A vector on which `hyperbolic4` is positive. -/
@[expose] public noncomputable def lightConeUp : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![1, 1, 0, 0]

/-- A vector on which `hyperbolic4` is negative. -/
@[expose] public noncomputable def lightConeDown : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![1, -1, 0, 0]

public theorem matrixQuadForm_lightConeUp :
    matrixQuadForm hyperbolic4 lightConeUp = 2 := by
  simp [matrixQuadForm, hyperbolic4, lightConeUp, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]
  norm_num

public theorem matrixQuadForm_lightConeDown :
    matrixQuadForm hyperbolic4 lightConeDown = -2 := by
  simp [matrixQuadForm, hyperbolic4, lightConeDown, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]
  norm_num

/-- **A nondiagonal indefinite form plus a germ on a line.**  The change of
coordinates `exists_model_congruence` produces here is not a rescaling of the
standard basis, so the general congruence is doing work no diagonal instance
would test. -/
public theorem hasLocalVolumeOrder_hyperbolic4_add_oddGerm :
    HasLocalVolumeOrder
      (fun w : EuclideanSpace ℝ (Fin (4 + 1)) =>
        |matrixQuadForm hyperbolic4 ((euclideanProdEquiv 4 1).symm w).1
          + oddGerm (((euclideanProdEquiv 4 1).symm w).2)|)
      0 1 1 :=
  hasLocalVolumeOrder_abs_matrixQuadForm_add_germ (by norm_num) hyperbolic4 hyperbolic4_isSymm
    (by rw [hyperbolic4_det]; norm_num)
    ⟨lightConeUp, by rw [matrixQuadForm_lightConeUp]; norm_num⟩
    ⟨lightConeDown, by rw [matrixQuadForm_lightConeDown]; norm_num⟩
    oddGerm continuous_oddGerm oddGerm_zero

end AISafetyAtlas.Examples.SingularLearning
