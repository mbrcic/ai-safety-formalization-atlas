module

public import AISafetyAtlas.SingularLearning.SylvesterPair

/-!
# A worked nondegenerate indefinite form

`hasLocalVolumeOrder_abs_matrixQuadForm` carries four hypotheses — symmetry, a
nonvanishing determinant, and one vector of each sign — and a theorem whose
hypotheses no matrix satisfies is a valid theorem about nothing.  This file
exhibits a matrix satisfying all four.

The witness is the signature-`(3,1)` diagonal form in dimension four, which is
where the MAIS-O77(b) programme's own `(3,1)` shape lives.  Both sign witnesses
are exhibited by name and evaluated, so the file records not merely that the
hypotheses can be discharged but what discharges them.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open scoped Matrix

/-- The signature-`(3,1)` diagonal form in dimension four. -/
@[expose] public noncomputable def minkowski4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, 1, 1, -1]

public theorem minkowski4_isSymm : minkowski4.IsSymm := Matrix.isSymm_diagonal _

public theorem minkowski4_det : minkowski4.det = -1 := by
  simp [minkowski4, Matrix.det_diagonal, Fin.prod_univ_four]

/-- A vector in the positive block. -/
@[expose] public noncomputable def spaceWitness : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![1, 0, 0, 0]

/-- A vector in the negative block. -/
@[expose] public noncomputable def timeWitness : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![0, 0, 0, 1]

public theorem matrixQuadForm_spaceWitness :
    matrixQuadForm minkowski4 spaceWitness = 1 := by
  simp [matrixQuadForm, minkowski4, spaceWitness, Matrix.mulVec, dotProduct,
    Matrix.diagonal, Fin.sum_univ_four]

public theorem matrixQuadForm_timeWitness :
    matrixQuadForm minkowski4 timeWitness = -1 := by
  simp [matrixQuadForm, minkowski4, timeWitness, Matrix.mulVec, dotProduct,
    Matrix.diagonal, Fin.sum_univ_four]

/-- **The band pair of the `(3,1)` form.**  Every hypothesis of
`hasLocalVolumeOrder_abs_matrixQuadForm` is discharged at an explicit matrix, so
the general theorem is not vacuous. -/
public theorem hasLocalVolumeOrder_abs_minkowski4 :
    HasLocalVolumeOrder (fun z => |matrixQuadForm minkowski4 z|) 0 1 1 :=
  hasLocalVolumeOrder_abs_matrixQuadForm (by norm_num) minkowski4 minkowski4_isSymm
    (by rw [minkowski4_det]; norm_num)
    ⟨spaceWitness, by rw [matrixQuadForm_spaceWitness]; norm_num⟩
    ⟨timeWitness, by rw [matrixQuadForm_timeWitness]; norm_num⟩

end AISafetyAtlas.Examples.SingularLearning
