module

public import AISafetyAtlas.SingularLearning.IndefiniteBlockPair

/-!
# A worked model whose Hessian is degenerate off the indefinite block

`hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block` carries eight hypotheses — a
smooth loss, a chart splitting the parameter space, a symmetric block matrix with nonvanishing
determinant and one vector of each sign, a critical point, and the identification of that matrix
with the Hessian's block — and a theorem no model satisfies is a valid theorem about nothing.

The model here is

    `L (x, v) = x₀² + x₁² − x₂² + v₀⁴`   on   `ℝ³ × ℝ¹`,

read on `EuclideanSpace ℝ (Fin 4)` through the coordinate split, with base point the origin.

Two things are checked that the general statement cannot check for itself.

* The hypotheses are **jointly satisfiable**: the origin is critical, and the `ℝ³` block of the
  Hessian there is `diag (2, 2, −2)`, which is symmetric, has determinant `−8`, and takes both
  signs.
* The Hessian is **identically zero off that block** — the second conjunct of the final theorem
  — so the model is not secretly a Morse function whose pair any nondegenerate argument would
  deliver. That degeneracy is the whole reason the theorem quantifies over an arbitrary
  complementary germ, and a witness with a nondegenerate complement would not test it.

The matrix handed to the theorem is `diag (2, 2, −2)`, not `diag (1, 1, −1)`. That is the
normalisation the block hypothesis fixes: it names the Hessian block itself, and the second
derivative of `x ↦ x²` is `2`. The halving is done inside the theorem, where the splitting's
factor `2⁻¹` is spent.

Every derivative here goes through one generic family: for continuous linear functionals
`a b c q` on a normed space, the function `y ↦ a y * a y + b y * b y − c y * c y + q y ^ 4` has
first derivative vanishing at the origin and constant second derivative there, the quartic
contributing nothing. Instantiating that at the three coordinates of the first factor and the
one coordinate of the second is what makes the model cheap.
-/

noncomputable section

open scoped ContDiff

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-! ## The generic quadratic-plus-quartic family -/

section Family

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem hasFDerivAt_family (a b c q : X →L[ℝ] ℝ) (x : X) :
    HasFDerivAt (fun y : X ↦ a y * a y + b y * b y - c y * c y + q y ^ 4)
      ((2 * a x) • a + (2 * b x) • b - (2 * c x) • c + ((4 : ℝ) * q x ^ 3) • q) x := by
  have hsq : ∀ t : X →L[ℝ] ℝ, HasFDerivAt (fun y : X ↦ t y * t y) ((2 * t x) • t) x := by
    intro t
    have hsmul : (2 * t x) • t = t x • (t : X →L[ℝ] ℝ) + t x • t := by
      rw [two_mul, add_smul]
    rw [hsmul]
    exact t.hasFDerivAt.mul t.hasFDerivAt
  have h4 : HasFDerivAt (fun y : X ↦ q y ^ 4) (((4 : ℝ) * q x ^ 3) • q) x := by
    simpa using q.hasFDerivAt.pow 4
  exact (((hsq a).add (hsq b)).sub (hsq c)).add h4

private theorem contDiff_family (a b c q : X →L[ℝ] ℝ) :
    ContDiff ℝ ∞ fun y : X ↦ a y * a y + b y * b y - c y * c y + q y ^ 4 :=
  (((a.contDiff.mul a.contDiff).add (b.contDiff.mul b.contDiff)).sub
    (c.contDiff.mul c.contDiff)).add (q.contDiff.pow 4)

private theorem fderiv_family (a b c q : X →L[ℝ] ℝ) :
    fderiv ℝ (fun y : X ↦ a y * a y + b y * b y - c y * c y + q y ^ 4)
      = fun x ↦ (2 * a x) • a + (2 * b x) • b - (2 * c x) • c + ((4 : ℝ) * q x ^ 3) • q :=
  funext fun x ↦ (hasFDerivAt_family a b c q x).fderiv

private theorem fderiv_fderiv_family (a b c q : X →L[ℝ] ℝ) (hq0 : q 0 = 0) :
    fderiv ℝ (fderiv ℝ fun y : X ↦ a y * a y + b y * b y - c y * c y + q y ^ 4) 0
      = ((2 : ℝ) • a).smulRight a + ((2 : ℝ) • b).smulRight b
        - ((2 : ℝ) • c).smulRight c := by
  rw [fderiv_family]
  refine HasFDerivAt.fderiv ?_
  have hsq : ∀ t : X →L[ℝ] ℝ, HasFDerivAt (fun x : X ↦ (2 * t x) • (t : X →L[ℝ] ℝ))
      (((2 : ℝ) • t).smulRight t) 0 := by
    intro t
    simpa using (((2 : ℝ) • t).hasFDerivAt).smul_const (t : X →L[ℝ] ℝ)
  have hp : HasFDerivAt (fun x : X ↦ (4 : ℝ) * q x ^ 3) (0 : X →L[ℝ] ℝ) 0 := by
    have hp0 := ((q.hasFDerivAt (x := (0 : X))).pow 3).const_mul (4 : ℝ)
    rw [hq0] at hp0
    simpa using hp0
  have h4 : HasFDerivAt (fun x : X ↦ ((4 : ℝ) * q x ^ 3) • (q : X →L[ℝ] ℝ))
      (0 : X →L[ℝ] (X →L[ℝ] ℝ)) 0 := by
    simpa using hp.smul_const (q : X →L[ℝ] ℝ)
  have hres := (((hsq a).add (hsq b)).sub (hsq c)).add h4
  rw [add_zero] at hres
  exact hres

end Family

/-! ## The model -/

/-- The `i`-th coordinate of the three-dimensional block. -/
@[expose] public noncomputable def coordFst (i : Fin 3) :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The single coordinate of the complementary block. -/
@[expose] public noncomputable def coordSnd :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The model in chart coordinates: `F (x, v) = x₀² + x₁² − x₂² + v₀⁴`. -/
@[expose] public noncomputable def blockModel
    (y : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)) : ℝ :=
  coordFst 0 y * coordFst 0 y + coordFst 1 y * coordFst 1 y
    - coordFst 2 y * coordFst 2 y + coordSnd y ^ 4

public theorem blockModel_def : blockModel = fun y => coordFst 0 y * coordFst 0 y
    + coordFst 1 y * coordFst 1 y - coordFst 2 y * coordFst 2 y + coordSnd y ^ 4 := rfl

/-- The loss on the ambient space: the model read through the coordinate split. -/
@[expose] public noncomputable def blockModelLoss (y : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  blockModel ((splitCLE 3 1).symm y)

public theorem contDiff_blockModelLoss : ContDiff ℝ ∞ blockModelLoss :=
  (contDiff_family _ _ _ _).comp (splitCLE 3 1).symm.contDiff

/-- Read in the chart at the origin, the loss is the model itself. -/
public theorem blockModelLoss_chart :
    (fun p => blockModelLoss ((0 : EuclideanSpace ℝ (Fin 4)) + splitCLE 3 1 p)) = blockModel := by
  funext p
  rw [blockModelLoss, zero_add, ContinuousLinearEquiv.symm_apply_apply]

/-- **The Hessian block**: `diag (2, 2, −2)`, twice the signature matrix `diag (1, 1, −1)`.
The theorem's block hypothesis names the Hessian itself, so the factor two of a second
derivative is carried here rather than absorbed. -/
@[expose] public noncomputable def blockMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![2, 2, -2]

public theorem blockMatrix_isSymm : blockMatrix.IsSymm := Matrix.isSymm_diagonal _

public theorem blockMatrix_det_ne_zero : blockMatrix.det ≠ 0 := by
  rw [blockMatrix, Matrix.det_diagonal, Fin.prod_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

public theorem matrixQuadForm_blockMatrix (z : EuclideanSpace ℝ (Fin 3)) :
    matrixQuadForm blockMatrix z = 2 * z 0 ^ 2 + 2 * z 1 ^ 2 - 2 * z 2 ^ 2 := by
  simp [matrixQuadForm, blockMatrix, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three]
  ring

public theorem blockMatrix_pos : ∃ z, 0 < matrixQuadForm blockMatrix z := by
  refine ⟨EuclideanSpace.single 0 1, ?_⟩
  rw [matrixQuadForm_blockMatrix]
  norm_num [PiLp.single_apply, Fin.ext_iff]

public theorem blockMatrix_neg : ∃ z, matrixQuadForm blockMatrix z < 0 := by
  refine ⟨EuclideanSpace.single 2 1, ?_⟩
  rw [matrixQuadForm_blockMatrix]
  norm_num [PiLp.single_apply, Fin.ext_iff]

/-- The origin is a critical point of the model. -/
public theorem blockModel_crit : fderiv ℝ blockModel 0 = 0 := by
  rw [blockModel_def, fderiv_family]
  simp

/-- The `ℝ³` block of the Hessian at the origin is the polar form of `diag (2, 2, −2)`. -/
public theorem blockModel_hessian_block (x y : EuclideanSpace ℝ (Fin 3)) :
    blockW (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 1))
      (fderiv ℝ (fderiv ℝ blockModel) 0) x y = matrixQuadPolar blockMatrix x y := by
  rw [blockW_apply, blockModel_def, fderiv_fderiv_family _ _ _ _ (by simp [coordSnd])]
  simp [matrixQuadPolar, blockMatrix, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three,
    coordFst]
  ring

/-- **The Hessian vanishes identically off the block.**  The complementary direction carries a
pure quartic, so nothing about nondegeneracy is available there — which is precisely what the
theorem does not ask for. -/
public theorem blockModel_hessian_free (v v' : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ (fderiv ℝ blockModel) 0 (0, v) (0, v') = 0 := by
  rw [blockModel_def, fderiv_fderiv_family _ _ _ _ (by simp [coordSnd])]
  simp [coordFst]

/-- **The theorem fires on a loss whose Hessian is degenerate off the indefinite block**, which
is the case it exists for.  The second conjunct records that degeneracy: the complementary block
of the Hessian is not merely small, it is zero. -/
public theorem hasLocalVolumeOrder_centeredBandGerm_blockModelLoss :
    HasLocalVolumeOrder (centeredBandGerm blockModelLoss 0) 0 1 1
      ∧ ∀ v v' : EuclideanSpace ℝ (Fin 1),
          fderiv ℝ (fderiv ℝ blockModel) 0 (0, v) (0, v') = 0 := by
  refine ⟨?_, blockModel_hessian_free⟩
  refine hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block (m := 3) (d := 1) rfl
    (by norm_num) contDiff_blockModelLoss 0 (splitCLE 3 1) blockMatrix blockMatrix_isSymm
    blockMatrix_det_ne_zero blockMatrix_pos blockMatrix_neg ?_ ?_
  · rw [blockModelLoss_chart]; exact blockModel_crit
  · rw [blockModelLoss_chart]; exact blockModel_hessian_block

end AISafetyAtlas.Examples.SingularLearning

end
