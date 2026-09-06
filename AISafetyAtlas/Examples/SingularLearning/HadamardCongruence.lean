module

public import AISafetyAtlas.SingularLearning.HadamardCongruence

/-!
# Worked models for the parameterised congruence

Every statement in `AISafetyAtlas.SingularLearning.HadamardCongruence` is an existence statement
under hypotheses, and each set of hypotheses that could be jointly empty is witnessed here rather
than assumed to be satisfiable.

* The **congruence over an arbitrary parameter** is fired at `P = ℝ`, `E = ℝ` with the family
  `B p w w' = (1 + p ^ 2) * w * w'`, which genuinely moves with the parameter — a constant family
  would witness nothing, since the identity would already be a congruence for it.

* The **Morse–Bott normal form** is fired at `W = V = ℝ` with `f (η, ζ) = η * η`. This is the
  smallest function satisfying all three hypotheses at once: it vanishes on `{0} × V`, its
  `W`-derivative vanishes there, and its `W`-block Hessian at the origin is doubling, which is
  invertible. Without a witness of this shape the Morse–Bott statement would be a theorem about
  nothing — the three hypotheses could in principle contradict each other, and no other check in
  the repository would notice.

* The **finite-dimensional Morse lemma** is fired at `EuclideanSpace ℝ (Fin 1)` with the same
  square, to check that the classical nondegeneracy hypothesis — the Hessian form annihilating no
  nonzero vector — is dischargeable in the coordinates a matrix consumer works in.

The derivative computations all go through one generic square: for a continuous linear functional
`c`, the function `y ↦ c y * c y` has first derivative `(2 * c y) • c` and constant second
derivative `((2 : ℝ) • c).smulRight c`. Instantiating that at `c = ContinuousLinearMap.fst` on
`ℝ × ℝ` and at `c = EuclideanSpace.proj 0` on `EuclideanSpace ℝ (Fin 1)` is what makes the two
models cheap.
-/

noncomputable section

open scoped ContDiff

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

section Square

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The square of a continuous linear functional is differentiable, with the expected
derivative. -/
private theorem hasFDerivAt_sq (c : X →L[ℝ] ℝ) (x : X) :
    HasFDerivAt (fun y : X ↦ c y * c y) ((2 * c x) • c) x := by
  have hsmul : (2 * c x) • c = c x • (c : X →L[ℝ] ℝ) + c x • c := by
    rw [two_mul, add_smul]
  rw [hsmul]
  exact c.hasFDerivAt.mul c.hasFDerivAt

private theorem fderiv_sq (c : X →L[ℝ] ℝ) :
    fderiv ℝ (fun y : X ↦ c y * c y) = fun x ↦ (2 * c x) • c :=
  funext fun x ↦ (hasFDerivAt_sq c x).fderiv

private theorem fderiv_fderiv_sq (c : X →L[ℝ] ℝ) (x : X) :
    fderiv ℝ (fderiv ℝ fun y : X ↦ c y * c y) x = ((2 : ℝ) • c).smulRight c := by
  have hfun : (fun x : X ↦ (2 * c x) • (c : X →L[ℝ] ℝ))
      = ⇑(((2 : ℝ) • c).smulRight c) := by
    funext y
    simp
  rw [fderiv_sq, hfun]
  exact (ContinuousLinearMap.hasFDerivAt _).fderiv

private theorem contDiff_sq (c : X →L[ℝ] ℝ) : ContDiff ℝ ∞ fun y : X ↦ c y * c y :=
  c.contDiff.mul c.contDiff

/-- The same computations for a sum of two squares, which is the shape of the model with a
nonvanishing germ on the fibre. -/
private theorem fderiv_sq_add (c d : X →L[ℝ] ℝ) :
    fderiv ℝ (fun y : X ↦ c y * c y + d y * d y) = fun x ↦ (2 * c x) • c + (2 * d x) • d :=
  funext fun x ↦ ((hasFDerivAt_sq c x).add (hasFDerivAt_sq d x)).fderiv

private theorem fderiv_fderiv_sq_add (c d : X →L[ℝ] ℝ) (x : X) :
    fderiv ℝ (fderiv ℝ fun y : X ↦ c y * c y + d y * d y) x
      = ((2 : ℝ) • c).smulRight c + ((2 : ℝ) • d).smulRight d := by
  have hfun : (fun x : X ↦ (2 * c x) • (c : X →L[ℝ] ℝ) + (2 * d x) • d)
      = ⇑(((2 : ℝ) • c).smulRight c + ((2 : ℝ) • d).smulRight d) := by
    funext y
    simp
  rw [fderiv_sq_add, hfun]
  exact (ContinuousLinearMap.hasFDerivAt _).fderiv

private theorem contDiff_sq_add (c d : X →L[ℝ] ℝ) :
    ContDiff ℝ ∞ fun y : X ↦ c y * c y + d y * d y :=
  (c.contDiff.mul c.contDiff).add (d.contDiff.mul d.contDiff)

end Square

/-! ## The congruence over an arbitrary parameter -/

/-- Multiplication on `ℝ`, as an equivalence onto the dual. -/
private def qOne : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (fun _ ↦ by simp) (fun _ ↦ by ext; simp [mul_comm])

private theorem coe_qOne : (qOne : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = ContinuousLinearMap.mul ℝ ℝ := rfl

/-- Doubled multiplication on `ℝ`, as an equivalence onto the dual. This is the `W`-block Hessian
of the model loss below. -/
private def qTwo : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.equivOfInverse ((2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
    ((2⁻¹ : ℝ) • ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (fun _ ↦ by simp)
    (fun _ ↦ by ext; simp [mul_comm])

private theorem coe_qTwo :
    (qTwo : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = (2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ := rfl

/-- A family of symmetric forms on `ℝ` that genuinely moves with a real parameter. -/
private def movingForm (p : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (1 + p ^ 2) • ContinuousLinearMap.mul ℝ ℝ

private theorem movingForm_apply (p w w' : ℝ) :
    movingForm p w w' = (1 + p ^ 2) * (w * w') := by
  simp [movingForm]

private theorem contDiff_movingForm : ContDiff ℝ ∞ movingForm := by
  have hbdd : IsBoundedSMul ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) _ _ _
  exact (contDiff_const.add (contDiff_id.pow 2)).smul contDiff_const

private theorem symm_movingForm (p w w' : ℝ) : movingForm p w w' = movingForm p w' w := by
  simp only [movingForm_apply]
  ring

private theorem coe_qOne_eq : (qOne : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = movingForm 0 := by
  rw [coe_qOne]
  simp [movingForm]

/-- **The parameterised congruence fires**: over the parameter space `ℝ`, on the form space `ℝ`,
for a family that is not constant in the parameter. -/
example : ∃ (R : ℝ → (ℝ →L[ℝ] ℝ)) (U : Set ℝ), IsOpen U ∧ (0 : ℝ) ∈ U ∧ R 0 = 1 ∧
    ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧
    ∀ p ∈ U, ∀ w w', qOne (R p w) (R p w') = movingForm p w w' :=
  exists_congruence_of_symmetric_family_param contDiff_movingForm symm_movingForm 0 qOne
    coe_qOne_eq

/-- **The vendored congruence, with the invertibility clause, fires** on the same family read as
one indexed by its own form space. -/
example : ∃ (R : ℝ → (ℝ →L[ℝ] ℝ)) (U : Set ℝ), IsOpen U ∧ (0 : ℝ) ∈ U ∧ R 0 = 1 ∧
    ContDiffOn ℝ ∞ R U ∧ (∀ v ∈ U, (R v).IsInvertible) ∧
    ∀ v ∈ U, ∀ w w', qOne (R v w) (R v w') = movingForm v w w' :=
  exists_congruence_isInvertible_of_symmetric_family contDiff_movingForm symm_movingForm qOne
    coe_qOne_eq

/-- The constant identity family is invertible near any point: `exists_open_isInvertible` on its
smallest input. -/
example : ∃ U' : Set ℝ, U' ⊆ Set.univ ∧ IsOpen U' ∧ (0 : ℝ) ∈ U' ∧
    ∀ p ∈ U', ((1 : ℝ →L[ℝ] ℝ)).IsInvertible :=
  exists_open_isInvertible (R := fun _ : ℝ ↦ (1 : ℝ →L[ℝ] ℝ)) isOpen_univ (Set.mem_univ 0) rfl
    continuousOn_const

/-! ## The Morse–Bott normal form -/

/-- The model loss on `ℝ × ℝ`: the square of the first coordinate. Its critical set is the whole
second axis, on which it vanishes identically — the Morse–Bott setting. -/
private def sqFst (p : ℝ × ℝ) : ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ p * ContinuousLinearMap.fst ℝ ℝ ℝ p

private theorem sqFst_def : sqFst = fun p : ℝ × ℝ ↦
    ContinuousLinearMap.fst ℝ ℝ ℝ p * ContinuousLinearMap.fst ℝ ℝ ℝ p := rfl

/-- **The strict Morse–Bott normal form fires.** All three hypotheses hold simultaneously for
`sqFst`, so that statement is not empty. -/
example : ∃ (R : ℝ × ℝ → (ℝ →L[ℝ] ℝ)) (U : Set (ℝ × ℝ)), IsOpen U ∧ (0 : ℝ × ℝ) ∈ U ∧ R 0 = 1 ∧
    ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧
    ∀ p ∈ U, sqFst p = (2 : ℝ)⁻¹ * qTwo (R p p.1) (R p p.1) := by
  refine exists_partial_congruence_normal_form_of_vanishing (contDiff_sq _) (fun ζ ↦ by simp)
    (fun ζ η ↦ ?_) qTwo ?_
  · rw [fderiv_sq]
    simp
  · refine ContinuousLinearMap.ext fun w ↦ ContinuousLinearMap.ext fun w' ↦ ?_
    rw [blockW_apply, fderiv_fderiv_sq, coe_qTwo]
    simp
    ring

/-- A model with a **nonvanishing germ on the fibre**: `f (η, ζ) = η * η + ζ * ζ`. Its
`W`-directional derivative still vanishes along `{0} × ℝ`, and its `W`-block Hessian at the
origin is still doubling, but `f (0, ζ) = ζ * ζ` is not identically zero. -/
private def sumSq (p : ℝ × ℝ) : ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ p * ContinuousLinearMap.fst ℝ ℝ ℝ p +
    ContinuousLinearMap.snd ℝ ℝ ℝ p * ContinuousLinearMap.snd ℝ ℝ ℝ p

/-- The germ this model leaves on the fibre is genuinely nonzero, so the example below is not
secretly the strict case again. -/
example : sumSq (0, 1) = 1 := by simp [sumSq]

/-- **The Gromoll–Meyer form fires with a nonvanishing fibre germ.** -/
example : ∃ (R : ℝ × ℝ → (ℝ →L[ℝ] ℝ)) (U : Set (ℝ × ℝ)), IsOpen U ∧ (0 : ℝ × ℝ) ∈ U ∧ R 0 = 1 ∧
    ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧
    ∀ p ∈ U, sumSq p = sumSq (0, p.2) + (2 : ℝ)⁻¹ * qTwo (R p p.1) (R p p.1) := by
  refine exists_partial_congruence_normal_form (contDiff_sq_add _ _) (fun ζ η ↦ ?_) qTwo ?_
  · rw [fderiv_sq_add]
    simp
  · refine ContinuousLinearMap.ext fun w ↦ ContinuousLinearMap.ext fun w' ↦ ?_
    rw [blockW_apply, fderiv_fderiv_sq_add, coe_qTwo]
    simp
    ring

/-- The fibre chart of the normal form has the family as its derivative along the critical set;
with the invertibility clause this is what makes it a chart. -/
example {R : ℝ × ℝ → (ℝ →L[ℝ] ℝ)} {U : Set (ℝ × ℝ)} {ζ : ℝ}
    (hUopen : IsOpen U) (hmem : ((0 : ℝ), ζ) ∈ U) (hR : ContDiffOn ℝ ∞ R U) :
    HasFDerivAt (fun η : ℝ ↦ R (η, ζ) η) (R (0, ζ)) 0 :=
  hasFDerivAt_apply_fst hUopen hmem hR

/-- The partial averaged Hessian is what the normal form runs on, and at the origin it is the
`W`-block of the Hessian. -/
example : partialHessianAverage sqFst 0 = blockW ℝ ℝ (fderiv ℝ (fderiv ℝ sqFst) 0) :=
  partialHessianAverage_zero sqFst

/-- Its values are the averaged Hessian read on the `W` block. -/
example (p : ℝ × ℝ) (w w' : ℝ) : partialHessianAverage sqFst p w w'
    = TauCeti.hessianAverage sqFst (0, p.2) (p.1, 0) (w, 0) (w', 0) :=
  partialHessianAverage_apply sqFst p w w'

/-- It is smooth in the whole parameter, base point and displacement together. -/
example : ContDiff ℝ ∞ (partialHessianAverage sqFst) :=
  contDiff_partialHessianAverage (contDiff_sq _)

/-- And it is symmetric. -/
example (p : ℝ × ℝ) (w w' : ℝ) :
    partialHessianAverage sqFst p w w' = partialHessianAverage sqFst p w' w :=
  partialHessianAverage_symm ((contDiff_sq _).of_le (by decide)) p w w'

/-! ## The finite-dimensional Morse lemma -/

/-- The model on `EuclideanSpace ℝ (Fin 1)`: the square of the single coordinate. -/
private def sqCoord (v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  EuclideanSpace.proj (0 : Fin 1) v * EuclideanSpace.proj (0 : Fin 1) v

private theorem sqCoord_def : sqCoord = fun v : EuclideanSpace ℝ (Fin 1) ↦
    EuclideanSpace.proj (0 : Fin 1) v * EuclideanSpace.proj (0 : Fin 1) v := rfl

/-- **The `Fin`-coordinate Morse lemma fires**, with nondegeneracy discharged in the classical
form. -/
example : ∃ (φ : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (U : Set (EuclideanSpace ℝ (Fin 1))),
    IsOpen U ∧ 0 ∈ U ∧ φ 0 = 0 ∧ ContDiffOn ℝ ∞ φ U ∧
    HasFDerivAt φ (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) 0 ∧
    ∀ v ∈ U, sqCoord (0 + v) = sqCoord 0 +
      (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ sqCoord) 0 (φ v) (φ v) := by
  refine exists_normal_form_euclidean (contDiff_sq _) ?_ ?_
  · rw [sqCoord_def, fderiv_sq]
    simp
  · intro w hw
    have h := hw w
    rw [sqCoord_def, fderiv_fderiv_sq] at h
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul] at h
    have h0 : EuclideanSpace.proj (0 : Fin 1) w = 0 := by nlinarith [h]
    ext i
    fin_cases i
    exact h0

end AISafetyAtlas.Examples.SingularLearning

end
