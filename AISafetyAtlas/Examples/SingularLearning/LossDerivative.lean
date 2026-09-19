module

public import AISafetyAtlas.SingularLearning.LossDerivative

/-!
# Worked models for the derivatives of the reduced-rank loss

`LossDerivative.lean` proves that `pairLoss` is `C^∞` and computes its first two derivatives.
Every statement there is a universally quantified identity, so each one is true of a loss no
model satisfies unless a model is exhibited.  This file exhibits two, both at the smallest
shape `M = N = H = 1`, and both at a **critical** point, since criticality is the hypothesis the
splitting step consumes.

The two models are chosen to separate the two summands of the Hessian:

* `Φ = 1`, `(A, B) = (0, 0)`: the residual is `-1` and the Gauss–Newton term vanishes, so the
  Hessian is carried entirely by the residual term and is **negative** in the diagonal
  direction `(1, 1)` — the critical point is a saddle, not a minimum.
* `Φ = 1`, `(A, B) = (1, 1)`: the residual is `0` and the residual term vanishes, so the Hessian
  is carried entirely by the Gauss–Newton term and is **positive** there.

Both points satisfy the two criticality equations, so `fderiv_pairLoss_eq_zero_of` applies to
each, and the numbers come out with opposite signs.  That is what makes the residual term of
`fderiv_fderiv_pairLoss_apply` non-vacuous: it is not a term that could have been dropped.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

open scoped ContDiff Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The `1 × 1` target of both models. -/
@[expose] public noncomputable def target : Matrix (Fin 1) (Fin 1) ℝ := 1

/-! ## The rank-deficient critical point, where the residual carries the Hessian -/

/-- The loss at the origin is the squared norm of the target. -/
public theorem pairLoss_zero : pairLoss target ((0 : Matrix (Fin 1) (Fin 1) ℝ),
    (0 : Matrix (Fin 1) (Fin 1) ℝ)) = 1 := by
  simp [pairLoss, frobeniusSq, target, Matrix.one_apply]

/-- The origin satisfies the first criticality equation. -/
public theorem crit_zero_left :
    (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *
      ((0 : Matrix (Fin 1) (Fin 1) ℝ) * (0 : Matrix (Fin 1) (Fin 1) ℝ) - target) = 0 := by
  simp

/-- The origin satisfies the second criticality equation. -/
public theorem crit_zero_right :
    ((0 : Matrix (Fin 1) (Fin 1) ℝ) * (0 : Matrix (Fin 1) (Fin 1) ℝ) - target) *
      (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ = 0 := by
  simp

/-- **The origin is a critical point of the loss**, so `fderiv_pairLoss_eq_zero_of` has a
model. -/
public theorem fderiv_pairLoss_zero :
    fderiv ℝ (pairLoss target) ((0 : Matrix (Fin 1) (Fin 1) ℝ),
      (0 : Matrix (Fin 1) (Fin 1) ℝ)) = 0 :=
  fderiv_pairLoss_eq_zero_of target 0 0 crit_zero_left crit_zero_right

/-- **The Hessian at the origin is negative in the direction `(1, 1)`.**  The Gauss–Newton term
is zero because `A` and `B` are, so the value `-4` is the residual term alone.  A critical point
of the reduced-rank loss can therefore be a saddle, which is what the splitting step of
MAIS-O77(b) has to contend with. -/
public theorem fderiv_fderiv_pairLoss_zero :
    fderiv ℝ (fderiv ℝ (pairLoss target)) ((0 : Matrix (Fin 1) (Fin 1) ℝ),
        (0 : Matrix (Fin 1) (Fin 1) ℝ)) (1, 1) (1, 1) = -4 := by
  rw [fderiv_fderiv_pairLoss_apply]
  simp [froIP, target, Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply]
  norm_num

/-! ## The zero-residual critical point, where Gauss–Newton carries the Hessian -/

/-- At `(1, 1)` the residual vanishes, so the loss is zero. -/
public theorem pairLoss_one : pairLoss target ((1 : Matrix (Fin 1) (Fin 1) ℝ),
    (1 : Matrix (Fin 1) (Fin 1) ℝ)) = 0 := by
  simp [pairLoss, target]

/-- **The Hessian at `(1, 1)` is positive in the direction `(1, 1)`.**  Here the residual term
is zero and the value `8` is the Gauss–Newton term alone. -/
public theorem fderiv_fderiv_pairLoss_one :
    fderiv ℝ (fderiv ℝ (pairLoss target)) ((1 : Matrix (Fin 1) (Fin 1) ℝ),
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) (1, 1) (1, 1) = 8 := by
  rw [fderiv_fderiv_pairLoss_apply]
  simp [froIP, target, Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply]
  norm_num

/-! ## The smoothness statement is inhabited -/

/-- `contDiff_pairLoss` applied at the shape both models use. -/
public theorem contDiff_pairLoss_one_one_one :
    ContDiff ℝ ∞ (pairLoss target :
      Matrix (Fin 1) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ → ℝ) :=
  contDiff_pairLoss target

end AISafetyAtlas.Examples.SingularLearning
