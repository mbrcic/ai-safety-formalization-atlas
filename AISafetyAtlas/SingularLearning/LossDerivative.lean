module

public import AISafetyAtlas.SingularLearning.LossExpansion
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The reduced-rank loss as a smooth function, with its first two derivatives

Everything `LossExpansion.lean` proves about `L(A, B) = ‖B A − Φ‖²_F` is entrywise matrix
algebra: exact polynomial identities, no derivative taken anywhere.  The splitting step of
MAIS-O77(b) §7.4 cannot consume that form, because the splitting lemma
(`HadamardCongruence.lean`) states its hypotheses as `fderiv ℝ f p = 0` and as a condition on
`fderiv ℝ (fderiv ℝ f) p`.  This module supplies the missing layer: the same loss, presented as
a `C^∞` function on the product of matrix spaces, with both derivatives computed explicitly.

## Primary surface

| Declaration | Content |
|---|---|
| `pairLoss` | `L(A, B) = ‖B A − Φ‖²_F` as a function of the pair `(A, B)` |
| `contDiff_pairLoss` | `L` is `C^∞` |
| `pairLossDeriv`, `hasFDerivAt_pairLoss` | `dL(A,B)(X, Y) = 2⟨B A − Φ, B X + Y A⟩` |
| `fderiv_pairLoss_apply` | the same, as an evaluation of `fderiv` |
| `fderiv_pairLoss_eq_zero_of` | the criticality equations `Bᵀ R = 0`, `R Aᵀ = 0` kill `dL` |
| `fderiv_fderiv_pairLoss_apply` | the polar form of the Hessian |

The Hessian reads

    `d²L(A,B)[(X,Y)][(X',Y')] = 2(⟨B X + Y A, B X' + Y' A⟩ + ⟨B A − Φ, Y X' + Y' X⟩)`,

whose diagonal `(X', Y') = (X, Y)` is `2(‖B X + Y A‖²_F + 2⟨B A − Φ, Y X⟩)` — exactly twice the
quadratic part of the expansion `frobeniusSq_full_variation_of_critical` records.  The two
summands are the Gauss–Newton term and the residual term; the second is what makes a critical
point with a nonzero residual a saddle rather than a minimum, and it is the reason the
degenerate directions of the Hessian are not the fibre directions of the product map.

## Which norm, and why the instance question is not neutral here

`Matrix ι κ ℝ` carries **no** global normed instance in Mathlib, so one has to be installed to
speak of `ContDiff` at all.  This file installs `Matrix.frobeniusNormedAddCommGroup` and
`Matrix.frobeniusNormedSpace` as local instances, the same pair `MatrixAnalytic.lean` and
`EliminationChart.lean` use.  Under it `‖X‖² = frobeniusSq X`, so the norm and the pairing this
file differentiates are the same object.

Nothing proved here depends on that choice: all norms on a finite-dimensional real vector space
are equivalent, and `HasFDerivAt`, `fderiv` and `ContDiff` see only the topology and the linear
structure.  What does depend on it is *elaboration*: `Matrix` has its own `TopologicalSpace` and
`Module` instances, which do not reduce to the ones the Frobenius norm supplies, so a
`→L[ℝ]` type written plainly and a `→L[ℝ]` type produced by `fderiv` are defeq but not
syntactically equal.  The proofs below bridge that with `show`, which checks at default
transparency; `rw` and `simp`, which do not, will fail on such a goal.  A consumer of these
statements has to install the same two local instances.

Nothing here computes a volume order, and nothing here proves the splitting itself.
-/

namespace AISafetyAtlas.SingularLearning

open scoped ContDiff Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section Pairing

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Frobenius pairing as a bilinear map. -/
@[expose] public noncomputable def froIPₗ :
    Matrix ι κ ℝ →ₗ[ℝ] Matrix ι κ ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ froIP froIP_add_left
    (fun c X Y => by
      simpa [froIP_comm X Y, froIP_comm (c • X) Y] using froIP_smul_right c Y X)
    froIP_add_right
    (fun c X Y => froIP_smul_right c X Y)

/-- The Frobenius pairing as a continuous bilinear map. -/
@[expose] public noncomputable def froIPL :
    Matrix ι κ ℝ →L[ℝ] Matrix ι κ ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix ι κ ℝ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Matrix ι κ ℝ →L[ℝ] ℝ)).toLinearMap ∘ₗ froIPₗ)

@[simp] public theorem froIPL_apply (X Y : Matrix ι κ ℝ) : froIPL X Y = froIP X Y := rfl

end Pairing

section Mul

variable {M N H : ℕ}

/-- Matrix multiplication, with the arguments in the order the parameter pair carries them. -/
@[expose] public noncomputable def mulₗ :
    Matrix (Fin H) (Fin M) ℝ →ₗ[ℝ] Matrix (Fin N) (Fin H) ℝ →ₗ[ℝ] Matrix (Fin N) (Fin M) ℝ :=
  LinearMap.mk₂ ℝ (fun A B => B * A)
    (fun A₁ A₂ B => Matrix.mul_add B A₁ A₂)
    (fun c A B => Matrix.mul_smul B c A)
    (fun A B₁ B₂ => Matrix.add_mul B₁ B₂ A)
    (fun c A B => Matrix.smul_mul c B A)

@[expose] public noncomputable def mulL :
    Matrix (Fin H) (Fin M) ℝ →L[ℝ] Matrix (Fin N) (Fin H) ℝ →L[ℝ] Matrix (Fin N) (Fin M) ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix (Fin N) (Fin H) ℝ →ₗ[ℝ] Matrix (Fin N) (Fin M) ℝ)
          ≃ₗ[ℝ] (Matrix (Fin N) (Fin H) ℝ →L[ℝ] Matrix (Fin N) (Fin M) ℝ)).toLinearMap ∘ₗ mulₗ)

@[simp] public theorem mulL_apply (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) : mulL A B = B * A := rfl

end Mul

section Loss

variable {M N H : ℕ}

/-- The first-order motion of the product `B * A` under a variation `(X, Y)` of the pair. -/
@[expose] public noncomputable def mulDerivL (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) :
    (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) →L[ℝ] Matrix (Fin N) (Fin M) ℝ :=
  (mulL.flip B).comp (ContinuousLinearMap.fst ℝ _ _)
    + (mulL A).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] public theorem mulDerivL_apply (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) : mulDerivL A B (X, Y) = B * X + Y * A := rfl

/-- The reduced-rank regression loss as a function on the product of matrix spaces. -/
@[expose] public noncomputable def pairLoss (Φ : Matrix (Fin N) (Fin M) ℝ)
    (p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) : ℝ :=
  frobeniusSq (p.2 * p.1 - Φ)

/-- The differential of `pairLoss` at `(A, B)`. -/
@[expose] public noncomputable def pairLossDeriv (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ) :
    (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) →L[ℝ] ℝ :=
  (2 : ℝ) • ((froIPL (B * A - Φ)).comp (mulDerivL A B))

@[simp] public theorem pairLossDeriv_apply (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    pairLossDeriv Φ A B (X, Y) = 2 * froIP (B * A - Φ) (B * X + Y * A) := by
  simp only [pairLossDeriv, smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, mulDerivL_apply, froIPL_apply, smul_eq_mul]

public theorem hasFDerivAt_pairProd (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) :
    HasFDerivAt (fun p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ => p.2 * p.1)
      (mulDerivL A B) (A, B) := by
  have h := (ContinuousLinearMap.isBoundedBilinearMap (mulL (M := M) (N := N) (H := H))).hasFDerivAt
    (A, B)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  obtain ⟨X, Y⟩ := q
  show Y * A + B * X = B * X + Y * A
  exact add_comm _ _

/-! ## Smoothness -/

/-- **The loss is `C^∞`.**  It is a polynomial in the entries: the product map is a bounded
bilinear map, and the Frobenius square is the diagonal of one. -/
public theorem contDiff_pairLoss (Φ : Matrix (Fin N) (Fin M) ℝ) :
    ContDiff ℝ ∞
      (pairLoss Φ : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ → ℝ) := by
  have hprod : ContDiff ℝ ∞
      (fun p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ => p.2 * p.1) :=
    (ContinuousLinearMap.isBoundedBilinearMap (mulL (M := M) (N := N) (H := H))).contDiff
  have hres : ContDiff ℝ ∞
      (fun p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ => p.2 * p.1 - Φ) :=
    hprod.sub contDiff_const
  have hpair : ContDiff ℝ ∞
      (fun z : Matrix (Fin N) (Fin M) ℝ × Matrix (Fin N) (Fin M) ℝ => froIP z.1 z.2) :=
    (ContinuousLinearMap.isBoundedBilinearMap (froIPL (ι := Fin N) (κ := Fin M))).contDiff
  have h := hpair.comp (hres.prodMk hres)
  have hfun : (fun p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
      froIP (p.2 * p.1 - Φ) (p.2 * p.1 - Φ)) = pairLoss Φ := by
    funext p; exact froIP_self _
  rw [← hfun]
  exact h

/-! ## The first derivative -/

/-- **The differential of the loss.**  The chain rule through the product map: the residual
`B * A - Φ` moves by `B * X + Y * A`, and the Frobenius square differentiates to twice the
pairing against that motion. -/
public theorem hasFDerivAt_pairLoss (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ) :
    HasFDerivAt (pairLoss Φ) (pairLossDeriv Φ A B) (A, B) := by
  have hres : HasFDerivAt
      (fun p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ => p.2 * p.1 - Φ)
      (mulDerivL A B) (A, B) := (hasFDerivAt_pairProd A B).sub_const Φ
  have hb := ContinuousLinearMap.isBoundedBilinearMap (froIPL (ι := Fin N) (κ := Fin M))
  have h := (hb.hasFDerivAt (B * A - Φ, B * A - Φ)).comp (A, B) (hres.prodMk hres)
  have hfun : (fun p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
      froIP (p.2 * p.1 - Φ) (p.2 * p.1 - Φ)) = pairLoss Φ := by
    funext p; exact froIP_self _
  rw [← hfun]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  obtain ⟨X, Y⟩ := q
  show froIP (B * A - Φ) (B * X + Y * A) + froIP (B * X + Y * A) (B * A - Φ)
      = 2 * froIP (B * A - Φ) (B * X + Y * A)
  rw [froIP_comm (B * X + Y * A)]
  ring

/-- The differential, evaluated. -/
public theorem fderiv_pairLoss_apply (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    fderiv ℝ (pairLoss Φ) (A, B) (X, Y) = 2 * froIP (B * A - Φ) (B * X + Y * A) := by
  rw [(hasFDerivAt_pairLoss Φ A B).fderiv]
  exact pairLossDeriv_apply Φ A B X Y

/-- **The criticality equations kill the differential.** -/
public theorem fderiv_pairLoss_eq_zero_of (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (h₁ : Bᵀ * (B * A - Φ) = 0) (h₂ : (B * A - Φ) * Aᵀ = 0) :
    fderiv ℝ (pairLoss Φ) (A, B) = 0 := by
  refine ContinuousLinearMap.ext fun q => ?_
  obtain ⟨X, Y⟩ := q
  rw [zero_apply, fderiv_pairLoss_apply,
    froIP_residual_first_order A B Φ h₁ h₂ X Y, mul_zero]

/-! ## The second derivative -/

/-- **The polar form of the Hessian of the loss.**  Both arguments are variations of the pair:
`(X, Y)` is the direction the differential is differentiated in, `(X', Y')` the direction the
resulting functional is evaluated at.  The first summand is the Gauss–Newton term, the second
the residual term that a nonzero residual contributes. -/
public theorem fderiv_fderiv_pairLoss_apply (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X X' : Matrix (Fin H) (Fin M) ℝ) (Y Y' : Matrix (Fin N) (Fin H) ℝ) :
    fderiv ℝ (fderiv ℝ (pairLoss Φ)) (A, B) (X, Y) (X', Y')
      = 2 * (froIP (B * X + Y * A) (B * X' + Y' * A)
              + froIP (B * A - Φ) (Y * X' + Y' * X)) := by
  -- the differential is itself `C^∞`, hence differentiable
  have hcd := (contDiff_pairLoss (H := H) Φ).fderiv_right (m := ∞) (by simp)
  have hF := (hcd.differentiable (by simp) (A, B)).hasFDerivAt
  -- evaluating a differential at a fixed direction is a continuous linear operation
  have h0 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ
      ((X', Y') : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ))).comp (A, B) hF
  have h1 : HasFDerivAt
      (fun q : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
        fderiv ℝ (pairLoss Φ) q (X', Y'))
      ((ContinuousLinearMap.apply ℝ ℝ
          ((X', Y') : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ)).comp
        (fderiv ℝ (fderiv ℝ (pairLoss Φ)) (A, B))) (A, B) := h0
  -- and it is the explicit cubic polynomial the first derivative computes to
  have hfun : (fun q : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
        fderiv ℝ (pairLoss Φ) q (X', Y'))
      = fun q : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
        (2 : ℝ) * froIP (q.2 * q.1 - Φ) (mulDerivL X' Y' q) := by
    funext q
    obtain ⟨A₀, B₀⟩ := q
    rw [fderiv_pairLoss_apply]
    show 2 * froIP (B₀ * A₀ - Φ) (B₀ * X' + Y' * A₀)
        = 2 * froIP (B₀ * A₀ - Φ) (Y' * A₀ + B₀ * X')
    rw [add_comm (Y' * A₀) (B₀ * X')]
  rw [hfun] at h1
  -- differentiate that polynomial directly
  have hu : HasFDerivAt
      (fun q : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ => q.2 * q.1 - Φ)
      (mulDerivL A B) (A, B) := (hasFDerivAt_pairProd A B).sub_const Φ
  have hv : HasFDerivAt
      (fun q : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ => mulDerivL X' Y' q)
      (mulDerivL X' Y') (A, B) := ContinuousLinearMap.hasFDerivAt _
  have hb := ContinuousLinearMap.isBoundedBilinearMap (froIPL (ι := Fin N) (κ := Fin M))
  have h3 := (hb.hasFDerivAt (B * A - Φ, mulDerivL X' Y' (A, B))).comp (A, B) (hu.prodMk hv)
  have h4 : HasFDerivAt
      (fun q : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
        (2 : ℝ) * froIP (q.2 * q.1 - Φ) (mulDerivL X' Y' q)) _ (A, B) := h3.const_smul (2 : ℝ)
  have hkey := ContinuousLinearMap.ext_iff.mp (h1.unique h4) (X, Y)
  calc fderiv ℝ (fderiv ℝ (pairLoss Φ)) (A, B) (X, Y) (X', Y')
      = 2 * (froIP (B * A - Φ) (Y' * X + Y * X')
              + froIP (B * X + Y * A) (Y' * A + B * X')) := hkey
    _ = 2 * (froIP (B * X + Y * A) (B * X' + Y' * A)
              + froIP (B * A - Φ) (Y * X' + Y' * X)) := by
        rw [add_comm (Y' * X) (Y * X'), add_comm (Y' * A) (B * X'),
          add_comm (froIP (B * A - Φ) (Y * X' + Y' * X))]

/-- **The diagonal of the polar form**, which is what ties this module to the entrywise
expansion.  Setting `(X', Y') = (X, Y)` gives twice the quadratic part of
`frobeniusSq_full_variation_of_critical`: the Frobenius square of the first-order motion, plus
twice the pairing of the residual against the second-order motion `Y X`. -/
public theorem fderiv_fderiv_pairLoss_diag (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    fderiv ℝ (fderiv ℝ (pairLoss Φ)) (A, B) (X, Y) (X, Y)
      = 2 * (frobeniusSq (B * X + Y * A) + 2 * froIP (B * A - Φ) (Y * X)) := by
  rw [fderiv_fderiv_pairLoss_apply, froIP_self, froIP_add_right]
  ring

end Loss

end AISafetyAtlas.SingularLearning
