module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Solving `2X + X C X = D` near `D = 0`

The Morse step of MAIS-O77(b) reduces, after the exact loss expansion in
`LossExpansion.lean` and the congruence algebra in `HessianBlock.lean`, to a single
question: given the Hessian block `K` at the rung point and the block `H(z)` at a nearby
point, is there an analytic-in-`z` matrix `X(z)`, vanishing at the rung point, with

    `2 X + X K⁻¹ X = H(z) - K`?

`congruence_of_solution` turns any such `X` into the congruence
`(1 + K⁻¹X)ᵀ K (1 + K⁻¹X) = H(z)`, which is the coordinate change the splitting needs.

This module answers the question for the equation itself, in the generality the equation
has: a real normed algebra. Nothing about matrices, saddle points or losses is used, and
nothing about them is assumed.

## Why the statement is `C^n` and not analytic

Because that is all the consumer needs, not because the analytic version is
unavailable. `hasLocalVolumeOrder_comp_of_lipschitz` states print's Lemma 6.4(i)
at the strength its proof consumes — local Lipschitz-ness — and
`ContDiffAt.exists_lipschitzOnWith` supplies that from `C¹`, so a `C^n` solution
operator transports a local volume order exactly as well as an analytic one.

Mathlib does have an analytic inverse function theorem in Banach space —
OpenPartialHomeomorph.analyticAt_symm', which lives in
`Mathlib/Analysis/Calculus/FDeriv/Analytic.lean` rather than under
`InverseFunctionTheorem/`, and which composed with
`HasStrictFDerivAt.toOpenPartialHomeomorph` gives an analytic local inverse. It
is not needed here: the Lipschitz route is weaker in hypotheses and suffices. `quadSolve` could therefore be upgraded to
`AnalyticAt`; it has not been, because no consumer needs it yet.

The vendored TauCeti.analyticAt_sqrtNearOne (see `vendor/TauCeti/`) is built on
that same Mathlib lemma, and proves the analytic square root near `1` in a Banach
algebra — which is the same construction as this module, one generality up.

## What is *not* proved here

This module answers a question about one equation. It computes no volume order,
and it is not the route O77(b) finally took.

When the docstring was written, solving this equation was described as one of two
obligations standing between the atlas and an unconditional O77(b), the other being
that `LossExpansion.lean` expands the loss only on the `2H`-dimensional slice
`dA = x vᵀ`, `dB = u yᵀ` while §7.4 asks for a splitting over the whole parameter
space. That framing was wrong about what §7.4 asks. A Gromoll–Meyer splitting runs
along **any** subspace whose Hessian block is nondegenerate, and the candidate names
that subspace: it is print's `2H` block. So the slice was never the deficiency, and
`exists_gromoll_meyer_splitting` in `CriticalFiber.lean` builds the splitting by the
inverse function theorem on the critical fibre rather than by solving `2X + X C X = D`.
`O77AllSaddlesHavePairOne` is proved, by `o77AllSaddlesHavePairOne_holds`, and this
module is not on the path.

It is kept because the equation is stated in the generality it has and nothing here
depends on the abandoned route.
-/

namespace AISafetyAtlas.SingularLearning

open Filter Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The left-hand side of the congruence equation: `X ↦ 2X + X C X`. The linear part is
invertible and the quadratic part vanishes to second order, which is the whole reason an
inverse function theorem applies. -/
@[expose] public def quadMap (C : A) (X : A) : A := (2 : ℝ) • X + X * C * X

public theorem quadMap_zero (C : A) : quadMap C 0 = 0 := by simp [quadMap]

/-- `(X, Y) ↦ X C Y` is a bounded bilinear map. Submultiplicativity of the norm gives the
bound; the constant is padded to `‖C‖ + 1` so that it is positive without a case split. -/
public theorem isBoundedBilinearMap_mul_const_mul (C : A) :
    IsBoundedBilinearMap ℝ (fun p : A × A => p.1 * C * p.2) where
  add_left := by intro x₁ x₂ y; simp [add_mul]
  smul_left := by intro c x y; simp
  add_right := by intro x y₁ y₂; simp [mul_add]
  smul_right := by intro c x y; simp
  bound := by
    refine ⟨‖C‖ + 1, by positivity, fun x y => ?_⟩
    calc ‖x * C * y‖ ≤ ‖x * C‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ (‖x‖ * ‖C‖) * ‖y‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (‖C‖ + 1) * ‖x‖ * ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg C]

/-- The quadratic part has vanishing derivative at the origin. -/
public theorem hasStrictFDerivAt_mul_const_mul_self (C : A) :
    HasStrictFDerivAt (fun X : A => X * C * X) (0 : A →L[ℝ] A) 0 := by
  set d : A → A × A := fun X => (X, X) with hd
  have hdiag : HasStrictFDerivAt d
      ((ContinuousLinearMap.id ℝ A).prod (ContinuousLinearMap.id ℝ A)) 0 :=
    (hasStrictFDerivAt_id _).prodMk (hasStrictFDerivAt_id _)
  have hbil : HasStrictFDerivAt (fun p : A × A => p.1 * C * p.2)
      ((isBoundedBilinearMap_mul_const_mul C).deriv (d 0)) (d 0) :=
    (isBoundedBilinearMap_mul_const_mul C).hasStrictFDerivAt _
  have h2 := hbil.comp (0 : A) hdiag
  have h3 : ((isBoundedBilinearMap_mul_const_mul C).deriv (d 0)).comp
      ((ContinuousLinearMap.id ℝ A).prod (ContinuousLinearMap.id ℝ A)) = 0 := by
    ext x; simp [hd, IsBoundedBilinearMap.deriv]
  rw [h3] at h2
  exact h2

public theorem contDiff_quadMap (C : A) : ContDiff ℝ (⊤ : ℕ∞) (quadMap C) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun X : A => (2 : ℝ) • X) := contDiff_id.const_smul _
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun X : A => X * C * X) :=
    ((isBoundedBilinearMap_mul_const_mul C).contDiff).comp (contDiff_id.prodMk contDiff_id)
  exact h1.add h2

/-- **Doubling, as a continuous linear equivalence.** This is the derivative of `quadMap C`
at the origin, and packaging it as an equivalence is what the inverse function theorem
asks for. -/
@[expose] public noncomputable def doubling (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] :
    A ≃L[ℝ] A :=
  ContinuousLinearEquiv.equivOfInverse ((2 : ℝ) • ContinuousLinearMap.id ℝ A)
    ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ A)
    (by intro x; simp [smul_smul]) (by intro x; simp [smul_smul])

public theorem coe_doubling : ((doubling A : A →L[ℝ] A)) = (2 : ℝ) • ContinuousLinearMap.id ℝ A :=
  rfl

/-- The derivative of `quadMap C` at the origin is doubling. -/
public theorem hasStrictFDerivAt_quadMap (C : A) :
    HasStrictFDerivAt (quadMap C) (doubling A : A →L[ℝ] A) 0 := by
  have h1 : HasStrictFDerivAt (fun X : A => (2 : ℝ) • X)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ A) 0 :=
    (hasStrictFDerivAt_id (0 : A)).const_smul (2 : ℝ)
  have h := h1.add (hasStrictFDerivAt_mul_const_mul_self C)
  rw [add_zero] at h
  exact h

section Solve

variable [CompleteSpace A]

/-- **The solution operator.** `quadSolve C D` is a preimage of `D` under `quadMap C`,
defined for every `D` but characterised only near the origin — which is all the local
statement needs, and all an inverse function theorem provides. -/
@[expose] public noncomputable def quadSolve (C : A) : A → A :=
  (hasStrictFDerivAt_quadMap C).localInverse _ _ _

/-- The rung point is fixed: the equation with `D = 0` is solved by `X = 0`. -/
public theorem quadSolve_zero (C : A) : quadSolve C (0 : A) = 0 := by
  have h := (hasStrictFDerivAt_quadMap C).localInverse_apply_image
  rwa [quadMap_zero] at h

/-- **The equation is solved near the origin.** -/
public theorem eventually_quadMap_quadSolve (C : A) :
    ∀ᶠ D in 𝓝 (0 : A), quadMap C (quadSolve C D) = D := by
  have h := (hasStrictFDerivAt_quadMap C).eventually_right_inverse
  rwa [quadMap_zero] at h

/-- **The solution is `C^n` at the origin**, for every finite order and for `ω`-free
`n = ⊤`. This is what `ContDiffAt.to_localInverse` gives and what the Lipschitz form of
Lemma 6.4(i) consumes. -/
public theorem contDiffAt_quadSolve (C : A) (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hC : ContDiffAt ℝ n (quadMap C) 0) :
    ContDiffAt ℝ n (quadSolve C) 0 := by
  have hfd : HasFDerivAt (quadMap C) (doubling A : A →L[ℝ] A) 0 :=
    (hasStrictFDerivAt_quadMap C).hasFDerivAt
  have h := hC.to_localInverse (f' := doubling A) hfd hn
  rw [quadMap_zero] at h
  exact h

/-- **The solution operator is Lipschitz near the origin.** This is the form
`hasLocalVolumeOrder_comp_of_lipschitz` asks for, and the reason the
missing analytic inverse function theorem is not on the critical path: the transport of a
local volume order through a coordinate change never differentiates the change, it only
needs it to move volume by a bounded factor in both directions. -/
public theorem exists_lipschitzOnWith_quadSolve (C : A) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 (0 : A), LipschitzOnWith K (quadSolve C) t := by
  have h1 : ContDiffAt ℝ 1 (quadMap C) 0 :=
    ((contDiff_quadMap C).of_le (by exact_mod_cast le_top)).contDiffAt
  exact (contDiffAt_quadSolve C 1 one_ne_zero h1).exists_lipschitzOnWith

end Solve

end AISafetyAtlas.SingularLearning
