module

public import AISafetyAtlas.Conjectures.MAIS.O77Proof
public import AISafetyAtlas.SingularLearning.HadamardCongruence
public import AISafetyAtlas.SingularLearning.LossDerivative
public import AISafetyAtlas.SingularLearning.ParamSplit
public import AISafetyAtlas.SingularLearning.QuadraticSplit
public import AISafetyAtlas.SingularLearning.SylvesterPair
public import AISafetyAtlas.SingularLearning.IndefiniteBlockPair

/-!
# The O77 chart, and the three inputs a splitting step consumes

MAIS-O77(b) reaches a point where the loss has to be read in coordinates adapted
to print's `2H`-dimensional variation block: the block first, a complement
after, the rung point at the origin.  `O77Proof.lean` supplies the block as a
subspace and the Hessian on it as a matrix; `ParamSplit.lean` supplies the
coordinate change along an arbitrary subspace; `LossDerivative.lean` supplies
the loss as a `C^∞` function with both derivatives computed.  This module is the
join, and it produces exactly three things.

## Primary surface

| Declaration | Content |
|---|---|
| `exists_o77_chart` | the parameter space split with the block first, and the two clauses saying the first factor is that block |
| `fderiv_o77LossCoords_eq_zero` | a saddle rung point is a critical point of the loss in coordinates |
| `fderiv_o77_chart_eq_zero` | the same, centred in the chart |
| `exists_o77_block_matrix` | the Hessian on the chart's first block as a symmetric nonsingular matrix taking both signs |
| `fderiv_fderiv_o77_chart_apply` | the chart Hessian, as the polar form of `o77HessianPolar` |
| `exists_o77_block_coords` | the linear isomorphism between the chart's first block and print's parametrisation |

## The factor the loss carries, and where it goes

Print's loss is `(1/2)‖BA − Φ‖²_F` and `AISafetyAtlas.SingularLearning.pairLoss`
is `‖BA − Φ‖²_F`, so the two differ by a factor of two; the bridge is
`rrrLoss_eq_frobeniusSq`, recorded here as `o77LossCoords_eq_pairLoss`.  The
factor is not cosmetic.  The second derivative of a Frobenius square carries a
factor of two of its own, and the two cancel: the chart Hessian is exactly the
polar form `o77HessianPolar`, and the matrix it produces is congruent to print's
own block matrix, not to twice it.  Dropping the half would have produced a
theorem about a different matrix that is symmetric, nonsingular and indefinite
all the same — a defect no build error would report.

## Congruent, not equal

The chart is built from an orthonormal basis of the block subspace, and print
parametrises the same subspace by a pair of vectors.  The two parametrisations
are injective linear maps with the same range, so they differ by a linear
isomorphism (`exists_o77_block_coords`), and the matrix delivered here is
congruent to print's rather than equal to it.  Congruence carries everything a
diagonalisation consumes: symmetry, nonsingularity, and the set of values of the
quadratic form, hence both signs.

## What is not here

No volume order, no splitting, no diagonalisation.  This module states the
Hessian's block in a chart and nothing about what the germ does.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open Module (finrank)

section Split

variable {n : ℕ}

/-- The split sends the first factor to the `castAdd` coordinates. -/
public theorem splitLE_castAdd (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) (i : Fin p) :
    splitLE p q (u, v) (Fin.castAdd q i) = u i := by
  simp [splitLE]

/-- The split sends the second factor to the `natAdd` coordinates. -/
public theorem splitLE_natAdd (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) (j : Fin q) :
    splitLE p q (u, v) (Fin.natAdd p j) = v j := by
  simp [splitLE]

/-- **A chart adapted to a subspace given as an orthogonal complement.** -/
public theorem exists_chart_of_orthogonal
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {m d : ℕ}
    (hm : finrank ℝ Vᗮ = m) (hd : finrank ℝ V = d) :
    ∃ Ξ : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n),
      (∀ z, Ξ (z, 0) ∈ Vᗮ) ∧ (∀ v ∈ Vᗮ, ∃ z, Ξ (z, 0) = v) := by
  subst hm
  subst hd
  refine ⟨((splitLE (finrank ℝ Vᗮ) (finrank ℝ V)).trans
      (paramSplitEquiv V).symm.toLinearEquiv).toContinuousLinearEquiv, ?_, ?_⟩
  · intro z
    rw [mem_orthogonal_iff_paramSplitEquiv_natAdd_eq_zero]
    intro j
    show paramSplitEquiv V ((paramSplitEquiv V).symm
      (splitLE (finrank ℝ Vᗮ) (finrank ℝ V) (z, 0))) _ = 0
    rw [LinearIsometryEquiv.apply_symm_apply, splitLE_natAdd]
    rfl
  · intro v hv
    refine ⟨((splitLE (finrank ℝ Vᗮ) (finrank ℝ V)).symm (paramSplitEquiv V v)).1, ?_⟩
    have hzero : ((splitLE (finrank ℝ Vᗮ) (finrank ℝ V)).symm (paramSplitEquiv V v)).2 = 0 := by
      ext j
      have h1 := splitLE_natAdd (finrank ℝ Vᗮ) (finrank ℝ V)
        ((splitLE (finrank ℝ Vᗮ) (finrank ℝ V)).symm (paramSplitEquiv V v)).1
        ((splitLE (finrank ℝ Vᗮ) (finrank ℝ V)).symm (paramSplitEquiv V v)).2 j
      rw [Prod.mk.eta, LinearEquiv.apply_symm_apply] at h1
      rw [← h1]
      exact (mem_orthogonal_iff_paramSplitEquiv_natAdd_eq_zero V v).1 hv j
    show (paramSplitEquiv V).symm (splitLE (finrank ℝ Vᗮ) (finrank ℝ V) (_, 0)) = v
    rw [← hzero, Prod.mk.eta, LinearEquiv.apply_symm_apply,
      LinearIsometryEquiv.symm_apply_apply]

end Split

section Chart

/-- **The O77 parameter space, split with print's `2H` variation block first.** -/
public theorem exists_o77_chart {M N H r : ℕ} (frame : O77SpectralFrame M N r) (α : Fin r) :
    ∃ (d : ℕ) (_ : 2 * H + d = H * M + N * H)
      (Xi : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (H * M + N * H))),
      (∀ z : EuclideanSpace ℝ (Fin (2 * H)), Xi (z, 0) ∈ o77BlockSubspace frame α) ∧
      (∀ v ∈ o77BlockSubspace frame α, ∃ z, Xi (z, 0) = v) := by
  set S := o77BlockSubspace (H := H) frame α with hSdef
  have hSS : Sᗮᗮ = S := Submodule.orthogonal_orthogonal S
  have hm : finrank ℝ (Sᗮ)ᗮ = 2 * H := by
    rw [hSS, hSdef]; exact finrank_o77BlockSubspace frame α
  obtain ⟨Xi, h1, h2⟩ := exists_chart_of_orthogonal Sᗮ hm rfl
  refine ⟨finrank ℝ Sᗮ, ?_, Xi, ?_, ?_⟩
  · rw [← hm]; exact finrank_orthogonal_add_finrank Sᗮ
  · intro z; have hz := h1 z; rwa [hSS] at hz
  · intro v hv; exact h2 v (by rw [hSS]; exact hv)

end Chart

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section AffineTransport

open scoped ContDiff

variable {W P : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **A critical point stays critical in an affine chart centred on it.** -/
public theorem fderiv_comp_affine_eq_zero (F : P → ℝ) (p₀ : P)
    (hF : DifferentiableAt ℝ F p₀) (Λ : W →L[ℝ] P) (h0 : fderiv ℝ F p₀ = 0) :
    fderiv ℝ (fun q => F (p₀ + Λ q)) 0 = 0 := by
  have hT0 : HasFDerivAt (fun q : W => p₀ + Λ q) Λ 0 := Λ.hasFDerivAt.const_add p₀
  have hF0 : HasFDerivAt F (fderiv ℝ F p₀) (p₀ + Λ 0) := by
    simpa using hF.hasFDerivAt
  have hcomp : HasFDerivAt (fun q : W => F (p₀ + Λ q)) ((fderiv ℝ F p₀).comp Λ) 0 :=
    hF0.comp (0 : W) hT0
  rw [hcomp.fderiv, h0, ContinuousLinearMap.zero_comp]

/-- **The second derivative in an affine chart is the second derivative pulled back
along the chart's linear part.** -/
public theorem fderiv_fderiv_comp_affine (F : P → ℝ) (hF : ContDiff ℝ ∞ F) (p₀ : P)
    (Λ : W →L[ℝ] P) (w w' : W) :
    fderiv ℝ (fderiv ℝ (fun q => F (p₀ + Λ q))) 0 w w'
      = fderiv ℝ (fderiv ℝ F) p₀ (Λ w) (Λ w') := by
  have hT : ∀ q : W, HasFDerivAt (fun q : W => p₀ + Λ q) Λ q := fun q =>
    Λ.hasFDerivAt.const_add p₀
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hg : ∀ q : W, HasFDerivAt (fun q : W => F (p₀ + Λ q))
      ((fderiv ℝ F (p₀ + Λ q)).comp Λ) q := fun q =>
    ((hFd (p₀ + Λ q)).hasFDerivAt).comp q (hT q)
  have hfd : fderiv ℝ (fun q : W => F (p₀ + Λ q))
      = fun q : W => (fderiv ℝ F (p₀ + Λ q)).comp Λ := funext fun q => (hg q).fderiv
  have hF2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p₀) (p₀ + Λ 0) := by
    have hcd := hF.fderiv_right (m := ∞) (by simp)
    simpa using ((hcd.differentiable (by simp)) p₀).hasFDerivAt
  have h1 : HasFDerivAt (fun q : W => fderiv ℝ F (p₀ + Λ q))
      ((fderiv ℝ (fderiv ℝ F) p₀).comp Λ) 0 := hF2.comp (0 : W) (hT 0)
  have h2 := (((ContinuousLinearMap.compL ℝ W P ℝ).flip Λ).hasFDerivAt
      (x := fderiv ℝ F (p₀ + Λ 0))).comp (0 : W) h1
  have hfd2 : (fun q : W => (fderiv ℝ F (p₀ + Λ q)).comp Λ)
      = ⇑((ContinuousLinearMap.compL ℝ W P ℝ).flip Λ)
        ∘ fun q : W => fderiv ℝ F (p₀ + Λ q) := rfl
  rw [hfd, hfd2, h2.fderiv]
  rfl

/-- **A critical point of `F` stays critical after a linear reparametrisation and a
constant rescaling.** -/
public theorem fderiv_comp_clm_smul_eq_zero (F : P → ℝ) (Λ : W →L[ℝ] P) (x : W) (c : ℝ)
    (hF : DifferentiableAt ℝ F (Λ x)) (h0 : fderiv ℝ F (Λ x) = 0) :
    fderiv ℝ (fun q => c * F (Λ q)) x = 0 := by
  have hcomp : HasFDerivAt (fun q : W => F (Λ q)) ((fderiv ℝ F (Λ x)).comp Λ) x :=
    hF.hasFDerivAt.comp x Λ.hasFDerivAt
  rw [(hcomp.const_mul c).fderiv, h0, ContinuousLinearMap.zero_comp, smul_zero]

/-- **A constant factor passes through the second derivative.** -/
public theorem fderiv_fderiv_const_mul (F : P → ℝ) (hF : ContDiff ℝ ∞ F) (c : ℝ) (x u v : P) :
    fderiv ℝ (fderiv ℝ fun p => c * F p) x u v = c * fderiv ℝ (fderiv ℝ F) x u v := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have h1 : (fderiv ℝ fun p : P => c * F p) = fun p => c • fderiv ℝ F p :=
    funext fun p => ((hFd p).hasFDerivAt.const_mul c).fderiv
  have hcd := hF.fderiv_right (m := ∞) (by simp)
  have h2 : HasFDerivAt (fun p : P => c • fderiv ℝ F p) (c • fderiv ℝ (fderiv ℝ F) x) x :=
    (((hcd.differentiable (by simp)) x).hasFDerivAt).const_smul c
  rw [h1, h2.fderiv]
  simp

end AffineTransport

section Critical

open scoped ContDiff

/-- **The O77 loss is half the pair loss, read through the coordinate packing.**
`rrrLoss` is Print's population loss, which carries the factor `1/2` that
`pairLoss` does not. -/
public theorem o77LossCoords_eq_pairLoss {M N H : ℕ} (C : Matrix (Fin N) (Fin M) ℝ) :
    o77LossCoords M N H C
      = fun x => (1 / 2 : ℝ) * pairLoss C ((matrixPairEquiv N M H).symm x) := by
  funext x
  simp only [o77LossCoords, rrrLossCoords]
  rw [rrrLoss_eq_frobeniusSq]
  rfl

/-- **A saddle rung point is a critical point of the O77 loss in coordinates.** -/
public theorem fderiv_o77LossCoords_eq_zero {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) :
    fderiv ℝ (o77LossCoords M N H frame.target) (matrixPairCoords A B) = 0 := by
  set E : EuclideanSpace ℝ (Fin (H * M + N * H)) →L[ℝ]
      (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) :=
    LinearMap.toContinuousLinearMap (matrixPairEquiv N M H).symm.toLinearMap with hE
  have hEc : E (matrixPairCoords A B) = (A, B) :=
    (matrixPairEquiv N M H).symm_apply_apply (A, B)
  have h0 : fderiv ℝ (pairLoss frame.target) (E (matrixPairCoords A B)) = 0 := by
    rw [hEc]
    exact fderiv_pairLoss_eq_zero_of frame.target A B (rung_transpose_mul_residual h)
      (rung_residual_mul_transpose h)
  have hdiff : DifferentiableAt ℝ (pairLoss frame.target) (E (matrixPairCoords A B)) := by
    rw [hEc]; exact (hasFDerivAt_pairLoss frame.target A B).differentiableAt
  rw [o77LossCoords_eq_pairLoss]
  exact fderiv_comp_clm_smul_eq_zero (pairLoss frame.target) E (matrixPairCoords A B)
    (1 / 2 : ℝ) hdiff h0

/-- **The chart form of criticality**, centred at the rung point. -/
public theorem fderiv_o77_chart_eq_zero {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) {d : ℕ}
    (Xi : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (H * M + N * H))) :
    fderiv ℝ (fun p => o77LossCoords M N H frame.target
      (matrixPairCoords A B + Xi p)) 0 = 0 :=
  fderiv_comp_affine_eq_zero (o77LossCoords M N H frame.target) (matrixPairCoords A B)
    ((contDiff_o77LossCoords frame.target).differentiable (by simp) _)
    (Xi : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) →L[ℝ]
      EuclideanSpace ℝ (Fin (H * M + N * H)))
    (fderiv_o77LossCoords_eq_zero h)

end Critical

section ChartHessian

open scoped ContDiff

/-- **The Hessian of the O77 loss in an affine chart centred at a parameter pair.**

Print's loss carries a factor `1/2` and the second derivative of a Frobenius
square carries a factor `2`; the two cancel, so the chart Hessian is exactly the
polar form of the Hessian the O77 layer works with, evaluated at the pair the
chart direction unpacks to. -/
public theorem fderiv_fderiv_o77_chart_apply {M N H r : ℕ} (frame : O77SpectralFrame M N r)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ) {d : ℕ}
    (Xi : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (H * M + N * H)))
    (p q : EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fderiv ℝ (fun p => o77LossCoords M N H frame.target
        (matrixPairCoords A B + Xi p))) 0 p q
      = o77HessianPolar frame A B
          ((matrixPairEquiv N M H).symm (Xi p)).1 ((matrixPairEquiv N M H).symm (Xi p)).2
          ((matrixPairEquiv N M H).symm (Xi q)).1 ((matrixPairEquiv N M H).symm (Xi q)).2 := by
  set E : EuclideanSpace ℝ (Fin (H * M + N * H)) →L[ℝ]
      (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) :=
    LinearMap.toContinuousLinearMap (matrixPairEquiv N M H).symm.toLinearMap
  set Lam : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) →L[ℝ]
      (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) :=
    E.comp (Xi : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) →L[ℝ]
      EuclideanSpace ℝ (Fin (H * M + N * H)))
  have hmp : (matrixPairEquiv N M H).symm (matrixPairCoords A B) = (A, B) :=
    (matrixPairEquiv N M H).symm_apply_apply (A, B)
  have hLam : ∀ w, Lam w = (matrixPairEquiv N M H).symm (Xi w) := fun _ => rfl
  have hF : ContDiff ℝ ∞ (fun P : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
      (1 / 2 : ℝ) * pairLoss frame.target P) := contDiff_const.mul (contDiff_pairLoss _)
  have hg : (fun p => o77LossCoords M N H frame.target (matrixPairCoords A B + Xi p))
      = fun p => (1 / 2 : ℝ) * pairLoss frame.target ((A, B) + Lam p) := by
    funext w
    rw [o77LossCoords_eq_pairLoss]
    show (1 / 2 : ℝ) * pairLoss frame.target
        ((matrixPairEquiv N M H).symm (matrixPairCoords A B + Xi w))
      = (1 / 2 : ℝ) * pairLoss frame.target ((A, B) + Lam w)
    rw [map_add, hmp, ← hLam w]
  have step1 : fderiv ℝ (fderiv ℝ (fun w => (1 / 2 : ℝ) * pairLoss frame.target
        ((A, B) + Lam w))) 0 p q
      = fderiv ℝ (fderiv ℝ (fun P : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
          (1 / 2 : ℝ) * pairLoss frame.target P)) (A, B) (Lam p) (Lam q) :=
    fderiv_fderiv_comp_affine _ hF (A, B) Lam p q
  have step2 := fderiv_fderiv_const_mul (pairLoss frame.target)
    (contDiff_pairLoss frame.target) (1 / 2 : ℝ) (A, B) (Lam p) (Lam q)
  have step3 := fderiv_fderiv_pairLoss_apply frame.target A B
    (Lam p).1 (Lam q).1 (Lam p).2 (Lam q).2
  rw [Prod.mk.eta, Prod.mk.eta] at step3
  have step23 : fderiv ℝ (fderiv ℝ (fun P : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ =>
        (1 / 2 : ℝ) * pairLoss frame.target P)) (A, B) (Lam p) (Lam q)
      = (1 / 2 : ℝ) * (2 * (froIP (B * (Lam p).1 + (Lam p).2 * A)
            (B * (Lam q).1 + (Lam q).2 * A)
          + froIP (B * A - frame.target)
              ((Lam p).2 * (Lam q).1 + (Lam q).2 * (Lam p).1))) :=
    step2.trans (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) step3)
  rw [hg, step1]
  refine step23.trans ?_
  rw [← hLam p, ← hLam q, o77HessianPolar]
  ring

end ChartHessian

section PolarMatrix

open Matrix

/-- **Every continuous bilinear form on a Euclidean space is a matrix form**, the
matrix being the table of its values on the standard basis. -/
public theorem matrixQuadPolar_toMatrix {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    Q x y = matrixQuadPolar (Matrix.of fun i j =>
      Q (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) x y := by
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ j, y j • EuclideanSpace.single j (1 : ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, hy]
  simp only [matrixQuadPolar, map_sum, _root_.sum_apply, map_smul, _root_.smul_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Polarisation for a symmetric matrix form.** -/
public theorem dotProduct_mulVec_symm {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ)
    (hK : K.IsSymm) (u v : ι → ℝ) : u ⬝ᵥ (K *ᵥ v) = v ⬝ᵥ (K *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hK.eq, dotProduct_comm]

public theorem dotProduct_mulVec_add_add {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ)
    (hK : K.IsSymm) (u v : ι → ℝ) :
    (u + v) ⬝ᵥ (K *ᵥ (u + v))
      = u ⬝ᵥ (K *ᵥ u) + 2 * (u ⬝ᵥ (K *ᵥ v)) + v ⬝ᵥ (K *ᵥ v) := by
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_mulVec_symm K hK v u]
  ring

end PolarMatrix

section BlockCoords

/-- **The chart's first block is print's variation block, in a linearly equivalent
basis.**  The chart is built from an orthonormal basis of the block subspace, and
print parametrises the same subspace by `(x, y)`; both parametrisations are
injective linear maps with the same range, so one factors through the other by a
linear isomorphism. -/
public theorem exists_o77_block_coords {M N H r : ℕ} (frame : O77SpectralFrame M N r)
    (α : Fin r) {d : ℕ}
    (Xi : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (H * M + N * H)))
    (hmem : ∀ z, Xi (z, 0) ∈ o77BlockSubspace frame α)
    (honto : ∀ v ∈ o77BlockSubspace frame α, ∃ z, Xi (z, 0) = v) :
    ∃ P : EuclideanSpace ℝ (Fin (2 * H)) ≃ₗ[ℝ] ((Fin H → ℝ) × (Fin H → ℝ)),
      ∀ z, (matrixPairEquiv N M H).symm (Xi (z, 0))
        = o77BlockVariation frame α (P z).1 (P z).2 := by
  set iota : EuclideanSpace ℝ (Fin (2 * H)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (H * M + N * H)) :=
    Xi.toLinearEquiv.toLinearMap.comp
      (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin (2 * H))) (EuclideanSpace ℝ (Fin d)))
  set mu : ((Fin H → ℝ) × (Fin H → ℝ)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (H * M + N * H)) :=
    (matrixPairEquiv N M H).toLinearMap.comp (o77BlockMap frame α)
  have hinj_i : Function.Injective iota := by
    intro a b hab
    exact congrArg Prod.fst (Xi.injective (hab : Xi (a, 0) = Xi (b, 0)))
  have hinj_m : Function.Injective mu := o77BlockSubspace_injective frame α
  have hrange : LinearMap.range iota = LinearMap.range mu := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact hmem z
    · rintro _ ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := honto (mu w) ⟨w, rfl⟩
      exact ⟨z, hz⟩
  refine ⟨((LinearEquiv.ofInjective iota hinj_i).trans (LinearEquiv.ofEq _ _ hrange)).trans
      (LinearEquiv.ofInjective mu hinj_m).symm, fun z => ?_⟩
  have hkey : mu (((LinearEquiv.ofInjective iota hinj_i).trans
        (LinearEquiv.ofEq _ _ hrange)).trans (LinearEquiv.ofInjective mu hinj_m).symm z)
      = iota z :=
    congrArg Subtype.val ((LinearEquiv.ofInjective mu hinj_m).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hrange) ((LinearEquiv.ofInjective iota hinj_i) z)))
  have hgoal : matrixPairEquiv N M H (o77BlockVariation frame α
      (((LinearEquiv.ofInjective iota hinj_i).trans (LinearEquiv.ofEq _ _ hrange)).trans
        (LinearEquiv.ofInjective mu hinj_m).symm z).1
      (((LinearEquiv.ofInjective iota hinj_i).trans (LinearEquiv.ofEq _ _ hrange)).trans
        (LinearEquiv.ofInjective mu hinj_m).symm z).2) = Xi (z, 0) := hkey
  rw [← hgoal, LinearEquiv.symm_apply_apply]

end BlockCoords

section BlockMatrix

open Matrix

/-- **The Hessian restricted to the chart's first block, as a matrix.**

The matrix is congruent to print's `K_α` rather than equal to it: the chart's
first block spans the same subspace as print's variation block, but in the
orthonormal basis the splitting produces rather than in print's `(x, y)`
parametrisation.  Congruence is enough for everything a diagonalisation
consumes — symmetry, nondegeneracy and both signs all transfer. -/
public theorem exists_o77_block_matrix {M N H r : ℕ} {frame : O77SpectralFrame M N r} {k : ℕ}
    {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (hrH : r < H) (α : Fin r) (hα : k ≤ (α : ℕ))
    {d : ℕ}
    (Xi : (EuclideanSpace ℝ (Fin (2 * H)) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (H * M + N * H)))
    (hmem : ∀ z, Xi (z, 0) ∈ o77BlockSubspace frame α)
    (honto : ∀ v ∈ o77BlockSubspace frame α, ∃ z, Xi (z, 0) = v) :
    ∃ K : Matrix (Fin (2 * H)) (Fin (2 * H)) ℝ,
      K.IsSymm ∧ K.det ≠ 0 ∧
      (∃ z, 0 < matrixQuadForm K z) ∧ (∃ z, matrixQuadForm K z < 0) ∧
      ∀ x y, blockW (EuclideanSpace ℝ (Fin (2 * H))) (EuclideanSpace ℝ (Fin d))
          (fderiv ℝ (fderiv ℝ (fun p => o77LossCoords M N H frame.target
            (matrixPairCoords A B + Xi p))) 0) x y
        = matrixQuadPolar K x y := by
  obtain ⟨P, hP⟩ := exists_o77_block_coords frame α Xi hmem honto
  set Ka : Matrix (Fin H ⊕ Fin H) (Fin H ⊕ Fin H) ℝ :=
    Matrix.fromBlocks (Bᵀ * B) ((-frame.singularValue α) • (1 : Matrix (Fin H) (Fin H) ℝ))
      ((-frame.singularValue α) • 1) (A * Aᵀ)
  set Pv : EuclideanSpace ℝ (Fin (2 * H)) → (Fin H ⊕ Fin H → ℝ) :=
    fun z => Sum.elim (P z).1 (P z).2 with hPvdef
  set Q : EuclideanSpace ℝ (Fin (2 * H)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * H)) →L[ℝ] ℝ :=
    blockW (EuclideanSpace ℝ (Fin (2 * H))) (EuclideanSpace ℝ (Fin d))
      (fderiv ℝ (fderiv ℝ (fun p => o77LossCoords M N H frame.target
        (matrixPairCoords A B + Xi p))) 0)
  set K : Matrix (Fin (2 * H)) (Fin (2 * H)) ℝ :=
    Matrix.of fun i j =>
      Q (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  have hQpolar : ∀ u v, Q u v = o77HessianPolar frame A B
      (o77BlockVariation frame α (P u).1 (P u).2).1
      (o77BlockVariation frame α (P u).1 (P u).2).2
      (o77BlockVariation frame α (P v).1 (P v).2).1
      (o77BlockVariation frame α (P v).1 (P v).2).2 := by
    intro u v
    have h1 := fderiv_fderiv_o77_chart_apply frame A B Xi (u, 0) (v, 0)
    rw [hP u, hP v] at h1
    exact h1
  have hQK : ∀ x y, Q x y = matrixQuadPolar K x y := matrixQuadPolar_toMatrix Q
  have hKsymm : K.IsSymm := by
    ext i j
    rw [Matrix.transpose_apply]
    show Q _ _ = Q _ _
    rw [hQpolar, hQpolar, o77HessianPolar_symm]
  have hdiag : ∀ z, matrixQuadForm K z = Pv z ⬝ᵥ (Ka *ᵥ Pv z) := by
    intro z
    rw [← matrixQuadPolar_self, ← hQK, hQpolar z z, o77HessianPolar_self,
      o77HessianForm_blockVariation_eq_matrixForm h α hα]
  have hPvadd : ∀ z w, Pv (z + w) = Pv z + Pv w := by
    intro z w
    funext i
    cases i with
    | inl a => simp [hPvdef, map_add]
    | inr a => simp [hPvdef, map_add]
  have hPvsurj : Function.Surjective Pv := by
    intro u
    refine ⟨P.symm (fun i => u (Sum.inl i), fun i => u (Sum.inr i)), ?_⟩
    funext i
    cases i with
    | inl a => simp [hPvdef]
    | inr a => simp [hPvdef]
  have hPvinj : ∀ z, Pv z = 0 → z = 0 := by
    intro z hz
    have ha : (P z).1 = 0 := funext fun i => congrFun hz (Sum.inl i)
    have hb : (P z).2 = 0 := funext fun i => congrFun hz (Sum.inr i)
    have h1 : P z = P 0 := by rw [map_zero]; exact Prod.ext ha hb
    exact P.injective h1
  have hKaSymm : Ka.IsSymm := isSymm_o77SaddleBlock (frame.singularValue α) A B
  have hpolar : ∀ z w, matrixQuadPolar K z w = Pv z ⬝ᵥ (Ka *ᵥ Pv w) := by
    intro z w
    have e1 : matrixQuadForm K (z + w)
        = matrixQuadForm K z + 2 * matrixQuadPolar K z w + matrixQuadForm K w :=
      dotProduct_mulVec_add_add K hKsymm (fun i => z i) (fun i => w i)
    have e2 : Pv (z + w) ⬝ᵥ (Ka *ᵥ Pv (z + w))
        = Pv z ⬝ᵥ (Ka *ᵥ Pv z) + 2 * (Pv z ⬝ᵥ (Ka *ᵥ Pv w))
          + Pv w ⬝ᵥ (Ka *ᵥ Pv w) := by
      rw [hPvadd]
      exact dotProduct_mulVec_add_add Ka hKaSymm _ _
    have e3 := hdiag (z + w)
    have e4 := hdiag z
    have e5 := hdiag w
    linarith
  have hKanondeg : Ka.Nondegenerate :=
    Matrix.nondegenerate_iff_det_ne_zero.mpr (det_o77SaddleBlock_ne_zero h α hα)
  have hdet : K.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hvK⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    refine hv0 ?_
    have hz : ∀ u, Pv (WithLp.toLp 2 v) ⬝ᵥ (Ka *ᵥ u) = 0 := by
      intro u
      obtain ⟨w, rfl⟩ := hPvsurj u
      rw [dotProduct_mulVec_symm Ka hKaSymm (Pv (WithLp.toLp 2 v)) (Pv w), ← hpolar]
      show (fun i => w i) ⬝ᵥ (K *ᵥ v) = 0
      rw [hvK, dotProduct_zero]
    have hzero := hPvinj _ (hKanondeg.eq_zero_of_ortho hz)
    funext i
    exact congrArg (fun z : EuclideanSpace ℝ (Fin (2 * H)) => z i) hzero
  obtain ⟨⟨un, hun⟩, ⟨up, hup⟩⟩ := o77SaddleBlock_quadForm_indefinite h hrH α
  obtain ⟨zn, hzn⟩ := hPvsurj un
  obtain ⟨zp, hzp⟩ := hPvsurj up
  refine ⟨K, hKsymm, hdet, ⟨zp, ?_⟩, ⟨zn, ?_⟩, hQK⟩
  · rw [hdiag zp, hzp]; exact hup
  · rw [hdiag zn, hzn]; exact hun

end BlockMatrix


/-! ## Part (b), assembled

Every piece print's argument names is now in hand, so the assembly is a matter of
handing them to the abstracted statement of that argument,
`SingularLearning.hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block`.

The dimension bound is print's own line: `k < r < H` forces `2H ≥ 4`, and the
band lemma asks for `3`. The mode is print's own choice of "a discarded singular
mode `α > k`", taken here at the first one, `α = k`; nothing distinguishes it,
and `o77SaddleBlock_quadForm_indefinite` does not even need `k ≤ α`. -/

/-- **Every point of every nonterminal critical set has two-sided pair `(1,1)`**,
which is MAIS-A7 Problem 3.9(b) at the candidate's answer. -/
public theorem o77_saddle_two_sided_pair {M N H r : ℕ} {frame : O77SpectralFrame M N r}
    {k : ℕ} {A : Matrix (Fin H) (Fin M) ℝ} {B : Matrix (Fin N) (Fin H) ℝ}
    (h : IsO77SaddleRungPoint frame k A B) (hrH : r < H) :
    HasO77TwoSidedPairAt frame.target (matrixPairCoords A B) 1 1 := by
  obtain ⟨d, hd, Xi, hmem, honto⟩ := exists_o77_chart frame ⟨k, h.1⟩
  obtain ⟨K, hsymm, hdet, hpos, hneg, hQ⟩ :=
    exists_o77_block_matrix h hrH ⟨k, h.1⟩ le_rfl Xi hmem honto
  have h3 : 3 ≤ 2 * H := by
    have := o77_variation_block_dim_ge h hrH
    omega
  have hweak := SingularLearning.hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block
    hd h3 (contDiff_o77LossCoords frame.target) (matrixPairCoords A B) Xi
    K hsymm hdet hpos hneg (fderiv_o77_chart_eq_zero h Xi) hQ
  exact ⟨hweak, hasStrictLocalVolumeOrder_of_hasLocalVolumeOrder hweak⟩

/-- **The candidate's part (b) answer, at print's own quantifiers.** -/
public theorem o77AllSaddlesHavePairOne_holds : O77AllSaddlesHavePairOne := by
  intro M N H r hrH frame k A B h
  exact o77_saddle_two_sided_pair h hrH

end AISafetyAtlas.Conjectures.MAIS
