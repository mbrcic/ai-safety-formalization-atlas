module

public import AISafetyAtlas.SingularLearning.HadamardCongruence
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The critical fibre, and the Gromoll–Meyer splitting along it

`HadamardCongruence` proves the second half of the parametrised Morse splitting: given that the
`W`-directional derivative of `f` vanishes along a section of the `V`-fibration, it flattens the
`W` part of `f` onto one fixed quadratic form. Its own docstring records the gap — the vanishing
is **assumed**, and nothing there establishes it for a particular `f`. This module closes that
gap and assembles the two halves into the splitting itself.

## What is here

* **The critical fibre.** `exists_critical_fiber`: for `f` smooth on `W × V` with `0` a critical
  point and the `W`-block of the Hessian at `0` invertible as a map `W → W∗`, the equation
  `∂_W f (η, ζ) = 0` has a smooth solution `η = ξ ζ` on a neighbourhood of `0` in `V`, with
  `ξ 0 = 0`. The proof is the inverse function theorem applied to
  `Φ (η, ζ) = (Q₀⁻¹ (∂_W f (η, ζ)), ζ)`, whose derivative at the origin is the shear
  `(u, v) ↦ (u + C v, v)`; `Φ` preserves the second coordinate, so its local inverse does too and
  the fibre coordinate reads off the first component of `Φ⁻¹ (0, ζ)`. Smoothness of the inverse on
  an **open** set — not merely at one point, which is all `ContDiffAt.contDiffOn` can give at
  `C^∞` — comes from `OpenPartialHomeomorph.contDiffAt_symm` applied at every point of the target
  where `fderiv ℝ Φ` is still invertible, a set that is open because the invertible operators are.

* **The congruence along a moving section.** `exists_shifted_congruence_normal_form` is
  `exists_partial_congruence_normal_form` with two changes that the fibre forces. The base point of
  the Taylor expansion moves along a smooth section `c : V → W` rather than sitting on `{0} × V`,
  and criticality is asked only on a neighbourhood `Uv ∋ 0` rather than on all of `V`, because a
  fibre produced by the implicit function theorem is local and can never satisfy the global
  hypothesis. `shiftedHessianAverage` is the corresponding family of forms; at the origin it is
  still the `W`-block of the Hessian, which is why no second-derivative chain rule is needed
  anywhere in this file. `exists_partial_congruence_normal_form_of_nhds` is the case `c = 0`:
  the neighbourhood form of the existing statement, obtained by intersecting the produced
  neighbourhood with `Prod.snd ⁻¹' Uv`.

* **The splitting.** `exists_gromoll_meyer_splitting` combines the two: near a critical point whose
  Hessian is nondegenerate on `W`, there are a chart `Θ` and a germ `g` on the complement with

      f q - f 0 = 2⁻¹ * Q₀ (Θ q).1 (Θ q).1 + g q.2,

  which is the printed equation. `Θ` is delivered in the **forward** direction — it maps the
  original coordinates to the normal-form ones, `Θ q = (R (q.1 - c q.2, q.2) (q.1 - c q.2), q.2)`
  — and it is a local diffeomorphism at the origin: `ContDiffOn ℝ ∞ Θ U` together with
  `HasFDerivAt Θ e 0` for an explicit `e : (W × V) ≃L[ℝ] (W × V)`, the shear by `-fderiv ℝ c 0`.
  That pair, not the equality of germs, is what a downstream volume-order argument needs, and it
  is why the conclusion carries an equivalence rather than a bare continuous linear map. The
  second coordinate is untouched, `(Θ q).2 = q.2`, so `g` is read at the same fibre coordinate on
  both sides.

The critical fibre `c` is returned alongside `Θ`, with `g ζ = f (c ζ, ζ) - f 0`. Without it `g`
would be an opaque function of the caller's own loss and nothing could be said about it; with it,
`g` is the restriction of `f` to the critical fibre, which is the printed germ, and a consumer can
compute it. `Examples/SingularLearning/CriticalFiber.lean` uses exactly that to show the germ is
not constant on the model `f (η, ζ) = η² − ζ⁴`, which is the whole point of this splitting as
against a strict Morse–Bott one.

## Auxiliaries

`shear D` is `(u, v) ↦ (u + D v, v)` as a continuous linear equivalence of `W × V`; it is the
derivative of both the fibre chart `Φ` above and of the shift `(η, ζ) ↦ (η + c ζ, ζ)`.

`exists_contDiff_eqOn_of_contDiffOn` extends a germ that is `C^∞` on an open set to a globally
`C^∞` function agreeing with it near a chosen point, by multiplying by a bump. It is the reason
`exists_gromoll_meyer_splitting` carries `[FiniteDimensional ℝ V]`: what supplies the bump is
Mathlib's bump-function typeclass, which a finite-dimensional real normed space satisfies and a
general Banach space need not, and the congruence machinery inherited from `HadamardCongruence`
asks for a section that is smooth on all of `V`, not merely near the origin. Nothing else in this file needs
finite dimensionality, and `exists_critical_fiber` and the shifted congruence are stated over
Banach spaces.

## What is still assumed

The splitting `W ⊕ V` is handed in, exactly as in `HadamardCongruence`: `V` is given, and that the
`W`-block of the Hessian is invertible is a hypothesis. What this module removes is the separate
assumption that `{0} × V` is critical in the `W` directions — that is now derived, and the fibre
along which it holds is produced rather than assumed to be a coordinate axis. What remains, and is
not attempted here, is the construction of the decomposition `W ⊕ V` from a degenerate critical
point, that is, the identification of `V` with the kernel of the Hessian.
-/

noncomputable section

open Filter Topology

open scoped ContDiff

namespace AISafetyAtlas.SingularLearning

section Shear

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The shear `(u, v) ↦ (u + D v, v)`**, as a continuous linear equivalence of `W × V`. -/
@[expose] public def shear (D : V →L[ℝ] W) : (W × V) ≃L[ℝ] (W × V) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ W V + D.comp (ContinuousLinearMap.snd ℝ W V)).prod
      (ContinuousLinearMap.snd ℝ W V))
    ((ContinuousLinearMap.fst ℝ W V - D.comp (ContinuousLinearMap.snd ℝ W V)).prod
      (ContinuousLinearMap.snd ℝ W V))
    (fun p ↦ by simp) (fun p ↦ by simp)

@[simp] public theorem shear_apply (D : V →L[ℝ] W) (p : W × V) :
    shear D p = (p.1 + D p.2, p.2) := rfl

public theorem coe_shear (D : V →L[ℝ] W) :
    (shear D : (W × V) →L[ℝ] (W × V))
      = (ContinuousLinearMap.fst ℝ W V + D.comp (ContinuousLinearMap.snd ℝ W V)).prod
          (ContinuousLinearMap.snd ℝ W V) := rfl

end Shear

section Extension

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **A smooth germ extends to a globally smooth function.** -/
public theorem exists_contDiff_eqOn_of_contDiffOn [FiniteDimensional ℝ X]
    {c : X → Y} {O : Set X} (hO : IsOpen O) {x₀ : X} (hx₀ : x₀ ∈ O)
    (hc : ContDiffOn ℝ ∞ c O) :
    ∃ (c' : X → Y) (O' : Set X), IsOpen O' ∧ x₀ ∈ O' ∧ O' ⊆ O ∧ ContDiff ℝ ∞ c' ∧
      ∀ x ∈ O', c' x = c x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x₀ hx₀
  let b : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hts : tsupport (b : X → ℝ) ⊆ O := by
    rw [b.tsupport_eq]
    intro y hy
    refine hball (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) ?_))
    show ε / 2 < ε
    linarith
  refine ⟨fun x ↦ b x • c x, Metric.ball x₀ (ε / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_, ?_, ?_⟩
  · exact fun x hx ↦ hball (Metric.ball_subset_ball (by linarith) hx)
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact (b.contDiff.contDiffAt).smul (hc.contDiffAt (hO.mem_nhds hx))
    · refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : X ↦ (0 : Y)) contDiffAt_const ?_
      filter_upwards [(isClosed_tsupport (b : X → ℝ)).isOpen_compl.mem_nhds
        (fun h ↦ hx (hts h))] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  · intro x hx
    have : (b : X → ℝ) x = 1 :=
      b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [this]

end Extension

section CriticalFiber

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The critical fibre.** -/
public theorem exists_critical_fiber [CompleteSpace W] [CompleteSpace V]
    {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcrit0 : fderiv ℝ f 0 = 0)
    (Q₀ : W ≃L[ℝ] (W →L[ℝ] ℝ))
    (hQ₀ : (Q₀ : W →L[ℝ] W →L[ℝ] ℝ) = blockW W V (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (ξ : V → W) (Uv : Set V), IsOpen Uv ∧ 0 ∈ Uv ∧ ξ 0 = 0 ∧ ContDiffOn ℝ ∞ ξ Uv ∧
      ∀ ζ ∈ Uv, ∀ η : W, fderiv ℝ f (ξ ζ, ζ) (η, 0) = 0 := by
  classical
  set L : ((W × V) →L[ℝ] ℝ) →L[ℝ] W :=
    (Q₀.symm : (W →L[ℝ] ℝ) →L[ℝ] W).comp
      ((ContinuousLinearMap.compL ℝ W (W × V) ℝ).flip (ContinuousLinearMap.inl ℝ W V)) with hLdef
  have hLapply : ∀ T : (W × V) →L[ℝ] ℝ,
      L T = Q₀.symm (T.comp (ContinuousLinearMap.inl ℝ W V)) := fun _ ↦ rfl
  set Φ : W × V → W × V := fun p ↦ (L (fderiv ℝ f p), p.2) with hΦdef
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hΦ : ContDiff ℝ ∞ Φ := (L.contDiff.comp hdf).prodMk contDiff_snd
  have hΦ0 : Φ 0 = 0 := by simp [hΦdef, hcrit0]
  set D2 : (W × V) →L[ℝ] (W × V) →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ f) 0 with hD2def
  set C : V →L[ℝ] W := (L.comp D2).comp (ContinuousLinearMap.inr ℝ W V) with hCdef
  have hd0 : HasFDerivAt (fderiv ℝ f) D2 0 :=
    ((hdf.differentiable (by simp)) 0).hasFDerivAt
  have hM : ∀ p : W × V, (L.comp D2) p = p.1 + C p.2 := by
    intro p
    have hsplit : (p.1, p.2) = ((p.1, (0 : V)) : W × V) + ((0 : W), p.2) := by simp
    have h1 : L (D2 (p.1, 0)) = p.1 := by
      have hb : (D2 (p.1, 0)).comp (ContinuousLinearMap.inl ℝ W V) = blockW W V D2 p.1 := rfl
      rw [hLapply, hb, hD2def, ← hQ₀]
      simp
    have h2 : L (D2 (0, p.2)) = C p.2 := rfl
    show L (D2 p) = p.1 + C p.2
    conv_lhs => rw [show p = ((p.1, (0 : V)) : W × V) + ((0 : W), p.2) from hsplit]
    rw [map_add, map_add, h1, h2]
  have hMshear : (L.comp D2).prod (ContinuousLinearMap.snd ℝ W V)
      = (shear C : (W × V) →L[ℝ] (W × V)) :=
    ContinuousLinearMap.ext fun p ↦ by
      show ((L.comp D2) p, p.2) = _
      rw [hM]; rfl
  have hΦd : HasFDerivAt Φ (shear C : (W × V) →L[ℝ] (W × V)) 0 := by
    rw [← hMshear]
    exact (L.hasFDerivAt.comp 0 hd0).prodMk hasFDerivAt_snd
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Φ' := hΦ.contDiffAt.toOpenPartialHomeomorph Φ hΦd hn with hΦ'def
  have hcoe : (Φ' : W × V → W × V) = Φ := rfl
  have h0src : (0 : W × V) ∈ Φ'.source :=
    hΦ.contDiffAt.mem_toOpenPartialHomeomorph_source hΦd hn
  have h0tgt : (0 : W × V) ∈ Φ'.target := by
    have h := hΦ.contDiffAt.image_mem_toOpenPartialHomeomorph_target hΦd hn
    rwa [hΦ0] at h
  have hsymm0 : Φ'.symm 0 = 0 := by
    have h := Φ'.left_inv h0src
    rwa [hcoe, hΦ0] at h
  set Sinv : Set (W × V) := (fderiv ℝ Φ) ⁻¹' Set.range
    (ContinuousLinearEquiv.toContinuousLinearMap :
      ((W × V) ≃L[ℝ] (W × V)) → ((W × V) →L[ℝ] (W × V))) with hSdef
  have hSopen : IsOpen Sinv :=
    ContinuousLinearEquiv.isOpen.preimage (hΦ.fderiv_right (m := ∞) (by simp)).continuous
  have h0S : (0 : W × V) ∈ Sinv := ⟨shear C, hΦd.fderiv.symm⟩
  set T : Set (W × V) := Φ'.target ∩ Φ'.symm ⁻¹' Sinv with hTdef
  have hTopen : IsOpen T := Φ'.isOpen_inter_preimage_symm hSopen
  have h0T : (0 : W × V) ∈ T := ⟨h0tgt, by rw [Set.mem_preimage, hsymm0]; exact h0S⟩
  have hsymm_cd : ∀ y ∈ T, ContDiffAt ℝ ∞ Φ'.symm y := by
    intro y hy
    obtain ⟨e, he⟩ := hy.2
    refine Φ'.contDiffAt_symm (f₀' := e) hy.1 ?_ hΦ.contDiffAt
    rw [hcoe, he]
    exact ((hΦ.differentiable (by simp)) _).hasFDerivAt
  set ι : V → W × V := fun ζ ↦ ((0 : W), ζ) with hιdef
  have hιcont : Continuous ι := by fun_prop
  refine ⟨fun ζ ↦ (Φ'.symm (ι ζ)).1, ι ⁻¹' T, hTopen.preimage hιcont, ?_, ?_, ?_, ?_⟩
  · show ι 0 ∈ T
    have hι0 : ι 0 = (0 : W × V) := rfl
    rw [hι0]; exact h0T
  · show (Φ'.symm (ι 0)).1 = 0
    have : ι 0 = (0 : W × V) := by simp [hιdef]
    rw [this, hsymm0]
    rfl
  · refine (hTopen.preimage hιcont).contDiffOn_iff.2 fun ζ hζ ↦ ?_
    exact (contDiff_fst.contDiffAt).comp ζ ((hsymm_cd _ hζ).comp ζ (by fun_prop))
  · intro ζ hζ η
    have hright : Φ (Φ'.symm (ι ζ)) = ι ζ := by
      have h := Φ'.right_inv hζ.1
      rwa [hcoe] at h
    have h2 : (Φ'.symm (ι ζ)).2 = ζ := congrArg Prod.snd hright
    have h1 : L (fderiv ℝ f (Φ'.symm (ι ζ))) = 0 := congrArg Prod.fst hright
    have hpt : ((Φ'.symm (ι ζ)).1, ζ) = Φ'.symm (ι ζ) := Prod.ext rfl h2.symm
    rw [hpt]
    have h3 : (fderiv ℝ f (Φ'.symm (ι ζ))).comp (ContinuousLinearMap.inl ℝ W V) = 0 := by
      have := congrArg (fun w : W ↦ (Q₀ : W →L[ℝ] W →L[ℝ] ℝ) w) h1
      simpa [hLapply] using this
    have := congrArg (fun A : W →L[ℝ] ℝ ↦ A η) h3
    simpa using this

end CriticalFiber

section ShiftedSplitting

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The `W`-block of the averaged Hessian along the shifted segment.** -/
@[expose] public def shiftedHessianAverage (f : W × V → ℝ) (c : V → W) (p : W × V) :
    W →L[ℝ] W →L[ℝ] ℝ :=
  blockW W V (TauCeti.hessianAverage f (c p.2, p.2) (p.1, 0))

public theorem shiftedHessianAverage_apply (f : W × V → ℝ) (c : V → W) (p : W × V) (w w' : W) :
    shiftedHessianAverage f c p w w'
      = TauCeti.hessianAverage f (c p.2, p.2) (p.1, 0) (w, 0) (w', 0) := rfl

public theorem shiftedHessianAverage_zero (f : W × V → ℝ) {c : V → W} (hc0 : c 0 = 0) :
    shiftedHessianAverage f c 0 = blockW W V (fderiv ℝ (fderiv ℝ f) 0) := by
  have h : ((c (0 : V) : W), (0 : V)) = (0 : W × V) := by rw [hc0]; rfl
  have h' : (((0 : W × V).1 : W), (0 : V)) = (0 : W × V) := rfl
  simp only [shiftedHessianAverage, Prod.snd_zero, h, h', TauCeti.hessianAverage_zero]

public theorem shiftedHessianAverage_symm {f : W × V → ℝ} (hf : ContDiff ℝ 2 f) (c : V → W)
    (p : W × V) (w w' : W) :
    shiftedHessianAverage f c p w w' = shiftedHessianAverage f c p w' w :=
  TauCeti.hessianAverage_symm hf _ _ _ _

public theorem contDiff_shiftedHessianAverage {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f)
    {c : V → W} (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (shiftedHessianAverage f c) := by
  have hbdd : IsBoundedSMul ℝ ((W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ ((W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) _ _ _
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hh : ContDiff ℝ ∞ (Function.uncurry fun (p : W × V) (t : ℝ) ↦
      (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (c p.2 + t • p.1, p.2)) := by
    have h1 : ContDiff ℝ ∞ fun z : (W × V) × ℝ ↦ 2 * (1 - z.2) := by fun_prop
    have h2 : ContDiff ℝ ∞ fun z : (W × V) × ℝ ↦
        fderiv ℝ (fderiv ℝ f) (c z.1.2 + z.2 • z.1.1, z.1.2) := by
      refine hd.comp ?_
      exact (((hc.comp (contDiff_snd.comp contDiff_fst)).add
        (contDiff_snd.smul (contDiff_fst.comp contDiff_fst))).prodMk
          (contDiff_snd.comp contDiff_fst))
    exact h1.smul h2
  have hint : ContDiff ℝ ∞ fun p : W × V ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (c p.2 + t • p.1, p.2) :=
    contDiff_integral_Icc_of_contDiff (⊤ : ℕ∞) _ hh
  have heq : (fun p : W × V ↦ TauCeti.hessianAverage f (c p.2, p.2) (p.1, 0))
      = fun p : W × V ↦ ∫ t in Set.Icc (0 : ℝ) 1,
        (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (c p.2 + t • p.1, p.2) := by
    funext p
    rw [TauCeti.hessianAverage_eq_integral_Icc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
    simp
  have hAvg : ContDiff ℝ ∞ fun p : W × V ↦ TauCeti.hessianAverage f (c p.2, p.2) (p.1, 0) := by
    rw [heq]; exact hint
  have hbw : ContDiff ℝ ∞ (blockW W V) := ContinuousLinearMap.contDiff _
  exact hbw.comp hAvg

/-- **The splitting in the `W` directions along a smooth shifted fibre.** -/
public theorem exists_shifted_congruence_normal_form [CompleteSpace W]
    {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f)
    {c : V → W} (hc : ContDiff ℝ ∞ c) (hc0 : c 0 = 0)
    {Uv : Set V} (hUv : IsOpen Uv) (h0Uv : (0 : V) ∈ Uv)
    (hcrit : ∀ ζ ∈ Uv, ∀ η : W, fderiv ℝ f (c ζ, ζ) (η, 0) = 0)
    (Q₀ : W ≃L[ℝ] (W →L[ℝ] ℝ))
    (hQ₀ : (Q₀ : W →L[ℝ] W →L[ℝ] ℝ) = blockW W V (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (R : W × V → (W →L[ℝ] W)) (U : Set (W × V)), IsOpen U ∧ 0 ∈ U ∧ R 0 = 1 ∧
      ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧ (∀ p ∈ U, p.2 ∈ Uv) ∧
      ∀ p ∈ U, f (p.1 + c p.2, p.2)
        = f (c p.2, p.2) + (2 : ℝ)⁻¹ * Q₀ (R p p.1) (R p p.1) := by
  obtain ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRinv, hRspec⟩ :=
    exists_congruence_of_symmetric_family_param (contDiff_shiftedHessianAverage hf hc)
      (shiftedHessianAverage_symm (hf.of_le (by decide)) c) 0 Q₀
      (by rw [hQ₀, shiftedHessianAverage_zero f hc0])
  refine ⟨R, U ∩ Prod.snd ⁻¹' Uv, hUopen.inter (hUv.preimage continuous_snd),
    ⟨h0U, h0Uv⟩, hR0, hRsmooth.mono Set.inter_subset_left,
    fun p hp ↦ hRinv p hp.1, fun p hp ↦ hp.2, fun p hp ↦ ?_⟩
  have hsplit : ((c p.2 : W), p.2) + (p.1, (0 : V)) = (p.1 + c p.2, p.2) :=
    Prod.ext (by simp [add_comm]) (by simp)
  have hTaylor := TauCeti.map_add_eq_add_hessianAverage (hf.of_le (by decide))
    ((c p.2 : W), p.2) (p.1, (0 : V))
  rw [hsplit, hcrit p.2 hp.2 p.1] at hTaylor
  have hkey : TauCeti.hessianAverage f (c p.2, p.2) (p.1, 0) (p.1, 0) (p.1, 0)
      = shiftedHessianAverage f c p p.1 p.1 := rfl
  rw [hTaylor, hkey, ← hRspec p hp.1 p.1 p.1]
  simp

/-- **The neighbourhood form of `exists_partial_congruence_normal_form`.** -/
public theorem exists_partial_congruence_normal_form_of_nhds [CompleteSpace W]
    {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f)
    {Uv : Set V} (hUv : IsOpen Uv) (h0Uv : (0 : V) ∈ Uv)
    (hcrit : ∀ ζ ∈ Uv, ∀ η : W, fderiv ℝ f (0, ζ) (η, 0) = 0)
    (Q₀ : W ≃L[ℝ] (W →L[ℝ] ℝ))
    (hQ₀ : (Q₀ : W →L[ℝ] W →L[ℝ] ℝ) = blockW W V (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (R : W × V → (W →L[ℝ] W)) (U : Set (W × V)), IsOpen U ∧ 0 ∈ U ∧ R 0 = 1 ∧
      ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧
      ∀ p ∈ U, f p = f (0, p.2) + (2 : ℝ)⁻¹ * Q₀ (R p p.1) (R p p.1) := by
  obtain ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRinv, -, hRspec⟩ :=
    exists_shifted_congruence_normal_form hf (c := fun _ ↦ (0 : W)) contDiff_const rfl hUv h0Uv
      hcrit Q₀ hQ₀
  exact ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRinv, fun p hp ↦ by simpa using hRspec p hp⟩

end ShiftedSplitting

section GromollMeyer

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The splitting.** -/
public theorem exists_gromoll_meyer_splitting [CompleteSpace W] [CompleteSpace V]
    [FiniteDimensional ℝ V]
    {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f) (hcrit0 : fderiv ℝ f 0 = 0)
    (Q₀ : W ≃L[ℝ] (W →L[ℝ] ℝ))
    (hQ₀ : (Q₀ : W →L[ℝ] W →L[ℝ] ℝ) = blockW W V (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (Θ : W × V → W × V) (c : V → W) (g : V → ℝ) (U : Set (W × V))
        (e : (W × V) ≃L[ℝ] (W × V)),
      IsOpen U ∧ 0 ∈ U ∧ Θ 0 = 0 ∧ ContDiffOn ℝ ∞ Θ U ∧
      HasFDerivAt Θ (e : (W × V) →L[ℝ] (W × V)) 0 ∧ (∀ q ∈ U, (Θ q).2 = q.2) ∧
      ContDiff ℝ ∞ c ∧ c 0 = 0 ∧
      (∀ q ∈ U, ∀ η : W, fderiv ℝ f (c q.2, q.2) (η, 0) = 0) ∧
      (∀ ζ : V, g ζ = f (c ζ, ζ) - f 0) ∧ g 0 = 0 ∧ ContDiff ℝ ∞ g ∧
      ∀ q ∈ U, f q - f 0 = (2 : ℝ)⁻¹ * Q₀ (Θ q).1 (Θ q).1 + g q.2 := by
  obtain ⟨ξ, Uv0, hUv0open, h0Uv0, hξ0, hξcd, hξcrit⟩ :=
    exists_critical_fiber hf hcrit0 Q₀ hQ₀
  obtain ⟨c, Uv, hUvopen, h0Uv, hUvsub, hc, hceq⟩ :=
    exists_contDiff_eqOn_of_contDiffOn hUv0open h0Uv0 hξcd
  have hc0 : c 0 = 0 := by rw [hceq 0 h0Uv, hξ0]
  have hcrit : ∀ ζ ∈ Uv, ∀ η : W, fderiv ℝ f (c ζ, ζ) (η, 0) = 0 := by
    intro ζ hζ η
    rw [hceq ζ hζ]
    exact hξcrit ζ (hUvsub hζ) η
  obtain ⟨R, U0, hU0open, h0U0, hR0, hRcd, hRinv, hRfib, hRspec⟩ :=
    exists_shifted_congruence_normal_form hf hc hc0 hUvopen h0Uv hcrit Q₀ hQ₀
  set σ : W × V → W × V := fun q ↦ (q.1 - c q.2, q.2) with hσdef
  have hσcd : ContDiff ℝ ∞ σ := (contDiff_fst.sub (hc.comp contDiff_snd)).prodMk contDiff_snd
  have hσ0 : σ 0 = 0 := by
    refine Prod.ext ?_ rfl
    show (0 : W) - c (0 : V) = 0
    rw [hc0, sub_zero]
  have hUopen : IsOpen (σ ⁻¹' U0) := hU0open.preimage hσcd.continuous
  have h0U : (0 : W × V) ∈ σ ⁻¹' U0 := by rw [Set.mem_preimage, hσ0]; exact h0U0
  set Dc : V →L[ℝ] W := fderiv ℝ c 0 with hDcdef
  have hcd0 : HasFDerivAt c Dc 0 := ((hc.differentiable (by simp)) 0).hasFDerivAt
  have hB : HasFDerivAt (fun q : W × V ↦ (σ q).1)
      (ContinuousLinearMap.fst ℝ W V - Dc.comp (ContinuousLinearMap.snd ℝ W V)) 0 := by
    have h2 : HasFDerivAt (fun q : W × V ↦ c q.2)
        (Dc.comp (ContinuousLinearMap.snd ℝ W V)) 0 :=
      HasFDerivAt.comp (0 : W × V) hcd0 hasFDerivAt_snd
    exact hasFDerivAt_fst.sub h2
  have hRσ : ContDiffOn ℝ ∞ (fun q ↦ R (σ q)) (σ ⁻¹' U0) :=
    hRcd.comp hσcd.contDiffOn (fun q hq ↦ hq)
  have hA : HasFDerivAt (fun q ↦ R (σ q)) (fderiv ℝ (fun q ↦ R (σ q)) 0) 0 :=
    ((hRσ.contDiffAt (hUopen.mem_nhds h0U)).differentiableAt (by simp)).hasFDerivAt
  have hshear : (ContinuousLinearMap.fst ℝ W V
        - Dc.comp (ContinuousLinearMap.snd ℝ W V)).prod (ContinuousLinearMap.snd ℝ W V)
      = (shear (-Dc) : (W × V) →L[ℝ] (W × V)) :=
    ContinuousLinearMap.ext fun q ↦ by
      show ((q.1 - Dc q.2 : W), q.2) = ((q.1 + (-Dc) q.2 : W), q.2)
      simp [sub_eq_add_neg]
  refine ⟨fun q ↦ (R (σ q) (σ q).1, q.2), c, fun ζ ↦ f (c ζ, ζ) - f 0, σ ⁻¹' U0, shear (-Dc),
    hUopen, h0U, ?_, ?_, ?_, fun q _ ↦ rfl, hc, hc0, ?_, fun ζ ↦ rfl, ?_, ?_, ?_⟩
  · show (R (σ 0) (σ 0).1, (0 : W × V).2) = 0
    rw [hσ0, hR0]
    rfl
  · exact (hRσ.clm_apply (contDiff_fst.comp hσcd).contDiffOn).prodMk contDiff_snd.contDiffOn
  · have hclm := hA.clm_apply hB
    have he : (R (σ 0)).comp (ContinuousLinearMap.fst ℝ W V
          - Dc.comp (ContinuousLinearMap.snd ℝ W V))
        + (fderiv ℝ (fun q ↦ R (σ q)) 0).flip ((σ 0).1)
        = ContinuousLinearMap.fst ℝ W V - Dc.comp (ContinuousLinearMap.snd ℝ W V) := by
      rw [hσ0, hR0]
      simp [ContinuousLinearMap.one_def]
    rw [he] at hclm
    rw [← hshear]
    exact hclm.prodMk hasFDerivAt_snd
  · intro q hq η
    exact hcrit q.2 (hRfib (σ q) hq) η
  · show f (c 0, (0 : V)) - f 0 = 0
    have : ((c (0 : V) : W), (0 : V)) = (0 : W × V) := by rw [hc0]; rfl
    rw [this, sub_self]
  · exact (hf.comp (hc.prodMk contDiff_id)).sub contDiff_const
  · intro q hq
    have hspec := hRspec (σ q) hq
    have e1 : (((σ q).1 + c (σ q).2 : W), (σ q).2) = q := by
      refine Prod.ext ?_ rfl
      show q.1 - c q.2 + c q.2 = q.1
      abel
    rw [e1] at hspec
    show f q - f 0 = (2 : ℝ)⁻¹ * Q₀ (R (σ q) (σ q).1) (R (σ q) (σ q).1) + (f (c q.2, q.2) - f 0)
    rw [hspec]
    show f (c q.2, q.2) + (2 : ℝ)⁻¹ * Q₀ (R (σ q) (σ q).1) (R (σ q) (σ q).1) - f 0 = _
    ring

end GromollMeyer

end AISafetyAtlas.SingularLearning

end
