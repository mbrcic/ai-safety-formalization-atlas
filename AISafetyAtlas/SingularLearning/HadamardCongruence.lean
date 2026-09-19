module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Congruence of a smooth family of bilinear forms, over an arbitrary parameter

`vendor/TauCeti/` supplies Palais's congruence lemma and the Banach Morse lemma built on it.
This module carries three things forward that a consumer of that cone needs and that the cone
does not state.

## What is here

* **Invertibility of the congruence family.** `TauCeti.exists_congruence_of_symmetric_family`
  produces `R` with `R 0 = 1` and `ContDiffOn ℝ ∞ R U`, and — as
  `vendor/TauCeti/PROVENANCE.md` records in as many words — it does **not** claim that `R v` is
  invertible. `exists_open_isInvertible` derives that on a smaller open set, from continuity and
  the openness of the invertible operators (`ContinuousLinearEquiv.isOpen`), and
  `exists_congruence_isInvertible_of_symmetric_family` is the vendored statement with that
  clause added.

* **An arbitrary parameter space.** The vendored congruence indexes its family of forms on `E`
  by `E` itself, which is all the Morse lemma needs, because there the parameter *is* the
  displacement. A Morse–Bott argument needs a family of forms on `W` indexed by `W × V`, and no
  substitution turns one into the other: the parameter space and the form space are genuinely
  different there. `exists_congruence_of_symmetric_family_param` is Palais's argument with the
  two separated. Its proof is upstream's, with the index type generalised and the base point
  moved off the origin; the operator square root it runs on is the vendored
  `TauCeti.sqrtNearOne`, not a second construction.

* **A parameterised splitting, in the Gromoll–Meyer form.**
  `exists_partial_congruence_normal_form` is the consequence: for `f : W × V → ℝ` whose
  `W`-directional derivative vanishes along `{0} × V`, and whose `W`-block Hessian at the origin
  is invertible, there is a smooth invertible family `R` on a neighbourhood of the origin with

      f (η, ζ) = f (0, ζ) + 2⁻¹ * Q₀ (R (η, ζ) η) (R (η, ζ) η),

  where `Q₀` is the `W`-block of the Hessian at the origin. So `ψ (η, ζ) = R (η, ζ) η` is a
  `ζ`-dependent chart in the `W` directions, flattening the `W` part of `f` onto one fixed
  quadratic form — the same form for every `ζ` — and leaving the germ `g ζ = f (0, ζ)` on the
  fibre untouched. Nothing is assumed about `g`; in particular it need not vanish, and it need
  not be quadratic. `exists_partial_congruence_normal_form_of_vanishing` is the strict
  Morse–Bott special case `g = 0`.

## The hypothesis that is assumed, not derived

`∂_W f (0, ζ) = 0` is a hypothesis of `exists_partial_congruence_normal_form`. It says that
`{0} × V` is critical in the `W` directions, which is what makes the first-order term of the
Taylor expansion in `η` drop out; establishing it for a particular `f` is a separate obligation
and is not attempted here. Nothing in this module derives it, and nothing here says that any
particular loss satisfies it.

## What is *not* here

This is not the full Gromoll–Meyer splitting lemma. That is
`exists_gromoll_meyer_splitting`, in `CriticalFiber`, which supplies the critical
fibre this module assumes and localizes the hypothesis below to a neighbourhood. That lemma takes a degenerate critical point
and *constructs* the splitting `W ⊕ V` — the nondegenerate directions and the kernel of the
Hessian — before producing the germ on the kernel. Here the splitting is handed in: `V` is given,
and the criticality of `f` along `{0} × V` in the `W` directions is a hypothesis. What is
produced is the second half of that lemma's conclusion, the normal form on the `W` factor
together with an arbitrary germ on the `V` factor. The gap recorded at the end of
`vendor/TauCeti/PROVENANCE.md` is therefore narrowed, not closed: what remains is the
construction of the splitting itself.

## What was already present, and is not restated

`TauCeti.IsNondegenerateCriticalPoint.exists_normal_form` is the Morse lemma in the form
`f (x + v) = f x + 2⁻¹ * D²f x (φ v) (φ v)` with `φ 0 = 0` and `fderiv ℝ φ 0 = id`. It is not
reproved. `exists_normal_form_of_hessian_nondegenerate` only restates it over a
finite-dimensional space with the nondegeneracy hypothesis in the form a matrix-space consumer
can discharge — the classical one, that the Hessian bilinear form annihilates no nonzero
vector — using the vendored `TauCeti.ContinuousLinearMap.isInvertible_of_injective` to reach
invertibility of the map into the dual. `exists_normal_form_euclidean` is that statement at
`EuclideanSpace ℝ (Fin n)`.
-/

noncomputable section

open Filter Topology

open scoped ContDiff

namespace AISafetyAtlas.SingularLearning

section Congruence

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ P] in
/-- **Invertibility near a point where the family is the identity.** A family of operators
continuous on an open set and equal to `1` at one of its points is invertible on a smaller open
neighbourhood of that point, because the invertible operators are open
(`ContinuousLinearEquiv.isOpen`). This is the clause
`TauCeti.exists_congruence_of_symmetric_family` deliberately does not claim. -/
public theorem exists_open_isInvertible [CompleteSpace E]
    {R : P → (E →L[ℝ] E)} {U : Set P} {p₀ : P}
    (hUopen : IsOpen U) (hp₀ : p₀ ∈ U) (hR₀ : R p₀ = 1) (hcont : ContinuousOn R U) :
    ∃ U' : Set P, U' ⊆ U ∧ IsOpen U' ∧ p₀ ∈ U' ∧ ∀ p ∈ U', (R p).IsInvertible := by
  refine ⟨U ∩ R ⁻¹' Set.range (ContinuousLinearEquiv.toContinuousLinearMap :
      (E ≃L[ℝ] E) → (E →L[ℝ] E)), Set.inter_subset_left,
    hcont.isOpen_inter_preimage hUopen ContinuousLinearEquiv.isOpen, ⟨hp₀, ?_⟩, fun p hp ↦ hp.2⟩
  simp only [Set.mem_preimage, hR₀]
  exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩

/-- **The vendored congruence, with invertibility supplied.** Identical to
`TauCeti.exists_congruence_of_symmetric_family` except that `R v` is now asserted invertible on
the (smaller) neighbourhood. -/
public theorem exists_congruence_isInvertible_of_symmetric_family [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B)
    (hsymm : ∀ v w w', B v w w' = B v w' w)
    (B₀ : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB₀ : (B₀ : E →L[ℝ] E →L[ℝ] ℝ) = B 0) :
    ∃ (R : E → (E →L[ℝ] E)) (U : Set E), IsOpen U ∧ 0 ∈ U ∧ R 0 = 1 ∧
      ContDiffOn ℝ ∞ R U ∧ (∀ v ∈ U, (R v).IsInvertible) ∧
      ∀ v ∈ U, ∀ w w', B₀ (R v w) (R v w') = B v w w' := by
  obtain ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRspec⟩ :=
    TauCeti.exists_congruence_of_symmetric_family hB hsymm B₀ hB₀
  obtain ⟨U', hU'sub, hU'open, h0U', hU'inv⟩ :=
    exists_open_isInvertible hUopen h0U hR0 hRsmooth.continuousOn
  exact ⟨R, U', hU'open, h0U', hR0, hRsmooth.mono hU'sub, hU'inv,
    fun v hv ↦ hRspec v (hU'sub hv)⟩

/-- **Congruence of a smooth symmetric family over an arbitrary parameter space.** A family `B`
of symmetric continuous bilinear forms on a Banach space `E`, depending smoothly on a parameter
in a normed space `P`, whose value at a base parameter `p₀` is invertible as a map `E → E∗`, is
near `p₀` the congruence of that value by a smooth family of invertible operators equal to the
identity at `p₀`.

`TauCeti.exists_congruence_of_symmetric_family` is the case `P = E`, `p₀ = 0`. The proof is
upstream's — the comparison operator `C p = B₀⁻¹ ∘ B p` is self-adjoint for the `B₀` pairing, so
its square root `TauCeti.sqrtNearOne` is too, and self-adjointness turns `R p * R p = C p` into
the congruence identity — with the index type separated from the form space. -/
public theorem exists_congruence_of_symmetric_family_param [CompleteSpace E]
    {B : P → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B)
    (hsymm : ∀ p w w', B p w w' = B p w' w) (p₀ : P)
    (B₀ : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB₀ : (B₀ : E →L[ℝ] E →L[ℝ] ℝ) = B p₀) :
    ∃ (R : P → (E →L[ℝ] E)) (U : Set P), IsOpen U ∧ p₀ ∈ U ∧ R p₀ = 1 ∧
      ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧
      ∀ p ∈ U, ∀ w w', B₀ (R p w) (R p w') = B p w w' := by
  set adj : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E)).comp
      (((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)).flip
          (B₀ : E →L[ℝ] E →L[ℝ] ℝ)).comp
        ((ContinuousLinearMap.compL ℝ E E ℝ).flip)) with hadjdef
  have adj_spec : ∀ (T : E →L[ℝ] E) (w w' : E), B₀ (adj T w) w' = B₀ w (T w') := by
    intro T w w'
    simp [hadjdef]
  have hdet : ∀ T₁ T₂ : E →L[ℝ] E, (∀ w w', B₀ (T₁ w) w' = B₀ (T₂ w) w') → T₁ = T₂ := by
    intro T₁ T₂ h
    ext w
    refine B₀.injective ?_
    ext w'
    exact h w w'
  have adj_one : adj 1 = 1 := by
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec]
    simp
  have adj_mul : ∀ S T : E →L[ℝ] E, adj (S * T) = adj T * adj S := by
    intro S T
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec, mul_apply_eq_comp, mul_apply_eq_comp, adj_spec, adj_spec]
  have hB₀symm : ∀ w w' : E, B₀ w w' = B₀ w' w := by
    intro w w'
    have h := hsymm p₀ w w'
    rw [← hB₀] at h
    simpa using h
  set C : P → (E →L[ℝ] E) := fun p ↦ (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E).comp (B p) with hCdef
  have hCapply : ∀ (p : P) (w w' : E), B₀ (C p w) w' = B p w w' := by
    intro p w w'
    simp [hCdef]
  have hC0 : C p₀ = 1 := by
    refine hdet _ _ fun w w' ↦ ?_
    rw [hCapply, ← hB₀]
    simp
  have hCsmooth : ContDiff ℝ ∞ C := by
    have h := (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E)).contDiff.comp hB
    exact h
  have hCadj : ∀ p, adj (C p) = C p := by
    intro p
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec, hCapply, hB₀symm, hCapply, hsymm]
  let R : P → (E →L[ℝ] E) := fun p ↦ TauCeti.sqrtNearOne (E →L[ℝ] E) (C p)
  have hR0 : R p₀ = 1 := by simp [R, hC0]
  have hten : Filter.Tendsto C (𝓝 p₀) (𝓝 1) :=
    hC0 ▸ hCsmooth.continuous.continuousAt
  have htenR : Filter.Tendsto R (𝓝 p₀) (𝓝 1) := by
    simpa [R, Function.comp_def] using
      (TauCeti.continuousAt_sqrtNearOne (A := E →L[ℝ] E)).tendsto.comp hten
  have htenA : Filter.Tendsto (fun p ↦ adj (R p)) (𝓝 p₀) (𝓝 1) := by
    simpa [adj_one, Function.comp_def] using (adj.continuous.tendsto 1).comp htenR
  have e1 := hten.eventually (TauCeti.eventually_mul_self_sqrtNearOne (A := E →L[ℝ] E))
  have e2 := htenA.eventually (TauCeti.eventually_sqrtNearOne_mul_self (A := E →L[ℝ] E))
  have hspec : ∀ᶠ p in 𝓝 p₀, ∀ w w', B₀ (R p w) (R p w') = B p w w' := by
    filter_upwards [e1, e2] with p h1 h2
    have h3 : adj (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p)) *
        adj (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p)) = C p := by
      rw [← adj_mul, h1, hCadj]
    have h4 : TauCeti.sqrtNearOne (E →L[ℝ] E) (C p)
        = adj (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p)) := by
      rw [h3] at h2
      exact h2
    have hself : ∀ w w' : E, B₀ (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p) w) w'
        = B₀ w (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p) w') := by
      intro w w'
      conv_lhs => rw [h4]
      exact adj_spec _ w w'
    intro w w'
    calc B₀ (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p) w)
            (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p) w')
        = B₀ w (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p)
            (TauCeti.sqrtNearOne (E →L[ℝ] E) (C p) w')) := hself w _
      _ = B₀ w ((TauCeti.sqrtNearOne (E →L[ℝ] E) (C p) *
            TauCeti.sqrtNearOne (E →L[ℝ] E) (C p)) w') := by rw [mul_apply_eq_comp]
      _ = B₀ w (C p w') := by rw [h1]
      _ = B p w w' := by
          rw [hB₀symm w (C p w'), hCapply p w' w]
          exact hsymm p w' w
  obtain ⟨W, hWsub, hWopen, h0W⟩ := mem_nhds_iff.1 hspec
  let S : Set (E →L[ℝ] E) := {a | AnalyticAt ℝ (TauCeti.sqrtNearOne (E →L[ℝ] E)) a}
  have hSopen : IsOpen S := isOpen_analyticAt ℝ (TauCeti.sqrtNearOne (E →L[ℝ] E))
  have h1S : (1 : E →L[ℝ] E) ∈ S := TauCeti.analyticAt_sqrtNearOne
  let U : Set P := W ∩ C ⁻¹' S
  have hUopen : IsOpen U := hWopen.inter (hSopen.preimage hCsmooth.continuous)
  have h0U : p₀ ∈ U := ⟨h0W, by simpa [hC0] using h1S⟩
  have hRsmooth : ContDiffOn ℝ ∞ R U := by
    intro p hp
    have hsqrt : ContDiffAt ℝ ∞ (TauCeti.sqrtNearOne (E →L[ℝ] E)) (C p) := hp.2.contDiffAt
    have hcomp := (hsqrt.comp p hCsmooth.contDiffAt).contDiffWithinAt (s := U)
    rwa [Function.comp_def] at hcomp
  obtain ⟨U', hU'sub, hU'open, hp₀U', hU'inv⟩ :=
    exists_open_isInvertible hUopen h0U hR0 hRsmooth.continuousOn
  exact ⟨R, U', hU'open, hp₀U', hR0, hRsmooth.mono hU'sub, hU'inv,
    fun p hp ↦ hWsub (hU'sub hp).1⟩

end Congruence

section NormalForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Morse lemma in finite dimensions, with the classical nondegeneracy hypothesis.** This
is `TauCeti.IsNondegenerateCriticalPoint.exists_normal_form`, restated so that the hypothesis is
the one a consumer working with an explicit Hessian can discharge: that the Hessian bilinear form
annihilates no nonzero vector. In finite dimensions that is equivalent to invertibility of the
second derivative as a map into the dual space, which is what the vendored statement asks for and
what `TauCeti.ContinuousLinearMap.isInvertible_of_injective` supplies. Nothing is reproved. -/
public theorem exists_normal_form_of_hessian_nondegenerate [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiff ℝ ∞ f) (hcrit : fderiv ℝ f x = 0)
    (hnd : ∀ w : E, (∀ w' : E, fderiv ℝ (fderiv ℝ f) x w w' = 0) → w = 0) :
    ∃ (φ : E → E) (U : Set E), IsOpen U ∧ 0 ∈ U ∧ φ 0 = 0 ∧ ContDiffOn ℝ ∞ φ U ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ v ∈ U, f (x + v) = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v) := by
  refine TauCeti.IsNondegenerateCriticalPoint.exists_normal_form hf
    ⟨(hf.of_le (by decide)).contDiffAt, hcrit, ?_⟩
  refine TauCeti.ContinuousLinearMap.isInvertible_of_injective ?_
  intro a b hab
  have h0 : fderiv ℝ (fderiv ℝ f) x (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.1 (hnd (a - b) fun w' ↦ by rw [h0]; simp)

/-- **The Morse lemma on `EuclideanSpace ℝ (Fin n)`.** The instance of
`exists_normal_form_of_hessian_nondegenerate` that a consumer whose parameter space is a space of
matrices, reindexed to `Fin`-coordinates, applies directly. -/
public theorem exists_normal_form_euclidean {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiff ℝ ∞ f) (hcrit : fderiv ℝ f x = 0)
    (hnd : ∀ w : EuclideanSpace ℝ (Fin n),
      (∀ w' : EuclideanSpace ℝ (Fin n), fderiv ℝ (fderiv ℝ f) x w w' = 0) → w = 0) :
    ∃ (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (U : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen U ∧ 0 ∈ U ∧ φ 0 = 0 ∧ ContDiffOn ℝ ∞ φ U ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 ∧
      ∀ v ∈ U, f (x + v) = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v) :=
  exists_normal_form_of_hessian_nondegenerate hf hcrit hnd

end NormalForm

section MorseBott

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Restriction of a continuous bilinear form on `W × V` to its `W` block**, packaged as a
continuous linear map so that smooth dependence on a parameter transports for free. -/
@[expose] public def blockW (W V : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ((W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ W ((W × V) →L[ℝ] ℝ) (W →L[ℝ] ℝ)
      ((ContinuousLinearMap.compL ℝ W (W × V) ℝ).flip (ContinuousLinearMap.inl ℝ W V))).comp
    ((ContinuousLinearMap.compL ℝ W (W × V) ((W × V) →L[ℝ] ℝ)).flip
      (ContinuousLinearMap.inl ℝ W V))

@[simp] public theorem blockW_apply (T : (W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) (w w' : W) :
    blockW W V T w w' = T (w, 0) (w', 0) := rfl

/-- **The `W`-block of the averaged Hessian along the segment from `(0, ζ)` to `(η, ζ)`.** This
is the family of forms on `W`, indexed by the whole of `W × V`, that
`exists_congruence_of_symmetric_family_param` is applied to. -/
@[expose] public def partialHessianAverage (f : W × V → ℝ) (p : W × V) : W →L[ℝ] W →L[ℝ] ℝ :=
  blockW W V (TauCeti.hessianAverage f (0, p.2) (p.1, 0))

public theorem partialHessianAverage_apply (f : W × V → ℝ) (p : W × V) (w w' : W) :
    partialHessianAverage f p w w'
      = TauCeti.hessianAverage f (0, p.2) (p.1, 0) (w, 0) (w', 0) := rfl

@[simp] public theorem partialHessianAverage_zero (f : W × V → ℝ) :
    partialHessianAverage f 0 = blockW W V (fderiv ℝ (fderiv ℝ f) 0) := by
  have h : ((0 : W), (0 : V)) = (0 : W × V) := rfl
  simp only [partialHessianAverage, Prod.fst_zero, Prod.snd_zero, h,
    TauCeti.hessianAverage_zero]

/-- The `W`-block of the averaged Hessian is symmetric, because the averaged Hessian is. -/
public theorem partialHessianAverage_symm {f : W × V → ℝ} (hf : ContDiff ℝ 2 f) (p : W × V)
    (w w' : W) : partialHessianAverage f p w w' = partialHessianAverage f p w' w :=
  TauCeti.hessianAverage_symm hf _ _ _ _

/-- **The `W`-block of the averaged Hessian depends smoothly on the whole parameter `(η, ζ)`.**
The vendored smoothness lemma for the averaged Hessian gives smoothness in the displacement at a
fixed base point; here the base point `(0, ζ)` moves too, so the parametrised-integral regularity
theorem is applied directly to the pair. -/
public theorem contDiff_partialHessianAverage {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialHessianAverage f) := by
  have hbdd : IsBoundedSMul ℝ ((W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ ((W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) _ _ _
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hh : ContDiff ℝ ∞ (Function.uncurry fun (p : W × V) (t : ℝ) ↦
      (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (t • p.1, p.2)) := by
    have h1 : ContDiff ℝ ∞ fun z : (W × V) × ℝ ↦ 2 * (1 - z.2) := by fun_prop
    have h2 : ContDiff ℝ ∞ fun z : (W × V) × ℝ ↦
        fderiv ℝ (fderiv ℝ f) (z.2 • z.1.1, z.1.2) := hd.comp (by fun_prop)
    exact h1.smul h2
  have hint : ContDiff ℝ ∞ fun p : W × V ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (t • p.1, p.2) :=
    contDiff_integral_Icc_of_contDiff (⊤ : ℕ∞) _ hh
  have heq : (fun p : W × V ↦ TauCeti.hessianAverage f (0, p.2) (p.1, 0))
      = fun p : W × V ↦ ∫ t in Set.Icc (0 : ℝ) 1,
        (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (t • p.1, p.2) := by
    funext p
    rw [TauCeti.hessianAverage_eq_integral_Icc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
    simp
  have hAvg : ContDiff ℝ ∞ fun p : W × V ↦ TauCeti.hessianAverage f (0, p.2) (p.1, 0) := by
    rw [heq]; exact hint
  have hbw : ContDiff ℝ ∞ (blockW W V) := ContinuousLinearMap.contDiff _
  exact hbw.comp hAvg

/-- **A splitting in the `W` directions, in the Gromoll–Meyer form.**

For `f : W × V → ℝ` smooth whose `W`-directional derivative vanishes along `{0} × V`, and whose
`W`-block Hessian at the origin is invertible as a map `W → W∗`, there is a smooth family `R` of
invertible operators on `W`, defined on a neighbourhood of the origin in `W × V` and equal to the
identity there, with

    f (η, ζ) = f (0, ζ) + 2⁻¹ * Q₀ (R (η, ζ) η) (R (η, ζ) η).

So `ψ (η, ζ) = R (η, ζ) η` is a `ζ`-dependent chart of the `W` directions carrying `f` to the
single quadratic form `Q₀` — the same form at every `ζ` — plus the germ `g ζ = f (0, ζ)` on the
fibre. Nothing is assumed or proved about `g`: it may be nonconstant, and it is exactly the
complementary germ a splitting lemma leaves behind.

`exists_partial_congruence_normal_form_of_vanishing` is the special case `g = 0`, the strict
Morse–Bott setting.

The vanishing of the `W`-derivative along `{0} × V` is **assumed**: this statement does not
establish that `{0} × V` is critical in the `W` directions for any particular `f`, and it does
not construct the complement `V`. -/
public theorem exists_partial_congruence_normal_form [CompleteSpace W]
    {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcrit : ∀ (ζ : V) (η : W), fderiv ℝ f (0, ζ) (η, 0) = 0)
    (Q₀ : W ≃L[ℝ] (W →L[ℝ] ℝ))
    (hQ₀ : (Q₀ : W →L[ℝ] W →L[ℝ] ℝ) = blockW W V (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (R : W × V → (W →L[ℝ] W)) (U : Set (W × V)), IsOpen U ∧ 0 ∈ U ∧ R 0 = 1 ∧
      ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧
      ∀ p ∈ U, f p = f (0, p.2) + (2 : ℝ)⁻¹ * Q₀ (R p p.1) (R p p.1) := by
  obtain ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRinv, hRspec⟩ :=
    exists_congruence_of_symmetric_family_param (contDiff_partialHessianAverage hf)
      (partialHessianAverage_symm (hf.of_le (by decide))) 0 Q₀
      (by rw [hQ₀, partialHessianAverage_zero])
  refine ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRinv, fun p hp ↦ ?_⟩
  have hsplit : ((0 : W), p.2) + (p.1, (0 : V)) = p := by
    simp
  have hTaylor := TauCeti.map_add_eq_add_hessianAverage (hf.of_le (by decide))
    ((0 : W), p.2) (p.1, (0 : V))
  rw [hsplit, hcrit p.2 p.1] at hTaylor
  have hkey : TauCeti.hessianAverage f (0, p.2) (p.1, 0) (p.1, 0) (p.1, 0)
      = partialHessianAverage f p p.1 p.1 := rfl
  rw [hTaylor, hkey, ← hRspec p hp p.1 p.1]
  simp

/-- **The strict Morse–Bott case** of `exists_partial_congruence_normal_form`: when `f` vanishes
identically on `{0} × V`, the complementary germ disappears and `f` is exactly its `W`-block
Hessian form read in the `ζ`-dependent chart. The extra hypothesis `f (0, ζ) = 0` is genuinely
extra — a smooth `f` with critical `W`-directions along `{0} × V` may grow in the `ζ`
directions, so the general form above is the one that always applies. -/
public theorem exists_partial_congruence_normal_form_of_vanishing [CompleteSpace W]
    {f : W × V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hval : ∀ ζ : V, f (0, ζ) = 0)
    (hcrit : ∀ (ζ : V) (η : W), fderiv ℝ f (0, ζ) (η, 0) = 0)
    (Q₀ : W ≃L[ℝ] (W →L[ℝ] ℝ))
    (hQ₀ : (Q₀ : W →L[ℝ] W →L[ℝ] ℝ) = blockW W V (fderiv ℝ (fderiv ℝ f) 0)) :
    ∃ (R : W × V → (W →L[ℝ] W)) (U : Set (W × V)), IsOpen U ∧ 0 ∈ U ∧ R 0 = 1 ∧
      ContDiffOn ℝ ∞ R U ∧ (∀ p ∈ U, (R p).IsInvertible) ∧
      ∀ p ∈ U, f p = (2 : ℝ)⁻¹ * Q₀ (R p p.1) (R p p.1) := by
  obtain ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRinv, hRspec⟩ :=
    exists_partial_congruence_normal_form hf hcrit Q₀ hQ₀
  refine ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRinv, fun p hp ↦ ?_⟩
  rw [hRspec p hp, hval p.2, zero_add]

/-- **The fibre chart really is a chart.** For a smooth family `R` on a neighbourhood of `(0, ζ)`,
the map `η ↦ R (η, ζ) η` has derivative `R (0, ζ)` at the origin of `W`. Combined with the
invertibility clause of `exists_partial_congruence_normal_form` this says that, at each parameter
`ζ` near `0`, the change of variables in the `W` directions is a local diffeomorphism at the
critical manifold. -/
public theorem hasFDerivAt_apply_fst {R : W × V → (W →L[ℝ] W)} {U : Set (W × V)} {ζ : V}
    (hUopen : IsOpen U) (hmem : ((0 : W), ζ) ∈ U) (hR : ContDiffOn ℝ ∞ R U) :
    HasFDerivAt (fun η : W ↦ R (η, ζ) η) (R (0, ζ)) 0 := by
  have h1 : ContDiffAt ℝ ∞ R ((0 : W), ζ) := (hR _ hmem).contDiffAt (hUopen.mem_nhds hmem)
  have hAt : ContDiffAt ℝ ∞ (fun η : W ↦ R (η, ζ)) 0 := by
    have := h1.comp (0 : W) (f := fun η : W ↦ (η, ζ)) (by fun_prop)
    rwa [Function.comp_def] at this
  have hd : HasFDerivAt (fun η : W ↦ R (η, ζ) η)
      ((R (0, ζ)).comp (ContinuousLinearMap.id ℝ W)
        + (fderiv ℝ (fun η : W ↦ R (η, ζ)) 0).flip 0) 0 :=
    ((hAt.differentiableAt (by simp)).hasFDerivAt).clm_apply (hasFDerivAt_id (𝕜 := ℝ) (0 : W))
  have he : (R (0, ζ)).comp (ContinuousLinearMap.id ℝ W)
      + (fderiv ℝ (fun η : W ↦ R (η, ζ)) 0).flip 0 = R (0, ζ) := by
    ext w
    simp
  rwa [he] at hd

end MorseBott

end AISafetyAtlas.SingularLearning

end
