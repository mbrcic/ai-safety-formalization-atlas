module

public import AISafetyAtlas.LinearSystems.Dynamics
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The flow of `ẋ = Ax`, and the only norm it needs

The remaining half of Klamka's §25 cell is the **sufficiency** of the rank
criterion for reachability: a controllable pair reaches every state. That
direction has to build an input, and every construction of one runs through the
matrix exponential. This module is that object and its four facts.

`Matrix (Fin n) (Fin n) ℂ` carries no default norm in Mathlib, and the
exponential needs a Banach-algebra one. `Matrix.Norms.Operator` is the scoped
instance under which matrix multiplication is submultiplicative; it is opened
here and nowhere else in the cluster, so no statement outside this file depends
on the choice.

## What is here

* `flow A t` is `exp (t • A)`, print's `Φ(t)`.
* `flow_mul_flow_neg` is its invertibility.
* `commute_flow` is `Φ(t) A = A Φ(t)`, proved from **uniqueness of the
  derivative** rather than from the series: Mathlib gives the derivative of
  `t ↦ exp (t • A)` in both multiplication orders, so the two values agree.
* `hasDerivAt_flow_entry` is the entrywise derivative, which is what a
  coordinatewise product rule consumes. It is obtained by composing with the
  entry-evaluation map as a *continuous linear* map -- available because the
  matrix space is finite-dimensional over `ℝ`, so it does not depend on which
  norm the instance above picked.
* `flow_isTrajectory` is the point of all of it: the free run through a state is
  a trajectory in the sense of `Dynamics`.
-/

namespace AISafetyAtlas.LinearSystems

open scoped Matrix.Norms.Operator
open Matrix

variable {n : ℕ}

/-- **Print's `Φ(t) = e^{At}`.** -/
@[expose] public noncomputable def flow (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (t • A)

@[simp] public theorem flow_zero (A : Matrix (Fin n) (Fin n) ℂ) : flow A 0 = 1 := by
  simp [flow, NormedSpace.exp_zero]

/-- **The flow is invertible, with the reverse flow as inverse.** -/
public theorem flow_mul_flow_neg (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    flow A t * flow A (-t) = 1 := by
  have hcomm : Commute (t • A) (-(t • A)) := (Commute.refl (t • A)).neg_right
  have h : NormedSpace.exp ((t • A) + -(t • A))
      = NormedSpace.exp (t • A) * NormedSpace.exp (-(t • A)) :=
    NormedSpace.exp_add_of_commute hcomm
  have hzero : (t • A) + -(t • A) = 0 := by abel
  rw [hzero, NormedSpace.exp_zero] at h
  simpa [flow, neg_smul] using h.symm

/-- **The state matrix commutes with its own flow.** Mathlib differentiates
`t ↦ exp (t • A)` in both multiplication orders; a function has one derivative,
so the two values are equal. No series manipulation is needed. -/
public theorem commute_flow (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    flow A t * A = A * flow A t :=
  (hasDerivAt_exp_smul_const A t).unique (hasDerivAt_exp_smul_const' A t)

/-- Entry evaluation on square matrices, as a continuous linear map over `ℝ`.
Continuity is automatic from finite-dimensionality, so this does not read the
norm instance. -/
@[expose] public noncomputable def entryCLM (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := by intro M N; simp
      map_smul' := by intro r M; simp }

@[simp] public theorem entryCLM_apply (i j : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) :
    entryCLM i j M = M i j := rfl

/-- **The flow differentiates entrywise.** -/
public theorem hasDerivAt_flow_entry (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow A s i j) ((flow A t * A) i j) t := by
  exact (entryCLM i j).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const A t)

/-- **The flow applied to a fixed state differentiates**, which is the shape the
state equation asks for. -/
public theorem hasDerivAt_flow_mulVec (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow A s *ᵥ v) ((A * flow A t) *ᵥ v) t := by
  rw [hasDerivAt_pi]
  intro i
  have hval : ((A * flow A t) *ᵥ v) i = ∑ j : Fin n, (flow A t * A) i j * v j := by
    rw [← commute_flow]
    rfl
  rw [hval]
  have hfun : (fun s : ℝ => (flow A s *ᵥ v) i) = fun s : ℝ => ∑ j : Fin n, flow A s i j * v j :=
    rfl
  rw [hfun]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_flow_entry A i j t).mul_const (v j)

/-- **The free run through a state is a trajectory**, at any input, because the
input enters through `B *ᵥ 0`. This is the object the sufficiency direction has
to drive, and it is the first time the cluster exhibits a solution of print's
equation that is not an eigen-run. -/
public theorem flow_isTrajectory (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) (v : Fin n → ℂ) (S : Set ℝ) :
    IsTrajectoryOn A B S (fun t => flow A t *ᵥ v) (fun _ => 0) := by
  intro t _
  have hval : A *ᵥ ((fun s : ℝ => flow A s *ᵥ v) t) + B *ᵥ ((fun _ : ℝ => (0 : Fin p → ℂ)) t)
      = (A * flow A t) *ᵥ v := by
    show A *ᵥ (flow A t *ᵥ v) + B *ᵥ (0 : Fin p → ℂ) = _
    rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec]
  rw [hval]
  exact hasDerivAt_flow_mulVec A v t

/-! ## Variation of constants

`drivenState` is the run from the origin under an input: print's
`x(t) = Φ(t) ∫₀ᵗ Φ(-s) B u(s) ds`, written with the two flow factors separated so
that only the upper limit of the integral depends on `t`. That separation is
what makes the derivative a product rule and a fundamental theorem of calculus
rather than a differentiation under the integral sign.

This is the object the sufficiency of the rank criterion has to drive: every
state the system reaches from rest is `drivenState A B u t` for some continuous
`u` and some `t`, and the direction still owed asks which states those are.
-/

/-- The flow is continuous in time. -/
public theorem continuous_flow (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun s : ℝ => flow A s := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_iff_continuousAt.mpr fun s => (hasDerivAt_flow_entry A i j s).continuousAt

/-- **Print's `Φ(-s) B u(s)`**, the integrand of variation of constants. -/
@[expose] public noncomputable def drivingTerm (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) (u : ℝ → (Fin p → ℂ)) (s : ℝ) : Fin n → ℂ :=
  flow A (-s) *ᵥ (B *ᵥ u s)

public theorem continuous_drivingTerm (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) {u : ℝ → (Fin p → ℂ)} (hu : Continuous u) :
    Continuous (drivingTerm A B u) := by
  have hBu : Continuous fun s : ℝ => B *ᵥ u s := by
    refine continuous_pi fun i => ?_
    show Continuous fun s : ℝ => ∑ k : Fin p, B i k * u s k
    exact continuous_finsetSum _ fun k _ =>
      continuous_const.mul ((continuous_apply k).comp hu)
  have hflow : Continuous fun s : ℝ => flow A (-s) := (continuous_flow A).comp continuous_neg
  refine continuous_pi fun i => ?_
  show Continuous fun s : ℝ => ∑ j : Fin n, flow A (-s) i j * (B *ᵥ u s) j
  exact continuous_finsetSum _ fun j _ =>
    (((continuous_apply j).comp ((continuous_apply i).comp hflow)).mul
      ((continuous_apply j).comp hBu))

/-- **The run from rest under an input.** -/
@[expose] public noncomputable def drivenState (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) (u : ℝ → (Fin p → ℂ)) (t : ℝ) : Fin n → ℂ :=
  flow A t *ᵥ (∫ s in (0 : ℝ)..t, drivingTerm A B u s)

@[simp] public theorem drivenState_zero (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) (u : ℝ → (Fin p → ℂ)) :
    drivenState A B u 0 = 0 := by
  simp [drivenState]

/-- **Variation of constants.** The run from rest solves print's state equation,
at every time, for every continuous input. -/
public theorem drivenState_isTrajectory (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) {u : ℝ → (Fin p → ℂ)} (hu : Continuous u) :
    IsTrajectory A B (drivenState A B u) u := by
  intro t _
  classical
  have hf := continuous_drivingTerm A B hu
  have hg : HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, drivingTerm A B u s)
      (drivingTerm A B u t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  set g : ℝ → (Fin n → ℂ) := fun r => ∫ s in (0 : ℝ)..r, drivingTerm A B u s with hgdef
  have hgpi : ∀ j : Fin n, HasDerivAt (fun r : ℝ => g r j) (drivingTerm A B u t j) t := by
    intro j
    exact (hasDerivAt_pi.mp hg) j
  have hval : A *ᵥ drivenState A B u t + B *ᵥ u t
      = (A * flow A t) *ᵥ g t + flow A t *ᵥ drivingTerm A B u t := by
    have h1 : A *ᵥ drivenState A B u t = (A * flow A t) *ᵥ g t := by
      rw [drivenState, Matrix.mulVec_mulVec]
    have h2 : flow A t *ᵥ drivingTerm A B u t = B *ᵥ u t := by
      rw [drivingTerm, Matrix.mulVec_mulVec, flow_mul_flow_neg, Matrix.one_mulVec]
    rw [h1, h2]
  rw [hval, hasDerivAt_pi]
  intro i
  have hfun : (fun r : ℝ => drivenState A B u r i)
      = fun r : ℝ => ∑ j : Fin n, flow A r i j * g r j := rfl
  have hout : ((A * flow A t) *ᵥ g t + flow A t *ᵥ drivingTerm A B u t) i
      = ∑ j : Fin n, ((flow A t * A) i j * g t j
          + flow A t i j * drivingTerm A B u t j) := by
    rw [← commute_flow]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
  rw [hfun, hout]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_flow_entry A i j t).mul (hgpi j)

/-! ## The adjoint run, and what a silent one proves

The sufficiency of the rank criterion for reachability comes down, in the end, to
this: a covector that annihilates everything the system reaches makes the
**adjoint** system silent, and a silent adjoint run is an unobservable state of
the transposed pair.

`adjointFlow A y s = Φ(s)ᵀ y` solves `φ' = Aᵀ φ`, so it is a free run of the pair
`(Aᵀ, Bᵀ)`. `Dynamics`'s `mulVec_pow_eq_zero_of_outputSignal_eq_zero` already
says a free run with zero output has every Kalman row vanish on it, and
`flow_zero` puts `y` itself at time zero. So the analytic half of the reachability
argument is the step that produces the silence; this half is free.
-/

/-- **The adjoint run**, `Φ(s)ᵀ y`. -/
@[expose] public noncomputable def adjointFlow (A : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin n → ℂ) (s : ℝ) : Fin n → ℂ :=
  (flow A s)ᵀ *ᵥ y

@[simp] public theorem adjointFlow_zero (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    adjointFlow A y 0 = y := by
  simp [adjointFlow]

/-- **It solves the adjoint equation** `φ' = Aᵀ φ`. -/
public theorem hasDerivAt_adjointFlow (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ)
    (s : ℝ) : HasDerivAt (adjointFlow A y) (Aᵀ *ᵥ adjointFlow A y s) s := by
  rw [hasDerivAt_pi]
  intro i
  have hfun : (fun r : ℝ => adjointFlow A y r i)
      = fun r : ℝ => ∑ j : Fin n, flow A r j i * y j := rfl
  have hval : (Aᵀ *ᵥ adjointFlow A y s) i
      = ∑ j : Fin n, (flow A s * A) j i * y j := by
    have h : Aᵀ *ᵥ ((flow A s)ᵀ *ᵥ y) = (flow A s * A)ᵀ *ᵥ y := by
      rw [Matrix.mulVec_mulVec, Matrix.transpose_mul]
    rw [adjointFlow, h]
    rfl
  rw [hfun, hval]
  exact HasDerivAt.fun_sum fun j _ =>
    (hasDerivAt_flow_entry A j i s).mul_const (y j)

/--
**A silent adjoint run is an unobservable state of the transposed pair.**

This is the bridge the reachability argument ends at: once a covector is known to
make `Bᵀ Φ(s)ᵀ y` vanish on a window around zero, the rank criterion for
`(Aᵀ, Bᵀ)` — which is the criterion for `(A, B)` by
`isControllable_iff_isObservable_transpose` — forces `y` to be zero.
-/
public theorem mem_unobservableSubspace_of_adjointFlow_eq_zero
    {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} {B : Matrix (Fin n) (Fin p) ℂ}
    {y : Fin n → ℂ} {S : Set ℝ} (hS : IsOpen S) {s₀ : ℝ} (hs₀ : s₀ ∈ S)
    (h : ∀ s ∈ S, Bᵀ *ᵥ adjointFlow A y s = 0) :
    adjointFlow A y s₀ ∈ unobservableSubspace Aᵀ Bᵀ := by
  have hall := mulVec_pow_eq_zero_of_outputSignal_eq_zero (A := Aᵀ) (C := Bᵀ)
    (d := adjointFlow A y) hS (fun s _ => hasDerivAt_adjointFlow A y s) h
  rw [mem_unobservableSubspace_iff]
  intro k
  exact hall (k : ℕ) s₀ hs₀

/-- The adjoint run vanishes nowhere unless it starts nowhere: the flow is
invertible, so its transpose is injective. -/
public theorem eq_zero_of_adjointFlow_eq_zero_at {A : Matrix (Fin n) (Fin n) ℂ}
    {y : Fin n → ℂ} {s₀ : ℝ} (h : adjointFlow A y s₀ = 0) : y = 0 := by
  have hinv : ((flow A (-s₀))ᵀ * (flow A s₀)ᵀ) = 1 := by
    rw [← Matrix.transpose_mul]
    have := flow_mul_flow_neg A s₀
    rw [this, Matrix.transpose_one]
  calc y = ((flow A (-s₀))ᵀ * (flow A s₀)ᵀ) *ᵥ y := by rw [hinv, Matrix.one_mulVec]
    _ = (flow A (-s₀))ᵀ *ᵥ adjointFlow A y s₀ := by rw [adjointFlow, Matrix.mulVec_mulVec]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

/--
**And then the covector is zero**, when the pair satisfies the rank criterion.

This is the endpoint of the reachability argument, and it asks only that the
window be non-empty -- not that it contain any particular time. The derivative
induction reads the Kalman rows off at whatever point of the window it is given,
and the flow's invertibility carries the conclusion back to the covector.
-/
public theorem eq_zero_of_adjointFlow_eq_zero
    {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} {B : Matrix (Fin n) (Fin p) ℂ}
    (hc : IsControllable A B) {y : Fin n → ℂ} {S : Set ℝ} (hS : IsOpen S)
    (hne : S.Nonempty) (h : ∀ s ∈ S, Bᵀ *ᵥ adjointFlow A y s = 0) : y = 0 := by
  obtain ⟨s₀, hs₀⟩ := hne
  have hobs : IsObservable Aᵀ Bᵀ := (isControllable_iff_isObservable_transpose A B).mp hc
  have hbot : unobservableSubspace Aᵀ Bᵀ = ⊥ :=
    (unobservableSubspace_eq_bot_iff_isObservable Aᵀ Bᵀ).mpr hobs
  have hmem := mem_unobservableSubspace_of_adjointFlow_eq_zero hS hs₀ h
  rw [hbot, Submodule.mem_bot] at hmem
  exact eq_zero_of_adjointFlow_eq_zero_at hmem

/-! ## Reading a run through a covector

`dotProduct_drivenState` is the identity the sufficiency argument turns on: a
covector read on the run from rest is the **adjoint signal** paired with the
input, integrated. Everything the system reaches is invisible to `z` exactly
when the adjoint signal `Bᵀ Φ(-s)ᵀ Φ(T)ᵀ z` is orthogonal to every continuous
input — and the input that exposes that is the signal's own conjugate.
-/

/-- Pairing with a fixed covector, as a continuous linear map. -/
@[expose] public noncomputable def dotCLM (y : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => y ⬝ᵥ v
      map_add' := by intro v w; simp [dotProduct_add]
      map_smul' := by
        intro r v
        simp [dotProduct, Finset.mul_sum, mul_left_comm] }

@[simp] public theorem dotCLM_apply (y v : Fin n → ℂ) : dotCLM y v = y ⬝ᵥ v := rfl

/-- **The adjoint signal** `Bᵀ Φ(-s)ᵀ y`: what a covector `y` sees of the input
channel at time `s`. -/
@[expose] public noncomputable def adjointSignal (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) (y : Fin n → ℂ) (s : ℝ) : Fin p → ℂ :=
  Bᵀ *ᵥ adjointFlow A y (-s)

/--
**A covector read on the run from rest.** The value is the adjoint signal paired
with the input, integrated over the run.

This is where the sufficiency of the rank criterion leaves the algebra and
enters the analysis: the left side is a statement about what the system reaches,
the right side is a statement about a function on an interval.
-/
public theorem dotProduct_drivenState (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) {u : ℝ → (Fin p → ℂ)} (hu : Continuous u)
    (z : Fin n → ℂ) (T : ℝ) :
    z ⬝ᵥ drivenState A B u T
      = ∫ s in (0 : ℝ)..T, adjointSignal A B ((flow A T)ᵀ *ᵥ z) s ⬝ᵥ u s := by
  classical
  set y : Fin n → ℂ := (flow A T)ᵀ *ᵥ z with hy
  have hstep : z ⬝ᵥ drivenState A B u T
      = y ⬝ᵥ ∫ s in (0 : ℝ)..T, drivingTerm A B u s := by
    rw [drivenState, dotProduct_mulVec, hy, Matrix.mulVec_transpose]
  have hpull : y ⬝ᵥ (∫ s in (0 : ℝ)..T, drivingTerm A B u s)
      = ∫ s in (0 : ℝ)..T, y ⬝ᵥ drivingTerm A B u s := by
    have hint : IntervalIntegrable (drivingTerm A B u) MeasureTheory.volume (0 : ℝ) T :=
      (continuous_drivingTerm A B hu).intervalIntegrable 0 T
    have h := (dotCLM y).intervalIntegral_comp_comm hint
    simpa using h.symm
  have hterm : ∀ s : ℝ, y ⬝ᵥ drivingTerm A B u s = adjointSignal A B y s ⬝ᵥ u s := by
    intro s
    rw [drivingTerm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_mulVec,
      ← Matrix.mulVec_transpose, adjointSignal, adjointFlow]
  rw [hstep, hpull]
  exact intervalIntegral.integral_congr fun s _ => hterm s

/-- The adjoint signal is continuous, so it is an admissible input once
conjugated. -/
public theorem continuous_adjointSignal (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) (y : Fin n → ℂ) :
    Continuous (adjointSignal A B y) := by
  have hflow : Continuous fun s : ℝ => flow A (-s) := (continuous_flow A).comp continuous_neg
  refine continuous_pi fun i => ?_
  show Continuous fun s : ℝ => ∑ j : Fin n, Bᵀ i j * ((flow A (-s))ᵀ *ᵥ y) j
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  show Continuous fun s : ℝ => ∑ k : Fin n, flow A (-s) k j * y k
  exact continuous_finsetSum _ fun k _ =>
    (((continuous_apply j).comp ((continuous_apply k).comp hflow)).mul continuous_const)

/-! ## The step that turns a vanishing integral into a silent signal -/

/--
**A non-negative continuous function whose integral vanishes is zero.**

The interior is where it is proved, and that is all the reachability argument
needs: `eq_zero_of_adjointFlow_eq_zero` asks only for a non-empty open window.

The proof is the standard one and is stated here because the pinned Mathlib has
the two halves separately -- a vanishing integral gives *almost everywhere*
zero, and a continuous function positive at a point is positive on a
neighbourhood, which is an open set of positive measure.
-/
public theorem eqOn_zero_of_intervalIntegral_eq_zero {g : ℝ → ℝ} (hg : Continuous g)
    (hnn : ∀ x, 0 ≤ g x) {T : ℝ} (hT : 0 < T)
    (h : ∫ x in (0 : ℝ)..T, g x = 0) : ∀ x ∈ Set.Ioo (0 : ℝ) T, g x = 0 := by
  intro x hx
  by_contra hne
  have hpos : 0 < g x := lt_of_le_of_ne (hnn x) (Ne.symm hne)
  have hae : g =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
      (Filter.Eventually.of_forall fun y => hnn y)
      (hg.intervalIntegrable 0 T)).mp h
  have hnull : MeasureTheory.volume ({y : ℝ | g y ≠ 0} ∩ Set.Ioc (0 : ℝ) T) = 0 := by
    have h0 := MeasureTheory.ae_iff.mp hae
    simp only [Pi.zero_apply] at h0
    have hmeas : MeasurableSet {y : ℝ | ¬ g y = 0} :=
      (hg.measurable (measurableSet_singleton (0 : ℝ))).compl
    rw [MeasureTheory.Measure.restrict_apply hmeas] at h0
    exact h0
  set U : Set ℝ := {y : ℝ | 0 < g y} ∩ Set.Ioo (0 : ℝ) T with hU
  have hUopen : IsOpen U := (isOpen_lt continuous_const hg).inter isOpen_Ioo
  have hUsub : U ⊆ {y : ℝ | g y ≠ 0} ∩ Set.Ioc (0 : ℝ) T := by
    rintro y ⟨hy1, hy2⟩
    exact ⟨ne_of_gt hy1, Set.Ioo_subset_Ioc_self hy2⟩
  have hUnull : MeasureTheory.volume U = 0 :=
    MeasureTheory.measure_mono_null hUsub hnull
  have hUpos : 0 < MeasureTheory.volume U := hUopen.measure_pos _ ⟨x, hpos, hx⟩
  rw [hUnull] at hUpos
  exact lt_irrefl _ hUpos

/-- The squared length of a complex vector, as a real number. -/
@[expose] public noncomputable def sqLen {p : ℕ} (w : Fin p → ℂ) : ℝ :=
  ∑ k : Fin p, Complex.normSq (w k)

public theorem sqLen_nonneg {p : ℕ} (w : Fin p → ℂ) : 0 ≤ sqLen w :=
  Finset.sum_nonneg fun k _ => Complex.normSq_nonneg (w k)

public theorem sqLen_eq_zero {p : ℕ} {w : Fin p → ℂ} (h : sqLen w = 0) : w = 0 := by
  funext k
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (w j))).mp h
  exact Complex.normSq_eq_zero.mp (hall k (Finset.mem_univ k))

/-- **Pairing a signal with its own conjugate is its squared length.** This is
the choice of input that turns "invisible to the covector" into "silent". -/
public theorem dotProduct_star {p : ℕ} (w : Fin p → ℂ) :
    w ⬝ᵥ (fun k => star (w k)) = (sqLen w : ℂ) := by
  rw [dotProduct, sqLen]
  push_cast
  exact Finset.sum_congr rfl fun k _ => Complex.mul_conj (w k)

/--
**A covector that sees nothing the system reaches makes the adjoint silent.**

This is the middle of the sufficiency argument, and the input that proves it is
the adjoint signal's own conjugate: pairing a signal with its conjugate gives a
non-negative real integrand, so a vanishing integral forces the signal itself to
vanish.
-/
public theorem adjointSignal_eq_zero_of_dotProduct_drivenState_eq_zero
    (A : Matrix (Fin n) (Fin n) ℂ) {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ)
    {z : Fin n → ℂ} {T : ℝ} (hT : 0 < T)
    (h : ∀ u : ℝ → (Fin p → ℂ), Continuous u → z ⬝ᵥ drivenState A B u T = 0) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T,
      adjointSignal A B ((flow A T)ᵀ *ᵥ z) s = 0 := by
  classical
  set y : Fin n → ℂ := (flow A T)ᵀ *ᵥ z with hy
  set w : ℝ → (Fin p → ℂ) := adjointSignal A B y with hw
  have hwc : Continuous w := continuous_adjointSignal A B y
  have hu : Continuous fun s : ℝ => (fun k => star (w s k)) := by
    refine continuous_pi fun k => ?_
    exact Complex.continuous_conj.comp ((continuous_apply k).comp hwc)
  have hzero := h _ hu
  rw [dotProduct_drivenState A B hu z T, ← hy] at hzero
  have hpt : ∀ s : ℝ, w s ⬝ᵥ (fun k => star (w s k)) = ((sqLen (w s) : ℝ) : ℂ) :=
    fun s => dotProduct_star (w s)
  rw [intervalIntegral.integral_congr (g := fun s => ((sqLen (w s) : ℝ) : ℂ))
    fun s _ => hpt s] at hzero
  have hsq : Continuous fun s : ℝ => sqLen (w s) := by
    refine continuous_finsetSum _ fun k _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply k).comp hwc)
  have hreal : ((∫ s in (0 : ℝ)..T, sqLen (w s) : ℝ) : ℂ) = 0 := by
    show Complex.ofRealCLM (∫ s in (0 : ℝ)..T, sqLen (w s)) = 0
    rw [← Complex.ofRealCLM.intervalIntegral_comp_comm (hsq.intervalIntegrable 0 T)]
    exact hzero
  have hrz : (∫ s in (0 : ℝ)..T, sqLen (w s)) = 0 := by
    exact_mod_cast hreal
  intro s hs
  exact sqLen_eq_zero
    (eqOn_zero_of_intervalIntegral_eq_zero hsq (fun r => sqLen_nonneg (w r)) hT hrz s hs)

/-! ## Sufficiency: a controllable pair reaches every state -/

/-- **The states reached from rest at a fixed time**, as a subspace. Inputs add
and scale, and the integral is linear, so the states they reach do too. -/
@[expose] public noncomputable def reachedSet (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) (T : ℝ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∃ u : ℝ → (Fin p → ℂ), Continuous u ∧ drivenState A B u T = x}
  zero_mem' := ⟨fun _ => 0, continuous_const, by
    have h : drivingTerm A B (fun _ => 0) = fun _ => 0 := by
      funext s
      rw [drivingTerm, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rw [drivenState, h]
    simp⟩
  add_mem' := by
    rintro x₁ x₂ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    refine ⟨fun s => u s + v s, hu.add hv, ?_⟩
    have hterm : drivingTerm A B (fun s => u s + v s)
        = fun s => drivingTerm A B u s + drivingTerm A B v s := by
      funext s
      rw [drivingTerm, drivingTerm, drivingTerm, Matrix.mulVec_add, Matrix.mulVec_add]
    rw [drivenState, drivenState, drivenState, hterm,
      intervalIntegral.integral_add ((continuous_drivingTerm A B hu).intervalIntegrable 0 T)
        ((continuous_drivingTerm A B hv).intervalIntegrable 0 T), Matrix.mulVec_add]
  smul_mem' := by
    rintro c x ⟨u, hu, rfl⟩
    refine ⟨fun s => c • u s, hu.const_smul c, ?_⟩
    have hterm : drivingTerm A B (fun s => c • u s) = fun s => c • drivingTerm A B u s := by
      funext s
      rw [drivingTerm, drivingTerm, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rw [drivenState, drivenState, hterm, intervalIntegral.integral_smul,
      Matrix.mulVec_smul]

public theorem mem_reachedSet_iff {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ}
    {B : Matrix (Fin n) (Fin p) ℂ} {T : ℝ} {x : Fin n → ℂ} :
    x ∈ reachedSet A B T ↔ ∃ u : ℝ → (Fin p → ℂ), Continuous u ∧ drivenState A B u T = x :=
  Iff.rfl

/-- A proper subspace of the state space is annihilated by a non-zero covector.
Print's argument says "choose a vector orthogonal to the reachable set"; this is
that choice, through the dual space rather than through an inner product. -/
public theorem exists_dotProduct_eq_zero_of_ne_top {W : Submodule ℂ (Fin n → ℂ)}
    (hW : W ≠ ⊤) : ∃ z : Fin n → ℂ, z ≠ 0 ∧ ∀ v ∈ W, z ⬝ᵥ v = 0 := by
  classical
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hW) inferInstance
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · intro hz
    refine hf0 (LinearMap.ext fun v => ?_)
    have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, congrFun hz i]
    simp
  · intro v hv
    have hfv : f v = 0 := by
      have := Submodule.mem_map_of_mem (f := f) hv
      rw [hfW, Submodule.mem_bot] at this
      exact this
    have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [dotProduct]
    rw [hv, map_sum] at hfv
    simp only [map_smul, smul_eq_mul] at hfv
    rw [← hfv]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/--
**Klamka's complete state controllability, from the rank criterion.**

The sufficiency direction, and with it the equivalence between the Kalman rank
condition and reachability of the continuous-time system. Print's system reaches
every state from rest exactly when its controllability matrix has full rank.

The argument is the classical one with the Gramian replaced by the three pieces
above: the states reached at a fixed positive time form a subspace, a covector
annihilating it makes the adjoint signal silent -- because the input that
exposes the silence is the signal's own conjugate -- and a silent adjoint run
under the rank criterion is zero.
-/
public theorem isReachable_of_isControllable {A : Matrix (Fin n) (Fin n) ℂ}
    {p : ℕ} {B : Matrix (Fin n) (Fin p) ℂ} (hc : IsControllable A B) :
    IsReachable A B := by
  classical
  have htop : reachedSet A B 1 = ⊤ := by
    by_contra hne
    obtain ⟨z, hz0, hz⟩ := exists_dotProduct_eq_zero_of_ne_top hne
    have hsil := adjointSignal_eq_zero_of_dotProduct_drivenState_eq_zero A B
      (z := z) (T := 1) one_pos
      (fun u hu => hz _ (mem_reachedSet_iff.mpr ⟨u, hu, rfl⟩))
    have hy : adjointFlow A z 1 = 0 := by
      refine eq_zero_of_adjointFlow_eq_zero hc (S := Set.Ioo (-1 : ℝ) 0) isOpen_Ioo
        ⟨-(1/2), by norm_num, by norm_num⟩ (fun σ hσ => ?_)
      have hneg : -σ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
      have h := hsil (-σ) hneg
      rwa [adjointSignal, neg_neg] at h
    exact hz0 (eq_zero_of_adjointFlow_eq_zero_at hy)
  intro x₁
  obtain ⟨u, hu, hux⟩ := mem_reachedSet_iff.mp (htop ▸ Submodule.mem_top (x := x₁))
  exact ⟨drivenState A B u, u, 1, drivenState_isTrajectory A B hu,
    drivenState_zero A B u, hux⟩

/-! ## Print's wording: from any state to any state -/

/-- **Complete state controllability at print's quantifier.** Print's phrase is
*completely state controllable*, which asks for a run between **any** two states,
not only out of the origin. -/
@[expose] public def IsCompletelyReachable (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) : Prop :=
  ∀ x₀ x₁ : Fin n → ℂ, ∃ (x : ℝ → (Fin n → ℂ)) (u : ℝ → (Fin p → ℂ)) (t₁ : ℝ),
    IsTrajectory A B x u ∧ x 0 = x₀ ∧ x t₁ = x₁

/-- **A free run and a driven run add.** The state equation is affine in the
state, so the shift by an initial condition costs nothing. -/
public theorem shifted_isTrajectory (A : Matrix (Fin n) (Fin n) ℂ)
    {p : ℕ} (B : Matrix (Fin n) (Fin p) ℂ) {u : ℝ → (Fin p → ℂ)} (hu : Continuous u)
    (x₀ : Fin n → ℂ) :
    IsTrajectory A B (fun t => flow A t *ᵥ x₀ + drivenState A B u t) u := by
  intro t _
  have h := (hasDerivAt_flow_mulVec A x₀ t).add (drivenState_isTrajectory A B hu t trivial)
  have hval : (A * flow A t) *ᵥ x₀ + (A *ᵥ drivenState A B u t + B *ᵥ u t)
      = A *ᵥ ((fun r => flow A r *ᵥ x₀ + drivenState A B u r) t) + B *ᵥ u t := by
    show _ = A *ᵥ (flow A t *ᵥ x₀ + drivenState A B u t) + B *ᵥ u t
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  rwa [hval] at h

/-- **Klamka's complete state controllability, at print's own quantifier.** -/
public theorem isCompletelyReachable_of_isControllable {A : Matrix (Fin n) (Fin n) ℂ}
    {p : ℕ} {B : Matrix (Fin n) (Fin p) ℂ} (hc : IsControllable A B) :
    IsCompletelyReachable A B := by
  have htop : reachedSet A B 1 = ⊤ := by
    by_contra hne
    obtain ⟨z, hz0, hz⟩ := exists_dotProduct_eq_zero_of_ne_top hne
    have hsil := adjointSignal_eq_zero_of_dotProduct_drivenState_eq_zero A B
      (z := z) (T := 1) one_pos
      (fun u hu => hz _ (mem_reachedSet_iff.mpr ⟨u, hu, rfl⟩))
    have hy : adjointFlow A z 1 = 0 := by
      refine eq_zero_of_adjointFlow_eq_zero hc (S := Set.Ioo (-1 : ℝ) 0) isOpen_Ioo
        ⟨-(1/2), by norm_num, by norm_num⟩ (fun σ hσ => ?_)
      have hneg : -σ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
      have h := hsil (-σ) hneg
      rwa [adjointSignal, neg_neg] at h
    exact hz0 (eq_zero_of_adjointFlow_eq_zero_at hy)
  intro x₀ x₁
  obtain ⟨u, hu, hux⟩ := mem_reachedSet_iff.mp
    (htop ▸ Submodule.mem_top (x := x₁ - flow A 1 *ᵥ x₀))
  refine ⟨fun t => flow A t *ᵥ x₀ + drivenState A B u t, u, 1,
    shifted_isTrajectory A B hu x₀, ?_, ?_⟩
  · show flow A 0 *ᵥ x₀ + drivenState A B u 0 = x₀
    rw [flow_zero, Matrix.one_mulVec, drivenState_zero, add_zero]
  · show flow A 1 *ᵥ x₀ + drivenState A B u 1 = x₁
    rw [hux]
    abel

/-- Reaching every state from any state is in particular reaching every state
from rest. -/
public theorem IsCompletelyReachable.isReachable {A : Matrix (Fin n) (Fin n) ℂ}
    {p : ℕ} {B : Matrix (Fin n) (Fin p) ℂ} (h : IsCompletelyReachable A B) :
    IsReachable A B := fun x₁ => h 0 x₁

/--
**Klamka's criterion and Klamka's property are the same thing.**

The rank condition on the controllability matrix holds **exactly when** the
continuous-time system is completely state controllable. Print states this
equivalence on page 726 and attributes it to Chen and Desoer; `NC-013` in
`formalization-search.json` records that no proof assistant had it as of
2026-09-20.
-/
public theorem isCompletelyReachable_iff_isControllable {A : Matrix (Fin n) (Fin n) ℂ}
    {p : ℕ} {B : Matrix (Fin n) (Fin p) ℂ} :
    IsCompletelyReachable A B ↔ IsControllable A B := by
  classical
  constructor
  · intro h
    by_contra hc
    exact not_isReachable_of_not_isControllable hc h.isReachable
  · exact isCompletelyReachable_of_isControllable

/-- The same at the origin, which is the form the necessity direction was proved
at. -/
public theorem isReachable_iff_isControllable {A : Matrix (Fin n) (Fin n) ℂ}
    {p : ℕ} {B : Matrix (Fin n) (Fin p) ℂ} :
    IsReachable A B ↔ IsControllable A B := by
  classical
  constructor
  · intro h
    by_contra hc
    exact not_isReachable_of_not_isControllable hc h
  · intro hc
    exact (isCompletelyReachable_of_isControllable hc).isReachable

end AISafetyAtlas.LinearSystems
