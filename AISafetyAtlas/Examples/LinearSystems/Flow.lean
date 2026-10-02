module

public import AISafetyAtlas.LinearSystems.Flow
public import AISafetyAtlas.Examples.LinearSystems.Dynamics

/-!
# The flow of the integrator, and the run it drives

`AISafetyAtlas.LinearSystems.Flow` builds `Φ(t) = e^{At}` and the run from rest
`x(t) = Φ(t) ∫₀ᵗ Φ(-s) B u(s) ds`. On the integrator `ẋ = u`, `y = x` the state
matrix is zero, so the flow is the identity and the run from rest is the
integral of the input. Under the unit input that is the ramp already in
`Examples.LinearSystems.Dynamics`, which is what ties the new machinery to the
solution that was written down by hand.
-/

namespace AISafetyAtlas.Examples.LinearSystems

open AISafetyAtlas.LinearSystems Matrix

/-- **The integrator has no dynamics of its own**, so its flow is the identity
at every time. -/
@[simp] public theorem integrator_flow (t : ℝ) : flow integratorA t = 1 := by
  have h : t • integratorA = 0 := by
    funext i j
    simp [integratorA]
  simp [flow, h, NormedSpace.exp_zero]

/-- At time zero nothing has flowed. -/
public theorem integrator_flow_zero : flow integratorA 0 = 1 := flow_zero integratorA

/-- The flow is invertible, read here. -/
public theorem integrator_flow_mul_neg (t : ℝ) :
    flow integratorA t * flow integratorA (-t) = 1 :=
  flow_mul_flow_neg integratorA t

/-- The state matrix commutes with its flow, read here. -/
public theorem integrator_commute_flow (t : ℝ) :
    flow integratorA t * integratorA = integratorA * flow integratorA t :=
  commute_flow integratorA t

/-- Entry evaluation, read here. -/
public theorem integrator_entryCLM (t : ℝ) :
    entryCLM (0 : Fin 1) 0 (flow integratorA t) = flow integratorA t 0 0 :=
  entryCLM_apply 0 0 _

/-- **The flow differentiates**, entrywise and applied to a state. -/
public theorem integrator_hasDerivAt_flow_entry (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow integratorA s 0 0)
      ((flow integratorA t * integratorA) 0 0) t :=
  hasDerivAt_flow_entry integratorA 0 0 t

public theorem integrator_hasDerivAt_flow_mulVec (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow integratorA s *ᵥ (fun _ : Fin 1 => (1 : ℂ)))
      ((integratorA * flow integratorA t) *ᵥ (fun _ : Fin 1 => (1 : ℂ))) t :=
  hasDerivAt_flow_mulVec integratorA _ t

/-- **A free run of the integrator is a trajectory.** -/
public theorem integrator_flow_isTrajectory :
    IsTrajectoryOn integratorA integratorB (Set.univ : Set ℝ)
      (fun t => flow integratorA t *ᵥ (fun _ : Fin 1 => (1 : ℂ))) (fun _ => 0) :=
  flow_isTrajectory integratorA integratorB _ _

public theorem integrator_continuous_flow : Continuous fun s : ℝ => flow integratorA s :=
  continuous_flow integratorA

public theorem integrator_continuous_drivingTerm :
    Continuous (drivingTerm integratorA integratorB unitInput) :=
  continuous_drivingTerm integratorA integratorB continuous_const

/-- **The driving term of the integrator under the unit input is the unit
input.** -/
public theorem integrator_drivingTerm (s : ℝ) :
    drivingTerm integratorA integratorB unitInput s = fun _ => 1 := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [drivingTerm, integratorB, unitInput, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- **Variation of constants, on a system that runs.** -/
public theorem integrator_drivenState_isTrajectory :
    IsTrajectory integratorA integratorB (drivenState integratorA integratorB unitInput)
      unitInput :=
  drivenState_isTrajectory integratorA integratorB continuous_const

/-- The run from rest starts at rest. -/
public theorem integrator_drivenState_zero :
    drivenState integratorA integratorB unitInput 0 = 0 :=
  drivenState_zero integratorA integratorB unitInput

/--
**The construction reproduces the hand-written solution.** The run the general
variation-of-constants formula drives out of the integrator under the unit input
is exactly `rampTrajectory`, which `Examples.LinearSystems.Dynamics` wrote down
directly. The two definitions of the same solution agree, which is what makes
the machinery a description of this system rather than a parallel one.
-/
public theorem integrator_drivenState_eq_ramp :
    drivenState integratorA integratorB unitInput = rampTrajectory := by
  funext t i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hint : (∫ s in (0 : ℝ)..t, drivingTerm integratorA integratorB unitInput s)
      = fun _ : Fin 1 => (t : ℂ) := by
    simp only [integrator_drivingTerm]
    rw [intervalIntegral.integral_const]
    funext j
    simp
  rw [drivenState, hint, integrator_flow]
  simp [rampTrajectory, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-! ## The adjoint run, read at both systems -/

/-- **The integrator satisfies the rank criterion**: one input, one state, and
the input enters directly. -/
public theorem integrator_isControllable : IsControllable integratorA integratorB := by
  intro x
  refine ⟨fun _ => x, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [integratorA, integratorB]

/-- With no dynamics the adjoint run stands still. -/
public theorem integrator_adjointFlow (y : Fin 1 → ℂ) (s : ℝ) :
    adjointFlow integratorA y s = y := by
  rw [adjointFlow, integrator_flow, Matrix.transpose_one, Matrix.one_mulVec]

/-- At time zero the adjoint run is its own covector. -/
public theorem integrator_adjointFlow_zero (y : Fin 1 → ℂ) :
    adjointFlow integratorA y 0 = y := adjointFlow_zero integratorA y

/-- It still solves the adjoint equation. -/
public theorem integrator_hasDerivAt_adjointFlow (y : Fin 1 → ℂ) (s : ℝ) :
    HasDerivAt (adjointFlow integratorA y) (integratorAᵀ *ᵥ adjointFlow integratorA y s) s :=
  hasDerivAt_adjointFlow integratorA y s

/-- **The deaf system makes every adjoint run silent**, so every covector is an
unobservable state of its transposed pair -- which is the same thing as the deaf
system reaching nothing. -/
public theorem deaf_mem_unobservableSubspace (y : Fin 1 → ℂ) :
    adjointFlow integratorA y 0 ∈ unobservableSubspace integratorAᵀ deafBᵀ := by
  refine mem_unobservableSubspace_of_adjointFlow_eq_zero isOpen_univ (Set.mem_univ (0 : ℝ))
    (fun s _ => ?_)
  rw [deafB, Matrix.transpose_zero, Matrix.zero_mulVec]

/-- **And on a system that does satisfy the criterion, silence forces the
covector to vanish.** -/
public theorem integrator_eq_zero_of_adjointFlow_eq_zero (y : Fin 1 → ℂ)
    (h : ∀ s ∈ (Set.univ : Set ℝ), integratorBᵀ *ᵥ adjointFlow integratorA y s = 0) :
    y = 0 :=
  eq_zero_of_adjointFlow_eq_zero integrator_isControllable isOpen_univ
    ⟨0, Set.mem_univ 0⟩ h

/-- The flow's invertibility carries a vanishing adjoint run back to its
covector. -/
public theorem integrator_eq_zero_of_adjointFlow_eq_zero_at (y : Fin 1 → ℂ)
    (h : adjointFlow integratorA y 3 = 0) : y = 0 :=
  eq_zero_of_adjointFlow_eq_zero_at h

/-! ## Reachability, both directions, at both systems -/

/-- **The integrator is completely state controllable**, at print's own
quantifier: any state to any state. -/
public theorem integrator_isCompletelyReachable :
    IsCompletelyReachable integratorA integratorB :=
  isCompletelyReachable_of_isControllable integrator_isControllable

/-- **And the deaf system is not**, which is the necessity direction read at a
system that fails the criterion. -/
public theorem deaf_not_isCompletelyReachable :
    ¬ IsCompletelyReachable integratorA deafB := fun h =>
  deaf_not_isReachable h.isReachable

/-- The sufficiency direction on its own, at the origin. -/
public theorem integrator_isReachable : IsReachable integratorA integratorB :=
  isReachable_of_isControllable integrator_isControllable

/-- Pairing with a covector, as the continuous linear map the integral pull-out
uses. -/
public theorem integrator_dotCLM_apply (y v : Fin 1 → ℂ) : dotCLM y v = y ⬝ᵥ v :=
  dotCLM_apply y v

/-- **The equivalence itself**, read at the integrator. -/
public theorem integrator_isCompletelyReachable_iff :
    IsCompletelyReachable integratorA integratorB ↔ IsControllable integratorA integratorB :=
  isCompletelyReachable_iff_isControllable

/-- And at the origin. -/
public theorem integrator_isReachable_iff :
    IsReachable integratorA integratorB ↔ IsControllable integratorA integratorB :=
  isReachable_iff_isControllable

/-- **Every state is reached at time one**, on a system that satisfies the
criterion. -/
public theorem integrator_reachedSet_eq_top :
    reachedSet integratorA integratorB 1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => mem_reachedSet_iff.mpr ⟨fun _ => x, continuous_const, ?_⟩
  have hterm : drivingTerm integratorA integratorB (fun _ => x) = fun _ : ℝ => x := by
    funext s i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp [drivingTerm, integratorB, Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [drivenState, hterm, integrator_flow, intervalIntegral.integral_const,
    Matrix.one_mulVec]
  funext i
  simp

/-- **A free run shifted by a driven one is a run**, read here. -/
public theorem integrator_shifted_isTrajectory (x₀ : Fin 1 → ℂ) :
    IsTrajectory integratorA integratorB
      (fun t => flow integratorA t *ᵥ x₀ + drivenState integratorA integratorB unitInput t)
      unitInput :=
  shifted_isTrajectory integratorA integratorB continuous_const x₀

/-- **A covector read on a run is the adjoint signal paired with the input.** -/
public theorem integrator_dotProduct_drivenState (z : Fin 1 → ℂ) (T : ℝ) :
    z ⬝ᵥ drivenState integratorA integratorB unitInput T
      = ∫ s in (0 : ℝ)..T,
          adjointSignal integratorA integratorB ((flow integratorA T)ᵀ *ᵥ z) s ⬝ᵥ unitInput s :=
  dotProduct_drivenState integratorA integratorB continuous_const z T

public theorem integrator_continuous_adjointSignal (y : Fin 1 → ℂ) :
    Continuous (adjointSignal integratorA integratorB y) :=
  continuous_adjointSignal integratorA integratorB y

/-- Pairing with the conjugate, and what it forces. -/
public theorem integrator_dotProduct_star (w : Fin 1 → ℂ) :
    w ⬝ᵥ (fun k => star (w k)) = (sqLen w : ℂ) := dotProduct_star w

public theorem integrator_sqLen_nonneg (w : Fin 1 → ℂ) : 0 ≤ sqLen w := sqLen_nonneg w

public theorem integrator_sqLen_eq_zero {w : Fin 1 → ℂ} (h : sqLen w = 0) : w = 0 :=
  sqLen_eq_zero h

/-- **A non-negative continuous function with vanishing integral is zero**, read
at the constant zero. -/
public theorem const_zero_eqOn_zero :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  refine eqOn_zero_of_intervalIntegral_eq_zero continuous_const (fun _ => le_refl 0)
    one_pos ?_
  simp

/-- **A proper subspace is annihilated by a covector**, read at the zero
subspace on a one-state system. -/
public theorem exists_dotProduct_eq_zero_bot :
    ∃ z : Fin 1 → ℂ, z ≠ 0 ∧ ∀ v ∈ (⊥ : Submodule ℂ (Fin 1 → ℂ)), z ⬝ᵥ v = 0 := by
  refine exists_dotProduct_eq_zero_of_ne_top ?_
  intro h
  have hx : (fun _ => (1 : ℂ)) ∈ (⊥ : Submodule ℂ (Fin 1 → ℂ)) := h ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at hx
  have := congrFun hx 0
  simp at this

/-- **The silence step**, read at a covector that sees nothing of the deaf
system. -/
public theorem deaf_adjointSignal_eq_zero (z : Fin 1 → ℂ) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      adjointSignal integratorA deafB ((flow integratorA 1)ᵀ *ᵥ z) s = 0 := by
  refine adjointSignal_eq_zero_of_dotProduct_drivenState_eq_zero integratorA deafB
    one_pos (fun u hu => ?_)
  have hterm : drivingTerm integratorA deafB u = fun _ : ℝ => (0 : Fin 1 → ℂ) := by
    funext s
    rw [drivingTerm, deafB, Matrix.zero_mulVec, Matrix.mulVec_zero]
  rw [drivenState, hterm]
  simp

end AISafetyAtlas.Examples.LinearSystems
