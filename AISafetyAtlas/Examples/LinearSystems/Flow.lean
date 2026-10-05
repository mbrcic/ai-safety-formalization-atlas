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

/-! ## A step input: a solution that is not a classical run -/

/-- A unit step switched on at time `0`. -/
public noncomputable def stepInput : ℝ → (Fin 1 → ℂ) :=
  fun t => if 0 ≤ t then fun _ => 1 else 0

/-- The ramp the integrator makes of it. -/
public noncomputable def rampState : ℝ → (Fin 1 → ℂ) :=
  fun t _ => ((max t 0 : ℝ) : ℂ)

theorem measurable_stepInput : Measurable stepInput :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem stepInput_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable stepInput MeasureTheory.volume a b := by
  refine (intervalIntegrable_const (c := (fun _ => 1 : Fin 1 → ℂ))).mono_fun
    measurable_stepInput.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  show ‖stepInput t‖ ≤ ‖(fun _ => 1 : Fin 1 → ℂ)‖
  by_cases h : 0 ≤ t <;> simp [stepInput, h]

theorem integrator_rhs (x u : ℝ → (Fin 1 → ℂ)) :
    (fun s => integratorA *ᵥ x s + integratorB *ᵥ u s) = u := by
  funext s; simp [integratorA, integratorB]

theorem hasDerivAt_rampState_pos {s : ℝ} (hs : 0 < s) :
    HasDerivAt rampState (stepInput s) s := by
  have heq : rampState =ᶠ[nhds s] fun t _ => ((t : ℝ) : ℂ) := by
    filter_upwards [lt_mem_nhds hs] with t ht
    funext i; simp [rampState, max_eq_left ht.le]
  have h : HasDerivAt (fun t : ℝ => fun _ : Fin 1 => ((t : ℝ) : ℂ)) (fun _ => 1) s := by
    rw [hasDerivAt_pi]; intro i; simpa using (hasDerivAt_id s).ofReal_comp
  rw [show stepInput s = fun _ => 1 by simp [stepInput, hs.le]]
  exact h.congr_of_eventuallyEq heq

theorem hasDerivAt_rampState_neg {s : ℝ} (hs : s < 0) :
    HasDerivAt rampState (stepInput s) s := by
  have heq : rampState =ᶠ[nhds s] fun _ => (0 : Fin 1 → ℂ) := by
    filter_upwards [gt_mem_nhds hs] with t ht
    funext i; simp [rampState, max_eq_right ht.le]
  rw [show stepInput s = 0 by simp [stepInput, not_le.mpr hs]]
  exact (hasDerivAt_const s (0 : Fin 1 → ℂ)).congr_of_eventuallyEq heq

theorem continuous_rampState : Continuous rampState :=
  continuous_pi fun _ => Complex.continuous_ofReal.comp (continuous_id.max continuous_const)

/-- **A step input drives the integrator along a solution.** -/
public theorem integrator_step_isSolution :
    IsSolution integratorA integratorB rampState stepInput := by
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun s => integratorA *ᵥ rampState s + integratorB *ᵥ stepInput s)
      MeasureTheory.volume a b := by
    intro a b; rw [integrator_rhs]; exact stepInput_intervalIntegrable a b
  refine ⟨continuous_rampState, hint, fun t => ?_⟩
  rw [integrator_rhs]
  have h0 : rampState 0 = 0 := by funext i; simp [rampState]
  rw [h0, zero_add]
  rcases le_or_gt 0 t with ht | ht
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
      continuous_rampState.continuousOn (fun s hs => hasDerivAt_rampState_pos hs.1)
      (stepInput_intervalIntegrable 0 t), h0, sub_zero]
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      ht.le continuous_rampState.continuousOn (fun s hs => hasDerivAt_rampState_neg hs.2)
      (stepInput_intervalIntegrable t 0), h0]
    have : rampState t = 0 := by funext i; simp [rampState, max_eq_right ht.le]
    rw [this]; simp

/-- **And it is not a classical run**: the ramp has a corner at `0`. -/
public theorem integrator_step_not_isTrajectory :
    ¬ IsTrajectory integratorA integratorB rampState stepInput := by
  intro h
  have h0 := h 0 trivial
  rw [show integratorA *ᵥ rampState 0 + integratorB *ᵥ stepInput 0 = stepInput 0 from
    congrFun (integrator_rhs rampState stepInput) 0] at h0
  have hl : HasDerivWithinAt rampState (stepInput 0) (Set.Iic 0) 0 := h0.hasDerivWithinAt
  have hz : HasDerivWithinAt rampState 0 (Set.Iic 0) 0 := by
    refine (hasDerivWithinAt_const 0 _ (0 : Fin 1 → ℂ)).congr (fun t ht => ?_) ?_
    · funext i; simp [rampState, max_eq_right (Set.mem_Iic.mp ht)]
    · funext i; simp [rampState]
  have huniq := (uniqueDiffOn_Iic (0 : ℝ) 0 (Set.mem_Iic.mpr le_rfl)).eq_deriv _ hl hz
  have : stepInput 0 0 = 1 := by simp [stepInput]
  rw [huniq] at this
  simp at this

/-! ## Both equivalences at print's solution class

The degenerate witnesses above fail the criteria by having no readout (`C = 0`) or
no input (`B = 0`). The two-state system below has both and still fails: the
readout sees only the first coordinate and the input moves only the first
coordinate, while `A = 0` never couples the second one in. -/

/-- Two decoupled states. -/
@[expose] public def pairA : Matrix (Fin 2) (Fin 2) ℂ := 0

/-- Read the first state. -/
@[expose] public def firstC : Matrix (Fin 1) (Fin 2) ℂ := !![1, 0]

/-- Drive the first state. -/
@[expose] public def firstB : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]

/-- **A real readout that still misses a state.** -/
public theorem pair_not_isObservable : ¬ IsObservable pairA firstC := by
  intro h
  have := h ![0, 1] fun k => by
    fin_cases k <;> ext i <;> fin_cases i <;>
      simp [firstC, pairA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simpa using congrFun this 1

/-- **A real input that still misses a state.** -/
public theorem pair_not_isControllable : ¬ IsControllable pairA firstB := by
  intro h
  obtain ⟨u, hu⟩ := h ![0, 1]
  have := congrFun hu 1
  simp [Fin.sum_univ_two, firstB, pairA, Matrix.mulVec, dotProduct] at this

/-- The integrator's output determines its state among solutions. -/
public theorem integrator_determinesStateSolOn :
    DeterminesStateSolOn integratorA integratorB integratorC Set.univ :=
  isObservable_imp_determinesStateSolOn isOpen_univ integrator_isObservable

/-- **The equivalence itself at the solution class**, read at the integrator. -/
public theorem integrator_determinesStateSolOn_iff :
    DeterminesStateSolOn integratorA integratorB integratorC Set.univ ↔
      IsObservable integratorA integratorC :=
  AISafetyAtlas.LinearSystems.determinesStateSolOn_iff_isObservable isOpen_univ ⟨0, trivial⟩

/-- The pair's does not, even among solutions with jumps in the input. -/
public theorem pair_not_determinesStateSolOn :
    ¬ DeterminesStateSolOn pairA firstB firstC Set.univ :=
  not_determinesStateSolOn_of_not_isObservable ⟨0, trivial⟩ pair_not_isObservable

/-- The integrator reaches every state from every state along a solution. -/
public theorem integrator_isCompletelyReachableSol :
    IsCompletelyReachableSol integratorA integratorB :=
  isCompletelyReachableSol_of_isControllable integrator_isControllable

/-- The pair does not, whatever input is allowed, step inputs included. -/
public theorem pair_not_isCompletelyReachableSol :
    ¬ IsCompletelyReachableSol pairA firstB := fun h =>
  pair_not_isControllable (isCompletelyReachableSol_iff_isControllable.mp h)

/-! ## The analytic steps, applied -/

/-- Two solutions under the same step input differ by a classical zero-input run:
here the ramp against itself. -/
public theorem integrator_step_sub_hasDerivAt :
    HasDerivAt (fun s => rampState s - rampState s)
      (integratorA *ᵥ (rampState 1 - rampState 1)) 1 :=
  AISafetyAtlas.LinearSystems.IsSolution.hasDerivAt_sub integrator_step_isSolution
    integrator_step_isSolution 1

/-- The pair at rest, with no input, is a solution. -/
public theorem pair_rest_isSolution :
    IsSolution pairA firstB (fun _ => (0 : Fin 2 → ℂ)) (fun _ => 0) :=
  ⟨continuous_const, fun a b => by simp, fun t => by simp⟩

/-- The pair at rest is a classical run too. -/
public theorem pair_rest_isTrajectory :
    IsTrajectory pairA firstB (fun _ => (0 : Fin 2 → ℂ)) (fun _ => 0) := by
  intro t _
  simpa using hasDerivAt_const t (0 : Fin 2 → ℂ)

/-- The covector that sees only the second state is a left eigenvector of
`pairA` (eigenvalue `0`) and annihilates `firstB`. -/
public theorem pair_second_eigen :
    pairAᵀ *ᵥ ![0, 1] = (0 : ℂ) • ![0, 1] ∧ firstBᵀ *ᵥ ![0, 1] = 0 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [pairA, firstB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Along a solution, the second-state readout solves `φ' = 0 · φ`. -/
public theorem pair_second_readout_sol :
    HasDerivAt (fun s : ℝ => (![0, 1] : Fin 2 → ℂ) ⬝ᵥ (fun _ : ℝ => (0 : Fin 2 → ℂ)) s)
      (0 * ((![0, 1] : Fin 2 → ℂ) ⬝ᵥ (fun _ : ℝ => (0 : Fin 2 → ℂ)) 0)) (0 : ℝ) :=
  AISafetyAtlas.LinearSystems.IsSolution.hasDerivAt_dotProduct_of_eigen pair_second_eigen.1
    pair_second_eigen.2 pair_rest_isSolution 0

/-- And along a classical run. -/
public theorem pair_second_readout :
    HasDerivAt (fun s : ℝ => (![0, 1] : Fin 2 → ℂ) ⬝ᵥ (fun _ : ℝ => (0 : Fin 2 → ℂ)) s)
      (0 * ((![0, 1] : Fin 2 → ℂ) ⬝ᵥ (fun _ : ℝ => (0 : Fin 2 → ℂ)) 0)) (0 : ℝ) :=
  AISafetyAtlas.LinearSystems.hasDerivAt_dotProduct_of_eigen pair_second_eigen.1
    pair_second_eigen.2 pair_rest_isTrajectory 0

end AISafetyAtlas.Examples.LinearSystems
