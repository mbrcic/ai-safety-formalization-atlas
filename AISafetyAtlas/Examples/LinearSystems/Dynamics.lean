module

public import AISafetyAtlas.LinearSystems.Dynamics
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# A system that runs

One state, one input, one output, `A = 0`, `B = 1`, `C = 1`: the integrator
`ẋ = u`, `y = x`. It is the smallest system in which print's two equations both
say something, and it makes every hypothesis of
`AISafetyAtlas.LinearSystems.Dynamics` inhabited rather than merely stated.

`rampTrajectory` is a genuine non-constant solution, so `IsTrajectory` is not
vacuous; `integrator_isObservable` discharges the rank criterion; and
`integrator_determinesInitialState` is print's observability delivered by it.
-/

namespace AISafetyAtlas.Examples.LinearSystems

open AISafetyAtlas.LinearSystems Matrix

/-- `ẋ = u`: the state integrates the input. -/
@[expose] public def integratorA : Matrix (Fin 1) (Fin 1) ℂ := 0

/-- The input enters directly. -/
@[expose] public def integratorB : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- The state is read out unchanged. -/
@[expose] public def integratorC : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- The constant unit input. -/
@[expose] public def unitInput : ℝ → (Fin 1 → ℂ) := fun _ _ => 1

/-- The state the unit input produces from rest: `x(t) = t`. -/
@[expose] public noncomputable def rampTrajectory : ℝ → (Fin 1 → ℂ) := fun t _ => (t : ℂ)

/-- The state the zero input produces from rest. -/
@[expose] public def restTrajectory : ℝ → (Fin 1 → ℂ) := fun _ _ => 0

/-- **A non-constant solution of print's state equation.** `IsTrajectory` is
therefore not a vacuous predicate, which is what makes the observability theorem
a statement about something. -/
public theorem ramp_isTrajectory :
    IsTrajectory integratorA integratorB rampTrajectory unitInput := by
  intro t _
  rw [hasDerivAt_pi]
  intro i
  have hval : (integratorA *ᵥ rampTrajectory t + integratorB *ᵥ unitInput t) i = 1 := by
    fin_cases i
    simp [integratorA, integratorB, unitInput]
  rw [hval]
  exact Complex.ofRealCLM.hasDerivAt

/-- **On the whole line the window drops out**, which is the form the ramp was
written in. -/
public theorem ramp_isTrajectory_forall (t : ℝ) :
    HasDerivAt rampTrajectory
      (integratorA *ᵥ rampTrajectory t + integratorB *ᵥ unitInput t) t :=
  (isTrajectoryOn_univ_iff.mp ramp_isTrajectory) t

/-- And the rest trajectory is one too, under the zero input. -/
public theorem rest_isTrajectory :
    IsTrajectory integratorA integratorB restTrajectory (fun _ _ => 0) := by
  intro t _
  rw [hasDerivAt_pi]
  intro i
  have hval : (integratorA *ᵥ restTrajectory t + integratorB *ᵥ (fun _ : Fin 1 => (0 : ℂ))) i
      = 0 := by
    fin_cases i
    simp [integratorA, integratorB]
  rw [hval]
  exact hasDerivAt_const t 0

/-- **The output of the ramp is the ramp**, which is print's `y = Cx` at `C = 1`. -/
public theorem outputSignal_ramp :
    outputSignal integratorC rampTrajectory = rampTrajectory := by
  funext t i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [outputSignal, integratorC, rampTrajectory, Matrix.mulVec, dotProduct,
    Matrix.one_apply]

/-- **The rank criterion holds here.** -/
public theorem integrator_isObservable : IsObservable integratorA integratorC := by
  intro x hx
  have h := hx 0
  simp only [Fin.isValue, Fin.val_zero, pow_zero, mul_one, integratorC] at h
  simpa using h

/-- **Print's complete state observability, delivered by the rank criterion.**
Two runs of this system driven by the same input and producing the same output
started from the same state. -/
public theorem integrator_determinesInitialState :
    DeterminesInitialState integratorA integratorB integratorC :=
  isObservable_imp_determinesInitialState integrator_isObservable

/-- Read at the two solutions above: the ramp and the rest state have different
outputs, so nothing here is a statement about equal things. -/
public theorem ramp_ne_rest : rampTrajectory 1 ≠ restTrajectory 1 := by
  intro h
  have := congrFun h 0
  simp [rampTrajectory, restTrajectory] at this

/-- **The zero-input form**, which is the one duality uses. -/
public theorem integrator_zeroInput :
    ∀ x : ℝ → (Fin 1 → ℂ), (∀ t ∈ (Set.univ : Set ℝ), HasDerivAt x (integratorA *ᵥ x t) t) →
      (∀ t ∈ (Set.univ : Set ℝ), integratorC *ᵥ x t = 0) → x 0 = 0 :=
  fun x hx h0 => isObservable_imp_zeroInput_state_eq isOpen_univ integrator_isObservable x hx h0
    (Set.mem_univ 0)

/-- **A matrix differentiates through a curve**, at this system. -/
public theorem integrator_hasDerivAt_mulVec (t : ℝ) :
    HasDerivAt (fun s => integratorC *ᵥ rampTrajectory s)
      (integratorC *ᵥ (integratorA *ᵥ rampTrajectory t + integratorB *ᵥ unitInput t)) t :=
  hasDerivAt_mulVec integratorC (ramp_isTrajectory t (Set.mem_univ t))

/-- **The difference of two runs under one input solves the free equation.** -/
public theorem integrator_hasDerivAt_sub (t : ℝ) :
    HasDerivAt (fun s => rampTrajectory s - rampTrajectory s)
      (integratorA *ᵥ (rampTrajectory t - rampTrajectory t)) t :=
  ramp_isTrajectory.hasDerivAt_sub ramp_isTrajectory (Set.mem_univ t)

/-- **Every Kalman row annihilates a silent free run**, here the rest state. -/
public theorem integrator_mulVec_pow_eq_zero (k : ℕ) (t : ℝ) :
    (integratorC * integratorA ^ k) *ᵥ restTrajectory t = 0 := by
  refine mulVec_pow_eq_zero_of_outputSignal_eq_zero (A := integratorA) (C := integratorC)
    (S := Set.univ) (d := restTrajectory) isOpen_univ (fun s _ => ?_) (fun s _ => ?_) k t
    (Set.mem_univ t)
  · have hz : restTrajectory s = 0 := rfl
    have hval : integratorA *ᵥ restTrajectory s = 0 := by rw [hz, Matrix.mulVec_zero]
    rw [hval]
    have hfun : restTrajectory = fun _ : ℝ => (0 : Fin 1 → ℂ) := rfl
    rw [hfun]
    exact hasDerivAt_const s 0
  · have hz : restTrajectory s = 0 := rfl
    rw [hz, Matrix.mulVec_zero]

/-! ## A system that hides, and a system that cannot be driven

The integrator above satisfies both rank criteria. These two do not, and they
are what makes the two necessity theorems statements about something: a blind
readout, and an input that reaches nothing.
-/

/-- No readout at all. -/
@[expose] public def blindC : Matrix (Fin 1) (Fin 1) ℂ := 0

/-- No input at all. -/
@[expose] public def deafB : Matrix (Fin 1) (Fin 1) ℂ := 0

/-- **The blind system fails the rank criterion.** -/
public theorem blind_not_isObservable : ¬ IsObservable integratorA blindC := by
  intro h
  have := h (fun _ => 1) (by intro k; simp [blindC])
  have h1 := congrFun this 0
  simp at h1

/-- **The deaf system fails the rank criterion.** -/
public theorem deaf_not_isControllable : ¬ IsControllable integratorA deafB := by
  intro h
  obtain ⟨u, hu⟩ := h (fun _ => 1)
  have h1 := congrFun hu 0
  simp [deafB] at h1

/-- **Print's observability fails where the criterion fails**, exhibited by an
eigen-run the blind readout cannot see. -/
public theorem blind_not_determinesStateOn :
    ¬ DeterminesStateOn integratorA integratorB blindC (Set.univ : Set ℝ) :=
  not_determinesStateOn_of_not_isObservable ⟨0, Set.mem_univ 0⟩ blind_not_isObservable

/-- **The equivalence, both ways, on the integrator.** -/
public theorem integrator_determinesStateOn_iff :
    DeterminesStateOn integratorA integratorB integratorC (Set.univ : Set ℝ) ↔
      IsObservable integratorA integratorC :=
  determinesStateOn_iff_isObservable isOpen_univ ⟨0, Set.mem_univ 0⟩

/-- **Print's controllability fails where the criterion fails**: with no input
the origin is the only state ever reached. -/
public theorem deaf_not_isReachable : ¬ IsReachable integratorA deafB :=
  not_isReachable_of_not_isControllable deaf_not_isControllable

/-- **An eigen-run of the blind system**, written out: the state moves and the
output does not. -/
public theorem blind_eigenTrajectory_isTrajectoryOn :
    IsTrajectoryOn integratorA integratorB (Set.univ : Set ℝ)
      (eigenTrajectory 0 (fun _ : Fin 1 => (1 : ℂ))) (fun _ => 0) := by
  refine eigenTrajectory_isTrajectoryOn ?_ _
  funext i
  simp [integratorA]

/-- And it never vanishes. -/
public theorem blind_eigenTrajectory_ne_zero (t : ℝ) :
    eigenTrajectory 0 (fun _ : Fin 1 => (1 : ℂ)) t ≠ 0 := by
  refine eigenTrajectory_ne_zero ?_ t
  intro h
  have := congrFun h 0
  simp at this

/-- **Its derivative**, which is what makes it a run. -/
public theorem blind_hasDerivAt_eigenTrajectory (t : ℝ) :
    HasDerivAt (eigenTrajectory (n := 1) (0 : ℂ) (fun _ => (1 : ℂ)))
      ((0 * Complex.exp (0 * (t : ℂ))) • (fun _ : Fin 1 => (1 : ℂ))) t :=
  hasDerivAt_eigenTrajectory (n := 1) 0 (fun _ => 1) t

/-- **Every Kalman row of the blind pair annihilates every state.** -/
public theorem blind_mulVec_pow_eq_zero (k : ℕ) :
    (blindC * integratorA ^ k) *ᵥ (fun _ : Fin 1 => (1 : ℂ)) = 0 := by
  refine mulVec_pow_eq_zero_of_mem_unobservableSubspace ?_ k
  rw [mem_unobservableSubspace_iff]
  intro j
  simp [blindC]

/-- …and every power of `A` keeps a state unobservable. -/
public theorem blind_mulVec_pow_mem (k : ℕ) :
    integratorA ^ k *ᵥ (fun _ : Fin 1 => (1 : ℂ)) ∈ unobservableSubspace integratorA blindC := by
  refine mulVec_pow_mem_unobservableSubspace ?_ k
  rw [mem_unobservableSubspace_iff]
  intro j
  simp [blindC]

end AISafetyAtlas.Examples.LinearSystems
