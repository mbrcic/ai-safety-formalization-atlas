module

public import AISafetyAtlas.LinearSystems.Hautus
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Klamka's system, as a system

J. Klamka, *Uncontrollability and unobservability of multivariable systems*,
IEEE Transactions on Automatic Control 17(5) (1972) 725-726, page 725:

> Consider the linear time-invariant system `S` described by the state equations
> `ẋ(t) = Ax(t) + Bu(t)`, `y(t) = Cx(t)` where the state vector `x(t)` is
> `n × 1`, the input vector `u(t)` is `p × 1`, and the output vector `y(t)` is
> `q × 1`.

`AISafetyAtlas.LinearSystems.Controllability` and `.Observability` carry the
Kalman rank criteria for that system's two properties. They carry them as
**algebraic conditions on the matrices**, and until this module the differential
equation above appeared nowhere in the atlas: the matrices were print's and the
dynamics were not.

`IsTrajectory` is print's state equation and `outputSignal` is print's output
equation, both written at print's shapes.

## What is proved, and what is not

`isObservable_imp_determinesInitialState` is the half of the observability
bridge that runs from the atlas's condition to print's property: **if the pair
`(A, C)` satisfies the rank criterion then the output signal determines the
initial state**, which is what complete state observability asserts. It is proved
without constructing any solution -- the argument differentiates the output
repeatedly and reads off the Kalman rows at time zero -- so it needs neither a
matrix exponential nor an existence theorem.

**Three things are deliberately absent, and the audit's section 25 costs them.**

* The converse, `DeterminesInitialState → IsObservable`. That direction has to
  exhibit a trajectory through an unobservable state, so it needs `exp (t • A)`
  and, to get from the first `n` Kalman rows to all of them, Cayley-Hamilton.
* Controllability as *reachability* in the sufficiency direction. That is in
  `AISafetyAtlas.LinearSystems.Flow`, which carries the flow, variation of
  constants and the adjoint argument, and it needs no Gramian.
* Uniqueness of solutions. Nothing here says that a trajectory is determined by
  its initial state. `DeterminesStateOn` concludes that two runs agree at every
  time in the window, which is stronger than agreeing at one, but it is still a
  statement about the states those runs pass through and not about the runs
  being the same object. Print does not use uniqueness either.

**Print does not define these notions.** Page 726 says *"It is well known [1]
that the system `S` is completely state controllable (observable) if and only if
for each `i` the set of `αᵢ` row vectors … are linearly independent"*, citing
Chen and Desoer. So print states the criterion it reasons with and imports the
notion behind it, exactly as this module states a criterion and connects it to
the property in one direction.
-/

namespace AISafetyAtlas.LinearSystems

open Matrix

variable {n p q : ℕ}

/-! ## Print's two equations -/

/--
**Print's state equation** `ẋ(t) = Ax(t) + Bu(t)`, as a predicate on a state
trajectory and an input signal.

Time is `ℝ` and the equation is asked on a **set** `s`, because print's `x(t)`
lives on a time interval and demanding the derivative at every real number would
be a different and stronger request -- it would admit fewer trajectories, which
would make the observability conclusion below weaker than print's. Every theorem
is stated at an arbitrary open `s` and the whole line is the corollary.
Nothing here asserts that a trajectory exists for a given input;
`IsTrajectoryOn` is a property of a pair, and every theorem below is conditional
on having one.
-/
@[expose] public def IsTrajectoryOn (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin p) ℂ) (s : Set ℝ) (x : ℝ → (Fin n → ℂ))
    (u : ℝ → (Fin p → ℂ)) : Prop :=
  ∀ t ∈ s, HasDerivAt x (A *ᵥ x t + B *ᵥ u t) t

/-- The state equation on the whole line, which is `IsTrajectoryOn` at
`Set.univ` and the special case nothing below is stated at. -/
@[expose] public def IsTrajectory (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin p) ℂ) (x : ℝ → (Fin n → ℂ)) (u : ℝ → (Fin p → ℂ)) : Prop :=
  IsTrajectoryOn A B Set.univ x u

public theorem isTrajectoryOn_univ_iff {A : Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin p) ℂ} {x : ℝ → (Fin n → ℂ)} {u : ℝ → (Fin p → ℂ)} :
    IsTrajectoryOn A B Set.univ x u ↔ ∀ t : ℝ, HasDerivAt x (A *ᵥ x t + B *ᵥ u t) t :=
  ⟨fun h t => h t (Set.mem_univ t), fun h t _ => h t⟩

/-- **Print's output equation** `y(t) = Cx(t)`. -/
@[expose] public def outputSignal (C : Matrix (Fin q) (Fin n) ℂ)
    (x : ℝ → (Fin n → ℂ)) : ℝ → (Fin q → ℂ) :=
  fun t => C *ᵥ x t

/--
**Complete state observability, as the property rather than as the criterion.**
The output signal determines the state the system started in.

This is what `IsObservable` is a criterion *for*. Print states the criterion and
cites Chen and Desoer for the equivalence; `isObservable_imp_determinesInitialState`
is the direction of that equivalence this module proves.
-/
@[expose] public def DeterminesStateOn (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin p) ℂ) (C : Matrix (Fin q) (Fin n) ℂ) (s : Set ℝ) : Prop :=
  ∀ (x y : ℝ → (Fin n → ℂ)) (u : ℝ → (Fin p → ℂ)),
    IsTrajectoryOn A B s x u → IsTrajectoryOn A B s y u →
      (∀ t ∈ s, outputSignal C x t = outputSignal C y t) → ∀ t ∈ s, x t = y t

/-- The same on the whole line. -/
@[expose] public def DeterminesInitialState (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin p) ℂ) (C : Matrix (Fin q) (Fin n) ℂ) : Prop :=
  DeterminesStateOn A B C Set.univ

/-! ## Differentiating a linear readout of a trajectory -/

/-- A fixed matrix applied to a differentiable curve differentiates through the
matrix. Proved coordinatewise, so it needs no continuous-linear-map instance on
matrices. -/
public theorem hasDerivAt_mulVec {m : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    {f : ℝ → (Fin n → ℂ)} {f' : Fin n → ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => M *ᵥ f s) (M *ᵥ f') t := by
  rw [hasDerivAt_pi] at hf ⊢
  intro i
  have hfun : (fun s => (M *ᵥ f s) i) = fun s => ∑ j : Fin n, M i j * f s j := rfl
  have hval : (M *ᵥ f') i = ∑ j : Fin n, M i j * f' j := rfl
  rw [hfun, hval]
  exact HasDerivAt.fun_sum fun j _ => (hf j).const_mul (M i j)

/-- **The difference of two trajectories under the same input is a zero-input
trajectory.** The input term cancels, which is why observability never sees it. -/
public theorem IsTrajectoryOn.hasDerivAt_sub {A : Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin p) ℂ} {S : Set ℝ} {x y : ℝ → (Fin n → ℂ)}
    {u : ℝ → (Fin p → ℂ)} (hx : IsTrajectoryOn A B S x u) (hy : IsTrajectoryOn A B S y u)
    {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun s => x s - y s) (A *ᵥ (x t - y t)) t := by
  have h := (hx t ht).sub (hy t ht)
  rwa [show A *ᵥ x t + B *ᵥ u t - (A *ᵥ y t + B *ᵥ u t) = A *ᵥ (x t - y t) by
    rw [Matrix.mulVec_sub]; abel] at h

/--
**Every Kalman row annihilates a zero-output zero-input trajectory, at every
time.** Induction on the power: the readout `(C · Aᵏ) x(t)` is identically zero,
so its derivative is identically zero, and that derivative is the next readout.

This is the whole analytic content of the bridge, and it constructs nothing.
-/
public theorem mulVec_pow_eq_zero_of_outputSignal_eq_zero
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin q) (Fin n) ℂ} {S : Set ℝ}
    (hS : IsOpen S) {d : ℝ → (Fin n → ℂ)} (hd : ∀ t ∈ S, HasDerivAt d (A *ᵥ d t) t)
    (h0 : ∀ t ∈ S, C *ᵥ d t = 0) :
    ∀ (k : ℕ), ∀ t ∈ S, (C * A ^ k) *ᵥ d t = 0 := by
  intro k
  induction k with
  | zero => intro t ht; simpa using h0 t ht
  | succ k ih =>
      intro t ht
      have hEq : (fun s => (C * A ^ k) *ᵥ d s) =ᶠ[nhds t] fun _ : ℝ => (0 : Fin q → ℂ) := by
        filter_upwards [hS.mem_nhds ht] with r hr using ih r hr
      have hzero : HasDerivAt (fun s => (C * A ^ k) *ᵥ d s) 0 t :=
        (hasDerivAt_const t (0 : Fin q → ℂ)).congr_of_eventuallyEq hEq
      have hstep : HasDerivAt (fun s => (C * A ^ k) *ᵥ d s)
          ((C * A ^ k) *ᵥ (A *ᵥ d t)) t :=
        hasDerivAt_mulVec _ (hd t ht)
      have h2 := hstep.unique hzero
      rw [Matrix.mulVec_mulVec] at h2
      rw [pow_succ, ← Matrix.mul_assoc]
      exact h2

/--
**The rank criterion delivers print's observability.**

If `(A, C)` satisfies the Kalman rank criterion then two trajectories driven by
the same input and producing the same output started at the same state. Print's
complete state observability, from print's criterion, in the direction that does
not need a solution to exist.
-/
public theorem isObservable_imp_determinesStateOn
    {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p) ℂ}
    {C : Matrix (Fin q) (Fin n) ℂ} {S : Set ℝ} (hS : IsOpen S) (hobs : IsObservable A C) :
    DeterminesStateOn A B C S := by
  intro x y u hx hy hout t₀ ht₀
  have hd : ∀ t ∈ S, HasDerivAt (fun s => x s - y s) (A *ᵥ ((fun s => x s - y s) t)) t :=
    fun t ht => hx.hasDerivAt_sub hy ht
  have h0 : ∀ t ∈ S, C *ᵥ ((fun s => x s - y s) t) = 0 := by
    intro t ht
    have h := hout t ht
    simp only [outputSignal] at h
    rw [Matrix.mulVec_sub, h, sub_self]
  have hall := mulVec_pow_eq_zero_of_outputSignal_eq_zero hS hd h0
  have := hobs (x t₀ - y t₀) fun k => hall (k : ℕ) t₀ ht₀
  exact sub_eq_zero.mp this

/-- The whole-line corollary. -/
public theorem isObservable_imp_determinesInitialState
    {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p) ℂ}
    {C : Matrix (Fin q) (Fin n) ℂ} (hobs : IsObservable A C) :
    DeterminesInitialState A B C :=
  isObservable_imp_determinesStateOn isOpen_univ hobs

/-- The same statement with the input held at zero, which is the form print's
duality argument uses. -/
public theorem isObservable_imp_zeroInput_state_eq
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin q) (Fin n) ℂ} {S : Set ℝ}
    (hS : IsOpen S) (hobs : IsObservable A C) (x : ℝ → (Fin n → ℂ))
    (hx : ∀ t ∈ S, HasDerivAt x (A *ᵥ x t) t) (h0 : ∀ t ∈ S, C *ᵥ x t = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ S) :
    x t₀ = 0 :=
  hobs (x t₀) fun k => mulVec_pow_eq_zero_of_outputSignal_eq_zero hS hx h0 (k : ℕ) t₀ ht₀

/-! ## The converse, and the equivalence

Print's criterion is necessary as well as sufficient, and the witness that makes
it so is an **eigenvector**: `exists_eigenvector_of_unobservableSubspace_neBot`,
already in `Hautus`, turns a non-trivial unobservable subspace into a `v ≠ 0`
with `A *ᵥ v = μ • v` and `C *ᵥ v = 0`. The trajectory through it is
`t ↦ exp (μ t) • v`, an elementary function -- no matrix exponential is needed
to exhibit an unobservable run, because an eigenvector turns the matrix
exponential into a scalar one.
-/

/-- **The run through an unobservable eigenvector.** -/
@[expose] public noncomputable def eigenTrajectory (μ : ℂ) (v : Fin n → ℂ) :
    ℝ → (Fin n → ℂ) :=
  fun t => Complex.exp (μ * t) • v

public theorem hasDerivAt_eigenTrajectory (μ : ℂ) (v : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (eigenTrajectory μ v) ((μ * Complex.exp (μ * t)) • v) t := by
  rw [hasDerivAt_pi]
  intro i
  have hlin : HasDerivAt (fun s : ℝ => μ * (s : ℂ)) μ t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul μ
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (μ * (s : ℂ)))
      (Complex.exp (μ * (t : ℂ)) * μ) t := hlin.cexp
  have := hexp.mul_const (v i)
  simpa [eigenTrajectory, mul_comm, mul_assoc, mul_left_comm] using this

/-- **The eigen-run solves the free state equation**, at any input, because the
input enters through `B *ᵥ 0`. -/
public theorem eigenTrajectory_isTrajectoryOn {A : Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin p) ℂ} {μ : ℂ} {v : Fin n → ℂ} (hv : A *ᵥ v = μ • v)
    (S : Set ℝ) : IsTrajectoryOn A B S (eigenTrajectory μ v) (fun _ => 0) := by
  intro t _
  have hAx : A *ᵥ eigenTrajectory μ v t + B *ᵥ ((fun _ : ℝ => (0 : Fin p → ℂ)) t)
      = (μ * Complex.exp (μ * t)) • v := by
    show A *ᵥ eigenTrajectory μ v t + B *ᵥ (0 : Fin p → ℂ) = _
    rw [Matrix.mulVec_zero, add_zero, eigenTrajectory, Matrix.mulVec_smul, hv, smul_smul,
      mul_comm]
  rw [hAx]
  exact hasDerivAt_eigenTrajectory μ v t

/-- It never vanishes, because a complex exponential does not. -/
public theorem eigenTrajectory_ne_zero {μ : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0) (t : ℝ) :
    eigenTrajectory μ v t ≠ 0 := by
  simp [eigenTrajectory, Complex.exp_ne_zero, hv]

/--
**The criterion is necessary.** If the rank criterion fails then two runs with
the same input and the same output pass through different states: the eigen-run
above and the run that stays at the origin.
-/
public theorem not_determinesStateOn_of_not_isObservable
    {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p) ℂ}
    {C : Matrix (Fin q) (Fin n) ℂ} {S : Set ℝ} (hne : S.Nonempty)
    (hobs : ¬ IsObservable A C) : ¬ DeterminesStateOn A B C S := by
  obtain ⟨μ, v, hv0, hAv, hCv⟩ :=
    exists_eigenvector_of_unobservableSubspace_neBot A C
      (fun hbot => hobs ((unobservableSubspace_eq_bot_iff_isObservable A C).mp hbot))
  intro hdet
  obtain ⟨t₀, ht₀⟩ := hne
  have hzero : IsTrajectoryOn A B S (fun _ => (0 : Fin n → ℂ)) (fun _ => 0) := by
    intro t _
    have hz : A *ᵥ ((fun _ : ℝ => (0 : Fin n → ℂ)) t)
        + B *ᵥ ((fun _ : ℝ => (0 : Fin p → ℂ)) t) = 0 := by
      show A *ᵥ (0 : Fin n → ℂ) + B *ᵥ (0 : Fin p → ℂ) = 0
      rw [Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
    rw [hz]
    exact hasDerivAt_const t 0
  have hout : ∀ t ∈ S, outputSignal C (eigenTrajectory μ v) t
      = outputSignal C (fun _ => (0 : Fin n → ℂ)) t := by
    intro t _
    simp only [outputSignal, eigenTrajectory, Matrix.mulVec_smul, hCv, smul_zero,
      Matrix.mulVec_zero]
  have := hdet (eigenTrajectory μ v) (fun _ => 0) (fun _ => 0)
    (eigenTrajectory_isTrajectoryOn hAv S) hzero hout t₀ ht₀
  exact eigenTrajectory_ne_zero hv0 t₀ this

/--
**Klamka's observability, criterion and property, are the same thing.**

The rank criterion holds exactly when the output determines the state, on any
non-empty open window of time. Print states the equivalence and cites Chen and
Desoer for it; this is the proof.
-/
public theorem determinesStateOn_iff_isObservable
    {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p) ℂ}
    {C : Matrix (Fin q) (Fin n) ℂ} {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) :
    DeterminesStateOn A B C S ↔ IsObservable A C := by
  classical
  constructor
  · intro hdet
    by_contra hobs
    exact not_determinesStateOn_of_not_isObservable hne hobs hdet
  · exact isObservable_imp_determinesStateOn hS

/-! ## Controllability as reachability

Print's complete state *controllability* is reachability: every state is reached
from the origin. `IsReachable` is that, on print's own equation. Only one
direction is proved, and it is the direction that needs no construction: **if
the rank criterion fails, some state is never reached.**

The route is the duality the cluster already carries,
`isControllable_iff_isObservable_transpose`, plus the eigenvector above read at
the transposed pair. It gives a `z ≠ 0` with `Aᵀ z = μ z` and `Bᵀ z = 0`, and
then `t ↦ z ⬝ᵥ x t` solves the scalar equation `φ' = μ φ` -- the input drops out
because `Bᵀ z = 0` -- so a run starting at the origin keeps `z ⬝ᵥ x t = 0`
forever and misses every state on which `z` does not vanish.

**The converse is in `Flow`**, as `isCompletelyReachable_iff_isControllable`. It
builds an input, and the classical construction for that is the controllability
Gramian; the route taken there replaces the Gramian by a subspace argument and
one integral-positivity step.
-/

/-- **Complete state controllability, as the property.** Every state is reached
from the origin, in some time, by some input. -/
@[expose] public def IsReachable (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin p) ℂ) : Prop :=
  ∀ x₁ : Fin n → ℂ, ∃ (x : ℝ → (Fin n → ℂ)) (u : ℝ → (Fin p → ℂ)) (t₁ : ℝ),
    IsTrajectory A B x u ∧ x 0 = 0 ∧ x t₁ = x₁

/-- A linear readout of a trajectory along a left eigenvector of `A` that
annihilates `B` solves the scalar equation `φ' = μ φ`. -/
public theorem hasDerivAt_dotProduct_of_eigen {A : Matrix (Fin n) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin p) ℂ} {μ : ℂ} {z : Fin n → ℂ}
    (hz : Aᵀ *ᵥ z = μ • z) (hzB : Bᵀ *ᵥ z = 0) {x : ℝ → (Fin n → ℂ)}
    {u : ℝ → (Fin p → ℂ)} (hx : IsTrajectory A B x u) (t : ℝ) :
    HasDerivAt (fun s => z ⬝ᵥ x s) (μ * (z ⬝ᵥ x t)) t := by
  have hd := hx t (Set.mem_univ t)
  have hstep : HasDerivAt (fun s => z ⬝ᵥ x s) (z ⬝ᵥ (A *ᵥ x t + B *ᵥ u t)) t := by
    rw [hasDerivAt_pi] at hd
    simp only [dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hd j).const_mul (z j)
  have hval : z ⬝ᵥ (A *ᵥ x t + B *ᵥ u t) = μ * (z ⬝ᵥ x t) := by
    rw [dotProduct_add, dotProduct_mulVec, dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose, hz, hzB, smul_dotProduct,
      zero_dotProduct, add_zero, smul_eq_mul]
  rwa [hval] at hstep

/-- A solution of `φ' = μ φ` that starts at zero stays at zero. -/
public theorem eq_zero_of_hasDerivAt_mul {μ : ℂ} {φ : ℝ → ℂ}
    (hφ : ∀ t : ℝ, HasDerivAt φ (μ * φ t) t) (h0 : φ 0 = 0) (t : ℝ) : φ t = 0 := by
  set ψ : ℝ → ℂ := fun s => Complex.exp (-μ * s) * φ s with hψ
  have hψ' : ∀ s : ℝ, HasDerivAt ψ 0 s := by
    intro s
    have hlin : HasDerivAt (fun r : ℝ => -μ * (r : ℂ)) (-μ) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-μ)
    have hexp : HasDerivAt (fun r : ℝ => Complex.exp (-μ * (r : ℂ)))
        (Complex.exp (-μ * (s : ℂ)) * (-μ)) s := hlin.cexp
    have hmul := hexp.mul (hφ s)
    have : Complex.exp (-μ * (s : ℂ)) * (-μ) * φ s
        + Complex.exp (-μ * (s : ℂ)) * (μ * φ s) = 0 := by ring
    rwa [this] at hmul
  have hconst : ψ t = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψ' s).differentiableAt)
      (fun s => (hψ' s).deriv) t 0
  have hψ0 : ψ 0 = 0 := by simp [hψ, h0]
  have hzt : Complex.exp (-μ * (t : ℂ)) * φ t = 0 := by
    have h := hconst.trans hψ0
    simpa [hψ] using h
  rcases mul_eq_zero.mp hzt with h | h
  · exact absurd h (Complex.exp_ne_zero _)
  · exact h

/--
**If the rank criterion fails, some state is never reached.**

Print's complete state controllability is necessary for the criterion, in the
direction that exhibits no input. The converse is in
`AISafetyAtlas.LinearSystems.Flow`.
-/
public theorem not_isReachable_of_not_isControllable
    {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p) ℂ}
    (hc : ¬ IsControllable A B) : ¬ IsReachable A B := by
  classical
  have hobs : ¬ IsObservable Aᵀ Bᵀ := fun h =>
    hc ((isControllable_iff_isObservable_transpose A B).mpr h)
  obtain ⟨μ, z, hz0, hAz, hBz⟩ :=
    exists_eigenvector_of_unobservableSubspace_neBot Aᵀ Bᵀ
      (fun hbot => hobs ((unobservableSubspace_eq_bot_iff_isObservable Aᵀ Bᵀ).mp hbot))
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    exact hz0 (funext fun i => not_not.mp (fun hne => h ⟨i, hne⟩))
  intro hreach
  obtain ⟨x, u, t₁, hx, hx0, hx1⟩ := hreach (fun j => if j = i then (z i)⁻¹ else 0)
  have hzero : ∀ t : ℝ, z ⬝ᵥ x t = 0 := by
    intro t
    refine eq_zero_of_hasDerivAt_mul (μ := μ)
      (fun s => hasDerivAt_dotProduct_of_eigen hAz hBz hx s) ?_ t
    rw [hx0, dotProduct_zero]
  have hone : z ⬝ᵥ x t₁ = 1 := by
    rw [hx1, dotProduct]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_inv_cancel₀ hi]
    · intro j _ hj; rw [if_neg hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hzero t₁] at hone
  exact zero_ne_one hone

end AISafetyAtlas.LinearSystems
