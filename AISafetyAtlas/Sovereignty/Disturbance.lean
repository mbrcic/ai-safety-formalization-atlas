module

public import AISafetyAtlas.Sovereignty.Constitution
public import AISafetyAtlas.LinearSystems.Controllability
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# A linear plant, and the quantifier the rank condition hides

The proposal's `B4` is the point at which its power layer meets ordinary linear
control. Stacking a horizon of `x_{t+1} = A x_t + B u_t + E w_t` gives a
terminal state that is a drift plus a linear image of the stacked input plus a
linear image of the stacked disturbance. `Plant` is that shape and nothing
more: no time index survives, because after stacking there is none.

## The two halves, and why only one is a rank condition

`reachesEvery_iff_surjective` is the first: with no disturbance and
unrestricted open-loop inputs, every terminal state is reachable exactly when
the input map is onto. `isControllable_iff_reachesEvery` says that is the
atlas's own `AISafetyAtlas.LinearSystems.IsControllable`, so the rank criterion
already in the tree *is* this half -- print's "full row rank" and the Kalman
rank condition are one statement.

`exists_robustInput_iff` is the second and it is not a rank condition at all.
A precommitted input succeeds against every admissible disturbance exactly when
it solves the target equation at one disturbance **and the disturbance map
annihilates every difference from it**. The rank of the input map does not
appear. That is print's warning made checkable: controllability without a
disturbance and information model is not a guarantee about anything.

`robustReachesEvery_of_disturbance_constant` is the corner where the two halves
agree, and `Examples.Sovereignty.Disturbance` shows they otherwise do not: a
plant whose input map is onto and which cannot hold a single target against two
admissible disturbances.

**What is deliberately absent.** Feedback. Print says so too: a strategy that
reads the disturbance before choosing the input lives in a different strategy
class and can cancel what a precommitted input cannot. Everything here is
open-loop, which is what makes the cancellation condition necessary rather than
merely sufficient.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

/--
**A horizon-stacked linear plant.** The terminal state is a drift, plus the
image of the stacked input, plus the image of the stacked disturbance.
-/
public structure Plant (𝕜 : Type*) [Field 𝕜] (U W V : Type*)
    [AddCommGroup U] [Module 𝕜 U] [AddCommGroup W] [Module 𝕜 W]
    [AddCommGroup V] [Module 𝕜 V] where
  /-- Where the state goes with no input and no disturbance. -/
  drift : V
  /-- How the stacked input moves the terminal state. -/
  input : U →ₗ[𝕜] V
  /-- How the stacked disturbance moves it. -/
  disturbance : W →ₗ[𝕜] V

namespace Plant

variable {𝕜 U W V : Type*} [Field 𝕜] [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup W] [Module 𝕜 W] [AddCommGroup V] [Module 𝕜 V]

/-- The terminal state under a stacked input and a stacked disturbance. -/
@[expose] public def terminal (P : Plant 𝕜 U W V) (u : U) (w : W) : V :=
  P.drift + P.input u + P.disturbance w

/-- **An input that holds a target against every admissible disturbance.** -/
@[expose] public def RobustInput (P : Plant 𝕜 U W V) (Wset : Set W) (z : V)
    (u : U) : Prop :=
  ∀ w ∈ Wset, P.terminal u w = z

/-! ## The undisturbed half -/

/--
**With no disturbance, reachability is surjectivity of the input map.**

The drift is irrelevant: translating the target by it is a bijection of the
state space. This is the half that becomes a rank condition.
-/
public theorem reachesEvery_iff_surjective (P : Plant 𝕜 U W V) (w₀ : W)
    (hw : P.disturbance w₀ = 0) :
    (∀ z : V, ∃ u : U, P.terminal u w₀ = z) ↔ Function.Surjective P.input := by
  simp only [terminal, hw, add_zero]
  constructor
  · intro h y
    obtain ⟨u, hu⟩ := h (P.drift + y)
    exact ⟨u, add_left_cancel hu⟩
  · intro h z
    obtain ⟨u, hu⟩ := h (z - P.drift)
    exact ⟨u, by rw [hu, add_sub_cancel]⟩

/-! ## The disturbed half -/

/--
**`B4`: when a precommitted input holds a target against every admissible
disturbance.**

Exactly when it solves the target equation at **one** admissible disturbance
and the disturbance map annihilates every difference from that one.

Neither side mentions the rank of the input map. The forward direction is where
the quantifier bites: an input that works for all of `Wset` works at any chosen
member, and subtracting the two equations leaves the cancellation condition,
which is a statement about the *disturbance* map alone.
-/
public theorem exists_robustInput_iff (P : Plant 𝕜 U W V) {Wset : Set W}
    (hne : Wset.Nonempty) (z : V) :
    (∃ u : U, P.RobustInput Wset z u) ↔
      ∃ w₀ ∈ Wset, (∃ u : U, P.terminal u w₀ = z) ∧
        ∀ w ∈ Wset, P.disturbance (w - w₀) = 0 := by
  obtain ⟨w₁, hw₁⟩ := hne
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨w₁, hw₁, ⟨u, hu w₁ hw₁⟩, fun w hw => ?_⟩
    have h := (hu w hw).trans (hu w₁ hw₁).symm
    rw [map_sub, sub_eq_zero]
    simpa [terminal] using h
  · rintro ⟨w₀, hw₀, ⟨u, hu⟩, hcancel⟩
    refine ⟨u, fun w hw => ?_⟩
    have h := hcancel w hw
    rw [map_sub, sub_eq_zero] at h
    rw [terminal, h, ← hu, terminal]

/-- **The corner where the two halves agree.** If the disturbance map is
constant on the admissible set, robust reachability of every target is
ordinary surjectivity. -/
public theorem robustReachesEvery_of_disturbance_constant (P : Plant 𝕜 U W V)
    {Wset : Set W} {w₀ : W} (hw₀ : w₀ ∈ Wset)
    (hconst : ∀ w ∈ Wset, P.disturbance (w - w₀) = 0)
    (hsurj : Function.Surjective P.input) (z : V) :
    ∃ u : U, P.RobustInput Wset z u := by
  refine (P.exists_robustInput_iff ⟨w₀, hw₀⟩ z).mpr ⟨w₀, hw₀, ?_, hconst⟩
  obtain ⟨u, hu⟩ := hsurj (z - P.drift - P.disturbance w₀)
  exact ⟨u, by rw [terminal, hu]; abel⟩

end Plant

/-! ## The undisturbed half is the atlas's controllability -/

open AISafetyAtlas.LinearSystems in
/--
**`IsControllable` is `B4`'s first half.** The Kalman rank criterion already in
the tree and print's "`𝒞_H` has full row rank" are the same statement: every
terminal state is reachable from the drift by an open-loop input.
-/
public theorem isControllable_iff_reachesEvery {n m : ℕ} {𝕜 : Type*} [Field 𝕜]
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (c : Fin n → 𝕜) :
    IsControllable A B ↔
      ∀ z : Fin n → 𝕜, ∃ u : Fin n × Fin m → 𝕜,
        (Plant.mk (𝕜 := 𝕜) (W := PUnit) c
          (controllabilityMatrix A B).mulVecLin 0).terminal u PUnit.unit = z := by
  rw [isControllable_iff_controllabilityMatrix_mulVec_surjective]
  rw [Plant.reachesEvery_iff_surjective _ PUnit.unit rfl]
  exact ⟨fun h y => h y, fun h y => h y⟩

end AISafetyAtlas.Sovereignty
