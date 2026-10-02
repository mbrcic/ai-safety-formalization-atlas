module

public import AISafetyAtlas.Sovereignty.Capability
public import Mathlib.Algebra.Order.Ring.Int
public import AISafetyAtlas.Sovereignty.Separations

/-!
# The source's own arithmetic, and two trajectories that fix the hypotheses

Three witnesses over `ℤ`.

* `sketch_case` is the reference case as printed: fallback falls from 2 to 1
  while assisted output rises from 2 to 4, on borrowed assistance 3.
* `expanding_floor` inhabits the maintenance floor's antecedent with `a = 2`,
  so "the theorem needs only its printed assumptions" is checked rather than
  asserted — a forgetting reading would require `a ≤ 1` and the theorem does not.
* `floor_fails_without_practice` removes the top-up floor and the conclusion
  fails at the first step, so that hypothesis is not decoration either.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Capability

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Knowledge

/-! ## The printed reference case -/

/-- Before: fallback 2, nothing borrowed. -/
@[expose] public def before : ℤ × ℤ := (2, 0)

/-- After: fallback 1, assistance 3. -/
@[expose] public def after : ℤ × ℤ := (1, 3)

/--
**The source's reference case.** Assisted output rises from 2 to 4 while fallback
capability falls from 2 to 1.
-/
public theorem sketch_case :
    assistedOutput before = 2 ∧ assistedOutput after = 4 ∧
      fallbackCapability after < fallbackCapability before := by
  unfold assistedOutput fallbackCapability before after
  decide

/-- So the two move in opposite directions at this pair. -/
public theorem sketch_case_opposed :
    assistedOutput before < assistedOutput after ∧
      fallbackCapability after < fallbackCapability before := by
  unfold assistedOutput fallbackCapability before after
  decide

/-- And no decoder on output recovers fallback, at these very levels. -/
public theorem fallback_unreadable :
    ¬ Knowable (assistedOutput (R := ℤ)) (fallbackCapability (R := ℤ)) :=
  fallback_not_knowable_from_assistedOutput (R := ℤ) (x := 2) (y := 1) (by decide)

/-! ## The floor holds with retention above one -/

/-- Retention 2, top-ups of `-1`, floor 1, start 1. -/
@[expose] public def expanding : ℕ → ℤ := fun _ => 1

/-- The top-up sequence: constant `-1`. -/
@[expose] public def drain : ℕ → ℤ := fun _ => -1

/-- It does obey the recurrence with `a = 2`. -/
public theorem expanding_affine : AffineCapability expanding drain 2 := by
  intro t
  unfold expanding drain
  decide

/--
**The antecedent is inhabited with `a = 2`.** Retention above one is allowed by
the theorem, and here it is used: nothing in `maintenanceFloor_of_practice_floor`
assumes `a ≤ 1`.
-/
public theorem expanding_floor : MaintenanceFloor expanding 1 :=
  maintenanceFloor_of_practice_floor expanding_affine (by decide) (by decide)
    (fun _ => by unfold drain; decide)

/-- **The floor binds at the start, not only in the limit.** A maintenance floor
is a statement about every time; reading it at time zero is what an argument
needs when it wants to say the capability was never below the floor to begin
with, and it is the projection the definition exists to make available. -/
public theorem expanding_floor_at_zero : (1 : ℤ) ≤ expanding 0 :=
  MaintenanceFloor.le_zero expanding_floor

/-! ## Without the top-up floor there is no floor -/

/-- Retention 1, a drain of `-1`, and a trajectory that walks down. -/
@[expose] public def leaking : ℕ → ℤ := fun t => 1 - (t : ℤ)

/-- It obeys the recurrence with `a = 1`. -/
public theorem leaking_affine : AffineCapability leaking drain 1 := by
  intro t
  unfold leaking drain
  omega

/--
**The top-up floor is load-bearing.** Here `a = 1`, so the floor demands
`0 ≤ p t`, and `p t = -1` violates it; the trajectory drops below `1` at the
first step.
-/
public theorem floor_fails_without_practice : ¬ MaintenanceFloor leaking 1 := by
  intro h
  have h1 := h 1
  unfold leaking at h1
  norm_num at h1
  exact absurd h1 (by decide)


/-! ## Optionality: the enlargement that helps, and the one that does not -/

/-- Agent `false` is the principal; agent `true` is everyone else. -/
@[expose] public def principal : Set Bool := {false}

/-- The baseline: nobody has a choice, and the outcome is always `0`. -/
@[expose] public def baseG : GameForm Bool (Fin 2) where
  strategy := fun _ => Unit
  outcome := fun _ => 0

/-- **The principal gains an option**, and its choice now names the outcome.
Agent `true` gains nothing. -/
@[expose] public def wideG : GameForm Bool (Fin 2) where
  strategy := fun b => cond b Unit (Fin 2)
  outcome := fun s => s false

/-- **Somebody else gains an option**, and it is *their* choice that names the
outcome. The principal still has nothing to say. -/
@[expose] public def foeG : GameForm Bool (Fin 2) where
  strategy := fun b => cond b (Fin 2) Unit
  outcome := fun s => s true

/-- The baseline guarantees `0`, trivially: no profile produces anything else. -/
public theorem base_forces_zero : Forces baseG principal {(0 : Fin 2)} :=
  ⟨fun _ => (), fun _ _ => rfl⟩

/-- Widening the principal's own options, and nobody else's, is an `Enlarges`. -/
@[expose] public def wideEnlarges : Enlarges baseG wideG principal where
  embed := fun b => match b with
    | true => fun _ => ()
    | false => fun _ => (0 : Fin 2)
  reduce := fun _ _ _ => ()
  embed_reduce := by
    rintro (_ | _) h t
    · exact absurd rfl h
    · rfl
  outcome_embed := fun _ => rfl

/-- **GK3 at this witness.** The guarantee survives the new options.

Written `Enlarges.forces wideEnlarges` rather than `wideEnlarges.forces`: four
declarations in the tree end in `forces`, so the dot form leaves nothing in the
source text that the debt report can attribute to this one, and the lemma
was reported as reaching no witness while this line was already its witness. -/
public theorem wide_forces_zero : Forces wideG principal {(0 : Fin 2)} :=
  Enlarges.forces wideEnlarges base_forces_zero

/-- **The whole effectivity family survives, not only the sets named here.**
`Enlarges` is a statement about one coalition's powers, and this is the form an
argument uses when it does not want to re-derive each guarantee: everything the
principal could force before, it can force now. -/
public theorem wide_effectivity_grows :
    effectivity baseG principal ⊆ effectivity wideG principal :=
  Enlarges.effectivity_subset wideEnlarges

/-- And the new options are real: the principal can now force `1`. -/
public theorem wide_forces_one : Forces wideG principal {(1 : Fin 2)} := by
  refine ⟨fun i => i.2 ▸ (1 : Fin 2), ?_⟩
  intro s hs
  have h : s false = _ := hs ⟨false, rfl⟩
  show s false ∈ ({1} : Set (Fin 2))
  rw [h]
  rfl

/-- It could not before, so `Enlarges` is not inhabited only by identities and
`wide_forces_zero` is not a restatement of `base_forces_zero`. -/
public theorem base_not_forces_one : ¬ Forces baseG principal {(1 : Fin 2)} := by
  rintro ⟨sC, h⟩
  exact absurd (h (fun _ => ()) (fun _ => rfl)) (by decide)

/-- The map that simulates the baseline inside `foeG`. -/
@[expose] public def foeEmbed : ∀ b, baseG.strategy b → foeG.strategy b := fun b =>
  match b with
  | true => fun _ => (0 : Fin 2)
  | false => fun _ => ()

/--
**The clause that carries the weight.** `foeEmbed` embeds every old option and
**the old semantics is simulated unchanged** — the first and last clauses of
`Enlarges` both hold — and the guarantee is destroyed anyway.

What fails is `embed_reduce`: agent `true` is outside the principal coalition
and gained an option. So GK3's requirement that *only the coalition's* options
grow is not decoration; drop it and the theorem is false.
-/
public theorem foe_breaks_forces :
    (∀ s, foeG.outcome (fun b => foeEmbed b (s b)) = baseG.outcome s) ∧
      Forces baseG principal {(0 : Fin 2)} ∧ ¬ Forces foeG principal {(0 : Fin 2)} := by
  refine ⟨fun _ => rfl, base_forces_zero, ?_⟩
  rintro ⟨sC, h⟩
  have hbad := h (fun b => match b with | true => (1 : Fin 2) | false => ()) ?_
  · exact absurd hbad (by decide)
  · intro i
    have hi : (i : Bool) = false := i.2
    have : i = ⟨false, rfl⟩ := Subtype.ext hi
    subst this
    rfl

end AISafetyAtlas.Examples.Sovereignty.Capability
