module

public import AISafetyAtlas.Sovereignty.Constitution
public import Mathlib.Tactic.FinCases

/-!
# A constitution that can be amended forward and never back

Three constitutions, `Fin 3`, with amendment permitted only in one direction:
`0 → 1 → 2`. `authorized_two` is the chain `C5` produces from a two-step
history. `not_authorized_zero_from_two` is the other half of why the notion has
content -- under this rule no chain runs backwards, so `AuthorizedFrom`
distinguishes reachable constitutions from unreachable ones.

Read against `authorizedFrom_of_total`, the pair is the whole lesson: a valid
chain says something here only because this amendment rule forbids something.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Constitution

open AISafetyAtlas.Sovereignty

/-- Amendment is permitted only from a constitution to its immediate
successor. -/
@[expose] public def step : Fin 3 → Fin 3 → Prop :=
  fun a b => b.val = a.val + 1

/-- The history: constitution `t` at time `t`, capped at `2`. -/
@[expose] public def hist : ℕ → Fin 3 :=
  fun t => ⟨min t 2, by omega⟩

/-- **`C5` at a two-step history.** -/
public theorem authorized_two : AuthorizedFrom step (hist 0) (hist 2) := by
  refine authorizedFrom_of_stepwise hist 2 ?_
  intro t ht
  have htt : t = 0 ∨ t = 1 := by omega
  rcases htt with rfl | rfl <;> · show _ = _ ; rfl

/-- **And no chain runs backwards.** Every amendment strictly increases the
index, so nothing authorizes a return to the anchor. -/
public theorem not_authorized_zero_from_two :
    ¬ AuthorizedFrom step (2 : Fin 3) (0 : Fin 3) := by
  intro h
  have key : ∀ a b : Fin 3, AuthorizedFrom step a b → a.val ≤ b.val := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | tail _ hstep ih =>
        refine le_trans ih ?_
        simp only [step] at hstep
        omega
  have hle : ((2 : Fin 3) : ℕ) ≤ ((0 : Fin 3) : ℕ) := key 2 0 h
  revert hle
  decide

/-! ## The chain's two structural moves -/

/-- The first amendment is permitted. -/
public theorem authorized_zero_one : AuthorizedFrom step (0 : Fin 3) (1 : Fin 3) :=
  Relation.ReflTransGen.single (by show ((1 : Fin 3) : ℕ) = ((0 : Fin 3) : ℕ) + 1; rfl)

/-- And so is the second. -/
public theorem authorized_one_two : AuthorizedFrom step (1 : Fin 3) (2 : Fin 3) :=
  Relation.ReflTransGen.single (by show ((2 : Fin 3) : ℕ) = ((1 : Fin 3) : ℕ) + 1; rfl)

/-- **Chains compose.** The same endpoint `authorized_two` reaches from a
history, reached instead by joining two single amendments -- which is what makes
a constitution's validity checkable one step at a time. -/
public theorem authorized_zero_two_by_trans :
    AuthorizedFrom step (0 : Fin 3) (2 : Fin 3) :=
  AuthorizedFrom.trans authorized_zero_one authorized_one_two

/-- **And loosening the rule preserves the chain.** Under an amendment rule that
permits everything the same endpoint stays authorized. Read against
`not_authorized_zero_from_two`, this is why monotonicity has content: the
backwards chain that the strict rule refuses is exactly what a looser rule would
admit. -/
public theorem authorized_two_under_total :
    AuthorizedFrom (fun _ _ : Fin 3 => True) (hist 0) (hist 2) :=
  AuthorizedFrom.mono authorized_two fun _ _ _ => trivial

end AISafetyAtlas.Examples.Sovereignty.Constitution
