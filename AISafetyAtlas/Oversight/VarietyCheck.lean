module

public import AISafetyAtlas.Oversight.VarietyBound
public import Mathlib.Data.Fintype.Card

/-!
# Deciding the variety bound

`Oversight.VarietyBound.not_forces_of_card_lt` has two hypotheses, and on a
finite effect table both are decidable. This module supplies the decision
procedure and the theorem saying it agrees with the `Prop`, so a consumer who
cannot read Lean can still get the verdict — that is what `atlas-check` is for,
and `kind: "variety"` is this checker.

`cannotForce` returns `true` exactly when the counting obstruction applies: every
intervention still separates situations, and there are fewer interventions than
situations. `not_forces_of_cannotForce` is the agreement theorem, and it is
stated for **every** observation type, so a `true` verdict rules out every
overseer and not merely the ones that see a particular thing.

A `false` verdict says nothing. The bound is a necessary condition, so failing it
means the obstruction does not apply here, not that oversight succeeds. The
checker reports that asymmetry rather than printing a verdict that reads like a
clearance.

## Explicit non-claims

- **Not** a decision procedure for `Forces`. It decides the counting obstruction,
  which is one sufficient reason for `Forces` to fail and not the only one.
- **A `false` result is not a safety verdict.** It means this argument does not
  apply.
- **Not** a proof term. Like the rest of `atlas-check`, the executable returns a
  verdict and names the theorem that certifies it; the kernel has checked the
  theorem, not the instance.
-/

namespace AISafetyAtlas.Oversight

open Function

/--
**The counting obstruction, decided.** `true` when every intervention still
distinguishes situations and there are fewer interventions than situations.
-/
@[expose] public def cannotForce {n m k : ℕ} (effect : Fin n → Fin m → Fin k) : Bool :=
  decide (∀ a : Fin m, Injective fun σ => effect σ a) && decide (m < n)

/--
**The agreement theorem.** A `true` verdict from `cannotForce` rules out every
overseer, over every observation type: no policy on any observation forces the
outcome to any single target.
-/
public theorem not_forces_of_cannotForce {n m k : ℕ} {effect : Fin n → Fin m → Fin k}
    (h : cannotForce effect = true) {Obs : Type*}
    (observe : Fin n → Obs) (act : Obs → Fin m) (target : Fin k) :
    ¬ Forces effect observe act target := by
  rw [cannotForce, Bool.and_eq_true] at h
  obtain ⟨hcol, hlt⟩ := h
  have hcol' : ∀ a : Fin m, Injective fun σ => effect σ a := of_decide_eq_true hcol
  have hlt' : Fintype.card (Fin m) < Fintype.card (Fin n) := by
    simpa using of_decide_eq_true hlt
  exact not_forces_of_card_lt hcol' hlt' act target

/--
The converse direction the checker deliberately does not claim: `cannotForce`
returning `false` leaves `Forces` open. Stated as the existence of a table where
the verdict is `false` and forcing does succeed, so that "not obstructed" can
never be read as "not possible".
-/
public theorem exists_cannotForce_false_and_forces :
    ∃ (effect : Fin 2 → Fin 1 → Fin 1) (act : Unit → Fin 1) (target : Fin 1),
      cannotForce effect = false
        ∧ Forces effect (fun _ => ()) act target := by
  refine ⟨fun _ _ => 0, fun _ => 0, 0, ?_, fun _ => rfl⟩
  decide

end AISafetyAtlas.Oversight
