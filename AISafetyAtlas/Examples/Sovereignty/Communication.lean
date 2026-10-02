module

public import AISafetyAtlas.Sovereignty.Communication
public import AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-!
# One bit through a channel you control, and none through one you do not

`decider_transmits` sends either bit: the principal names the outcome, and the
two singletons are disjoint regions it can force.

`bitMatch_not_transmits` is the other side. In the simultaneous-bit game every
commitment by the principal leaves both outcomes possible, so the only
forceable target is everything, and two disjoint everythings do not exist. The
channel is not noisy; it is adversarial, and zero-error capacity is zero.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Communication

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-- **The principal can send either bit.** -/
public theorem decider_transmits :
    TransmitsZeroError decider {false} (id : Bool → Bool) Bool := by
  refine ⟨fun m => {m}, fun m m' hmm => ?_, fun m => ?_⟩
  · exact Set.disjoint_singleton.mpr hmm
  · exact principalDecides_forces_singleton m

/-- **In the simultaneous-bit game every commitment leaves both outcomes
possible**, so only the full target is forceable. -/
public theorem bitMatch_forces_both {A : Set Bool}
    (h : Forces bitMatch {false} A) : (true : Bool) ∈ A ∧ (false : Bool) ∈ A := by
  obtain ⟨sC, hsC⟩ := h
  have key : ∀ x : Bool, sC ⟨false, rfl⟩ = x →
      (true : Bool) ∈ A ∧ (false : Bool) ∈ A := by
    intro x hx
    have hm := hsC (fun _ => x) (by rintro ⟨i, hi⟩; obtain rfl : i = false := hi; exact hx.symm)
    have hn := hsC (fun i => if i then !x else x)
      (by rintro ⟨i, hi⟩; obtain rfl : i = false := hi; simpa using hx.symm)
    have hm' : (true : Bool) ∈ A := by
      have : bitMatch.outcome (fun _ => x) = true := by cases x <;> rfl
      exact this ▸ hm
    have hn' : (false : Bool) ∈ A := by
      have : bitMatch.outcome (fun i => if i then !x else x) = false := by
        cases x <;> rfl
      exact this ▸ hn
    exact ⟨hm', hn'⟩
  exact key _ rfl

/-- **So it can send nothing at all**: two disjoint forceable regions would
each have to contain both outcomes. -/
public theorem bitMatch_not_transmits :
    ¬ TransmitsZeroError bitMatch {false} (id : Bool → Bool) Bool := by
  rintro ⟨D, hdisj, hforce⟩
  have h0 := (bitMatch_forces_both (hforce false)).1
  have h1 := (bitMatch_forces_both (hforce true)).1
  exact Set.disjoint_left.mp (hdisj false true (by decide)) h0 h1

/-! ## The two structural moves, at the channel the principal controls -/

/-- **Fewer messages are easier to send.** A one-message alphabet goes through
by `comp_injective`, along any injection into the alphabet already sent. -/
public theorem decider_transmits_unit :
    TransmitsZeroError decider {false} (id : Bool → Bool) Unit :=
  decider_transmits.comp_injective (fun _ => true) fun _ _ _ => Subsingleton.elim _ _

/-- The fine reading: the outcome, reported twice. -/
@[expose] public def duplicate : Bool → Bool × Bool := fun b => (b, b)

/-- **And coarsening cannot help.** The principal sends a bit through the first
coordinate alone, so `of_comp` returns the same alphabet through the whole pair.
A channel is never improved by discarding part of what it reports, which is the
qualitative shadow of `Q8`. -/
public theorem decider_transmits_duplicate :
    TransmitsZeroError decider {false} duplicate Bool :=
  TransmitsZeroError.of_comp (g := Prod.fst) decider_transmits

end AISafetyAtlas.Examples.Sovereignty.Communication
