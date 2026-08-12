module

import AISafetyAtlas.SelfAwareness
import Mathlib.Data.Fintype.Powerset

/-!
# Non-vacuity and boundary examples for limited self-awareness

The first model satisfies every field of `SelfAwareness.Model` while retaining
an ordinary two-process awareness cycle. Its two singleton processes observe one
another; their joint composite remains unobserved, exactly as Theorem 4.8 says.

The final two examples omit composite closure. They show that Proposition 4.7
alone does not imply limited self-awareness: a flat two-node graph can have no
self-loops while every node still has an observer.

No public declarations are added.
-/

namespace AISafetyAtlas.Examples.SelfAwareness

open AISafetyAtlas.SelfAwareness

private abbrev Process := Finset Bool

private def left : Process := {false}
private def right : Process := {true}

/-- Reciprocal awareness between the two incomparable singleton processes. -/
private def mutualAwareness (observer target : Process) : Prop :=
  (observer = left ∧ target = right) ∨
    (observer = right ∧ target = left)

/-- A concrete bounded model with a genuine awareness cycle. -/
private def cyclicModel : Model Process where
  available := Set.univ
  available_finite := Set.toFinite _
  available_nonempty := Set.univ_nonempty
  aware := mutualAwareness
  cost := Finset.card
  minAwarenessCost := 1
  minAwarenessCost_pos := by decide
  awareness_cost := by
    rintro observer target (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      decide
  awareness_closed := by
    intro observer target _ _ _
    exact Set.mem_univ _

/-- The ordinary awareness graph contains `left → right`. -/
example : cyclicModel.aware left right :=
  Or.inl ⟨rfl, rfl⟩

/-- And it contains `right → left`: cycles are not prohibited. -/
example : cyclicModel.aware right left :=
  Or.inr ⟨rfl, rfl⟩

/-- Proposition 4.7 still excludes a self-loop at every composite. -/
example (p : Process) : ¬ cyclicModel.aware p p :=
  cyclicModel.process_not_self_aware p

/-- Every maximal available composite is excluded, not only one chosen witness. -/
example {target : Process} (hmax : Maximal (· ∈ cyclicModel.available) target) :
    ¬ AgentAware cyclicModel target :=
  cyclicModel.not_agentAware_of_maximal hmax

/-- The full hypotheses are jointly satisfiable and Theorem 4.8 applies. -/
example : ∃ target ∈ cyclicModel.available,
    ∀ observer ∈ cyclicModel.available,
      ¬ cyclicModel.aware observer target :=
  cyclicModel.limited_self_awareness

/-- In this witness the joint two-process composite is explicitly unobserved. -/
example : ∀ observer ∈ cyclicModel.available,
    ¬ cyclicModel.aware observer (left ⊔ right) := by
  intro observer _ haware
  rcases haware with ⟨hobserver, htarget⟩ | ⟨hobserver, htarget⟩
  · subst observer
    have hmem := congrArg (fun s : Process => false ∈ s) htarget
    simp [left, right] at hmem
  · subst observer
    have hmem := congrArg (fun s : Process => true ∈ s) htarget
    simp [left, right] at hmem

/-! ## Why Proposition 4.7 alone is insufficient -/

private def flatTwoCycle (observer target : Bool) : Prop :=
  observer ≠ target

/-- A two-cycle has no self-aware node. -/
example : ∀ p : Bool, ¬ flatTwoCycle p p := by
  simp [flatTwoCycle]

/-- Nevertheless every node in that flat graph has an observer. Composite
closure is what turns Proposition 4.7 into Theorem 4.8. -/
example : ∀ p : Bool, ∃ q : Bool, flatTwoCycle q p := by
  intro p
  cases p <;> simp [flatTwoCycle]

end AISafetyAtlas.Examples.SelfAwareness
