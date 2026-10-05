module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Basic

/-!
# Refinement of finite sets over a preorder

Given a preorder on `α`, one finite set **refines** another when every element
of the second is matched by an element of the first that sits at or below it:

`A ⊑ B  ⟺  ∀ b ∈ B, ∃ a ∈ A, a ≤ b`

This is the upper (Smyth) preorder on finite sets. Two facts about it do the
work, and they are the reason it is worth naming: a superset refines a subset
(`refines_of_subset`), and a set of lower elements refines a set of higher ones
(`refines_singleton` in the one-element case). So a single relation carries both
"drop an element" and "move up the order", which are otherwise stated as two
separate closure moves.

The degenerate case is the sharpest. Where the order relates nothing but an
element to itself, refinement is exactly reverse inclusion
(`refines_iff_subset_of_discrete`) — so a discretely ordered carrier is not a
different mechanism, it is this one with the order switched off.

Domain-neutral and written to be lifted upstream. Mathlib carries the
corresponding upper-set and lower-set constructions and `Finset.sups`, but not
this relation on `Finset` at the pinned revision. No module in this repository
consumes it yet; `AISafetyAtlas.Examples.Order.FinsetRefinement` is its worked
model.
-/

namespace AISafetyAtlas.Order

variable {α : Type*} [Preorder α]

/--
**`A` refines `B`.** Every element of `B` is matched by an element of `A` at or
below it.

The upper (Smyth) preorder: `A` is the lower, more specific, more demanding
side.
-/
@[expose] public def Refines (A B : Finset α) : Prop :=
  ∀ b ∈ B, ∃ a ∈ A, a ≤ b

/-- Refinement is reflexive. -/
public theorem Refines.refl (A : Finset α) : Refines A A :=
  fun a ha => ⟨a, ha, le_refl a⟩

/-- Refinement is transitive. -/
public theorem Refines.trans {A B C : Finset α}
    (h : Refines A B) (h' : Refines B C) : Refines A C := by
  intro c hc
  obtain ⟨b, hb, hle'⟩ := h' c hc
  obtain ⟨a, ha, hle⟩ := h b hb
  exact ⟨a, ha, hle.trans hle'⟩

/-- A superset refines a subset: dropping elements is a refinement move. -/
public theorem refines_of_subset {A B : Finset α} (h : B ⊆ A) : Refines A B :=
  fun b hb => ⟨b, h hb, le_refl b⟩

/-- Moving down the order is a refinement move, in the one-element case. -/
public theorem refines_singleton {a b : α} (h : a ≤ b) :
    Refines ({a} : Finset α) {b} :=
  fun _ hx => ⟨a, Finset.mem_singleton_self a, (Finset.mem_singleton.mp hx) ▸ h⟩

/-- Refining a one-element set is exactly having a witness at or below it. This
is the form that is decidable when `≤` is, so it is what a computation filters
on. -/
public theorem refines_singleton_iff {A : Finset α} {b : α} :
    Refines A {b} ↔ ∃ a ∈ A, a ≤ b := by
  constructor
  · intro h
    exact h b (Finset.mem_singleton_self b)
  · rintro ⟨a, ha, hle⟩ x hx
    exact ⟨a, ha, (Finset.mem_singleton.mp hx) ▸ hle⟩

/-- The defining condition is the relation, stated for readers who want it
pointwise. -/
public theorem refines_of_forall {A B : Finset α}
    (h : ∀ b ∈ B, ∃ a ∈ A, a ≤ b) : Refines A B :=
  h

/-- Everything refines the empty set. -/
public theorem refines_empty (A : Finset α) : Refines A (∅ : Finset α) :=
  fun _ hb => absurd hb (Finset.notMem_empty _)

/-- Nothing but the empty set refines from the empty set. -/
public theorem refines_empty_iff {B : Finset α} :
    Refines (∅ : Finset α) B ↔ B = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨a, ha, _⟩ := h b hb
    exact absurd ha (Finset.notMem_empty a)
  · rintro rfl
    exact refines_empty ∅

/--
**On a discrete order, refinement is reverse inclusion.** Where `≤` relates an
element only to itself, `Refines A B` holds exactly when `B ⊆ A`.

This is why a discretely ordered carrier needs no separate treatment: it is this
relation with the order contributing nothing, and the only refinement move left
is dropping an element.
-/
public theorem refines_iff_subset_of_discrete (hdisc : ∀ a b : α, a ≤ b → a = b)
    (A B : Finset α) : Refines A B ↔ B ⊆ A := by
  constructor
  · intro h b hb
    obtain ⟨a, ha, hle⟩ := h b hb
    exact (hdisc a b hle) ▸ ha
  · exact refines_of_subset

end AISafetyAtlas.Order
