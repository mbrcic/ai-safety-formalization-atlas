import AISafetyAtlas.Sovereignty.TrulyPlayable

/-!
Goranko, Jamroga and Turrini (2013), Definition 9, manuscript p. 13. An
effectivity function is a crown exactly when every effective set of the grand coalition
contains an outcome whose singleton is effective for that coalition.
The cited definition is `IsCrown`.

The map transfers the empty and grand coalition families to a one-player
effectivity function by taking images under `Option.some`. This gives a nonempty outcome type
and preserves both membership in an effective set and effectiveness of a singleton.

Checked: `lake env lean docs/provenance/transfers/243-crown.lean`
-/

namespace Transfer243

open AISafetyAtlas.Sovereignty

def PrintStatement {P X : Type*} [Finite P] [Nonempty P] [Nonempty X]
    (E : Set P → Set (Set X)) : Prop :=
  ∀ A ∈ E Set.univ, ∃ x ∈ A, ({x} : Set X) ∈ E Set.univ

def LeanStatement {N X : Type*} (E : Set N → Set (Set X)) : Prop :=
  IsCrown E

def phi {N X : Type*} (E : Set N → Set (Set X)) : Set Unit → Set (Set (Option X)) :=
  fun D ↦ (Set.image Option.some) '' E ((fun _ : N ↦ ()) ⁻¹' D)

theorem defining_condition {N X : Type*} (E : Set N → Set (Set X)) :
    LeanStatement E ↔ PrintStatement (phi E) := by
  let F := E Set.univ
  change (∀ A ∈ F, ∃ x ∈ A, {x} ∈ F) ↔
    (∀ B ∈ (Set.image Option.some) '' E ((fun _ : N ↦ ()) ⁻¹' Set.univ),
      ∃ y ∈ B, {y} ∈ (Set.image Option.some) '' E ((fun _ : N ↦ ()) ⁻¹' Set.univ))
  rw [Set.preimage_univ]
  constructor
  · intro h _ hB
    obtain ⟨A, hA, rfl⟩ := hB
    obtain ⟨x, hx, hSingle⟩ := h A hA
    exact ⟨some x, ⟨x, hx, rfl⟩, ⟨{x}, hSingle, Set.image_singleton⟩⟩
  · intro h A hA
    obtain ⟨_, ⟨x, hx, rfl⟩, B, hB, hSingle⟩ :=
      h (Option.some '' A) ⟨A, hA, rfl⟩
    rw [← Set.image_singleton] at hSingle
    have hEq : B = {x} := (Option.some_injective X).image_injective hSingle
    exact ⟨x, hx, hEq ▸ hB⟩

theorem lean_of_print {N X : Type*} (E : Set N → Set (Set X)) :
    PrintStatement (phi E) → LeanStatement E :=
  (defining_condition E).mpr

theorem print_of_lean {P X : Type*} [Finite P] [Nonempty P] [Nonempty X]
    (E : Set P → Set (Set X)) :
    LeanStatement E → PrintStatement E :=
  id

end Transfer243
