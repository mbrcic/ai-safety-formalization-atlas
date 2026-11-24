import AISafetyAtlas.Sovereignty.Representation

/-!
Peleg (1998), §3, effectivity-function condition (iv), p. 72. The whole
outcome set belongs to the effectivity family of every coalition.
The cited definition clause is `IsEffectivityFunction.safe`. The cited
`forces_univ` supplies the clause for game forms with nonempty strategies.

The map uses one player and the outcome type `Option X`. At every printed
coalition it puts a set in the effectivity family exactly when its preimage
under `some` belongs to the Lean family at every Lean coalition.

Checked: `lake env lean docs/provenance/transfers/112-effectivity-safety.lean`
-/

namespace Transfer112

def PrintStatement {n : ℕ} {X : Type*} (E : Set (Fin n) → Set (Set X)) : Prop :=
  ∀ D : Set (Fin n), Set.univ ∈ E D

def LeanStatement {N X : Type*} (E : Set N → Set (Set X)) : Prop :=
  ∀ C : Set N, Set.univ ∈ E C

def phi {N X : Type*} (E : Set N → Set (Set X)) :
    Set (Fin 1) → Set (Set (Option X)) :=
  fun _ => {B | ∀ C : Set N, Option.some ⁻¹' B ∈ E C}

theorem defining_condition {N X : Type*} (E : Set N → Set (Set X)) :
    LeanStatement E ↔ PrintStatement (phi E) := by
  change (∀ C : Set N, Set.univ ∈ E C) ↔
    (∀ _ : Set (Fin 1), ∀ C : Set N, Option.some ⁻¹' Set.univ ∈ E C)
  rw [Set.preimage_univ]
  exact ⟨fun h _ => h, fun h => h ∅⟩

theorem lean_of_print {N X : Type*} (E : Set N → Set (Set X)) :
    PrintStatement (phi E) → LeanStatement E :=
  (defining_condition E).mpr

theorem print_of_lean {n : ℕ} {X : Type*} (E : Set (Fin n) → Set (Set X)) :
    LeanStatement E → PrintStatement E :=
  fun h => h

end Transfer112
