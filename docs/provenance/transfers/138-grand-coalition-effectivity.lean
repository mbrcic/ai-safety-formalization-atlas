import AISafetyAtlas.Sovereignty.Representation

/-!
Peleg (1998), §3, effectivity-function condition (ii), p. 72. The grand
coalition is effective for exactly the nonempty subsets of the social states.
The cited definition clause is `IsEffectivityFunction.univ`.

The map keeps the outcome type and gives every coalition of a one-member
society the original grand coalition's effectivity family.

Checked: `lake env lean docs/provenance/transfers/138-grand-coalition-effectivity.lean`
-/

namespace Transfer138

def PrintStatement {n : ℕ} {X : Type*} (E : Set (Fin n) → Set (Set X)) : Prop :=
  E Set.univ = Set.univ \ {∅}

def LeanStatement {N X : Type*} (E : Set N → Set (Set X)) : Prop :=
  E Set.univ = {A : Set X | A.Nonempty}

def phi {N X : Type*} (E : Set N → Set (Set X)) : Set (Fin 1) → Set (Set X) :=
  fun _ ↦ E Set.univ

private theorem nonempty_sets {X : Type*} :
    {A : Set X | A.Nonempty} = Set.univ \ {∅} := by
  ext A
  simp [Set.nonempty_iff_ne_empty]

theorem defining_condition {N X : Type*} (E : Set N → Set (Set X)) :
    LeanStatement E ↔ PrintStatement (phi E) := by
  unfold LeanStatement PrintStatement phi
  rw [nonempty_sets]

theorem lean_of_print {N X : Type*} (E : Set N → Set (Set X)) :
    PrintStatement (phi E) → LeanStatement E :=
  (defining_condition E).mpr

theorem print_of_lean {n : ℕ} {X : Type*} (E : Set (Fin n) → Set (Set X)) :
    LeanStatement E → PrintStatement E := by
  unfold LeanStatement PrintStatement
  rw [nonempty_sets]
  exact id

end Transfer138
