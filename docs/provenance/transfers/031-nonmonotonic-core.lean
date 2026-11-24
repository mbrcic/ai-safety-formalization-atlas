import AISafetyAtlas.Sovereignty.TrulyPlayable

/-!
Goranko, Jamroga and Turrini (2013), Definition 4, manuscript p. 5.
The nonmonotonic core of a coalition consists of the inclusion-minimal members
of its effectivity family. The cited declaration is `nonmonotonicCore`.

The map uses one player and makes the family constant at the selected coalition's
family. Taking images under `Option.some` preserves strict inclusion and gives
a nonempty printed outcome type even when the Lean outcome type is empty.

Checked: `lake env lean docs/provenance/transfers/031-nonmonotonic-core.lean`
-/

namespace Transfer031

open AISafetyAtlas.Sovereignty

def PrintStatement {P X : Type*} [Finite P] [Nonempty P] [Nonempty X]
    (E : Set P → Set (Set X)) (C : Set P) (A : Set X) : Prop :=
  A ∈ E C ∧ ¬ ∃ B ∈ E C, B ⊂ A

def LeanStatement {N X : Type*}
    (E : Set N → Set (Set X)) (C : Set N) (A : Set X) : Prop :=
  A ∈ nonmonotonicCore E C

def phi {N X : Type*} (E : Set N → Set (Set X)) (C : Set N) :
    Set Unit → Set (Set (Option X)) :=
  fun _ => (Set.image Option.some) '' E C

private theorem image_ssubset_iff {X : Type*} {A B : Set X} :
    Option.some '' B ⊂ Option.some '' A ↔ B ⊂ A := by
  rw [ssubset_iff_subset_not_subset, ssubset_iff_subset_not_subset,
    Set.image_subset_image_iff (Option.some_injective X),
    Set.image_subset_image_iff (Option.some_injective X)]

theorem defining_condition {N X : Type*}
    (E : Set N → Set (Set X)) (C : Set N) (A : Set X) :
    LeanStatement E C A ↔ PrintStatement (phi E C) Set.univ (Option.some '' A) := by
  change (A ∈ E C ∧ ¬ ∃ B ∈ E C, B ⊂ A) ↔
    (Option.some '' A ∈ (Set.image Option.some) '' E C ∧
      ¬ ∃ B' ∈ (Set.image Option.some) '' E C, B' ⊂ Option.some '' A)
  constructor
  · rintro ⟨hA, hmin⟩
    refine ⟨⟨A, hA, rfl⟩, ?_⟩
    rintro ⟨_, ⟨B, hB, rfl⟩, hBA⟩
    exact hmin ⟨B, hB, image_ssubset_iff.mp hBA⟩
  · rintro ⟨⟨B, hB, hBA⟩, hmin⟩
    have hEq : B = A := Set.image_injective.mpr (Option.some_injective X) hBA
    subst B
    refine ⟨hB, ?_⟩
    rintro ⟨B, hB, hBA⟩
    exact hmin ⟨Option.some '' B, ⟨B, hB, rfl⟩, image_ssubset_iff.mpr hBA⟩

theorem lean_of_print {N X : Type*}
    (E : Set N → Set (Set X)) (C : Set N) (A : Set X) :
    PrintStatement (phi E C) Set.univ (Option.some '' A) → LeanStatement E C A :=
  (defining_condition E C A).mpr

theorem print_of_lean {P X : Type*} [Finite P] [Nonempty P] [Nonempty X]
    (E : Set P → Set (Set X)) (C : Set P) (A : Set X) :
    LeanStatement E C A → PrintStatement E C A :=
  fun h => h

end Transfer031
