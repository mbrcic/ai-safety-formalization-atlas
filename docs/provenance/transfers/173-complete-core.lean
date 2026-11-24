import AISafetyAtlas.Sovereignty.TrulyPlayable

/-!
Goranko, Jamroga and Turrini (2013), Definition 5, manuscript p. 5. The
nonmonotonic core of a coalition is complete exactly when every member of its
effectivity family contains a member of the core. The cited definition is `CompleteCore`.

The map uses one player and gives each coalition the images under `Option.some`
of the original coalition's effective sets. The embedding preserves and
reflects inclusion and strict inclusion, and supplies a nonempty outcome type.

Checked: `lake env lean docs/provenance/transfers/173-complete-core.lean`
-/

namespace Transfer173

open AISafetyAtlas.Sovereignty

def PrintStatement {P X : Type*} [Finite P] [Nonempty P] [Nonempty X]
    (E : Set P → Set (Set X)) (D : Set P) : Prop :=
  ∀ A ∈ E D, ∃ B ∈ nonmonotonicCore E D, B ⊆ A

def LeanStatement {N X : Type*} (E : Set N → Set (Set X)) (C : Set N) : Prop :=
  CompleteCore E C

def phi {N X : Type*} (E : Set N → Set (Set X)) (C : Set N) :
    Set Unit → Set (Set (Option X)) :=
  fun _ ↦ (Set.image Option.some) '' E C

private theorem mem_core_iff {N X : Type*} (E : Set N → Set (Set X)) (C : Set N)
    (B : Set X) :
    Option.some '' B ∈ nonmonotonicCore (phi E C) Set.univ ↔ B ∈ nonmonotonicCore E C := by
  have hImage := (Option.some_injective X).image_injective
  have hStrict {A B : Set X} : Option.some '' A ⊂ Option.some '' B ↔ A ⊂ B := by
    rw [ssubset_iff_subset_not_subset, ssubset_iff_subset_not_subset,
      Set.image_subset_image_iff (Option.some_injective X),
      Set.image_subset_image_iff (Option.some_injective X)]
  constructor
  · rintro ⟨⟨B', hB', hEq⟩, hMin⟩
    have hB : B' = B := hImage hEq
    subst B'
    refine ⟨hB', ?_⟩
    rintro ⟨A, hA, hAB⟩
    exact hMin ⟨Option.some '' A, ⟨A, hA, rfl⟩, hStrict.mpr hAB⟩
  · rintro ⟨hB, hMin⟩
    refine ⟨⟨B, hB, rfl⟩, ?_⟩
    rintro ⟨_, ⟨A, hA, rfl⟩, hAB⟩
    exact hMin ⟨A, hA, hStrict.mp hAB⟩

theorem defining_condition {N X : Type*} (E : Set N → Set (Set X)) (C : Set N) :
    LeanStatement E C ↔ PrintStatement (phi E C) Set.univ := by
  constructor
  · intro h _ hA
    obtain ⟨A, hA, rfl⟩ := hA
    obtain ⟨B, hB, hBA⟩ := h A hA
    exact ⟨Option.some '' B, (mem_core_iff E C B).mpr hB, Set.image_mono hBA⟩
  · intro h A hA
    obtain ⟨B', hB', hBA⟩ := h (Option.some '' A) ⟨A, hA, rfl⟩
    obtain ⟨B, _, rfl⟩ := hB'.1
    exact ⟨B, (mem_core_iff E C B).mp hB',
      (Set.image_subset_image_iff (Option.some_injective X)).mp hBA⟩

theorem lean_of_print {N X : Type*} (E : Set N → Set (Set X)) (C : Set N) :
    PrintStatement (phi E C) Set.univ → LeanStatement E C :=
  (defining_condition E C).mpr

theorem print_of_lean {P X : Type*} [Finite P] [Nonempty P] [Nonempty X]
    (E : Set P → Set (Set X)) (C : Set P) :
    LeanStatement E C → PrintStatement E C :=
  id

end Transfer173
