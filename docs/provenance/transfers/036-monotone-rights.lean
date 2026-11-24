import AISafetyAtlas.Sovereignty.Rights

/-!
Peleg (1998), p. 72, (3.4). A society's access correspondence is monotone
with respect to rights if every enlargement of a rights set enlarges the
corresponding access family. The cited definition is
`AISafetyAtlas.Sovereignty.Constitution.MonotoneRights`.

The map uses one member and two rights. At the singleton and full rights sets,
each test of an original inclusion is represented by a distinct singleton
outcome set. The whole space is always admitted and contains an extra point.

Checked: `lake env lean docs/provenance/transfers/036-monotone-rights.lean`
-/

namespace Transfer036

open AISafetyAtlas.Sovereignty Classical

def PrintStatement {N X R : Type*} [Finite N] [Finite R]
    (κ : Constitution N X R) (_standing : κ.Standing) : Prop :=
  ∀ (S : Set N) (θ θ' : Set R), θ ⊆ θ' → κ.access S θ ⊆ κ.access S θ'

def LeanStatement {N X R : Type*} (κ : Constitution N X R) : Prop :=
  κ.MonotoneRights

structure Test (N X R : Type*) where
  coalition : Set N
  before : Set R
  after : Set R
  subset : before ⊆ after
  outcome : Set X

noncomputable def phi {N X R : Type*} (κ : Constitution N X R) :
    Constitution Unit (Option (Test N X R)) Bool where
  assign := fun _ ↦ ∅
  access := fun S θ ↦ {B | B = Set.univ ∨
    (() ∈ S ∧ false ∈ θ ∧ ∃ t : Test N X R, B = {some t} ∧
      t.outcome ∈ κ.access t.coalition (if true ∈ θ then t.after else t.before))}

theorem H {N X R : Type*} (κ : Constitution N X R) : (phi κ).Standing := by
  constructor
  · rfl
  · intro θ
    ext B
    simp [phi]
  · intro S
    ext B
    simp [phi]

theorem defining_condition {N X R : Type*} (κ : Constitution N X R) :
    LeanStatement κ ↔ PrintStatement (phi κ) (H κ) := by
  constructor
  · intro h S θ θ' hsub B hB
    rcases hB with hB | ⟨hS, hfalse, t, rfl, ht⟩
    · exact Or.inl hB
    · refine Or.inr ⟨hS, hsub hfalse, t, rfl, ?_⟩
      by_cases htrue : true ∈ θ
      · simpa only [if_pos htrue, if_pos (hsub htrue)] using ht
      · by_cases htrue' : true ∈ θ'
        · simp only [if_neg htrue] at ht
          simpa only [if_pos htrue'] using h t.coalition t.before t.after t.subset ht
        · simpa only [if_neg htrue, if_neg htrue'] using ht
  · intro h S θ θ' hsub Y hY
    let t : Test N X R := ⟨S, θ, θ', hsub, Y⟩
    have hB : ({some t} : Set (Option (Test N X R))) ∈
        (phi κ).access Set.univ {false} :=
      Or.inr ⟨Set.mem_univ (), by simp, t, rfl, by simpa [t] using hY⟩
    have hResult := h Set.univ {false} Set.univ (Set.subset_univ _) hB
    rcases hResult with hAll | ⟨_, _, t', hs, ht'⟩
    · have hn : (none : Option (Test N X R)) ∈ Set.univ := Set.mem_univ _
      rw [← hAll] at hn
      simp at hn
    · have ht : t = t' := by simpa using hs
      subst t'
      simpa [t] using ht'

theorem lean_of_print {N X R : Type*} (κ : Constitution N X R) :
    PrintStatement (phi κ) (H κ) → LeanStatement κ :=
  (defining_condition κ).mpr

theorem print_of_lean {N X R : Type*} [Finite N] [Finite R]
    (κ : Constitution N X R) (h : κ.Standing) : LeanStatement κ → PrintStatement κ h :=
  fun hκ ↦ hκ

end Transfer036
