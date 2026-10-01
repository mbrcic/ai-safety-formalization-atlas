module

public import AISafetyAtlas.Sovereignty.Representation

/-!
# A society whose rights are held by one member

Two members, two social states, one right. Member `true` holds the right; member
`false` holds none. Holding the right means being able to force any non-empty
set of states; holding none means being able to force only the whole space.

Every hypothesis of Peleg's Theorem 3.5 is discharged here, so
`AISafetyAtlas.Sovereignty.Constitution.exists_represents` is not conditional on
an empty antecedent. The constitution is written down directly rather than read
off a game form -- `Constitution.ofGameForm` would make the representation
question trivial, which is exactly what `represents_ofGameForm` says.

The access correspondence is written as one formula over all `θ` rather than by
cases, so no decidability of set membership is needed anywhere.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- **The society.** `true` is the member holding the right. -/
@[expose] public def dictatorConstitution : Constitution Bool Bool Unit where
  assign := fun C => {_r : Unit | (true : Bool) ∈ C}
  access := fun _ θ => {B : Set Bool | (θ.Nonempty → B.Nonempty) ∧ (θ = ∅ → B = Set.univ)}

/-- A coalition is assigned the right exactly when it contains the member who
holds it. -/
public theorem dictator_assign_nonempty {C : Set Bool} :
    (dictatorConstitution.assign C).Nonempty ↔ (true : Bool) ∈ C := by
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨(), h⟩

/-- And is assigned nothing exactly when it does not. -/
public theorem dictator_assign_eq_empty {C : Set Bool} :
    dictatorConstitution.assign C = ∅ ↔ (true : Bool) ∉ C := by
  rw [← Set.not_nonempty_iff_eq_empty, dictator_assign_nonempty]

/-- **(3.1) read off.** A coalition containing the right-holder is effective for
every non-empty set; one without it is effective for the whole space alone. -/
public theorem dictator_mem_induced {C : Set Bool} {B : Set Bool} :
    B ∈ dictatorConstitution.induced C ↔
      ((true : Bool) ∈ C → B.Nonempty) ∧ ((true : Bool) ∉ C → B = Set.univ) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun hC => h₁ (dictator_assign_nonempty.mpr hC),
      fun hC => h₂ (dictator_assign_eq_empty.mpr hC)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun hθ => h₁ (dictator_assign_nonempty.mp hθ),
      fun hθ => h₂ (dictator_assign_eq_empty.mp hθ)⟩

/-- Print's EF condition (i), on this society. -/
public theorem dictator_induced_empty :
    dictatorConstitution.induced (∅ : Set Bool) = ({Set.univ} : Set (Set Bool)) := by
  ext B
  rw [dictator_mem_induced, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, h⟩; exact h (by simp)
  · rintro rfl; exact ⟨fun h => absurd h (by simp), fun _ => rfl⟩

/-- Print's EF condition (ii) -- citizen's sovereignty -- on this society. -/
public theorem dictator_induced_univ :
    dictatorConstitution.induced (Set.univ : Set Bool) = {B : Set Bool | B.Nonempty} := by
  ext B
  rw [dictator_mem_induced]
  constructor
  · rintro ⟨h, -⟩; exact h (Set.mem_univ _)
  · intro h; exact ⟨fun _ => h, fun hC => absurd (Set.mem_univ _) hC⟩

/-- **All four of print's page-72 conditions**, discharged. -/
public theorem dictator_isEF : IsEffectivityFunction dictatorConstitution.induced where
  empty := dictator_induced_empty
  univ := dictator_induced_univ
  live := by
    intro C hC
    rw [dictator_mem_induced] at hC
    by_cases h : (true : Bool) ∈ C
    · exact (hC.1 h).ne_empty rfl
    · have : (∅ : Set Bool) = Set.univ := hC.2 h
      exact absurd (this ▸ Set.mem_univ true) (by simp)
  safe := by
    intro C
    rw [dictator_mem_induced]
    exact ⟨fun _ => ⟨true, Set.mem_univ _⟩, fun _ => rfl⟩

/-- **Print's condition (i)**, and at every set of rights rather than only on the
diagonal: both families the access correspondence ever takes are closed upwards. -/
public theorem dictator_monotoneAlternatives : dictatorConstitution.MonotoneAlternatives := by
  rintro S θ B B' ⟨h₁, h₂⟩ hBB'
  refine ⟨fun hθ => (h₁ hθ).mono hBB', fun hθ => ?_⟩
  rw [← Set.univ_subset_iff, ← h₂ hθ]
  exact hBB'

/-- **Print's condition (ii).** Disjoint coalitions cannot both contain the
right-holder, so one of the two sets is the whole space and the intersection is
the other. -/
public theorem dictator_superadditive : Superadditive dictatorConstitution.induced := by
  intro S₁ S₂ B₁ B₂ hd h₁ h₂
  rw [dictator_mem_induced] at h₁ h₂ ⊢
  by_cases hs₁ : (true : Bool) ∈ S₁
  · have hs₂ : (true : Bool) ∉ S₂ := fun h => Set.disjoint_left.mp hd hs₁ h
    rw [h₂.2 hs₂, Set.inter_univ]
    exact ⟨fun _ => h₁.1 hs₁, fun h => absurd (Or.inl hs₁ : _ ∈ S₁ ∪ S₂) h⟩
  · rw [h₁.2 hs₁, Set.univ_inter]
    by_cases hs₂ : (true : Bool) ∈ S₂
    · exact ⟨fun _ => h₂.1 hs₂, fun h => absurd (Or.inr hs₂ : _ ∈ S₁ ∪ S₂) h⟩
    · refine ⟨fun h => ?_, fun _ => h₂.2 hs₂⟩
      rcases h with h | h
      · exact absurd h hs₁
      · exact absurd h hs₂

/-- **The society has a social state.** Print's conditions (iii) and (iv) say the
whole space is effective everywhere and the empty set is effective nowhere, so
the two differ -- which is where `A ≠ ∅` comes from, rather than from an
assumption. -/
public theorem dictator_nonempty_outcomes : (Set.univ : Set Bool).Nonempty :=
  dictator_isEF.nonempty_outcomes

/-- **And it does not satisfy print's standing assumptions**, which is one of the
two axes on which the sufficiency theorem is wider than print. Page 69 requires
`γ(∅, θ) = {A}` at every set of rights; here the empty coalition's access at a
non-empty set of rights is every non-empty set, because `access` reads the rights
and not the coalition. The induced effectivity function still has print's
`E(∅) = {A}`, because the empty coalition is assigned nothing -- and
`IsEffectivityFunction` asks for that and no more. -/
public theorem dictator_not_standing : ¬ dictatorConstitution.Standing := by
  intro h
  have hEq := h.access_empty_coalition (Set.univ : Set Unit)
  have hmem : ({true} : Set Bool) ∈ dictatorConstitution.access ∅ (Set.univ : Set Unit) :=
    ⟨fun _ => ⟨true, rfl⟩, fun hθ => absurd (hθ ▸ Set.mem_univ ()) (by simp)⟩
  rw [hEq, Set.mem_singleton_iff] at hmem
  exact absurd (hmem ▸ Set.mem_univ false) (by simp)

/-! ## What the theorem gives -/

/-- **The five playability conditions**, derived from print's four plus his two.
-/
public theorem dictator_playable : Playable dictatorConstitution.induced :=
  dictator_isEF.playable dictator_superadditive
    (Constitution.upwardClosed_induced dictator_monotoneAlternatives)

/-- **The constructed game form reaches every social state.** -/
public theorem dictator_surjective :
    Function.Surjective (paulyGame dictator_playable).outcome :=
  dictator_playable.surjective_paulyGame_outcome

/-- **The equality at every coalition**, including the two ends Pauly's converse
cannot reach. -/
public theorem dictator_effectivity_paulyGame :
    effectivity (paulyGame dictator_playable) = dictatorConstitution.induced :=
  dictator_isEF.effectivity_paulyGame dictator_superadditive
    (Constitution.upwardClosed_induced dictator_monotoneAlternatives)

/-- **A bare effectivity function is some game form's**, once print's ends are
pinned. -/
public theorem dictator_exists_gameForm :
    ∃ G : GameForm.{0, 0, 0} Bool Bool, effectivity G = dictatorConstitution.induced :=
  exists_gameForm_of_isEffectivityFunction dictator_isEF dictator_superadditive
    (Constitution.upwardClosed_induced dictator_monotoneAlternatives)

/-- **Peleg's Theorem 3.5, sufficiency, on an actual society.** -/
public theorem dictator_exists_represents :
    ∃ G : GameForm.{0, 0, 0} Bool Bool, Represents G dictatorConstitution :=
  Constitution.exists_represents dictator_isEF dictator_monotoneAlternatives
    dictator_superadditive

/-- **And the biconditional**, with print's condition (i) standing. -/
public theorem dictator_exists_represents_iff :
    (∃ G : GameForm.{0, 0, 0} Bool Bool, Represents G dictatorConstitution) ↔
      Superadditive dictatorConstitution.induced :=
  Constitution.exists_represents_iff_superadditive dictator_isEF dictator_monotoneAlternatives

end AISafetyAtlas.Examples.Sovereignty
