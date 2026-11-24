import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
Chen, Ju and Ågotnes (2026), Definition 12, item 4, p. 12. On a finite-agent
alpha neighborhood frame, the alpha powers of a coalition at a state are
included in those of any larger coalition at that state.
The cited defining declarations are `AlphaNeighborhoodFrame` and
`AlphaNeighborhoodFrame.CoalitionMonotone`. Specializing the transferred
condition to an induced frame gives the conclusions of
`IsGCGF.alphaFrame_coalitionMonotone` and `IsGCGF.alphaPower_mono_coalition`.
The cited grand-coalition extension lemma and the `endFrame` instance supply
supporting facts about action frames.

The map uses one agent and a tagged state for every original coalition
inclusion at every original state. The two coalitions use the two neighborhoods
at that tag, with outcome sets pulled back along the copy of the original states.

Checked: `lake env lean docs/provenance/transfers/041-coalition-monotonicity.lean`
-/

namespace Transfer041

open AISafetyAtlas.Sovereignty Classical

def PrintStatement {AG ST : Type*} [Finite AG] [Nonempty AG] [Nonempty ST]
    (F : AlphaNeighborhoodFrame AG ST) : Prop :=
  ∀ (s : ST) (C D : Set AG), C ⊆ D → F.nbhd C s ⊆ F.nbhd D s

def LeanStatement {AG ST : Type*} (F : AlphaNeighborhoodFrame AG ST) : Prop :=
  F.CoalitionMonotone

structure Test (AG ST : Type*) where
  state : ST
  smaller : Set AG
  larger : Set AG
  subset : smaller ⊆ larger

abbrev PrintState (AG ST : Type*) := ST ⊕ Option (Test AG ST)

instance {AG ST : Type*} : Nonempty (PrintState AG ST) := ⟨Sum.inr none⟩

noncomputable def phi {AG ST : Type*} (F : AlphaNeighborhoodFrame AG ST) :
    AlphaNeighborhoodFrame Unit (PrintState AG ST) where
  nbhd C s := match s with
    | Sum.inr (some t) =>
        {X | Sum.inl ⁻¹' X ∈ F.nbhd (if () ∈ C then t.larger else t.smaller) t.state}
    | _ => ∅
  upward := by
    intro C s X Y hX hXY
    rcases s with s | (_ | t)
    · exact hX
    · exact hX
    · exact F.upward _ t.state _ _ hX (Set.preimage_mono hXY)

theorem defining_condition {AG ST : Type*} (F : AlphaNeighborhoodFrame AG ST) :
    LeanStatement F ↔ PrintStatement (phi F) := by
  constructor
  · intro h s C D hCD X hX
    rcases s with s | (_ | t)
    · exact hX
    · exact hX
    · change Sum.inl ⁻¹' X ∈ F.nbhd (if () ∈ C then t.larger else t.smaller) t.state at hX
      change Sum.inl ⁻¹' X ∈ F.nbhd (if () ∈ D then t.larger else t.smaller) t.state
      by_cases hC : () ∈ C
      · simpa only [if_pos hC, if_pos (hCD hC)] using hX
      · by_cases hD : () ∈ D
        · simp only [if_neg hC] at hX
          simpa only [if_pos hD] using h t.state t.smaller t.larger t.subset hX
        · simpa only [if_neg hC, if_neg hD] using hX
  · intro h s C D hCD X hX
    let t : Test AG ST := ⟨s, C, D, hCD⟩
    let Y : Set (PrintState AG ST) := Sum.inl '' X
    have hY : Sum.inl ⁻¹' Y = X := Set.preimage_image_eq _ Sum.inl_injective
    have hLeft : Y ∈ (phi F).nbhd ∅ (Sum.inr (some t)) := by
      simpa [phi, hY, t] using hX
    have hRight := h (Sum.inr (some t)) ∅ Set.univ (Set.empty_subset _) hLeft
    simpa [phi, hY, t] using hRight

theorem lean_of_print {AG ST : Type*} (F : AlphaNeighborhoodFrame AG ST) :
    PrintStatement (phi F) → LeanStatement F :=
  (defining_condition F).mpr

theorem print_of_lean {AG ST : Type*} [Finite AG] [Nonempty AG] [Nonempty ST]
    (F : AlphaNeighborhoodFrame AG ST) : LeanStatement F → PrintStatement F :=
  fun h ↦ h

end Transfer041
