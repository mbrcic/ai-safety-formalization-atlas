import AISafetyAtlas.Sovereignty.TrulyPlayable

/-!
Goranko, Jamroga and Turrini (2013), Proposition 1(1), manuscript p. 5.
For a playable effectivity function, the empty coalition's family is a proper
filter in the sense of footnote 2. The cited declarations are
`Playable.emptyFilter`, `Playable.emptyFilter_neBot`, `Playable.mem_emptyFilter`,
`Playable.mem_empty_univ`, `Playable.empty_not_mem_empty`,
`Playable.inter_mem_empty` and `Playable.upward_mem_empty`.

The map pulls coalitions back along the constant map to one player. In particular,
the printed empty coalition pulls back to the Lean empty coalition.

Checked: `lake env lean docs/provenance/transfers/072-empty-coalition-filter.lean`
-/

namespace Transfer072

open AISafetyAtlas.Sovereignty

universe u v

def FilterClauses {X : Type v} (F : Set (Set X)) : Prop :=
  Set.univ ∈ F ∧ ∅ ∉ F ∧
    (∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F) ∧
    (∀ ⦃A B⦄, A ∈ F → A ⊆ B → B ∈ F)

def PrintStatement : Prop :=
  ∀ (P : Type u) [Finite P] [Nonempty P] (X : Type v) [Nonempty X]
    (E : Set P → Set (Set X)), Playable E → FilterClauses (E ∅)

def LeanConclusion {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (hE : Playable E) : Prop :=
  hE.emptyFilter.NeBot ∧
    (∀ A : Set X, A ∈ hE.emptyFilter ↔ A ∈ E ∅) ∧ FilterClauses (E ∅)

def LeanStatement : Prop :=
  ∀ (N : Type u) (X : Type v) (E : Set N → Set (Set X))
    (hE : Playable E), LeanConclusion hE

def phi {N : Type u} {X : Type v} (E : Set N → Set (Set X)) :
    Set (PUnit.{u + 1}) → Set (Set X) :=
  fun K => E ((fun _ : N => PUnit.unit) ⁻¹' K)

theorem H {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (hE : Playable E) : Nonempty X ∧ Playable (phi E) := by
  refine ⟨?_, ?_⟩
  · by_contra hX
    have hEmpty : (Set.univ : Set X) = ∅ := by
      ext x
      exact (hX ⟨x⟩).elim
    exact hE.live ∅ (hEmpty ▸ hE.safe ∅)
  · let f : N → PUnit.{u + 1} := fun _ => PUnit.unit
    change Playable (fun K => E (f ⁻¹' K))
    refine ⟨fun K => hE.live _, fun K => hE.safe _, ?_,
      fun K => hE.mono (f ⁻¹' K), ?_⟩
    · simpa only [Set.preimage_empty, Set.preimage_univ] using hE.maximal
    · intro K L A B hKL hA hB
      rw [Set.preimage_union]
      exact hE.superadd _ _ A B (hKL.preimage f) hA hB

theorem C {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (hE : Playable E) (hPrint : FilterClauses (phi E ∅)) : LeanConclusion hE := by
  have hClauses : FilterClauses (E ∅) := by
    simpa only [phi, Set.preimage_empty] using hPrint
  refine ⟨?_, fun _ => Iff.rfl, hClauses⟩
  apply Filter.neBot_iff.mpr
  intro hBot
  exact hClauses.2.1 (Filter.empty_mem_iff_bot.mpr hBot)

theorem lean_of_print : PrintStatement.{u, v} → LeanStatement.{u, v} := by
  intro hPrint N X E hE
  obtain ⟨hX, hPlayable⟩ := H hE
  let : Nonempty X := hX
  exact C hE (hPrint PUnit X (phi E) hPlayable)

theorem print_of_lean : LeanStatement.{u, v} → PrintStatement.{u, v} := by
  intro hLean P _ _ X _ E hE
  exact (hLean P X E hE).2.2

end Transfer072
