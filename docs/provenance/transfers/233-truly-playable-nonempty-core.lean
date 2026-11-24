import AISafetyAtlas.Sovereignty.TrulyPlayable

/-!
Goranko, Jamroga and Turrini (2013), Proposition 5 (1) ↔ (2), manuscript p. 13.
For a playable effectivity function, true playability is equivalent to
nonemptiness of the empty coalition's nonmonotonic core. The cited theorem is
`Playable.trulyPlayable_iff_nonmonotonicCore_empty_nonempty`.

The map keeps the outcome space and uses one player. Each printed coalition
gets the original family at its preimage under the constant map to that player.
Thus the empty and grand coalitions retain their original effectivity families.
Liveness and safety ensure the outcome type is nonempty.

Checked: `lake env lean docs/provenance/transfers/233-truly-playable-nonempty-core.lean`
-/

namespace Transfer233

open AISafetyAtlas.Sovereignty

universe u v

def PrintStatement : Prop :=
  ∀ (P : Type u) [Finite P] [Nonempty P] (X : Type v) [Nonempty X]
    (E : Set P → Set (Set X)),
    Playable E → (TrulyPlayable E ↔ (nonmonotonicCore E ∅).Nonempty)

def LeanStatement : Prop :=
  ∀ (N : Type u) (X : Type v) (E : Set N → Set (Set X)),
    Playable E → (TrulyPlayable E ↔ (nonmonotonicCore E ∅).Nonempty)

def phi {N : Type u} {X : Type v} (E : Set N → Set (Set X)) :
    Set (ULift.{u} Unit) → Set (Set X) :=
  fun D ↦ E ((fun _ : N ↦ (⟨()⟩ : ULift.{u} Unit)) ⁻¹' D)

theorem H {N : Type u} {X : Type v} {E : Set N → Set (Set X)} (hE : Playable E) :
    Nonempty X ∧ Playable (phi E) := by
  have hUniv : (Set.univ : Set X) ≠ ∅ := by
    intro h
    exact hE.live ∅ (h ▸ hE.safe ∅)
  refine ⟨(Set.nonempty_iff_ne_empty.mpr hUniv).to_type, ?_⟩
  refine ⟨fun _ ↦ hE.live _, fun _ ↦ hE.safe _, ?_, ?_, ?_⟩
  · simpa only [phi, Set.preimage_empty, Set.preimage_univ] using hE.maximal
  · intro _ A B hAB hA
    exact hE.mono _ A B hAB hA
  · intro D K A B hDK hA hB
    simpa only [phi, Set.preimage_union] using hE.superadd _ _ A B (hDK.preimage _) hA hB

theorem C {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (hE : Playable E) (hPhi : Playable (phi E))
    (hPrint : TrulyPlayable (phi E) ↔ (nonmonotonicCore (phi E) ∅).Nonempty) :
    TrulyPlayable E ↔ (nonmonotonicCore E ∅).Nonempty := by
  simp only [TrulyPlayable, hPhi, true_and, CompleteCore, nonmonotonicCore, phi,
    Set.preimage_empty] at hPrint
  simpa only [TrulyPlayable, hE, true_and, CompleteCore, nonmonotonicCore] using hPrint

theorem lean_of_print : PrintStatement.{u, v} → LeanStatement.{u, v} := by
  intro hPrint N X E hE
  obtain ⟨hX, hPhi⟩ := H hE
  let := hX
  exact C hE hPhi (hPrint (ULift.{u} Unit) X (phi E) hPhi)

theorem print_of_lean : LeanStatement.{u, v} → PrintStatement.{u, v} := by
  intro hLean P _ _ X _ E hE
  exact hLean P X E hE

end Transfer233
