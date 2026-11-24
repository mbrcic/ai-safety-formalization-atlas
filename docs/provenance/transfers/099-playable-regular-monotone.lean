import AISafetyAtlas.Sovereignty.PlayableConverse
import AISafetyAtlas.Sovereignty.Rights

/-!
Pauly (2002), Lemma 3.1, p. 152. Every playable effectivity function is regular
and coalition-monotonic. The cited declarations are `Playable.regular` and
`Playable.mono_coalition`.

The map sends each player to its pair of membership bits for the two tested
coalitions and pulls the effectivity function back along this map. The first
bit recovers the coalition for the regularity test. The two bits together and
the second bit recover the nested coalitions for the monotonicity test.

Checked: `lake env lean docs/provenance/transfers/099-playable-regular-monotone.lean`
-/

namespace Transfer099

open AISafetyAtlas.Sovereignty

universe u v

def PrintStatement : Prop :=
  ∀ (P : Type u) [Finite P] [Nonempty P] (X : Type v) [Nonempty X]
    (E : Set P → Set (Set X)), Playable E → EFRegular E ∧ CoalitionMonotone E

def LeanStatement : Prop :=
  ∀ (N : Type u) (X : Type v) (E : Set N → Set (Set X)),
    Playable E → EFRegular E ∧ CoalitionMonotone E

noncomputable def player {N : Type u} (S T : Set N) : N → ULift.{u} (Bool × Bool) := by
  classical
  exact fun i => ⟨decide (i ∈ S), decide (i ∈ T)⟩

noncomputable def phi {N : Type u} {X : Type v}
    (E : Set N → Set (Set X)) (S T : Set N) :
    Set (ULift.{u} (Bool × Bool)) → Set (Set X) :=
  fun K => E (player S T ⁻¹' K)

theorem H {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (hE : Playable E) (S T : Set N) : Nonempty X ∧ Playable (phi E S T) := by
  refine ⟨?_, ?_⟩
  · by_contra hX
    have hEmpty : (Set.univ : Set X) = ∅ := by
      ext x
      exact (hX ⟨x⟩).elim
    exact hE.live ∅ (hEmpty ▸ hE.safe ∅)
  · let f := player S T
    change Playable (fun K => E (f ⁻¹' K))
    refine ⟨fun K => hE.live _, fun K => hE.safe _, ?_,
      fun K => hE.mono (f ⁻¹' K), ?_⟩
    · simpa only [Set.preimage_empty, Set.preimage_univ] using hE.maximal
    · intro K L A B hKL hA hB
      rw [Set.preimage_union]
      exact hE.superadd _ _ A B (hKL.preimage f) hA hB

theorem C {N : Type u} {X : Type v} (E : Set N → Set (Set X)) (S T : Set N)
    (hPrint : EFRegular (phi E S T) ∧ CoalitionMonotone (phi E S T)) :
    CRegular S E ∧ (S ⊆ T → E S ⊆ E T) := by
  classical
  let first : Set (ULift.{u} (Bool × Bool)) := {p | p.down.1 = true}
  let second : Set (ULift.{u} (Bool × Bool)) := {p | p.down.2 = true}
  have hFirst : player S T ⁻¹' first = S := by
    ext i
    simp [first, player]
  have hSecond : player S T ⁻¹' second = T := by
    ext i
    simp [second, player]
  constructor
  · have h := hPrint.1 first
    simpa only [CRegular, phi, Set.preimage_compl, hFirst] using h
  · intro hST
    have h := hPrint.2 (first ∩ second) second Set.inter_subset_right
    simpa only [phi, Set.preimage_inter, hFirst, hSecond,
      Set.inter_eq_left.mpr hST] using h

theorem lean_of_print : PrintStatement.{u, v} → LeanStatement.{u, v} := by
  intro hPrint N X E hE
  have atPair (S T : Set N) :=
    let ⟨hX, hPlayable⟩ := H hE S T
    @hPrint (ULift.{u} (Bool × Bool)) inferInstance inferInstance X hX
      (phi E S T) hPlayable
  exact ⟨fun S => (C E S Set.univ (atPair S Set.univ)).1,
    fun S T => (C E S T (atPair S T)).2⟩

theorem print_of_lean : LeanStatement.{u, v} → PrintStatement.{u, v} := by
  intro hLean P _ _ X _ E hE
  exact hLean P X E hE

end Transfer099
