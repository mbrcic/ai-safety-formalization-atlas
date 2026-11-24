module

public import AISafetyAtlas.Sovereignty.TrulyPlayableRepresentation

/-!
# A playable function Peleg's theorem does not reach, and Pauly's game gets wrong

One player, and every coalition effective for exactly the sets containing a fixed
outcome x. The family is playable, and it is not one of Peleg's effectivity
functions: the empty coalition is effective for {x}, not only for the whole
space. So `AISafetyAtlas.Sovereignty.exists_gameForm_of_isEffectivityFunction` does
not apply, and Pauly's own game is the wrong carrier: it reaches every outcome, so
at two or more outcomes its grand coalition can force a set missing x.

`AISafetyAtlas.Sovereignty.Playable.exists_gameForm_of_finite` represents it at
`Bool`, and `AISafetyAtlas.Sovereignty.TrulyPlayable.exists_gameForm` at ℕ,
where no finiteness is available.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- One player; every coalition is effective for the sets containing x. -/
@[expose] public def pointEff {X : Type} (x : X) : Set Unit → Set (Set X) :=
  fun _ => {A | x ∈ A}

/-- The family is playable, all five of Pauly's conditions. -/
public theorem pointEff_playable {X : Type} (x : X) : Playable (pointEff x) where
  live := fun _ h => h
  safe := fun _ => Set.mem_univ x
  maximal := fun _ hA => by
    by_contra h
    exact hA h
  mono := fun _ _ _ hAB hA => hAB hA
  superadd := fun _ _ _ _ _ hA hB => ⟨hA, hB⟩

/-- The family is truly playable at any outcome type: {x} is the least member of
the empty coalition's family. -/
public theorem pointEff_trulyPlayable {X : Type} (x : X) : TrulyPlayable (pointEff x) :=
  (pointEff_playable x).trulyPlayable_iff_principal.mpr
    ⟨{x}, Set.mem_singleton x, fun _ hB => Set.singleton_subset_iff.mpr hB⟩

/-- At two or more outcomes it is not one of Peleg's effectivity functions, so
`AISafetyAtlas.Sovereignty.exists_gameForm_of_isEffectivityFunction` does not
reach it. -/
public theorem not_isEffectivityFunction_pointEff :
    ¬ IsEffectivityFunction (pointEff true) := by
  intro h
  have hmem : ({true} : Set Bool) ∈ pointEff true (∅ : Set Unit) := Set.mem_singleton true
  rw [h.empty, Set.mem_singleton_iff] at hmem
  have : false ∈ ({true} : Set Bool) := hmem ▸ Set.mem_univ false
  exact Bool.false_ne_true this

/-- **Pauly's game is the wrong carrier**, even at a finite outcome set. It reaches
false, so its grand coalition is effective for {false}, which misses true.
This is Goranko, Jamroga and Turrini's grand-coalition obstruction. -/
public theorem effectivity_paulyGame_pointEff_ne :
    effectivity (paulyGame (pointEff_playable true)) ≠ pointEff true := by
  intro h
  have hsurj := Playable.surjective_paulyGame_outcome (pointEff_playable true)
  have hmem : ({false} : Set Bool) ∈ effectivity (paulyGame (pointEff_playable true))
      (Set.univ : Set Unit) := by
    rw [effectivity_univ_eq_nonempty hsurj]
    exact Set.singleton_nonempty false
  rw [h] at hmem
  exact Bool.false_ne_true hmem.symm

/-- **The finite repair represents it.** A game form with non-empty strategy sets
whose empty coalition is effective for {true} and whose grand coalition is not
effective for {false}: neither end is the one Pauly's game produces. -/
public theorem exists_gameForm_pointEff :
    ∃ G : GameForm.{0, 0, 0} Unit Bool, (∀ i, Nonempty (G.strategy i)) ∧
      ({true} : Set Bool) ∈ effectivity G (∅ : Set Unit) ∧
      ({false} : Set Bool) ∉ effectivity G (Set.univ : Set Unit) := by
  obtain ⟨G, hne, hG⟩ :=
    AISafetyAtlas.Sovereignty.Playable.exists_gameForm_of_finite (pointEff_playable true)
  refine ⟨G, hne, ?_, ?_⟩
  · rw [hG]; exact Set.mem_singleton true
  · rw [hG]; exact fun h => Bool.false_ne_true h.symm

/-- **At an infinite outcome set, truly playable suffices.** -/
public theorem exists_gameForm_pointEff_nat :
    ∃ G : GameForm.{0, 0, 0} Unit ℕ, (∀ i, Nonempty (G.strategy i)) ∧
      effectivity G = pointEff 0 :=
  AISafetyAtlas.Sovereignty.TrulyPlayable.exists_gameForm (pointEff_trulyPlayable 0)

/-- The corrected Theorem 3.2 as a biconditional, run at ℕ. -/
example : ∃ G : GameForm.{0, 0, 0} Unit ℕ, (∀ i, Nonempty (G.strategy i)) ∧
    effectivity G = pointEff 0 :=
  AISafetyAtlas.Sovereignty.exists_gameForm_iff_trulyPlayable.mpr (pointEff_trulyPlayable 0)

/-- And back: the veto game's effectivity function is truly playable. -/
example : TrulyPlayable (effectivity vetoGame) :=
  AISafetyAtlas.Sovereignty.exists_gameForm_iff_trulyPlayable.mp
    ⟨vetoGame, fun _ => ⟨true⟩, rfl⟩

/-- Pauly's Theorem 3.2 at a finite outcome set, both directions, run at `Bool`. -/
example : ∃ G : GameForm.{0, 0, 0} Unit Bool, (∀ i, Nonempty (G.strategy i)) ∧
    effectivity G = pointEff true :=
  AISafetyAtlas.Sovereignty.exists_gameForm_iff_playable_of_finite.mpr
    (pointEff_playable true)

/-- The finite repair at the shape of the printed claim in
docs/provenance/refutations/pauly-thm-3-2-literal.lean, with [Finite S] added. -/
example : ∀ (N S : Type) [Finite N] [Nonempty N] [Nonempty S] [Finite S]
    (E : Set N → Set (Set S)), Playable E →
      ∃ G : GameForm.{0, 0, 0} N S, (∀ i, Nonempty (G.strategy i)) ∧ effectivity G = E :=
  fun _ _ _ _ _ _ _ hE => AISafetyAtlas.Sovereignty.Playable.exists_gameForm_of_finite hE

end AISafetyAtlas.Examples.Sovereignty
