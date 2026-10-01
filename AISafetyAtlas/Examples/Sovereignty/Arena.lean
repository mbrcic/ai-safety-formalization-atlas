module

public import AISafetyAtlas.Sovereignty.Arena

/-!
# Setting a boundary is not holding one

`Arena.Sovereign` and `Arena.Dictates` differ in a single quantifier, so the
question of whether they differ at all is the question of whether some arena
satisfies the existential and not the universal. This one does.

`gate` is the two-choice arena `outcome c r = c && r`. Choosing `false` settles
the outcome whatever the residue does; choosing `true` hands the outcome to the
residue entirely. So the party can *set* what the boundary shows and does not
*hold* it: its sovereignty depends on which choice it makes, which is exactly
what `Sovereign` forbids and `Dictates` allows.

This is why the containment `Arena.Sovereign.dictates` runs in only one
direction, and it is the arena-level form of the observation that power is
necessary for sovereignty without being sufficient for it.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- Choosing `false` settles the outcome; choosing `true` surrenders it. -/
@[expose] public def gate : Arena Bool Bool Bool where
  outcome := fun c r => c && r

/-- The party can settle what the outcome shows, by choosing `false`. -/
public theorem gate_dictates : gate.Dictates (id : Bool → Bool) :=
  ⟨false, fun _ _ ↦ rfl⟩

/-- It does not hold the outcome, because its other choice surrenders it. -/
public theorem gate_not_sovereign : ¬ gate.Sovereign (id : Bool → Bool) :=
  Arena.not_sovereign_of_residue_moves (A := gate) true true false (by decide)

/-- **Dictation does not imply sovereignty.** The converse implication is
`Arena.Sovereign.dictates`, and this is the witness that it is strict. -/
public theorem dictates_without_sovereignty :
    gate.Dictates (id : Bool → Bool) ∧ ¬ gate.Sovereign (id : Bool → Bool) :=
  ⟨gate_dictates, gate_not_sovereign⟩

/-- The surrendering choice is not decisive; the settling one is. -/
public theorem gate_decisive_iff (c : Bool) :
    (gate.map (id : Bool → Bool)).Decisive c ↔ c = false := by
  cases c
  · exact ⟨fun _ ↦ rfl, fun _ _ _ ↦ rfl⟩
  · exact ⟨fun h ↦ Bool.noConfusion (h true false), fun h ↦ Bool.noConfusion h⟩

/-! ## The arena vocabulary at `gate`

The lemmas below are the general arena theory instantiated at the one arena this
file builds. They add no mathematics; they are here so that each general
statement has a concrete arena where its hypotheses actually hold.
-/

/-- **Forcing is collapsing into the target**, read at `gate` and the singleton
`{false}` that the settling choice lands on. -/
public theorem gate_forces_iff_collapse_subset :
    gate.Forces {false} ↔ ∃ c, gate.collapse c ⊆ ({false} : Set Bool) :=
  Arena.forces_iff_exists_collapse_subset

/-- The settling choice is decisive on the outcome itself, not only in a view. -/
public theorem gate_decisive_false : gate.Decisive false :=
  fun _ _ ↦ rfl

/-- **A decisive choice forces the singleton it lands on.** `gate` has a residue
available, so the hypothesis of the general lemma is met, not assumed. -/
public theorem gate_forces_singleton :
    gate.Forces {gate.outcome false false} :=
  Arena.forces_singleton_of_decisive gate_decisive_false false

/-- Forcing the whole outcome space is free once any choice exists. -/
public theorem gate_forces_univ : gate.Forces (Set.univ : Set Bool) :=
  Arena.forces_univ

/-- Reading `gate` through a view composes with the view, by definition. -/
public theorem gate_map_outcome (c r : Bool) :
    (gate.map (fun b ↦ !b)).outcome c r = !(gate.outcome c r) :=
  Arena.map_outcome (A := gate) _ c r

/-- **A boundary that shows nothing is held by everything**, `gate` included --
which is why `gate_not_sovereign` had to pick a view that shows something. -/
public theorem gate_sovereign_const (b : Bool) :
    gate.Sovereign (fun _ ↦ b) :=
  Arena.sovereign_const b

/-- Sovereignty at `gate`, read in the collapse vocabulary. -/
public theorem gate_sovereign_iff_collapse :
    gate.Sovereign (id : Bool → Bool) ↔
      ∀ c, ((gate.map (id : Bool → Bool)).collapse c).Subsingleton :=
  Arena.sovereign_iff_forall_collapse_subsingleton

end AISafetyAtlas.Examples.Sovereignty
