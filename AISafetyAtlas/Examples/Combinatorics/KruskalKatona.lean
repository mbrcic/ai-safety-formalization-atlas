module

public import AISafetyAtlas.Combinatorics.KruskalKatona

/-!
# Worked example: Kruskal-Katona away from `Fin n`

Mathlib states the Lovasz form over `Finset (Finset (Fin n))`. The point of
`AISafetyAtlas.Combinatorics.choose_le_card_shadow_iterate` is that the ground
type need not be `Fin n`, so the witness here uses a four-constructor inductive
and a three-element `s` inside it.

The family is all three pairs from `{parse, plan, recall}`. It has `3.choose 2`
members, so the theorem forces its shadow to have at least `3.choose 1` — which it
does, exactly, since the three pairs among three cards reach all three singles.
-/

namespace AISafetyAtlas.Examples.Combinatorics.KruskalKatona

/-- Four cards. The fourth is present so that `s` is a proper subset of the type
and the bound is not secretly about the whole of it. -/
inductive Skill where
  | parse
  | plan
  | recall
  | recover
  deriving DecidableEq, Repr

open Skill

/-- The ground set the bound is taken relative to. -/
def ground : Finset Skill := {parse, plan, recall}

/-- All three pairs inside `ground`. -/
def pairs : Finset (Finset Skill) := {{parse, plan}, {parse, recall}, {plan, recall}}

/-- Every member is a pair drawn from `ground`. -/
theorem pairs_subset : ∀ A ∈ pairs, A ⊆ ground := by decide

/-- The family is sized. -/
theorem pairs_sized : ((pairs : Finset (Finset Skill)) : Set (Finset Skill)).Sized 2 :=
  fun _ hx => (by decide : ∀ B ∈ pairs, B.card = 2) _ (Finset.mem_coe.mp hx)

/-- **A finite set is the range of an embedding out of `Fin` of its size.** This
is what lets the ground type be changed at all. -/
example : ∃ f : Fin ground.card ↪ Skill, ∀ a, a ∈ ground ↔ ∃ i, f i = a :=
  AISafetyAtlas.Combinatorics.exists_embedding_range_eq ground

/-- **The transported Lovasz bound, on a ground type that is not `Fin n`.** Three
pairs among three cards force all three singles. -/
example : Nat.choose 3 (2 - 1) ≤ (Finset.shadow^[1] pairs).card :=
  AISafetyAtlas.Combinatorics.choose_le_card_shadow_iterate
    (s := ground) (r := 2) (i := 1) (k := 3)
    pairs_subset pairs_sized (by decide) (by decide) (by decide) (by decide)

end AISafetyAtlas.Examples.Combinatorics.KruskalKatona
