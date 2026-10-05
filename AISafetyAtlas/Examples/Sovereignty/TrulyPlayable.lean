module

public import AISafetyAtlas.Sovereignty.TrulyPlayable
public import AISafetyAtlas.Examples.Sovereignty.PlayableConverse

/-!
# Truly playable effectivity functions, on both sides of the separation

`TrulyPlayable` states Goranko, Jamroga and Turrini's repair of Pauly's Theorem
3.2. This file runs it on the two objects `PlayableConverse` already carries.

* The veto game on `Bool` is truly playable, and its nonmonotonic core at the
  empty coalition is the singleton of its reachable set -- print's Proposition 2.
* `cofiniteEff` is playable and **not** truly playable, and the reason is the one
  print gives: its core at the empty coalition is empty.

The second is the separating pair: `exists_playable_not_trulyPlayable` says the
two classes differ, which is the whole point of the paper.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-! ## A game form is truly playable -/

example : TrulyPlayable (effectivity vetoGame) := trulyPlayable_effectivity

/-- Print's Proposition 2 on a concrete game: the core at the empty coalition is
the singleton whose element is the set of outcomes some profile produces. -/
example : nonmonotonicCore (effectivity vetoGame) (∅ : Set Bool) =
    {Set.range vetoGame.outcome} :=
  nonmonotonicCore_effectivity_empty

/-! ## The cofinite filter is playable and not truly playable -/

example : Playable cofiniteEff := cofiniteEff_playable

example : ¬ TrulyPlayable cofiniteEff := not_trulyPlayable_cofiniteEff

/-- Print's reason, not a repackaging of the conclusion: there are no minimal
cofinite sets. -/
example : nonmonotonicCore cofiniteEff (∅ : Set Unit) = ∅ :=
  nonmonotonicCore_cofiniteEff_empty

/-- **The two classes are different.** Playability does not imply true
playability, which is why Pauly's characterization needed repairing. -/
public theorem exists_playable_not_trulyPlayable :
    ∃ E : Set Unit → Set (Set ℕ), Playable E ∧ ¬ TrulyPlayable E :=
  ⟨cofiniteEff, cofiniteEff_playable, not_trulyPlayable_cofiniteEff⟩

/-! ## Proposition 1 (1) as a filter, and Proposition 5 (3) in Mathlib's words

`Playable.emptyFilter` is the object print names rather than the four conditions
it lists, which is what lets Proposition 6 be proved print's way. Both sides of
the separation are filters; only one of them is principal. -/

/-- The veto game's `E ∅` is a proper filter, print's Proposition 1 (1). -/
example : (vetoGame_playable.emptyFilter).NeBot := vetoGame_playable.emptyFilter_neBot

/-- And it is principal, which by Proposition 5 (3) is true playability. -/
example : ∃ A : Set Bool, vetoGame_playable.emptyFilter = Filter.principal A :=
  vetoGame_playable.trulyPlayable_iff_emptyFilter_principal.mp trulyPlayable_effectivity

/-- The cofinite filter is a filter too -- that is not what separates the two
classes. What separates them is that this one is **not principal**. -/
example : ¬ ∃ A : Set ℕ, cofiniteEff_playable.emptyFilter = Filter.principal A :=
  fun h => not_trulyPlayable_cofiniteEff
    (cofiniteEff_playable.trulyPlayable_iff_emptyFilter_principal.mpr h)

/-! ## The generality the atlas adds over the finite route

Print's Proposition 6 and the `cl-lean` route both want a finite domain. The
general form wants a minimal element of the family, and the finite outcome type
is two corollaries away. Both are exercised here, on a two-outcome game where
either hypothesis is available. -/

example : TrulyPlayable (effectivity vetoGame) :=
  vetoGame_playable.trulyPlayable_of_finite

example : TrulyPlayable (effectivity vetoGame) :=
  vetoGame_playable.trulyPlayable_of_finite_empty (Set.toFinite _)

/-- The general form, given the least element outright: no finiteness used. -/
example : TrulyPlayable (effectivity vetoGame) :=
  vetoGame_playable.trulyPlayable_of_exists_minimal
    ⟨Set.range vetoGame.outcome, range_outcome_mem_effectivity_empty,
      fun _ hB hlt =>
        hlt.ne (hlt.subset.antisymm (range_outcome_subset_of_mem_effectivity_empty hB))⟩

/-- `cofiniteEff` shows the finiteness hypotheses are not removable for free: the
family `cofiniteEff ∅` is infinite, and the conclusion genuinely fails. -/
example : ¬ ∃ A ∈ cofiniteEff (∅ : Set Unit),
    ∀ B ∈ cofiniteEff (∅ : Set Unit), ¬ B ⊂ A := by
  rintro ⟨A, hA, hmin⟩
  have : A ∈ nonmonotonicCore cofiniteEff (∅ : Set Unit) :=
    ⟨hA, by rintro ⟨B, hB, hlt⟩; exact hmin B hB hlt⟩
  rw [nonmonotonicCore_cofiniteEff_empty] at this
  exact this

/-! ## Proposition 5, as named results

As in `PlayableConverse`, the `example`s above demonstrate without grounding. -/

/-- **The core at the empty coalition holds at most one set.** Print's
Proposition 2 gives the exact singleton for the veto game; this is the general
bound it lives under, and it is what makes "the minimal set" a definite
description rather than a choice. -/
public theorem vetoGame_nonmonotonicCore_empty_subsingleton :
    Set.Subsingleton (nonmonotonicCore (effectivity vetoGame) (∅ : Set Bool)) :=
  Playable.subsingleton_nonmonotonicCore_empty vetoGame_playable

/-- **And true playability is principality of the empty-coalition filter**,
Proposition 5 (3), read at the game that has it. The separating pair is the same
statement read at `cofiniteEff`, where the filter is a filter and is not
principal. -/
public theorem vetoGame_emptyFilter_principal :
    ∃ A : Set Bool, vetoGame_playable.emptyFilter = Filter.principal A :=
  (Playable.trulyPlayable_iff_emptyFilter_principal vetoGame_playable).mp
    trulyPlayable_effectivity

end AISafetyAtlas.Examples.Sovereignty
