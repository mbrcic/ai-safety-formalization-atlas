module

public import AISafetyAtlas.Sovereignty.Retargetable
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# The smallest retargetable decision-maker

`Retargetable` proves that retargetability forces a counting inequality. Both
statements are implications, so they say nothing until something satisfies the
antecedent. This file supplies that: a two-parameter decision-maker which favours
`A` at one parameter and `B` at the other, and which the swap retargets.

The parameter type is `Bool`, the group is its permutations, and `flipA`/`flipB`
disagree at both parameters. The swap sends the `A`-favouring parameter to the
`B`-favouring one, which is simple retargetability, so `MostOrbit` follows.

The point of the file is `simplyRetargetable_flip`: without a witness,
`SimplyRetargetable.mostOrbit` is a statement about nothing.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- Favours `A` at `true`. -/
@[expose] public def flipA : Bool → ℝ := fun b => if b then 1 else 0

/-- Favours `B` at `false`. -/
@[expose] public def flipB : Bool → ℝ := fun b => if b then 0 else 1

/-- At `true` the decision-maker prefers `A`. -/
public theorem flipA_gt_at_true : flipB true < flipA true := by
  simp [flipA, flipB]

/-- At `false` it prefers `B`. -/
public theorem flipB_gt_at_false : flipA false < flipB false := by
  simp [flipA, flipB]

/-- **The antecedent is inhabited.** The swap retargets every `A`-preference into
a `B`-preference, so `SimplyRetargetable` is not vacuous. -/
public theorem simplyRetargetable_flip :
    SimplyRetargetable (Equiv.Perm Bool) (Set.univ : Set Bool) flipA flipB := by
  refine ⟨Equiv.swap true false, ?_⟩
  intro θA _ h
  cases θA
  · exact absurd h (by simp [flipA, flipB])
  · show flipA (Equiv.swap true false • true) < flipB (Equiv.swap true false • true)
    simpa [Equiv.swap_apply_left] using flipB_gt_at_false

/-- **So the conclusion holds of something.** Every orbit has at least as many
parameters favouring `B` as favouring `A`. -/
public theorem mostOrbit_flip :
    MostOrbit (Equiv.Perm Bool) 1 (Set.univ : Set Bool) flipA flipB :=
  SimplyRetargetable.mostOrbit (fun _ _ _ => Set.mem_univ _) simplyRetargetable_flip

/-- The `A`-favouring part of the orbit is genuinely non-empty, so
`mostOrbit_flip` is not the trivial `0 ≤ n` case. -/
public theorem orbitAgainst_flip_nonempty :
    true ∈ orbitAgainst (Equiv.Perm Bool) (Set.univ : Set Bool) flipA flipB true :=
  ⟨⟨⟨1, rfl⟩, Set.mem_univ _⟩, flipA_gt_at_true⟩

/-! ## The copy count, at its two structural moves -/

/-- **Any subset is one copy of itself inside a superset**, carried by the
identity. This is the cheapest possible inhabitant of `ContainsCopies`, and it
is here so that the count below is a weakening of something rather than of
nothing. -/
public theorem univ_containsCopies_singleton :
    ContainsCopies (Equiv.Perm Bool) 1 (Set.univ : Set Bool) ({true} : Set Bool) :=
  containsCopies_one_of_subset (G := Equiv.Perm Bool) (Set.subset_univ _)

/-- **And containing one copy weakens to containing none.** The count is
monotone downwards, so a hypothesis at `n` copies is never weaker than the same
hypothesis at `m ≤ n` -- which is why a theorem that assumes many copies assumes
strictly more. -/
public theorem univ_containsCopies_zero :
    ContainsCopies (Equiv.Perm Bool) 0 (Set.univ : Set Bool) ({true} : Set Bool) :=
  ContainsCopies.mono (Nat.zero_le 1) univ_containsCopies_singleton

end AISafetyAtlas.Examples.Sovereignty
