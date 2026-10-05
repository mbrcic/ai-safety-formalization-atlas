module

public import AISafetyAtlas.Combinatorics.PermInvariance
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The permutation-invariance vocabulary, applied

Four checks on `AISafetyAtlas.Combinatorics.PermInvariance` that had no
worked instance anywhere in the tree: the closed-set count, the two-point
transitivity lemmas, and the graph dichotomy. `oneEdge` and the complete/
empty graphs on `Fin 3` are the cheapest witnesses that exercise each one
on a genuine (non-diagonal, non-trivial) relation.
-/

namespace AISafetyAtlas.Examples.Combinatorics.PermInvariance

open AISafetyAtlas.Combinatorics

/-- **Igel–Toussaint's Theorem 3, first equation, evaluated.** The
permutation-closed subsets of `Fin 2 ^ Fin 4` number `2 ^ C(5, 4) = 32`. -/
theorem card_closedUnderPermutation_fin :
    Nat.card {F : Set (Fin 4 → Fin 2) // ClosedUnderPermutation F} = 32 :=
  card_closedUnderPermutation (X := Fin 4) (Y := Fin 2)

/-- Three points, one edge: `0` and `1` neighbour, nothing else does. -/
def oneEdge : SimpleGraph (Fin 3) where
  Adj a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨by rintro a (⟨h, h'⟩ | ⟨h, h'⟩) <;> exact absurd (h.symm.trans h') (by decide)⟩

/-- **A non-trivial relation can be moved onto any pair of distinct
points**, at `oneEdge` moved from `(0, 1)` onto `(0, 2)`. -/
theorem exists_perm_oneEdge_at_zero_two :
    ∃ π : Equiv.Perm (Fin 3), oneEdge.Adj (π 0) (π 2) :=
  exists_perm_rel_of_ne (r := oneEdge.Adj) ⟨0, 1, by decide, Or.inl ⟨rfl, rfl⟩⟩
    (by decide : (0 : Fin 3) ≠ 2)

/-- The complete graph is fixed by every relabelling. -/
theorem top_permInvariant (π : Equiv.Perm (Fin 3)) (a b : Fin 3) :
    (⊤ : SimpleGraph (Fin 3)).Adj (π a) (π b) ↔ (⊤ : SimpleGraph (Fin 3)).Adj a b := by
  simp [π.injective.ne_iff]

/-- **A relation invariant under every permutation is constant on the
diagonal**, at the complete graph — vacuously irreflexive, so both sides
are `False`. -/
theorem rel_diag_iff_top (x y : Fin 3) :
    (⊤ : SimpleGraph (Fin 3)).Adj x x ↔ (⊤ : SimpleGraph (Fin 3)).Adj y y :=
  rel_diag_iff_of_permInvariant top_permInvariant x y

/-- **The graph dichotomy**, at the complete graph on `Fin 3`: every
distinct pair is adjacent. -/
theorem forall_adj_or_forall_not_adj_top :
    (∀ a b : Fin 3, a ≠ b → (⊤ : SimpleGraph (Fin 3)).Adj a b) ∨
      ∀ a b : Fin 3, ¬ (⊤ : SimpleGraph (Fin 3)).Adj a b :=
  forall_adj_or_forall_not_adj_of_permInvariant (⊤ : SimpleGraph (Fin 3)) top_permInvariant

end AISafetyAtlas.Examples.Combinatorics.PermInvariance
