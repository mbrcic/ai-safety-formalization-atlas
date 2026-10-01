module

public import AISafetyAtlas.Combinatorics.CascadeFamily

/-!
# Worked example: colex rank counts what it says it counts

`colexRank s` is meant to be the number of sets of the same size strictly below
`s` in colexicographic order. The examples below check that on the smallest cases
where the answer can be listed by hand, and apply the recursion that strips the
largest element.

These are compiling documentation examples, not public theorems.
-/

namespace AISafetyAtlas.Examples.Combinatorics.CascadeFamily

open AISafetyAtlas.Combinatorics
open scoped FinsetFamily

/-- The first pair has rank zero. -/
example : colexRank {0, 1} = 0 := by decide

/-- `{1, 2}` is third: `{0,1}` and `{0,2}` come before it. -/
example : colexRank {1, 2} = 2 := by decide

/-- And there really are two pairs below it. -/
example :
    ((Finset.univ : Finset (Fin 4)).powersetCard 2
      |>.filter fun t => toColex t < toColex ({1, 2} : Finset (Fin 4))).card
      = 2 := by decide

/-- `{0, 3}` is fourth. -/
example : colexRank {0, 3} = 3 := by decide

/-- `{2, 3}` is sixth, which is where the cascade of the *count* stops agreeing
with the elements of the set: `colexRank {2,3} + 1 = 6` has leading cascade digit
`4`, not `3`. -/
example : colexRank {2, 3} = 5 := by decide

/-- The leading digit of the cascade of `6` really is `4`. -/
example : cascadeTop 2 6 = 4 :=
  AISafetyAtlas.Combinatorics.cascadeTop_eq (r := 1) (by decide) (by decide)

/-- The empty set is first. -/
example : colexRank ∅ = 0 :=
  AISafetyAtlas.Combinatorics.colexRank_empty

/-- A singleton's rank is its element. -/
example : colexRank {7} = 7 :=
  AISafetyAtlas.Combinatorics.colexRank_singleton 7

/-- **The recursion.** Strip the largest element and the rank drops by that
element's own binomial: `colexRank {2,3} = C(3,2) + colexRank {2}`. -/
example : colexRank {2, 3} =
    ((({2, 3} : Finset ℕ).max' (by decide)).choose ({2, 3} : Finset ℕ).card) +
      colexRank (({2, 3} : Finset ℕ).erase (({2, 3} : Finset ℕ).max' (by decide))) :=
  AISafetyAtlas.Combinatorics.colexRank_erase_max {2, 3} (by decide)

/-- The greedy remainder is strictly under the next binomial down, which is why
the representation terminates. -/
example : 6 - (cascadeTop 2 6).choose 2 < (cascadeTop 2 6).choose 1 :=
  AISafetyAtlas.Combinatorics.sub_cascadeTop_choose_lt 1 6
    (AISafetyAtlas.Combinatorics.cascadeTop_choose_le 1 6)

/-! ## The initial family over a finite ground set -/

/-- Ranking through values does not change the size. -/
example : (({1, 2} : Finset (Fin 4)).image Fin.val).card = ({1, 2} : Finset (Fin 4)).card :=
  AISafetyAtlas.Combinatorics.card_image_val _

/-- The rank of a pair in `Fin 4` lands below `C(4,2) = 6`. -/
example : finRank ({1, 2} : Finset (Fin 4)) < Nat.choose 4 ({1, 2} : Finset (Fin 4)).card :=
  AISafetyAtlas.Combinatorics.finRank_lt _

/-- And it respects colex here too. -/
example : finRank ({0, 2} : Finset (Fin 4)) < finRank ({1, 2} : Finset (Fin 4)) :=
  AISafetyAtlas.Combinatorics.finRank_lt_finRank (by decide) (by decide)

/-- Distinct pairs get distinct ranks. -/
example {s t : Finset (Fin 4)}
    (hs : s ∈ (Finset.univ.powersetCard 2 : Finset (Finset (Fin 4))))
    (ht : t ∈ (Finset.univ.powersetCard 2 : Finset (Finset (Fin 4))))
    (h : finRank s = finRank t) : s = t :=
  AISafetyAtlas.Combinatorics.finRank_injOn 2 (Finset.mem_coe.mpr hs) (Finset.mem_coe.mpr ht) h

/-- Membership in the initial family, unfolded. -/
example {s : Finset (Fin 4)} :
    s ∈ AISafetyAtlas.Combinatorics.initFamily 4 2 3 ↔ s.card = 2 ∧ finRank s < 3 :=
  AISafetyAtlas.Combinatorics.mem_initFamily_iff

/-- **It is a colexicographic initial segment**, which is what Kruskal-Katona
asks to be handed. -/
example : Finset.Colex.IsInitSeg (AISafetyAtlas.Combinatorics.initFamily 4 2 3) 2 :=
  AISafetyAtlas.Combinatorics.isInitSeg_initFamily 2 3

/-- The ranks of a whole layer are an initial interval. -/
example : (Finset.univ.powersetCard 2 : Finset (Finset (Fin 4))).image finRank
    = Finset.range (Nat.choose 4 2) :=
  AISafetyAtlas.Combinatorics.image_finRank_powersetCard 2

/-- **And the family has exactly the size asked for.** Three pairs, from a layer
of six. -/
example : (AISafetyAtlas.Combinatorics.initFamily 4 2 3).card = 3 :=
  AISafetyAtlas.Combinatorics.card_initFamily 2 3 (by decide)

/-! ## The combinatorial number system, and Kruskal-Katona in cascade form -/

/-- Mathlib's generated initial segment is this file's, cut at one past the rank. -/
example : Finset.Colex.initSeg ({1, 2} : Finset (Fin 4))
    = AISafetyAtlas.Combinatorics.initFamily 4 ({1, 2} : Finset (Fin 4)).card
        (finRank ({1, 2} : Finset (Fin 4)) + 1) :=
  AISafetyAtlas.Combinatorics.initSeg_eq_initFamily _

/-- **The rank is the position.** `{1,2}` ranks second, and its initial segment
holds three pairs. -/
example : (Finset.Colex.initSeg ({1, 2} : Finset (Fin 4))).card
    = finRank ({1, 2} : Finset (Fin 4)) + 1 :=
  AISafetyAtlas.Combinatorics.card_initSeg _

/-- Erasing the least element commutes with reading a set through its values. -/
example : (({1, 2} : Finset (Fin 4)).erase (({1, 2} : Finset (Fin 4)).min' (by decide))).image
      Fin.val
    = ((({1, 2} : Finset (Fin 4)).image Fin.val)).erase
        (((({1, 2} : Finset (Fin 4)).image Fin.val)).min' ((by decide : ({1, 2} : Finset (Fin 4)).Nonempty).image _)) :=
  AISafetyAtlas.Combinatorics.image_val_erase_min _ (by decide)

/-- **The closing identity**, on the set where the digits stop agreeing. -/
example : cascadeShadow 2 (colexRank ({2, 3} : Finset ℕ) + 1)
    = colexRank ((({2, 3} : Finset ℕ)).erase ((({2, 3} : Finset ℕ)).min' (by decide))) + 1 :=
  AISafetyAtlas.Combinatorics.cascadeShadow_colexRank_succ 1 {2, 3} (by decide) (by decide)

/-- The boundary case: a set that ranks last among those of its size. -/
example : ∀ hv : ({1, 2} : Finset ℕ).Nonempty,
    colexRank ((({1, 2} : Finset ℕ)).erase ((({1, 2} : Finset ℕ)).min' hv)) + 1
      = Nat.choose 3 1 :=
  AISafetyAtlas.Combinatorics.colexRank_erase_min_of_maximal 1 {1, 2} 3 (by decide)
    (by decide) (by decide)

/-- **The shadow of an initial family, counted.** The first three pairs in `Fin 4`
touch exactly `cascadeShadow 2 3 = 3` single cards. -/
example : (∂ (AISafetyAtlas.Combinatorics.initFamily 4 2 3)).card = cascadeShadow 2 3 :=
  AISafetyAtlas.Combinatorics.card_shadow_initFamily 2 3 (by decide)

/-- **Kruskal-Katona in cascade form**, over `Fin n`. -/
example {𝒜 : Finset (Finset (Fin 4))} (h : (𝒜 : Set (Finset (Fin 4))).Sized 2) :
    cascadeShadow 2 𝒜.card ≤ (∂ 𝒜).card :=
  AISafetyAtlas.Combinatorics.cascadeShadow_le_card_shadow h

/-- **And over an arbitrary ground type.** Three pairs drawn from three naturals
touch three singletons, which is exactly the bound. -/
example : cascadeShadow 2 (({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ))).card
    ≤ (∂ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ))).card :=
  AISafetyAtlas.Combinatorics.cascadeShadow_le_card_shadow' (s := {0, 1, 2}) (by decide)
    (fun _ hx =>
      (by decide : ∀ B ∈ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)), B.card = 2) _
        (Finset.mem_coe.mp hx))

/-- **The cap is reached.** Three cards permit three pairs, and there is a family
of exactly three pairs inside `Fin 4` whose shadow is no larger than three -- the
triangle on the first three. Without this the word "tight" would be a claim about
a number rather than about families. -/
example : ∃ 𝔅 : Finset (Finset (Fin 4)),
    (𝔅 : Set (Finset (Fin 4))).Sized (0 + 2) ∧
      𝔅.card = AISafetyAtlas.Combinatorics.cascadeUpper (0 + 1) 3 ∧
      (∂ 𝔅).card ≤ 3 :=
  AISafetyAtlas.Combinatorics.exists_card_eq_cascadeUpper_of_le (n := 4) (r := 0) (a := 3)
    (by decide)

end AISafetyAtlas.Examples.Combinatorics.CascadeFamily
