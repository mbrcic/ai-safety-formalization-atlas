import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Order.Basic
import SocialChoice.Profile

namespace SocialChoice

open Finset

/--
`rank r c` is the number of candidates strictly above `c` in the linear order `r`.
We define a 1-based `position` as `rank + 1`.
-/
def rank {A : Type} [Fintype A] (r : LinearOrder A) (c : A) : Nat :=
  (Finset.univ.filter (fun d => r.lt d c)).card

def position {A : Type} [Fintype A] (r : LinearOrder A) (c : A) : Nat :=
  rank r c + 1

theorem position_eq_rank_succ {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    position r c = rank r c + 1 := rfl

theorem rank_le_card {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    rank r c ≤ Fintype.card A := by
  classical
  change (Finset.univ.filter (fun d => r.lt d c)).card ≤ (Finset.univ : Finset A).card
  exact
    Finset.card_le_card
      (Finset.filter_subset (s := (Finset.univ : Finset A)) (p := fun d => r.lt d c))

theorem rank_lt_card {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    rank r c < Fintype.card A := by
  classical
  change (Finset.univ.filter (fun d => r.lt d c)).card < (Finset.univ : Finset A).card
  have hsubset :
      (Finset.univ.filter (fun d => r.lt d c)) ⊂ (Finset.univ : Finset A) := by
    refine (Finset.ssubset_iff_of_subset
      (Finset.filter_subset (s := (Finset.univ : Finset A)) (p := fun d => r.lt d c))).2 ?_
    refine ⟨c, by simp, ?_⟩
    simp
  exact Finset.card_lt_card hsubset

lemma rank_lt_of_lt {A : Type} [Fintype A] (r : LinearOrder A) {c d : A} (hcd : r.lt c d) :
    rank r c < rank r d := by
  classical
  let _ := r
  have hsubset :
      (Finset.univ.filter (fun a : A => a < c)) ⊆
        (Finset.univ.filter (fun a : A => a < d)) := by
    intro a ha
    have ha' : a < c := (Finset.mem_filter.mp ha).2
    have had : a < d := lt_trans ha' hcd
    exact Finset.mem_filter.mpr ⟨by simp, had⟩
  have hssub :
      (Finset.univ.filter (fun a : A => a < c)) ⊂
        (Finset.univ.filter (fun a : A => a < d)) := by
    refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
    refine ⟨c, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simp, hcd⟩
    · intro hc
      have hc' : c < c := (Finset.mem_filter.mp hc).2
      exact (lt_irrefl _ hc')
  simpa [rank] using (Finset.card_lt_card hssub)

theorem position_le_card {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    position r c ≤ Fintype.card A := by
  have h := rank_lt_card r c
  simpa [position, Nat.succ_eq_add_one] using (Nat.succ_le_of_lt h)

/-! ## Top Choice Extraction -/

/-- Get the top-ranked candidate for a voter in a profile.
    This is the minimum element under the linear order (lower rank = more preferred). -/
noncomputable def topChoice {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (v : V) : A := by
  classical
  letI := P.pref v
  exact Finset.min' Finset.univ Finset.univ_nonempty

/-- The top choice satisfies TopRank. -/
lemma topChoice_topRank {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (v : V) : TopRank P v (topChoice P v) := by
  intro d hd
  unfold topChoice Prefers
  letI := P.pref v
  have hle := Finset.min'_le Finset.univ d (Finset.mem_univ d)
  exact lt_of_le_of_ne hle (Ne.symm hd)

/-- TopRank uniquely determines the top choice. -/
lemma topRank_eq_topChoice {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (v : V) (c : A) (htop : TopRank P v c) : c = topChoice P v := by
  by_contra hne
  have hc_beats := htop (topChoice P v) (Ne.symm hne)
  have htop_beats := topChoice_topRank P v c hne
  unfold Prefers at hc_beats htop_beats
  letI := P.pref v
  exact lt_asymm hc_beats htop_beats

/-- TopRank implies the candidate equals the topChoice. -/
lemma eq_topChoice_of_topRank {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (v : V) (c : A) (htop : TopRank P v c) : c = topChoice P v :=
  topRank_eq_topChoice P v c htop

end SocialChoice
