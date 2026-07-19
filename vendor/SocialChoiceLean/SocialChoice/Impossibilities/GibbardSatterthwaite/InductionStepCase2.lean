import SocialChoice.Impossibilities.GibbardSatterthwaite.Common
import Mathlib.Order.Interval.Finset.Fin

namespace SocialChoice

/-!
# Gibbard-Satterthwaite Induction Step: Case 2

Case 2 of the induction step: If the dictator in the cloned rule g is voter 1
(i.e., v₁), then either v₁ or v₂ is the dictator in f.

This is the most intricate part of the proof, following Steps (i)-(v)
from the Bandhu-Kumar paper.

The original proof is available in the file `gs-induction-proof.md`, lines 68-91.

## Main Result

* `gs_case2`: If v₁ is the dictator in g, then either v₁ or v₂ is the dictator in f.

## Proof Outline

The proof proceeds in five steps:

1. **Step (i)**: For any sub-profile P_{-12} and distinct a, b, at the profile where
   voter 1 has a > b > ... and voter 2 has b > a > ..., the outcome is a or b.

2. **Step (ii)**: If f(P) = a at such a profile, then voter 1 gets a whenever
   it is ranked first by voter 1, for any ballots of voter 2.

3. **Step (iii)**: Extend to arbitrary ballot of voter 2.

4. **Step (iv)**: Extend decisiveness from a to all alternatives.

5. **Step (v)**: Show independence from other voters' sub-profiles.
-/

open Finset

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [Nonempty A]

/-! ## Preliminary: Profile Construction Helpers -/

/-- Ballot-level structural facts about `updateProfile` towers.  These stay at the
data (ballot) level and never touch the `.lt` instance chain, so they are stable
across Mathlib's `LinearOrder` field reshuffles. -/
theorem updateProfile_updateProfile_self (P : Profile V A) (v : V)
    (b1 b2 : LinearOrder A) :
    updateProfile (updateProfile P v b1) v b2 = updateProfile P v b2 := by
  apply Profile.ext
  intro w
  by_cases h : w = v
  · subst h
    rw [updateProfile_pref_self, updateProfile_pref_self]
  · rw [updateProfile_pref_of_ne _ v _ h, updateProfile_pref_of_ne _ v _ h,
        updateProfile_pref_of_ne _ v _ h]

theorem updateProfile_updateProfile_comm (P : Profile V A) (v₁ v₂ : V)
    (h : v₁ ≠ v₂) (b1 b2 : LinearOrder A) :
    updateProfile (updateProfile P v₁ b1) v₂ b2
      = updateProfile (updateProfile P v₂ b2) v₁ b1 := by
  apply Profile.ext
  intro w
  by_cases hw2 : w = v₂
  · rw [hw2, updateProfile_pref_self, updateProfile_pref_of_ne _ v₁ _ (Ne.symm h),
        updateProfile_pref_self]
  · by_cases hw1 : w = v₁
    · rw [hw1, updateProfile_pref_of_ne _ v₂ _ h, updateProfile_pref_self,
          updateProfile_pref_self]
    · rw [updateProfile_pref_of_ne _ v₂ _ hw2, updateProfile_pref_of_ne _ v₁ _ hw1,
          updateProfile_pref_of_ne _ v₁ _ hw1, updateProfile_pref_of_ne _ v₂ _ hw2]

/-- A profile where everyone ranks c at top. -/
noncomputable def someLinearOrder (A : Type) [Fintype A] : LinearOrder A := by
  classical
  let e := Fintype.equivFin A
  exact LinearOrder.lift' e e.injective

noncomputable def ballotWithTop {A : Type} [Fintype A] (c : A) : LinearOrder A := by
  classical
  letI : Nonempty A := ⟨c⟩
  let r0 : LinearOrder A := someLinearOrder A
  letI : LinearOrder A := r0
  let m : A := Finset.min' (Finset.univ : Finset A) Finset.univ_nonempty
  exact relabelBallot r0 (Equiv.swap c m)

/-- A ballot with `a` ranked first and `b` ranked second.

This is implemented by starting from a canonical linear order on `A`, and then relabeling
by a permutation so that `a` becomes the minimal element and `b` becomes the second-minimal.

Requires `2 ≤ Fintype.card A` and `a ≠ b`.
-/
noncomputable def ballotWithTopTwo {A : Type} [Fintype A] (a b : A)
  (hcard : 2 ≤ Fintype.card A) (_hab : a ≠ b) : LinearOrder A := by
  classical
  letI : Nonempty A := ⟨a⟩
  let r0 : LinearOrder A := someLinearOrder A
  -- Use the canonical identification A ≃ Fin n to pick the 0th and 1st elements.
  let e := Fintype.equivFin A
  let n := Fintype.card A
  have hn1 : 1 < n := by have : n = Fintype.card A := rfl; omega
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_two (by simpa [n] using hcard)
  let m0 : A := e.symm ⟨0, hn0⟩
  let m1 : A := e.symm ⟨1, hn1⟩
  -- First swap a into the 0-position, then swap b (after the first swap) into the 1-position.
  let σ1 : Equiv.Perm A := Equiv.swap a m0
  let σ2 : Equiv.Perm A := Equiv.swap (σ1 b) m1
  -- NOTE: `Equiv.trans` composes right-to-left, so `σ1.trans σ2` means `σ2 ∘ σ1`.
  let σ : Equiv.Perm A := σ1.trans σ2
  exact relabelBallot r0 σ

/-! ### Rank/TopRank helper lemmas -/

lemma rank_relabelBallot {A : Type} [Fintype A]
    (r : LinearOrder A) (σ : Equiv.Perm A) (c : A) :
    rank (relabelBallot r σ) c = rank r (σ c) := by
  classical
  -- By definition, `relabelBallot r σ` compares `a` and `b` via `r.lt (σ a) (σ b)`.
  have hlt :
      ∀ {a b : A}, (relabelBallot r σ).lt a b ↔ r.lt (σ a) (σ b) := by
    intro a b
    rfl
  have hcard :
      (Finset.univ.filter (fun d => r.lt (σ d) (σ c))).card =
        (Finset.univ.filter (fun d => r.lt d (σ c))).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun d => r.lt (σ d) (σ c)))
      (t := Finset.univ.filter (fun d => r.lt d (σ c)))
      (i := fun d _ => σ d) ?_ ?_ ?_
    · intro d hd
      have hd' : r.lt (σ d) (σ c) := (Finset.mem_filter.mp hd).2
      exact Finset.mem_filter.mpr ⟨by simp, hd'⟩
    · intro d1 hd1 d2 hd2 h
      exact σ.injective h
    · intro d hd
      refine ⟨σ.symm d, ?_, by simp⟩
      have hd' : r.lt d (σ c) := (Finset.mem_filter.mp hd).2
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hd'⟩
  simpa [rank, hlt] using hcard

lemma rank_someLinearOrder_eq_val {A : Type} [Fintype A]
    (c : A) :
    rank (someLinearOrder A) c = (Fintype.equivFin A c).val := by
  classical
  let e := Fintype.equivFin A
  -- `someLinearOrder A` is obtained by transporting the usual order on `Fin n`.
  have hlt :
      ∀ {a b : A}, (someLinearOrder A).lt a b ↔ (e a) < (e b) := by
    intro a b
    rfl
  -- Count elements below `c` by mapping via `e` to `Fin (card A)`.
  have hcard :
      (Finset.univ.filter (fun d : A => (e d) < (e c))).card =
        (Finset.Iio (e c)).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun d : A => (e d) < (e c)))
      (t := Finset.Iio (e c))
      (i := fun d _ => e d) ?_ ?_ ?_
    · intro d hd
      have hd' : e d < e c := (Finset.mem_filter.mp hd).2
      -- membership in `Iio` is just `<`.
      simpa [Finset.mem_Iio] using hd'
    · intro d1 hd1 d2 hd2 h
      exact e.injective h
    · intro x hx
      refine ⟨e.symm x, ?_, by simp⟩
      have hx' : x < e c := by
        simpa [Finset.mem_Iio] using hx
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hx'⟩
  -- Now rewrite `rank` for the transported order and use `Fin.card_Iio`.
  have : rank (someLinearOrder A) c = (Finset.Iio (e c)).card := by
    simp [rank, hlt, hcard]
  simpa [Fin.card_Iio] using this

lemma topRank_iff_rank_eq_zero {A : Type} [Fintype A]
    (r : LinearOrder A) (c : A) :
    (∀ d : A, d ≠ c → r.lt c d) ↔ rank r c = 0 := by
  classical
  constructor
  · intro htop
    -- If c beats everyone, nobody can be strictly above it.
    by_contra h
    have hpos : 0 < rank r c := Nat.pos_of_ne_zero h
    -- pick some d with d < c from the filter definition
    have hex : ∃ d, r.lt d c := by
      -- if card(filter) > 0, filter is nonempty
      have : (Finset.univ.filter (fun d => r.lt d c)).Nonempty := by
        exact Finset.card_pos.mp hpos
      rcases this with ⟨d, hd⟩
      exact ⟨d, (Finset.mem_filter.mp hd).2⟩
    rcases hex with ⟨d, hdc⟩
    have hcd : r.lt c d := htop d (by
      intro hEq
      subst hEq
      exact lt_irrefl _ hdc)
    exact lt_asymm hdc hcd
  · intro hrank d hd
    -- If nobody is strictly above c, then for d ≠ c we must have c < d.
    have hnot : ¬ r.lt d c := by
      intro hdc
      -- then d is in the "above c" filter, contradicting rank=0
      have : d ∈ (Finset.univ.filter (fun x => r.lt x c)) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ d, hdc⟩
      have hcard : 0 < (Finset.univ.filter (fun x => r.lt x c)).card :=
        Finset.card_pos.mpr ⟨d, this⟩
      have : 0 < rank r c := by
        simpa [rank] using hcard
      -- contradiction to rank=0
      simp [hrank] at this
    have hle : c ≤ d := le_of_not_gt hnot
    exact lt_of_le_of_ne hle hd.symm

lemma prefers_second_over_others_of_rank_eq_one {A : Type} [Fintype A]
    (r : LinearOrder A) (a b c : A)
    (hrb : rank r b = 1) (hab : r.lt a b) (hca : c ≠ a) (hcb : c ≠ b) : r.lt b c := by
  classical
  -- If b is not below c, then c < b. But then c contributes to rank(b).
  by_contra hbc
  have hcb' : r.lt c b := lt_of_le_of_ne (le_of_not_gt hbc) hcb
  -- a is also below b, so {a,c} are two distinct elements below b.
  have ha_mem : a ∈ (Finset.univ.filter (fun x => r.lt x b)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, hab⟩
  have hc_mem : c ∈ (Finset.univ.filter (fun x => r.lt x b)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcb'⟩
  have hne_ac : a ≠ c := by
    intro hEq
    subst hEq
    exact hca rfl
  have hcard_ge2 : 2 ≤ (Finset.univ.filter (fun x => r.lt x b)).card := by
    -- {a,c} is a 2-element subset of the filter
    have : ({a, c} : Finset A) ⊆ (Finset.univ.filter (fun x => r.lt x b)) := by
      intro x hx
      have hx' : x = a ∨ x = c := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx
      cases hx' with
      | inl hxa =>
        subst hxa
        exact ha_mem
      | inr hxc =>
        subst hxc
        exact hc_mem
    have hcard := Finset.card_le_card this
    have hcard_ac : ({a, c} : Finset A).card = 2 := by
      simp [hne_ac]
    -- combine
    exact (by simpa [hcard_ac] using hcard)
  -- But rank(b) = card(filter) = 1.
  have : (Finset.univ.filter (fun x => r.lt x b)).card = 1 := by
    simpa [rank] using hrb
  omega

/-! ### Facts about `ballotWithTopTwo` -/

lemma rank_ballotWithTopTwo_top {A : Type} [Fintype A]
    (a b : A) (hcard : 2 ≤ Fintype.card A) (hab : a ≠ b) :
    rank (ballotWithTopTwo (A := A) a b hcard hab) a = 0 := by
  classical
  letI : Nonempty A := ⟨a⟩
  let r0 : LinearOrder A := someLinearOrder A
  let e := Fintype.equivFin A
  let n := Fintype.card A
  have hn1 : 1 < n := by have : n = Fintype.card A := rfl; omega
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_two (by simpa [n] using hcard)
  let m0 : A := e.symm ⟨0, hn0⟩
  let m1 : A := e.symm ⟨1, hn1⟩
  let σ1 : Equiv.Perm A := Equiv.swap a m0
  let σ2 : Equiv.Perm A := Equiv.swap (σ1 b) m1
  let σ : Equiv.Perm A := σ1.trans σ2

  have hm0_ne_m1 : m0 ≠ m1 := by
    intro h
    have : (⟨0, hn0⟩ : Fin n) = ⟨1, hn1⟩ := by
      simpa [m0, m1] using congrArg e h
    have : (0 : Nat) = 1 := congrArg Fin.val this
    exact Nat.zero_ne_one this

  have hm0_ne_σ1b : m0 ≠ σ1 b := by
    by_cases hb0 : b = m0
    · subst hb0
      have : m0 ≠ a := hab.symm
      simpa [σ1] using this
    · have hb0' : b ≠ m0 := hb0
      have hσ1b : σ1 b = b := by
        -- since `b ≠ a` and `b ≠ m0`, the swap does nothing.
        simpa [σ1] using (Equiv.swap_apply_of_ne_of_ne hab.symm hb0')
      simpa [hσ1b] using hb0'.symm

  have hσa : σ a = m0 := by
    -- σ a = σ2 (σ1 a) = σ2 m0 = m0
    have hσ1a : σ1 a = m0 := by simp [σ1]
    have hσ2m0 : σ2 m0 = m0 := by
      simpa [σ2] using (Equiv.swap_apply_of_ne_of_ne hm0_ne_σ1b hm0_ne_m1)
    -- unfold `Equiv.trans` to see it is function composition.
    simp [σ, Equiv.trans, hσ1a, hσ2m0]

  -- Now compute the rank.
  change rank (relabelBallot r0 σ) a = 0
  calc
    rank (relabelBallot r0 σ) a = rank r0 (σ a) := by
      simpa using (rank_relabelBallot (r := r0) (σ := σ) (c := a))
    _ = rank r0 m0 := by simp [hσa]
    _ = 0 := by
      have : rank (someLinearOrder A) m0 = (e m0).val := by
        simpa [r0] using (rank_someLinearOrder_eq_val (A := A) (c := m0))
      simpa [m0] using this

lemma rank_ballotWithTopTwo_second {A : Type} [Fintype A]
    (a b : A) (hcard : 2 ≤ Fintype.card A) (hab : a ≠ b) :
    rank (ballotWithTopTwo (A := A) a b hcard hab) b = 1 := by
  classical
  letI : Nonempty A := ⟨a⟩
  let r0 : LinearOrder A := someLinearOrder A
  let e := Fintype.equivFin A
  let n := Fintype.card A
  have hn1 : 1 < n := by have : n = Fintype.card A := rfl; omega
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_two (by simpa [n] using hcard)
  let m0 : A := e.symm ⟨0, hn0⟩
  let m1 : A := e.symm ⟨1, hn1⟩
  let σ1 : Equiv.Perm A := Equiv.swap a m0
  let σ2 : Equiv.Perm A := Equiv.swap (σ1 b) m1
  let σ : Equiv.Perm A := σ1.trans σ2

  have hσb : σ b = m1 := by
    -- σ b = σ2 (σ1 b) = m1 by definition of `swap`.
    simp [σ, Equiv.trans, σ2]

  change rank (relabelBallot r0 σ) b = 1
  calc
    rank (relabelBallot r0 σ) b = rank r0 (σ b) := by
      simpa using (rank_relabelBallot (r := r0) (σ := σ) (c := b))
    _ = rank r0 m1 := by simp [hσb]
    _ = 1 := by
      have : rank (someLinearOrder A) m1 = (e m1).val := by
        simpa [r0] using (rank_someLinearOrder_eq_val (A := A) (c := m1))
      simpa [m1] using this

lemma topRank_ballotWithTopTwo {A : Type} [Fintype A]
    (a b : A) (hcard : 2 ≤ Fintype.card A) (hab : a ≠ b) :
    (∀ d : A, d ≠ a → (ballotWithTopTwo (A := A) a b hcard hab).lt a d) := by
  classical
  have hr : rank (ballotWithTopTwo (A := A) a b hcard hab) a = 0 :=
    rank_ballotWithTopTwo_top (A := A) a b hcard hab
  exact (topRank_iff_rank_eq_zero (r := ballotWithTopTwo (A := A) a b hcard hab) (c := a)).2 hr

lemma prefers_second_over_others_ballotWithTopTwo {A : Type} [Fintype A]
    (a b c : A) (hcard : 3 ≤ Fintype.card A) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (ballotWithTopTwo (A := A) a b (by omega) hab).lt b c := by
  classical
  let r := ballotWithTopTwo (A := A) a b (by omega) hab
  have hrb : rank r b = 1 := rank_ballotWithTopTwo_second (A := A) a b (by omega) hab
  have hra : rank r a = 0 := rank_ballotWithTopTwo_top (A := A) a b (by omega) hab
  have hab_lt : r.lt a b := by
    by_contra hab'
    have hba : r.lt b a := lt_of_le_of_ne (le_of_not_gt hab') hab.symm
    have hlt := rank_lt_of_lt (r := r) (c := b) (d := a) hba
    have hlt' := hlt
    simp [hra, hrb] at hlt'
  exact prefers_second_over_others_of_rank_eq_one (r := r) (a := a) (b := b) (c := c)
    hrb hab_lt hca hcb

/-! ## Step (i): Outcome is a or b at certain profiles -/

/-- At a profile where v₁ ranks a > b and v₂ ranks b > a (with g dictating for v₁),
    the outcome of f must be either a or b. -/
lemma outcome_is_a_or_b
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
  (P : Profile V A) (a b : A)
    (hb_second_v1 : ∀ c, c ≠ a → c ≠ b → Prefers P v₁ b c)
    (hb_top_v2 : TopRank P v₂ b)
  :
    f P = {a} ∨ f P = {b} := by
  classical

  -- Let c be the (unique) winner at P.
  let c := theWinner f P hf
  have hc : f P = {c} := (eq_singleton_iff_theWinner_eq f P hf c).mpr rfl

  by_cases hca : c = a
  · left
    simpa [hca] using hc

  by_cases hcb : c = b
  · right
    simpa [hcb] using hc

  -- Otherwise (c ≠ a and c ≠ b), we show voter v₁ can manipulate by reporting v₂'s ballot.
  -- Build the reduced profile where voter v₁'s ballot is replaced by voter v₂'s ballot.
  let P' : Profile {w : V // w ≠ v₂} A :=
    { pref := fun w => if w.val = v₁ then P.pref v₂ else P.pref w.val }

  -- In P', voter ⟨v₁, hne⟩ has exactly voter v₂'s ballot, hence has b on top.
  have hb_top' : TopRank P' ⟨v₁, hne⟩ b := by
    have hpp : P'.pref ⟨v₁, hne⟩ = P.pref v₂ := if_pos rfl
    exact (topRank_congr_ballot P' P ⟨v₁, hne⟩ v₂ hpp b).mpr hb_top_v2

  have htopChoice' : topChoice P' ⟨v₁, hne⟩ = b := by
    symm
    exact topRank_eq_topChoice P' ⟨v₁, hne⟩ b hb_top'

  -- By dictatorship of the cloned rule g at v₁, f at the expanded profile is {b}.
  have hdictP' : clonedRule f v₁ v₂ hne P' = {b} := by
    simpa [htopChoice'] using hdict_g P'
  have hb_expanded : f (expandProfile v₁ v₂ hne P') = {b} := by
    simpa [clonedRule] using hdictP'

  -- The expanded profile equals P updated at v₁ with v₂'s ballot.
  have hexpand : expandProfile v₁ v₂ hne P' = updateProfile P v₁ (P.pref v₂) := by
    apply Profile.ext
    intro v
    by_cases hv2 : v = v₂
    · subst hv2
      rw [expandProfile_pref_v2, updateProfile_pref_of_ne P v₁ _ (Ne.symm hne)]
      exact if_pos rfl
    · rw [expandProfile_pref_of_ne v₁ v₂ hne P' hv2]
      by_cases hv1 : v = v₁
      · subst hv1
        rw [updateProfile_pref_self]
        exact if_pos rfl
      · rw [updateProfile_pref_of_ne P v₁ _ hv1]
        exact if_neg hv1

  have hb_update : f (updateProfile P v₁ (P.pref v₂)) = {b} := by
    simpa [hexpand] using hb_expanded

  -- Strategyproofness forbids v₁ from preferring the new outcome b over the old outcome c.
  have hnot : ¬ Prefers P v₁ b c :=
    hf_sp P v₁ (P.pref v₂) c b hc hb_update

  -- But by assumption, b is second for v₁, hence preferred to any c ≠ a,b.
  have hpref : Prefers P v₁ b c := hb_second_v1 c hca hcb
  exact (hnot hpref).elim

/-! ## Steps (i)-(iii): Paper-style lemmas on a fixed subprofile -/

/-!
The Bandhu–Kumar proof works with a fixed subprofile $\bar P_{-12}$.
In Lean we represent this by an arbitrary base profile `Pbar` and then overwrite
voters `v₁` and `v₂` with the “crossed top-two” ballots.

The next lemmas implement Steps (i)–(iii) of the paper for this fixed subprofile.
-/

/-- The “crossed top-two” profile from Step (i), based on a fixed `Pbar` for the other voters.

Voter `v₁` gets ballot `a > b > ...` and voter `v₂` gets ballot `b > a > ...`.
-/
noncomputable def crossedTopTwoProfile
    (hcard : 3 ≤ Fintype.card A)
    (Pbar : Profile V A) (v₁ v₂ : V) (a b : A) (hab : a ≠ b) : Profile V A := by
  classical
  have hcard2 : 2 ≤ Fintype.card A := by omega
  exact
    updateProfile
      (updateProfile Pbar v₁ (ballotWithTopTwo (A := A) a b hcard2 hab))
      v₂ (ballotWithTopTwo (A := A) b a hcard2 hab.symm)

omit [Nonempty A] in
lemma topRank_crossedTopTwoProfile_v2
    (hcard : 3 ≤ Fintype.card A)
    (Pbar : Profile V A) (v₁ v₂ : V) (a b : A) (hab : a ≠ b) :
    TopRank (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) v₂ b := by
  classical
  have hcard2 : 2 ≤ Fintype.card A := by omega
  intro d hd
  have hbal : (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab).pref v₂
      = ballotWithTopTwo (A := A) b a hcard2 hab.symm := by
    unfold crossedTopTwoProfile
    exact updateProfile_pref_self _ v₂ _
  unfold Prefers
  rw [hbal]
  exact topRank_ballotWithTopTwo (A := A) b a hcard2 hab.symm d hd

omit [Nonempty A] in
lemma prefers_b_over_others_crossedTopTwoProfile_v1
    (hcard : 3 ≤ Fintype.card A)
    (Pbar : Profile V A) (v₁ v₂ : V) (hne : v₁ ≠ v₂) (a b : A) (hab : a ≠ b) :
    ∀ c, c ≠ a → c ≠ b →
      Prefers (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) v₁ b c := by
  classical
  intro c hca hcb
  -- v₁'s ballot is `ballotWithTopTwo a b`, where b is second and beats all other c.
  have hbal : (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab).pref v₁
      = ballotWithTopTwo (A := A) a b (by omega) hab := by
    unfold crossedTopTwoProfile
    rw [updateProfile_pref_of_ne _ v₂ _ hne, updateProfile_pref_self]
  unfold Prefers
  rw [hbal]
  exact prefers_second_over_others_ballotWithTopTwo (A := A) a b c hcard hab hca hcb

/-- Step (i) (paper): at the crossed-top-two profile, the outcome is `a` or `b`.

This is exactly `outcome_is_a_or_b`, instantiated with the constructed ballots.
-/
lemma step_i_outcome_is_a_or_b
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A) (a b : A) (hab : a ≠ b) :
    f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {a} ∨
      f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {b} := by
  classical
  refine outcome_is_a_or_b
    (f := f) (hf := hf) (hf_sp := hf_sp)
    (v₁ := v₁) (v₂ := v₂) (hne := hne) (hdict_g := hdict_g)
    (P := crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab)
    (a := a) (b := b)
    (hb_second_v1 := prefers_b_over_others_crossedTopTwoProfile_v1 (V := V) (A := A) hcard Pbar v₁ v₂ hne a b hab)
    (hb_top_v2 := topRank_crossedTopTwoProfile_v2 (V := V) (A := A) hcard Pbar v₁ v₂ a b hab)

/-!
### Paper Step (ii)–(iii): voter 1 is decisive over `a` (at fixed `Pbar`).

The paper’s Step (iii) concludes that, once the canonical crossed profile yields `{a}`,
then *whenever voter 1 ranks `a` first*, the outcome is `{a}` for any ballot of voter 2.

* Step (ii): if voter 1 ranks `a` first and voter 2 ranks `b` first, outcome is `{a}`.
* Step (iii): for any ballot of voter 2, outcome is `{a}` whenever voter 1 ranks `a` first.
-/

/-- Update voters `v₁` and `v₂` on top of a fixed base profile `Pbar`.

This is the Lean analogue of “fix $\bar P_{-12}$ and vary voters 1 and 2”.
-/
noncomputable def setV1V2
    (Pbar : Profile V A) (v₁ v₂ : V)
    (ballot₁ ballot₂ : LinearOrder A) : Profile V A := by
  classical
  exact updateProfile (updateProfile Pbar v₁ ballot₁) v₂ ballot₂

/-- Step (ii) (paper): if voter 1 ranks `a` first and voter 2 ranks `b` first,
then the outcome is `{a}` (for the fixed subprofile `Pbar`). -/
lemma step_ii_case_a_v1_top_a_v2_top_b_outcome_a
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A)
    (a b : A) (hab : a ≠ b)
    (hfa : f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {a})
    (ballot₁' ballot₂' : LinearOrder A)
    (ha_top₁ : ∀ d, d ≠ a → ballot₁'.lt a d)
    (hb_top₂ : ∀ d, d ≠ b → ballot₂'.lt b d) :
    f (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') = {a} := by
  classical
  -- First, we show `{a}` when voter 1 uses the canonical ballot `a>b` and voter 2 uses `ballot₂'` (b-top).
  -- (This is the paper’s Step (ii) sub-argument: it cannot be `{b}`, else voter 2 manipulates at the crossed profile.)
  have hcard2 : 2 ≤ Fintype.card A := by omega
  let ballot_ab : LinearOrder A := ballotWithTopTwo (A := A) a b hcard2 hab
  have h_base : f (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') = {a} := by
    let P0 : Profile V A := setV1V2 Pbar v₁ v₂ ballot_ab ballot₂'
    let c := theWinner f P0 hf
    have hc : f P0 = {c} := (eq_singleton_iff_theWinner_eq f P0 hf c).mpr rfl

    by_cases hca : c = a
    · simpa [P0, hca] using hc

    -- Show the winner must be either `a` or `b` (since v₁ uses `a>b>...` and v₂ has `b` on top).
    have h_or : f P0 = {a} ∨ f P0 = {b} := by
      refine outcome_is_a_or_b
        (f := f) (hf := hf) (hf_sp := hf_sp)
        (v₁ := v₁) (v₂ := v₂) (hne := hne) (hdict_g := hdict_g)
        (P := P0)
        (a := a) (b := b)
        (hb_second_v1 := ?_) (hb_top_v2 := ?_)
      · intro c' hc'a hc'b
        have hbal : P0.pref v₁ = ballot_ab := by
          show (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂').pref v₁ = ballot_ab
          unfold setV1V2
          rw [updateProfile_pref_of_ne _ v₂ _ hne, updateProfile_pref_self]
        unfold Prefers
        rw [hbal]
        exact prefers_second_over_others_ballotWithTopTwo
          (A := A) (a := a) (b := b) (c := c') hcard hab hc'a hc'b
      · intro d hd
        have hbal : P0.pref v₂ = ballot₂' := by
          show (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂').pref v₂ = ballot₂'
          unfold setV1V2
          exact updateProfile_pref_self _ v₂ _
        unfold Prefers
        rw [hbal]
        exact hb_top₂ d hd

    -- Since `c ≠ a`, it must be `b`.
    have hcb : c = b := by
      rcases h_or with hA | hB
      · have : theWinner f P0 hf = a := (eq_singleton_iff_theWinner_eq f P0 hf a).1 hA
        exact (hca (by simpa [c] using this)).elim
      · have : theWinner f P0 hf = b := (eq_singleton_iff_theWinner_eq f P0 hf b).1 hB
        simpa [c] using this
    have hc_b : f P0 = {b} := by simpa [hcb] using hc

    -- If the outcome is `{b}`, voter 2 can manipulate at the crossed-top-two profile.
    let P_cross : Profile V A :=
      crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab
    have hb_top_orig : TopRank P_cross v₂ b :=
      topRank_crossedTopTwoProfile_v2 (V := V) (A := A) hcard Pbar v₁ v₂ a b hab
    have hpref : Prefers P_cross v₂ b a := by
      unfold Prefers
      exact hb_top_orig a (by simp [hab])
    have hupd : updateProfile P_cross v₂ ballot₂' = P0 := by
      show updateProfile (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab)
          v₂ ballot₂' = setV1V2 Pbar v₁ v₂ ballot_ab ballot₂'
      unfold crossedTopTwoProfile setV1V2
      rw [updateProfile_updateProfile_self]
    have hnot : ¬ Prefers P_cross v₂ b a :=
      hf_sp P_cross v₂ ballot₂' a b hfa (by simpa [hupd] using hc_b)
    exact (hnot hpref).elim

  -- Now show that at the profile with `ballot₁'` (a-top), the outcome must also be `{a}`:
  -- otherwise voter 1 would manipulate by misreporting `ballot_ab`.
  let P12 : Profile V A := setV1V2 Pbar v₁ v₂ ballot₁' ballot₂'
  let d := theWinner f P12 hf
  have hd : f P12 = {d} := (eq_singleton_iff_theWinner_eq f P12 hf d).mpr rfl
  by_cases hda : d = a
  · simpa [P12, hda] using hd
  have ha_pref : Prefers P12 v₁ a d := by
    -- voter 1's ballot in P12 is ballot₁'
    have hbal : P12.pref v₁ = ballot₁' := by
      show (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂').pref v₁ = ballot₁'
      unfold setV1V2
      rw [updateProfile_pref_of_ne _ v₂ _ hne, updateProfile_pref_self]
    unfold Prefers
    rw [hbal]
    exact ha_top₁ d hda
  have h_dev : f (updateProfile P12 v₁ ballot_ab) = {a} := by
    -- Updating v₁ to ballot_ab yields exactly the base profile handled above.
    have hupd : updateProfile P12 v₁ ballot_ab = setV1V2 Pbar v₁ v₂ ballot_ab ballot₂' := by
      show updateProfile (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₁ ballot_ab
          = setV1V2 Pbar v₁ v₂ ballot_ab ballot₂'
      unfold setV1V2
      rw [updateProfile_updateProfile_comm _ _ _ (Ne.symm hne),
          updateProfile_updateProfile_self]
    simpa [hupd] using h_base
  have hnot : ¬ Prefers P12 v₁ a d :=
    hf_sp P12 v₁ ballot_ab d a hd h_dev
  exact (hnot ha_pref).elim

/-- Step (iii) (paper): for any ballot of voter 2, if voter 1 ranks `a` first,
then the outcome is `{a}` (for the fixed subprofile `Pbar`). -/
lemma step_iii_case_a_v1_top_a_any_v2_outcome_a
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A)
    (a b : A) (hab : a ≠ b)
    (hfa : f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {a})
    (ballot₁' : LinearOrder A)
    (ha_top₁ : ∀ d, d ≠ a → ballot₁'.lt a d) :
    ∀ ballot₂'' : LinearOrder A,
      f (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂'') = {a} := by
  classical
  intro ballot₂''
  let P12 : Profile V A := setV1V2 Pbar v₁ v₂ ballot₁' ballot₂''
  let c := theWinner f P12 hf
  have hc : f P12 = {c} := (eq_singleton_iff_theWinner_eq f P12 hf c).mpr rfl
  by_cases hca : c = a
  · simpa [P12, hca] using hc

  -- Otherwise, c ≠ a. Build a ballot for voter 2 with top b and (if needed) c as second,
  -- so that voter 2 would prefer c to a, and hence could manipulate.
  have hcard2 : 2 ≤ Fintype.card A := by omega
  by_cases hcb : c = b
  · -- If c = b, pick any b-top ballot and derive the same contradiction.
    have hb_top₂ : ∀ d, d ≠ b → (ballotWithTopTwo (A := A) b a hcard2 hab.symm).lt b d :=
      topRank_ballotWithTopTwo (A := A) b a hcard2 hab.symm
    let ballot₂' : LinearOrder A := ballotWithTopTwo (A := A) b a hcard2 hab.symm
    have hP1 : f (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') = {a} :=
      step_ii_case_a_v1_top_a_v2_top_b_outcome_a
        (V := V) (A := A)
        hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a b hab hfa ballot₁' ballot₂' ha_top₁ hb_top₂
    have hc' : f P12 = {b} := by simpa [hcb] using hc
    have hpref : Prefers (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ b a := by
      -- v₂'s ballot at this profile is `ballot₂'` with b on top.
      have hbal : (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂').pref v₂ = ballot₂' := by
        unfold setV1V2
        exact updateProfile_pref_self _ v₂ _
      unfold Prefers
      rw [hbal]
      exact hb_top₂ a (by simp [hab])
    have hnot : ¬ Prefers (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ b a :=
      hf_sp (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ ballot₂'' a b hP1 (by
        -- updating v₂ twice is just the last update
        have hupd :
            updateProfile (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ ballot₂'' = P12 := by
          show updateProfile (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ ballot₂''
              = setV1V2 Pbar v₁ v₂ ballot₁' ballot₂''
          unfold setV1V2
          rw [updateProfile_updateProfile_self]
        simpa [hupd] using hc')
    exact (hnot hpref).elim
  · -- If c ≠ a and c ≠ b, pick ballot₂' with b top and c second.
    have hbc : b ≠ c := by simpa [ne_comm] using hcb
    let ballot₂' : LinearOrder A := ballotWithTopTwo (A := A) b c hcard2 hbc
    have hb_top₂ : ∀ d, d ≠ b → ballot₂'.lt b d :=
      topRank_ballotWithTopTwo (A := A) b c hcard2 hbc
    have hP1 : f (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') = {a} :=
      step_ii_case_a_v1_top_a_v2_top_b_outcome_a
        (V := V) (A := A)
        hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a b hab hfa ballot₁' ballot₂' ha_top₁ hb_top₂

    have hpref : Prefers (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ c a := by
      -- In ballot₂' = (b > c > ...), c beats a (since a ≠ b and a ≠ c).
      have hbal : (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂').pref v₂ = ballot₂' := by
        unfold setV1V2
        exact updateProfile_pref_self _ v₂ _
      unfold Prefers
      rw [hbal]
      refine prefers_second_over_others_ballotWithTopTwo
        (A := A) (a := b) (b := c) (c := a) hcard hbc ?_ ?_
      · exact hab
      · exact Ne.symm hca
    have hnot : ¬ Prefers (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ c a :=
      hf_sp (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ ballot₂'' a c hP1 (by
        have hupd :
            updateProfile (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ ballot₂'' = P12 := by
          show updateProfile (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ ballot₂''
              = setV1V2 Pbar v₁ v₂ ballot₁' ballot₂''
          unfold setV1V2
          rw [updateProfile_updateProfile_self]
        simpa [hupd] using hc)
    exact (hnot hpref).elim

/-
Now the symmetric case where the crossed-top-two profile yields `{b}`.
We need Steps (ii)–(iii) again, but with roles of `a` and `b` swapped.
-/
lemma step_ii_case_b_v1_top_a_v2_top_b_outcome_b
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A)
    (a b : A) (hab : a ≠ b)
    (hfb : f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {b})
    (ballot₁' ballot₂' : LinearOrder A)
    (ha_top₁ : ∀ d, d ≠ a → ballot₁'.lt a d)
    (hb_top₂ : ∀ d, d ≠ b → ballot₂'.lt b d) :
    f (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') = {b} := by
  classical
  have hcard2 : 2 ≤ Fintype.card A := by omega
  let ballot_ab : LinearOrder A := ballotWithTopTwo (A := A) a b hcard2 hab
  let ballot_ba : LinearOrder A := ballotWithTopTwo (A := A) b a hcard2 hab.symm

  -- First show the key base case: with voter 2 using the canonical `b>a` ballot, the outcome is `{b}`.
  have h_base : f (setV1V2 Pbar v₁ v₂ ballot₁' ballot_ba) = {b} := by
    let P0 : Profile V A := setV1V2 Pbar v₁ v₂ ballot₁' ballot_ba
    let c := theWinner f P0 hf
    have hc : f P0 = {c} := (eq_singleton_iff_theWinner_eq f P0 hf c).mpr rfl
    by_cases hcb : c = b
    · simpa [P0, hcb] using hc
    by_cases hca : c = a
    · -- If the outcome were `{a}`, voter 1 could manipulate at the crossed profile.
      let P_cross : Profile V A :=
        crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab
      have h_eq_cross : P_cross = setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba := by
        show crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab
            = setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba
        unfold crossedTopTwoProfile setV1V2
        rfl
      have hcross : f (setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba) = {b} := by
        rw [← h_eq_cross]; exact hfb

      -- Deviating v₁ at the crossed profile to `ballot₁'` yields `P0`.
      have hupd : updateProfile (setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba) v₁ ballot₁' = P0 := by
        show updateProfile (setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba) v₁ ballot₁'
            = setV1V2 Pbar v₁ v₂ ballot₁' ballot_ba
        unfold setV1V2
        rw [updateProfile_updateProfile_comm _ _ _ (Ne.symm hne),
            updateProfile_updateProfile_self]

      have hc_a : f P0 = {a} := by simpa [hca] using hc
      have hnot : ¬ Prefers (setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba) v₁ a b :=
        hf_sp (setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba) v₁ ballot₁' b a hcross (by
          simpa [hupd] using hc_a)
      have hpref : Prefers (setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba) v₁ a b := by
        have hbal : (setV1V2 Pbar v₁ v₂ ballot_ab ballot_ba).pref v₁ = ballot_ab := by
          unfold setV1V2
          rw [updateProfile_pref_of_ne _ v₂ _ hne, updateProfile_pref_self]
        unfold Prefers
        rw [hbal]
        have ha_top_ab : ∀ d, d ≠ a → ballot_ab.lt a d :=
          topRank_ballotWithTopTwo (A := A) a b hcard2 hab
        exact ha_top_ab b hab.symm
      exact (hnot hpref).elim

    -- Otherwise, c is neither a nor b. Voter 2 can deviate to match voter 1 and obtain `{a}`.
    have hca' : c ≠ a := by
      intro h
      exact (hca h).elim
    have hcb' : c ≠ b := hcb
    -- Show that if both voters report `ballot₁'`, the outcome is `{a}` via the cloned-rule dictatorship.
    let P_same : Profile V A := setV1V2 Pbar v₁ v₂ ballot₁' ballot₁'
    let P' : Profile {w : V // w ≠ v₂} A :=
      { pref := fun w => if w.val = v₁ then ballot₁' else Pbar.pref w.val }
    have ha_top' : TopRank P' ⟨v₁, hne⟩ a := by
      intro d hd
      -- At ⟨v₁, hne⟩, the ballot is exactly `ballot₁'`.
      have hbal : P'.pref ⟨v₁, hne⟩ = ballot₁' := if_pos rfl
      unfold Prefers
      rw [hbal]
      exact ha_top₁ d hd
    have htopChoice' : topChoice P' ⟨v₁, hne⟩ = a := by
      symm
      exact topRank_eq_topChoice P' ⟨v₁, hne⟩ a ha_top'
    have hdictP' : clonedRule f v₁ v₂ hne P' = {a} := by
      simpa [htopChoice'] using hdict_g P'
    have ha_same : f P_same = {a} := by
      have hexpand : expandProfile v₁ v₂ hne P' = P_same := by
        apply Profile.ext
        intro v
        show (expandProfile v₁ v₂ hne P').pref v
            = (setV1V2 Pbar v₁ v₂ ballot₁' ballot₁').pref v
        unfold setV1V2
        by_cases hv2 : v = v₂
        · subst hv2
          rw [expandProfile_pref_v2, updateProfile_pref_self]
          exact if_pos rfl
        · rw [expandProfile_pref_of_ne v₁ v₂ hne P' hv2]
          by_cases hv1 : v = v₁
          · subst hv1
            rw [updateProfile_pref_of_ne _ v₂ _ hv2, updateProfile_pref_self]
            exact if_pos rfl
          · rw [updateProfile_pref_of_ne _ v₂ _ hv2, updateProfile_pref_of_ne _ v₁ _ hv1]
            exact if_neg hv1
      -- unfold clonedRule and rewrite
      simpa [clonedRule, hexpand] using hdictP'

    have hupd_same : updateProfile P0 v₂ ballot₁' = P_same := by
      show updateProfile (setV1V2 Pbar v₁ v₂ ballot₁' ballot_ba) v₂ ballot₁'
          = setV1V2 Pbar v₁ v₂ ballot₁' ballot₁'
      unfold setV1V2
      rw [updateProfile_updateProfile_self]

    have hpref : Prefers P0 v₂ a c := by
      have hbal : P0.pref v₂ = ballot_ba := by
        show (setV1V2 Pbar v₁ v₂ ballot₁' ballot_ba).pref v₂ = ballot_ba
        unfold setV1V2
        exact updateProfile_pref_self _ v₂ _
      unfold Prefers
      rw [hbal]
      -- In ballot_ba = (b > a > ...), a beats any c ≠ a,b.
      refine prefers_second_over_others_ballotWithTopTwo
        (A := A) (a := b) (b := a) (c := c) hcard hab.symm ?_ ?_
      · exact hcb'
      · exact hca'
    have hnot : ¬ Prefers P0 v₂ a c :=
      hf_sp P0 v₂ ballot₁' c a hc (by simpa [hupd_same] using ha_same)
    exact (hnot hpref).elim

  -- Now prove the stated goal by showing voter 2 cannot profitably deviate to `ballot_ba`.
  let P12 : Profile V A := setV1V2 Pbar v₁ v₂ ballot₁' ballot₂'
  let d := theWinner f P12 hf
  have hd : f P12 = {d} := (eq_singleton_iff_theWinner_eq f P12 hf d).mpr rfl
  by_cases hdb : d = b
  · simpa [P12, hdb] using hd
  have hpref : Prefers P12 v₂ b d := by
    have hbal : P12.pref v₂ = ballot₂' := by
      show (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂').pref v₂ = ballot₂'
      unfold setV1V2
      exact updateProfile_pref_self _ v₂ _
    unfold Prefers
    rw [hbal]
    exact hb_top₂ d hdb
  have hupd : updateProfile P12 v₂ ballot_ba = setV1V2 Pbar v₁ v₂ ballot₁' ballot_ba := by
    show updateProfile (setV1V2 Pbar v₁ v₂ ballot₁' ballot₂') v₂ ballot_ba
        = setV1V2 Pbar v₁ v₂ ballot₁' ballot_ba
    unfold setV1V2
    rw [updateProfile_updateProfile_self]
  have hnot : ¬ Prefers P12 v₂ b d :=
    hf_sp P12 v₂ ballot_ba d b hd (by simpa [hupd] using h_base)
  exact (hnot hpref).elim

lemma step_iii_case_b_any_v1_v2_top_b_outcome_b
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A)
    (a b : A) (hab : a ≠ b)
    (hfb : f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {b})
    (ballot₂' : LinearOrder A)
    (hb_top₂ : ∀ d, d ≠ b → ballot₂'.lt b d) :
    ∀ ballot₁'' : LinearOrder A,
      f (setV1V2 Pbar v₁ v₂ ballot₁'' ballot₂') = {b} := by
  classical
  intro ballot₁''
  have hcard2 : 2 ≤ Fintype.card A := by omega

  let P12 : Profile V A := setV1V2 Pbar v₁ v₂ ballot₁'' ballot₂'
  let c := theWinner f P12 hf
  have hc : f P12 = {c} := (eq_singleton_iff_theWinner_eq f P12 hf c).mpr rfl

  by_cases hcb : c = b
  · simpa [P12, hcb] using hc

  -- Otherwise, `c ≠ b`. We build a “true” ballot for voter 1 with `a` on top and arranged so that
  -- voter 1 prefers `c` over `b`, while Step (ii) forces the truthful outcome to be `{b}`.
  by_cases hca : c = a
  · -- If `c = a`, take the canonical ballot `a>b>...` so voter 1 prefers `a` over `b`.
    let ballot_ab : LinearOrder A := ballotWithTopTwo (A := A) a b hcard2 hab
    have ha_top₁ : ∀ d, d ≠ a → ballot_ab.lt a d :=
      topRank_ballotWithTopTwo (A := A) a b hcard2 hab
    have htruth : f (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') = {b} :=
      step_ii_case_b_v1_top_a_v2_top_b_outcome_b
        (V := V) (A := A)
        hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a b hab hfb
        ballot_ab ballot₂' ha_top₁ hb_top₂
    have hupd : updateProfile (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') v₁ ballot₁'' = P12 := by
      show updateProfile (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') v₁ ballot₁''
          = setV1V2 Pbar v₁ v₂ ballot₁'' ballot₂'
      unfold setV1V2
      rw [updateProfile_updateProfile_comm _ _ _ (Ne.symm hne),
          updateProfile_updateProfile_self]
    have hmis : f (updateProfile (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') v₁ ballot₁'') = {a} := by
      simpa [hupd, hca] using hc
    have hnot : ¬ Prefers (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') v₁ a b :=
      hf_sp (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') v₁ ballot₁'' b a htruth hmis
    have hpref : Prefers (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂') v₁ a b := by
      have hbal : (setV1V2 Pbar v₁ v₂ ballot_ab ballot₂').pref v₁ = ballot_ab := by
        unfold setV1V2
        rw [updateProfile_pref_of_ne _ v₂ _ hne, updateProfile_pref_self]
      unfold Prefers
      rw [hbal]
      exact ha_top₁ b hab.symm
    exact (hnot hpref).elim
  · -- If `c ≠ a` and `c ≠ b`, take ballot `a>c>...` so voter 1 prefers `c` over `b`.
    have hac : a ≠ c := by
      intro h
      exact (hca h.symm).elim
    let ballot_ac : LinearOrder A := ballotWithTopTwo (A := A) a c hcard2 hac
    have ha_top₁ : ∀ d, d ≠ a → ballot_ac.lt a d :=
      topRank_ballotWithTopTwo (A := A) a c hcard2 hac
    have htruth : f (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂') = {b} :=
      step_ii_case_b_v1_top_a_v2_top_b_outcome_b
        (V := V) (A := A)
        hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a b hab hfb
        ballot_ac ballot₂' ha_top₁ hb_top₂
    have hupd : updateProfile (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂') v₁ ballot₁'' = P12 := by
      show updateProfile (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂') v₁ ballot₁''
          = setV1V2 Pbar v₁ v₂ ballot₁'' ballot₂'
      unfold setV1V2
      rw [updateProfile_updateProfile_comm _ _ _ (Ne.symm hne),
          updateProfile_updateProfile_self]
    have hmis : f (updateProfile (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂') v₁ ballot₁'') = {c} := by
      simpa [hupd] using hc
    have hnot : ¬ Prefers (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂') v₁ c b :=
      hf_sp (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂') v₁ ballot₁'' b c htruth hmis
    have hpref : Prefers (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂') v₁ c b := by
      have hbal : (setV1V2 Pbar v₁ v₂ ballot_ac ballot₂').pref v₁ = ballot_ac := by
        unfold setV1V2
        rw [updateProfile_pref_of_ne _ v₂ _ hne, updateProfile_pref_self]
      have hbc : b ≠ c := by
        intro h
        exact hcb h.symm
      unfold Prefers
      rw [hbal]
      refine prefers_second_over_others_ballotWithTopTwo
        (A := A) (a := a) (b := c) (c := b) hcard hac hab.symm hbc
    exact (hnot hpref).elim

/-!
### Consequence of Steps (i)–(iii): decisiveness for a pair (a,b) with fixed `Pbar`.

Fix a base profile `Pbar` for all voters other than `v₁,v₂`.

Call `v₁` **`a`-decisive** (relative to `Pbar`) if, whenever `v₁` ranks `a` top,
the outcome is `{a}` for *any* ballot of `v₂`.
Similarly, call `v₂` **`b`-decisive** if, whenever `v₂` ranks `b` top,
the outcome is `{b}` for *any* ballot of `v₁`.

The two Step (iii) lemmas together imply that for any distinct alternatives `(a,b)`,
either `v₁` is `a`-decisive or `v₂` is `b`-decisive.
-/

/-- `v₁` is `x`-decisive (relative to fixed `Pbar`) if whenever `v₁` ranks `x` top,
the outcome is `{x}` for any ballot of `v₂`. -/
def V1DecisiveAt
    (Pbar : Profile V A) (f : VotingRule) (v₁ v₂ : V) (x : A) : Prop :=
  ∀ ballot₁ : LinearOrder A,
    (∀ d, d ≠ x → ballot₁.lt x d) →
    ∀ ballot₂ : LinearOrder A,
      f (setV1V2 Pbar v₁ v₂ ballot₁ ballot₂) = {x}

/-- `v₂` is `x`-decisive (relative to fixed `Pbar`) if whenever `v₂` ranks `x` top,
the outcome is `{x}` for any ballot of `v₁`. -/
def V2DecisiveAt
    (Pbar : Profile V A) (f : VotingRule) (v₁ v₂ : V) (x : A) : Prop :=
  ∀ ballot₂ : LinearOrder A,
    (∀ d, d ≠ x → ballot₂.lt x d) →
    ∀ ballot₁ : LinearOrder A,
      f (setV1V2 Pbar v₁ v₂ ballot₁ ballot₂) = {x}

/-- `v₁` is fully decisive (relative to fixed `Pbar`) if it is decisive for every alternative. -/
def V1FullyDecisiveAt
    (Pbar : Profile V A) (f : VotingRule) (v₁ v₂ : V) : Prop :=
  ∀ x : A, V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x

/-- `v₂` is fully decisive (relative to fixed `Pbar`) if it is decisive for every alternative. -/
def V2FullyDecisiveAt
    (Pbar : Profile V A) (f : VotingRule) (v₁ v₂ : V) : Prop :=
  ∀ x : A, V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x

lemma step_iii_pair_decisiveness
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A)
    (a b : A) (hab : a ≠ b) :
    V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ a ∨
      V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ b := by
  classical
  have h_cross :
      f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {a} ∨
        f (crossedTopTwoProfile (V := V) (A := A) hcard Pbar v₁ v₂ a b hab) = {b} :=
    step_i_outcome_is_a_or_b
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a b hab
  rcases h_cross with hfa | hfb
  · left
    intro ballot₁ ha_top₁ ballot₂
    exact (step_iii_case_a_v1_top_a_any_v2_outcome_a
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a b hab
      hfa ballot₁ ha_top₁ ballot₂)
  · right
    intro ballot₂ hb_top₂ ballot₁
    exact (step_iii_case_b_any_v1_v2_top_b_outcome_b
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a b hab
      hfb ballot₂ hb_top₂ ballot₁)

/-!
### Step (iv) (paper): `v₁` and `v₂` cannot be decisive for distinct alternatives.

If `v₁` is `x`-decisive and `v₂` is `y`-decisive (relative to the same fixed `Pbar`),
then necessarily `x = y`.

In particular, there do not exist distinct `x,y` such that `v₁` is `x`-decisive
and `v₂` is `y`-decisive.
-/

omit [DecidableEq V] [Nonempty A] in
lemma step_iv_v1_v2_decisive_implies_eq
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule)
    (Pbar : Profile V A) (v₁ v₂ : V)
    (x y : A)
    (hx : V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x)
    (hy : V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ y) :
    x = y := by
  classical
  have hcard2 : 2 ≤ Fintype.card A := by omega
  by_cases hxy : x = y
  · exact hxy

  let ballot_xy : LinearOrder A := ballotWithTopTwo (A := A) x y hcard2 hxy
  let ballot_yx : LinearOrder A := ballotWithTopTwo (A := A) y x hcard2 (Ne.symm hxy)
  have hx_top : ∀ d, d ≠ x → ballot_xy.lt x d :=
    topRank_ballotWithTopTwo (A := A) x y hcard2 hxy
  have hy_top : ∀ d, d ≠ y → ballot_yx.lt y d :=
    topRank_ballotWithTopTwo (A := A) y x hcard2 (Ne.symm hxy)

  have hx_out : f (setV1V2 Pbar v₁ v₂ ballot_xy ballot_yx) = {x} :=
    hx ballot_xy hx_top ballot_yx
  have hy_out : f (setV1V2 Pbar v₁ v₂ ballot_xy ballot_yx) = {y} :=
    hy ballot_yx hy_top ballot_xy

  have hsing : ({x} : Finset A) = {y} := by
    simpa [hx_out] using hy_out
  -- contradict `x ≠ y`
  exact (hxy (by
    simpa using (Finset.singleton_inj.1 hsing))).elim

omit [DecidableEq V] [Nonempty A] in
lemma step_iv_no_distinct_v1_v2_decisive
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule)
    (Pbar : Profile V A) (v₁ v₂ : V)
    (x y : A) (hxy : x ≠ y) :
    ¬ (V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x ∧
        V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ y) := by
  intro h
  have : x = y :=
    step_iv_v1_v2_decisive_implies_eq (V := V) (A := A) hcard f Pbar v₁ v₂ x y h.1 h.2
  exact hxy this

/-!
### Step (iv) (paper): one voter is decisive for all alternatives.

Combining `step_iii_pair_decisiveness` with the incompatibility of being decisive for
distinct alternatives, we obtain the dichotomy:

* either `v₁` is `x`-decisive for every `x`,
* or `v₂` is `x`-decisive for every `x`.
-/

lemma step_iv_global_decisiveness
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A) :
    (∀ x : A, V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x) ∨
      (∀ x : A, V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x) := by
  classical
  by_cases hV1 : ∀ x : A, V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x
  · exact Or.inl hV1
  by_cases hV2 : ∀ x : A, V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x
  · exact Or.inr hV2

  -- pick witnesses of non-decisiveness for each voter
  rcases not_forall.1 hV1 with ⟨x, hx⟩
  rcases not_forall.1 hV2 with ⟨y, hy⟩

  by_cases hxy : x = y
  · subst hxy
    -- From `3 ≤ card A`, pick three pairwise-distinct elements u,v,w.
    let n := Fintype.card A
    let e := Fintype.equivFin A
    have hn0 : 0 < n := by
      have : 1 ≤ n := by omega
      exact Nat.pos_of_ne_zero (by
        intro hz
        have : n = 0 := hz
        omega)
    have hn1 : 1 < n := by omega
    have hn2 : 2 < n := by omega
    let u : A := e.symm ⟨0, hn0⟩
    let v : A := e.symm ⟨1, hn1⟩
    let w : A := e.symm ⟨2, hn2⟩

    have huv : u ≠ v := by
      intro h
      have : (⟨0, hn0⟩ : Fin n) = ⟨1, hn1⟩ := by
        simpa [u, v] using congrArg e h
      exact Nat.zero_ne_one (congrArg Fin.val this)
    have huw : u ≠ w := by
      intro h
      have : (⟨0, hn0⟩ : Fin n) = ⟨2, hn2⟩ := by
        simpa [u, w] using congrArg e h
      have : (0 : Nat) = 2 := congrArg Fin.val this
      exact (by decide : (0 : Nat) ≠ 2) this
    have hvw : v ≠ w := by
      intro h
      have : (⟨1, hn1⟩ : Fin n) = ⟨2, hn2⟩ := by
        simpa [v, w] using congrArg e h
      have : (1 : Nat) = 2 := congrArg Fin.val this
      exact (by decide : (1 : Nat) ≠ 2) this

    -- Among u,v,w at most one can equal x, so pick a,b distinct from x.
    have hab_exists : ∃ a b : A, a ≠ x ∧ b ≠ x ∧ a ≠ b := by
      by_cases hxu : x = u
      · refine ⟨v, w, ?_, ?_, hvw⟩
        · intro hxv; exact huv (by simpa [hxu] using hxv.symm)
        · intro hxw; exact huw (by simpa [hxu] using hxw.symm)
      · by_cases hxv : x = v
        · refine ⟨u, w, Ne.symm hxu, ?_, huw⟩
          intro hxw; exact hvw (by simpa [hxv] using hxw.symm)
        · -- x is neither u nor v, so take (u,v)
          refine ⟨u, v, Ne.symm hxu, Ne.symm hxv, huv⟩

    rcases hab_exists with ⟨a, b, hax, hbx, hab⟩

    -- Apply pair decisiveness to (a,x) and (x,b), using the non-decisiveness hypotheses.
    have hxV2 : ¬ V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x := hy
    have hxV1 : ¬ V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ x := hx

    have ha_dec : V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ a := by
      have hpair :=
        step_iii_pair_decisiveness
          (V := V) (A := A)
          hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar a x hax
      rcases hpair with ha | hx2
      · exact ha
      · exact (hxV2 hx2).elim

    have hb_dec : V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ b := by
      have hpair :=
        step_iii_pair_decisiveness
          (V := V) (A := A)
          hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar x b (Ne.symm hbx)
      rcases hpair with hx1 | hb
      · exact (hxV1 hx1).elim
      · exact hb

    -- Contradiction: v₁ decisive for a and v₂ decisive for b with a ≠ b.
    have hcontra :
        ¬ (V1DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ a ∧
            V2DecisiveAt (V := V) (A := A) Pbar f v₁ v₂ b) :=
      step_iv_no_distinct_v1_v2_decisive
        (V := V) (A := A) hcard f Pbar v₁ v₂ a b hab
    exact (hcontra ⟨ha_dec, hb_dec⟩).elim
  · -- x ≠ y: pair decisiveness for (x,y) contradicts the chosen witnesses.
    have hpair :=
      step_iii_pair_decisiveness
        (V := V) (A := A)
        hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar x y hxy
    rcases hpair with hx' | hy'
    · exact (hx hx').elim
    · exact (hy hy').elim

lemma step_iv_global_fully_decisive
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩})
    (Pbar : Profile V A) :
    V1FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂ ∨
      V2FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂ := by
  classical
  simpa [V1FullyDecisiveAt, V2FullyDecisiveAt] using
    (step_iv_global_decisiveness
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne hdict_g Pbar)

/-!
## Step (v) (paper): full decisiveness is independent of the sub-profile.

We prove that for any two base profiles `Pbar` and `Pbar'` (for voters other than `v₁,v₂`),
if `v₁` is fully decisive at `Pbar` then `v₁` is fully decisive at `Pbar'`.

This is done by induction on the number of voters (other than `v₁,v₂`) where `Pbar`
and `Pbar'` disagree.
-/

/-- The set of voters (excluding `v₁,v₂`) whose ballots differ between `Pbar` and `Pbar'`. -/
noncomputable def diffVoters
    (Pbar Pbar' : Profile V A) (v₁ v₂ : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ v₁ ∧ v ≠ v₂ ∧ Pbar.pref v ≠ Pbar'.pref v)

omit [Nonempty A] in
lemma diffVoters_mem_iff
    (Pbar Pbar' : Profile V A) (v₁ v₂ v : V) :
    v ∈ diffVoters (V := V) (A := A) Pbar Pbar' v₁ v₂ ↔
      v ≠ v₁ ∧ v ≠ v₂ ∧ Pbar.pref v ≠ Pbar'.pref v := by
  classical
  simp [diffVoters]

omit [Nonempty A] in
lemma diffVoters_updateProfile_eq_erase
    (Pbar Pbar' : Profile V A) (v₁ v₂ v₃ : V)
    (hv₁ : v₃ ≠ v₁) (hv₂ : v₃ ≠ v₂)
    (hv : v₃ ∈ diffVoters (V := V) (A := A) Pbar Pbar' v₁ v₂) :
    diffVoters (V := V) (A := A)
        (updateProfile Pbar v₃ (Pbar'.pref v₃)) Pbar' v₁ v₂
      = (diffVoters (V := V) (A := A) Pbar Pbar' v₁ v₂).erase v₃ := by
  classical
  ext v
  by_cases hve : v = v₃
  · subst hve
    simp [diffVoters, hv₁, hv₂, updateProfile]
  · simp [diffVoters, updateProfile, hve]

/-!
### Step (v), one-voter change: if `v₁` is fully decisive, changing one other voter’s ballot
preserves full decisiveness.
-/

lemma step_v_change_one_voter_v1
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ v₃ : V)
    (hne12 : v₁ ≠ v₂)
    (hne13 : v₃ ≠ v₁) (hne23 : v₃ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne12 P' = {topChoice P' ⟨v₁, hne12⟩})
    (Pbar : Profile V A)
    (hv1full : V1FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂)
    (ballot₃' : LinearOrder A) :
    V1FullyDecisiveAt (V := V) (A := A)
      (updateProfile Pbar v₃ ballot₃') f v₁ v₂ := by
  classical
  have hcard2 : 2 ≤ Fintype.card A := by omega
  -- Pick two distinct alternatives and orient them according to voter v₃'s (old) ballot.
  let z0 : A := Classical.choice (inferInstance : Nonempty A)
  have hone : 1 < Fintype.card A := by omega
  obtain ⟨w0, hw0⟩ := Fintype.exists_ne_of_one_lt_card (α := A) hone z0
  let r3 : LinearOrder A := Pbar.pref v₃
  let w : A := if r3.lt w0 z0 then w0 else z0
  let z : A := if r3.lt w0 z0 then z0 else w0
  have hwz : r3.lt w z := by
    by_cases hlt : r3.lt w0 z0
    · simp [w, z, hlt]
    · have hzlt : r3.lt z0 w0 := by
        have : z0 ≠ w0 := by simpa [ne_comm] using hw0
        exact lt_of_le_of_ne (le_of_not_gt hlt) this
      simp [w, z, hlt, hzlt]
  have hwz_ne : z ≠ w := by
    intro h
    have hwz' : r3.lt w w := by
      simp [h] at hwz
    exact lt_irrefl _ hwz'

  let ballot_zw : LinearOrder A := ballotWithTopTwo (A := A) z w hcard2 hwz_ne
  let ballot_wz : LinearOrder A := ballotWithTopTwo (A := A) w z hcard2 (Ne.symm hwz_ne)

  -- At the old base profile, `v₁` fully decisive forces outcome `{z}`.
  have hz_top : ∀ d, d ≠ z → ballot_zw.lt z d :=
    topRank_ballotWithTopTwo (A := A) z w hcard2 hwz_ne
  have h_old : f (setV1V2 Pbar v₁ v₂ ballot_zw ballot_wz) = {z} := by
    -- use full decisiveness at `z`
    exact (hv1full z) ballot_zw hz_top ballot_wz

  -- Consider the crossed profile built over the updated base.
  let Pnew : Profile V A := setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_zw ballot_wz

  -- Step (i): at `Pnew`, the outcome is either `{z}` or `{w}`.
  have hw_top₂ : TopRank Pnew v₂ w := by
    intro d hd
    have hbal : Pnew.pref v₂ = ballot_wz := by
      show (setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_zw ballot_wz).pref v₂
          = ballot_wz
      unfold setV1V2
      exact updateProfile_pref_self _ v₂ _
    unfold Prefers
    rw [hbal]
    exact (topRank_ballotWithTopTwo (A := A) w z hcard2 (Ne.symm hwz_ne)) d hd
  have hw_second_v1 : ∀ c, c ≠ z → c ≠ w → Prefers Pnew v₁ w c := by
    intro c hcz hcw
    have hbal : Pnew.pref v₁ = ballot_zw := by
      show (setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_zw ballot_wz).pref v₁
          = ballot_zw
      unfold setV1V2
      rw [updateProfile_pref_of_ne _ v₂ _ hne12, updateProfile_pref_self]
    unfold Prefers
    rw [hbal]
    exact prefers_second_over_others_ballotWithTopTwo
      (A := A) (a := z) (b := w) (c := c) hcard hwz_ne hcz hcw

  have h_or : f Pnew = {z} ∨ f Pnew = {w} := by
    refine outcome_is_a_or_b
      (V := V) (A := A)
      (f := f) (hf := hf) (hf_sp := hf_sp)
      (v₁ := v₁) (v₂ := v₂) (hne := hne12) (hdict_g := hdict_g)
      (P := Pnew) (a := z) (b := w)
      (hb_second_v1 := hw_second_v1) (hb_top_v2 := hw_top₂)

  -- Show the outcome cannot be `{w}`, else voter `v₃` manipulates at the old profile.
  have h_new : f Pnew = {z} := by
    rcases h_or with hz | hw
    · exact hz
    · -- If the updated profile yields `{w}`, voter `v₃` can obtain `{w}` by reporting `ballot₃'`.
      let Pold : Profile V A := setV1V2 Pbar v₁ v₂ ballot_zw ballot_wz
      have hupd : updateProfile Pold v₃ ballot₃' = Pnew := by
        show updateProfile (setV1V2 Pbar v₁ v₂ ballot_zw ballot_wz) v₃ ballot₃'
            = setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_zw ballot_wz
        unfold setV1V2
        rw [updateProfile_updateProfile_comm _ v₂ v₃ (Ne.symm hne23),
            updateProfile_updateProfile_comm _ v₁ v₃ (Ne.symm hne13)]

      have hpref : Prefers Pold v₃ w z := by
        -- At voter v₃, the ballot is still the old `r3` (Pold agrees with Pbar at v₃).
        have hbal : Pold.pref v₃ = Pbar.pref v₃ := by
          show (setV1V2 Pbar v₁ v₂ ballot_zw ballot_wz).pref v₃ = Pbar.pref v₃
          unfold setV1V2
          rw [updateProfile_pref_of_ne _ v₂ _ hne23, updateProfile_pref_of_ne _ v₁ _ hne13]
        unfold Prefers
        rw [hbal]
        exact hwz

      have hnot : ¬ Prefers Pold v₃ w z :=
        hf_sp Pold v₃ ballot₃' z w h_old (by simpa [hupd] using hw)
      exact (hnot hpref).elim

  -- From the crossed profile outcome `{z}`, Step (iii) gives that `v₁` is `z`-decisive at the new base.
  have hz_dec_new : V1DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ z := by
    intro ballot₁ hz_top₁ ballot₂
    -- instantiate Step (iii) with a=z, b=w and the crossed outcome `h_new`
    have hcross_eq :
        crossedTopTwoProfile (V := V) (A := A) hcard (updateProfile Pbar v₃ ballot₃') v₁ v₂ z w hwz_ne = Pnew := by
      show crossedTopTwoProfile (V := V) (A := A) hcard (updateProfile Pbar v₃ ballot₃') v₁ v₂ z w hwz_ne
          = setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_zw ballot_wz
      unfold crossedTopTwoProfile setV1V2
      rfl
    have hfa' :
        f (crossedTopTwoProfile (V := V) (A := A) hcard (updateProfile Pbar v₃ ballot₃') v₁ v₂ z w hwz_ne) = {z} := by
      rw [hcross_eq]; exact h_new
    exact (step_iii_case_a_v1_top_a_any_v2_outcome_a
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne12 hdict_g
      (updateProfile Pbar v₃ ballot₃') z w hwz_ne
      hfa' ballot₁ hz_top₁ ballot₂)

  -- Apply Step (iv) at the new base: either v₁ is fully decisive or v₂ is fully decisive.
  have hglobal :=
    step_iv_global_fully_decisive
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne12 hdict_g (updateProfile Pbar v₃ ballot₃')
  rcases hglobal with hV1 | hV2
  · exact hV1
  · -- If v₂ were fully decisive, it would be `w`-decisive, contradicting Step (iv) incompatibility.
    have hw_dec : V2DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ w := hV2 w
    have hcontra :
        ¬ (V1DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ z ∧
            V2DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ w) :=
      step_iv_no_distinct_v1_v2_decisive
        (V := V) (A := A) hcard f (updateProfile Pbar v₃ ballot₃') v₁ v₂ z w hwz_ne
    exact (hcontra ⟨hz_dec_new, hw_dec⟩).elim

lemma step_v_change_one_voter_v2
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ v₃ : V)
    (hne12 : v₁ ≠ v₂)
    (hne13 : v₃ ≠ v₁) (hne23 : v₃ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne12 P' = {topChoice P' ⟨v₁, hne12⟩})
    (Pbar : Profile V A)
    (hv2full : V2FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂)
    (ballot₃' : LinearOrder A) :
    V2FullyDecisiveAt (V := V) (A := A)
      (updateProfile Pbar v₃ ballot₃') f v₁ v₂ := by
  classical
  have hcard2 : 2 ≤ Fintype.card A := by omega
  -- Pick two distinct alternatives and orient them according to voter v₃'s (old) ballot.
  let z0 : A := Classical.choice (inferInstance : Nonempty A)
  have hone : 1 < Fintype.card A := by omega
  obtain ⟨w0, hw0⟩ := Fintype.exists_ne_of_one_lt_card (α := A) hone z0
  let r3 : LinearOrder A := Pbar.pref v₃
  let w : A := if r3.lt w0 z0 then w0 else z0
  let z : A := if r3.lt w0 z0 then z0 else w0
  have hwz : r3.lt w z := by
    by_cases hlt : r3.lt w0 z0
    · simp [w, z, hlt]
    · have hzlt : r3.lt z0 w0 := by
        have : z0 ≠ w0 := by simpa [ne_comm] using hw0
        exact lt_of_le_of_ne (le_of_not_gt hlt) this
      simp [w, z, hlt, hzlt]
  have hwz_ne : z ≠ w := by
    intro h
    have hwz' : r3.lt w w := by
      simp [h] at hwz
    exact lt_irrefl _ hwz'

  let ballot_zw : LinearOrder A := ballotWithTopTwo (A := A) z w hcard2 hwz_ne
  let ballot_wz : LinearOrder A := ballotWithTopTwo (A := A) w z hcard2 (Ne.symm hwz_ne)

  -- At the old base profile, `v₂` fully decisive forces outcome `{z}`.
  have hz_top : ∀ d, d ≠ z → ballot_zw.lt z d :=
    topRank_ballotWithTopTwo (A := A) z w hcard2 hwz_ne
  have h_old : f (setV1V2 Pbar v₁ v₂ ballot_wz ballot_zw) = {z} := by
    -- use full decisiveness at `z`
    exact (hv2full z) ballot_zw hz_top ballot_wz

  -- Consider the crossed profile built over the updated base.
  let Pnew : Profile V A := setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_wz ballot_zw

  -- Step (i): at `Pnew`, the outcome is either `{z}` or `{w}`.
  have hz_top₂ : TopRank Pnew v₂ z := by
    intro d hd
    have hbal : Pnew.pref v₂ = ballot_zw := by
      show (setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_wz ballot_zw).pref v₂
          = ballot_zw
      unfold setV1V2
      exact updateProfile_pref_self _ v₂ _
    unfold Prefers
    rw [hbal]
    exact (topRank_ballotWithTopTwo (A := A) z w hcard2 hwz_ne) d hd
  have hz_second_v1 : ∀ c, c ≠ w → c ≠ z → Prefers Pnew v₁ z c := by
    intro c hcw hcz
    have hbal : Pnew.pref v₁ = ballot_wz := by
      show (setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_wz ballot_zw).pref v₁
          = ballot_wz
      unfold setV1V2
      rw [updateProfile_pref_of_ne _ v₂ _ hne12, updateProfile_pref_self]
    unfold Prefers
    rw [hbal]
    exact prefers_second_over_others_ballotWithTopTwo
      (A := A) (a := w) (b := z) (c := c) hcard (Ne.symm hwz_ne) hcw hcz

  have h_or : f Pnew = {w} ∨ f Pnew = {z} := by
    refine outcome_is_a_or_b
      (V := V) (A := A)
      (f := f) (hf := hf) (hf_sp := hf_sp)
      (v₁ := v₁) (v₂ := v₂) (hne := hne12) (hdict_g := hdict_g)
      (P := Pnew) (a := w) (b := z)
      (hb_second_v1 := hz_second_v1) (hb_top_v2 := hz_top₂)

  -- Show the outcome cannot be `{w}`, else voter `v₃` manipulates at the old profile.
  have h_new : f Pnew = {z} := by
    rcases h_or with hw | hz
    · -- If the updated profile yields `{w}`, voter `v₃` can obtain `{w}` by reporting `ballot₃'`.
      let Pold : Profile V A := setV1V2 Pbar v₁ v₂ ballot_wz ballot_zw
      have hupd : updateProfile Pold v₃ ballot₃' = Pnew := by
        show updateProfile (setV1V2 Pbar v₁ v₂ ballot_wz ballot_zw) v₃ ballot₃'
            = setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_wz ballot_zw
        unfold setV1V2
        rw [updateProfile_updateProfile_comm _ v₂ v₃ (Ne.symm hne23),
            updateProfile_updateProfile_comm _ v₁ v₃ (Ne.symm hne13)]

      have hpref : Prefers Pold v₃ w z := by
        -- At voter v₃, the ballot is still the old `r3` (Pold agrees with Pbar at v₃).
        have hbal : Pold.pref v₃ = Pbar.pref v₃ := by
          show (setV1V2 Pbar v₁ v₂ ballot_wz ballot_zw).pref v₃ = Pbar.pref v₃
          unfold setV1V2
          rw [updateProfile_pref_of_ne _ v₂ _ hne23, updateProfile_pref_of_ne _ v₁ _ hne13]
        unfold Prefers
        rw [hbal]
        exact hwz

      have hnot : ¬ Prefers Pold v₃ w z :=
        hf_sp Pold v₃ ballot₃' z w h_old (by simpa [hupd] using hw)
      exact (hnot hpref).elim
    · exact hz

  -- From the crossed profile outcome `{z}`, Step (iii) gives that `v₁` is `z`-decisive at the new base.
  have hz_dec_new : V2DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ z := by
    intro ballot₂ hz_top₂ ballot₁
    -- instantiate Step (iii) (case b) with a = w, b = z and the crossed outcome `h_new`
    have hcross_eq :
        crossedTopTwoProfile (V := V) (A := A) hcard (updateProfile Pbar v₃ ballot₃') v₁ v₂ w z (Ne.symm hwz_ne) = Pnew := by
      show crossedTopTwoProfile (V := V) (A := A) hcard (updateProfile Pbar v₃ ballot₃') v₁ v₂ w z (Ne.symm hwz_ne)
          = setV1V2 (updateProfile Pbar v₃ ballot₃') v₁ v₂ ballot_wz ballot_zw
      unfold crossedTopTwoProfile setV1V2
      rfl
    have hfb' :
        f (crossedTopTwoProfile (V := V) (A := A) hcard (updateProfile Pbar v₃ ballot₃') v₁ v₂ w z (Ne.symm hwz_ne)) = {z} := by
      rw [hcross_eq]; exact h_new
    exact (step_iii_case_b_any_v1_v2_top_b_outcome_b
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne12 hdict_g
      (updateProfile Pbar v₃ ballot₃') w z (Ne.symm hwz_ne)
      hfb' ballot₂ hz_top₂ ballot₁)

  -- Apply Step (iv) at the new base: either v₁ is fully decisive or v₂ is fully decisive.
  have hglobal :=
    step_iv_global_fully_decisive
      (V := V) (A := A)
      hcard f hf hf_sp v₁ v₂ hne12 hdict_g (updateProfile Pbar v₃ ballot₃')
  rcases hglobal with hV1 | hV2
  · -- If v₁ were fully decisive, it would be `w`-decisive, contradicting Step (iv) incompatibility.
    have hw_dec : V1DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ w := hV1 w
    have hcontra :
        ¬ (V1DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ w ∧
            V2DecisiveAt (V := V) (A := A) (updateProfile Pbar v₃ ballot₃') f v₁ v₂ z) :=
      step_iv_no_distinct_v1_v2_decisive
        (V := V) (A := A) hcard f (updateProfile Pbar v₃ ballot₃') v₁ v₂ w z (Ne.symm hwz_ne)
    exact (hcontra ⟨hw_dec, hz_dec_new⟩).elim
  · exact hV2

lemma step_v_invariant_v1
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne12 : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne12 P' = {topChoice P' ⟨v₁, hne12⟩})
    (Pbar Pbar' : Profile V A) :
    V1FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂ →
      V1FullyDecisiveAt (V := V) (A := A) Pbar' f v₁ v₂ := by
  classical
  -- Induction on the number of differing voters.
  have main :
      ∀ n : Nat,
        ∀ P : Profile V A,
          (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).card = n →
            V1FullyDecisiveAt (V := V) (A := A) P f v₁ v₂ →
              V1FullyDecisiveAt (V := V) (A := A) Pbar' f v₁ v₂ := by
    intro n
    induction n with
    | zero =>
      intro P hcard0 hfull
      -- If there are no differing voters, `setV1V2` profiles built from `P` and `Pbar'` coincide.
      have hD0 : diffVoters (V := V) (A := A) P Pbar' v₁ v₂ = ∅ := by
        exact Finset.card_eq_zero.mp (by simpa using hcard0)
      -- Show ballots agree for all voters except v₁,v₂.
      have hagree : ∀ v : V, v ≠ v₁ → v ≠ v₂ → P.pref v = Pbar'.pref v := by
        intro v hv1 hv2
        by_contra hne
        have : v ∈ diffVoters (V := V) (A := A) P Pbar' v₁ v₂ := by
          have : v ∈ Finset.univ.filter (fun u => u ≠ v₁ ∧ u ≠ v₂ ∧ P.pref u ≠ Pbar'.pref u) := by
            simp [hv1, hv2, hne]
          simpa [diffVoters] using this
        simp [hD0] at this
      -- Now transfer full decisiveness by rewriting the underlying profile.
      intro x ballot₁ hx_top ballot₂
      have : setV1V2 P v₁ v₂ ballot₁ ballot₂ = setV1V2 Pbar' v₁ v₂ ballot₁ ballot₂ := by
        apply Profile.ext
        intro v
        show (setV1V2 P v₁ v₂ ballot₁ ballot₂).pref v
            = (setV1V2 Pbar' v₁ v₂ ballot₁ ballot₂).pref v
        unfold setV1V2
        by_cases hv2 : v = v₂
        · subst hv2
          rw [updateProfile_pref_self, updateProfile_pref_self]
        · rw [updateProfile_pref_of_ne _ v₂ _ hv2, updateProfile_pref_of_ne _ v₂ _ hv2]
          by_cases hv1 : v = v₁
          · subst hv1
            rw [updateProfile_pref_self, updateProfile_pref_self]
          · rw [updateProfile_pref_of_ne _ v₁ _ hv1, updateProfile_pref_of_ne _ v₁ _ hv1]
            exact hagree v hv1 hv2
      simpa [this] using (hfull x) ballot₁ hx_top ballot₂
    | succ n ih =>
      intro P hcardS hfull
      -- Pick a voter v₃ where P and Pbar' differ.
      have hne0 : (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).Nonempty := by
        apply Finset.card_pos.mp
        -- from card = n+1
        have : 0 < (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).card := by
          simp [hcardS]
        exact this
      rcases hne0 with ⟨v₃, hv₃⟩
      have hv₃' := (diffVoters_mem_iff (V := V) (A := A) P Pbar' v₁ v₂ v₃).1 hv₃
      have hv13 : v₃ ≠ v₁ := hv₃'.1
      have hv23 : v₃ ≠ v₂ := hv₃'.2.1

      let P1 : Profile V A := updateProfile P v₃ (Pbar'.pref v₃)
      have hfull1 : V1FullyDecisiveAt (V := V) (A := A) P1 f v₁ v₂ := by
        exact step_v_change_one_voter_v1
          (V := V) (A := A)
          hcard f hf hf_sp v₁ v₂ v₃ hne12 hv13 hv23 hdict_g P hfull (Pbar'.pref v₃)

      have hD1 : (diffVoters (V := V) (A := A) P1 Pbar' v₁ v₂).card = n := by
        have hEq : diffVoters (V := V) (A := A) P1 Pbar' v₁ v₂ =
            (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).erase v₃ := by
          simpa [P1] using
            diffVoters_updateProfile_eq_erase
              (V := V) (A := A)
              P Pbar' v₁ v₂ v₃ hv13 hv23 hv₃
        -- card drops by one
        simpa [hEq, hcardS] using (Finset.card_erase_of_mem hv₃)

      -- Apply IH.
      exact ih P1 hD1 hfull1

  -- Apply the induction with n = card of the initial difference set.
  intro hfull
  exact main (diffVoters (V := V) (A := A) Pbar Pbar' v₁ v₂).card Pbar rfl hfull

lemma step_v_invariant_v2
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne12 : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne12 P' = {topChoice P' ⟨v₁, hne12⟩})
    (Pbar Pbar' : Profile V A) :
    V2FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂ →
      V2FullyDecisiveAt (V := V) (A := A) Pbar' f v₁ v₂ := by
  classical
  -- Induction on the number of differing voters.
  have main :
      ∀ n : Nat,
        ∀ P : Profile V A,
          (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).card = n →
            V2FullyDecisiveAt (V := V) (A := A) P f v₁ v₂ →
              V2FullyDecisiveAt (V := V) (A := A) Pbar' f v₁ v₂ := by
    intro n
    induction n with
    | zero =>
      intro P hcard0 hfull
      -- If there are no differing voters, `setV1V2` profiles built from `P` and `Pbar'` coincide.
      have hD0 : diffVoters (V := V) (A := A) P Pbar' v₁ v₂ = ∅ := by
        exact Finset.card_eq_zero.mp (by simpa using hcard0)
      -- Show ballots agree for all voters except v₁,v₂.
      have hagree : ∀ v : V, v ≠ v₁ → v ≠ v₂ → P.pref v = Pbar'.pref v := by
        intro v hv1 hv2
        by_contra hne
        have : v ∈ diffVoters (V := V) (A := A) P Pbar' v₁ v₂ := by
          have : v ∈ Finset.univ.filter (fun u => u ≠ v₁ ∧ u ≠ v₂ ∧ P.pref u ≠ Pbar'.pref u) := by
            simp [hv1, hv2, hne]
          simpa [diffVoters] using this
        simp [hD0] at this
      -- Now transfer full decisiveness by rewriting the underlying profile.
      intro x ballot₂ hx_top ballot₁
      have : setV1V2 P v₁ v₂ ballot₁ ballot₂ = setV1V2 Pbar' v₁ v₂ ballot₁ ballot₂ := by
        apply Profile.ext
        intro v
        show (setV1V2 P v₁ v₂ ballot₁ ballot₂).pref v
            = (setV1V2 Pbar' v₁ v₂ ballot₁ ballot₂).pref v
        unfold setV1V2
        by_cases hv2 : v = v₂
        · subst hv2
          rw [updateProfile_pref_self, updateProfile_pref_self]
        · rw [updateProfile_pref_of_ne _ v₂ _ hv2, updateProfile_pref_of_ne _ v₂ _ hv2]
          by_cases hv1 : v = v₁
          · subst hv1
            rw [updateProfile_pref_self, updateProfile_pref_self]
          · rw [updateProfile_pref_of_ne _ v₁ _ hv1, updateProfile_pref_of_ne _ v₁ _ hv1]
            exact hagree v hv1 hv2
      simpa [this] using (hfull x) ballot₂ hx_top ballot₁
    | succ n ih =>
      intro P hcardS hfull
      -- Pick a voter v₃ where P and Pbar' differ.
      have hne0 : (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).Nonempty := by
        apply Finset.card_pos.mp
        -- from card = n+1
        have : 0 < (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).card := by
          simp [hcardS]
        exact this
      rcases hne0 with ⟨v₃, hv₃⟩
      have hv₃' := (diffVoters_mem_iff (V := V) (A := A) P Pbar' v₁ v₂ v₃).1 hv₃
      have hv13 : v₃ ≠ v₁ := hv₃'.1
      have hv23 : v₃ ≠ v₂ := hv₃'.2.1

      let P1 : Profile V A := updateProfile P v₃ (Pbar'.pref v₃)
      have hfull1 : V2FullyDecisiveAt (V := V) (A := A) P1 f v₁ v₂ := by
        exact step_v_change_one_voter_v2
          (V := V) (A := A)
          hcard f hf hf_sp v₁ v₂ v₃ hne12 hv13 hv23 hdict_g P hfull (Pbar'.pref v₃)

      have hD1 : (diffVoters (V := V) (A := A) P1 Pbar' v₁ v₂).card = n := by
        have hEq : diffVoters (V := V) (A := A) P1 Pbar' v₁ v₂ =
            (diffVoters (V := V) (A := A) P Pbar' v₁ v₂).erase v₃ := by
          simpa [P1] using
            diffVoters_updateProfile_eq_erase
              (V := V) (A := A)
              P Pbar' v₁ v₂ v₃ hv13 hv23 hv₃
        -- card drops by one
        simpa [hEq, hcardS] using (Finset.card_erase_of_mem hv₃)

      -- Apply IH.
      exact ih P1 hD1 hfull1

  -- Apply the induction with n = card of the initial difference set.
  intro hfull
  exact main (diffVoters (V := V) (A := A) Pbar Pbar' v₁ v₂).card Pbar rfl hfull

lemma step_v_decisive
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne12 : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne12 P' = {topChoice P' ⟨v₁, hne12⟩}):
    (∀ Pbar : Profile V A, V1FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂)
      ∨ (∀ Pbar : Profile V A, V2FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂) := by
  classical
  by_cases h : ∃ Pbar, V1FullyDecisiveAt (V := V) (A := A) Pbar f v₁ v₂
  · left
    intro Pbar'
    obtain ⟨Pbar, hPbar⟩ := h
    exact step_v_invariant_v1 hcard f hf hf_sp v₁ v₂ hne12 hdict_g Pbar Pbar' hPbar
  · right
    intro Pbar
    have h_or := step_iv_global_fully_decisive hcard f hf hf_sp v₁ v₂ hne12 hdict_g Pbar
    rcases h_or with hV1 | hV2
    · exfalso
      exact h ⟨Pbar, hV1⟩
    · exact hV2

/-- Case 2: If dictator in g is voter 1, then either voter 1 or voter 2
    is the dictator in f. -/
theorem gs_case2
    (hcard : 3 ≤ Fintype.card A)
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩}) :
    (∀ P : Profile V A, f P = {topChoice P v₁}) ∨
    (∀ P : Profile V A, f P = {topChoice P v₂}) := by
  classical
  have h_decisive := step_v_decisive hcard f hf hf_sp v₁ v₂ hne hdict_g
  rcases h_decisive with hV1 | hV2
  · left
    intro P
    let Pbar := P
    let x := topChoice P v₁
    have hx_top : ∀ d, d ≠ x → (P.pref v₁).lt x d := by
      intro d hd
      exact topChoice_topRank P v₁ d hd
    have hset : setV1V2 Pbar v₁ v₂ (P.pref v₁) (P.pref v₂) = P := by
      apply Profile.ext
      intro v
      show (setV1V2 P v₁ v₂ (P.pref v₁) (P.pref v₂)).pref v = P.pref v
      unfold setV1V2
      by_cases hv2 : v = v₂
      · subst hv2
        rw [updateProfile_pref_self]
      · rw [updateProfile_pref_of_ne _ v₂ _ hv2]
        by_cases hv1 : v = v₁
        · subst hv1
          rw [updateProfile_pref_self]
        · rw [updateProfile_pref_of_ne _ v₁ _ hv1]
    specialize hV1 P x (P.pref v₁) hx_top (P.pref v₂)
    rw [hset] at hV1
    exact hV1
  · right
    intro P
    let Pbar := P
    let x := topChoice P v₂
    have hx_top : ∀ d, d ≠ x → (P.pref v₂).lt x d := by
      intro d hd
      exact topChoice_topRank P v₂ d hd
    have hset : setV1V2 Pbar v₁ v₂ (P.pref v₁) (P.pref v₂) = P := by
      apply Profile.ext
      intro v
      show (setV1V2 P v₁ v₂ (P.pref v₁) (P.pref v₂)).pref v = P.pref v
      unfold setV1V2
      by_cases hv2 : v = v₂
      · subst hv2
        rw [updateProfile_pref_self]
      · rw [updateProfile_pref_of_ne _ v₂ _ hv2]
        by_cases hv1 : v = v₁
        · subst hv1
          rw [updateProfile_pref_self]
        · rw [updateProfile_pref_of_ne _ v₁ _ hv1]
    specialize hV2 P x (P.pref v₂) hx_top (P.pref v₁)
    rw [hset] at hV2
    exact hV2

end SocialChoice
