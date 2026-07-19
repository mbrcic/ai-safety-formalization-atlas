import SocialChoice.Axioms.Core
import SocialChoice.Axioms.Unanimity
import SocialChoice.Axioms.Strategyproofness
import SocialChoice.Axioms.Dictatorship
import SocialChoice.GSShim
import Mathlib.Data.Fintype.Basic

namespace SocialChoice

/-!
# Common Definitions for Gibbard-Satterthwaite Theorem

This file contains the voter cloning construction and property preservation lemmas
used in the induction proof of the Gibbard-Satterthwaite theorem.

## Main Definitions

* `clonedRule`: Given a voting rule f and two voters v₁, v₂, constructs a new rule g
  on n-1 voters where v₂ is removed and v₁'s ballot is used for both v₁ and v₂.

## Main Results

* `clonedRule_resolute`: If f is resolute, so is the cloned rule.
* `clonedRule_unanimity`: If f is unanimous, so is the cloned rule.
* `clonedRule_strategyproof`: If f is strategy-proof, so is the cloned rule.
-/

open Finset

variable {V A : Type} [Fintype V] [Fintype A] [Nonempty A] [DecidableEq V]

/-! ## Voter Cloning Construction -/

/-- Expand a profile on {w : V // w ≠ v₂} to a full profile on V,
    where v₂ uses v₁'s ballot. -/
noncomputable def expandProfile {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) (P' : Profile {w : V // w ≠ v₂} A) : Profile V A where
  pref := fun v =>
    if h : v = v₂ then
      P'.pref ⟨v₁, hne⟩  -- v₂ uses v₁'s ballot
    else
      P'.pref ⟨v, h⟩     -- other voters use their own

/-! ### Ballot projections (shim) — reduce constructor ballots at the data level -/

@[simp] theorem expandProfile_pref_v2 {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) (P' : Profile {w : V // w ≠ v₂} A) :
    (expandProfile v₁ v₂ hne P').pref v₂ = P'.pref ⟨v₁, hne⟩ := by
  unfold expandProfile; exact dif_pos rfl

theorem expandProfile_pref_of_ne {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) (P' : Profile {w : V // w ≠ v₂} A) {v : V} (h : v ≠ v₂) :
    (expandProfile v₁ v₂ hne P').pref v = P'.pref ⟨v, h⟩ := by
  unfold expandProfile; exact dif_neg h

theorem updateProfile_pref_self {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (ballot : LinearOrder A) :
    (updateProfile P v ballot).pref v = ballot := by
  unfold updateProfile; exact if_pos rfl

theorem updateProfile_pref_of_ne {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (ballot : LinearOrder A) {w : V} (h : w ≠ v) :
    (updateProfile P v ballot).pref w = P.pref w := by
  unfold updateProfile; exact if_neg h

/--
Given a VotingRule f on voter type V, construct a VotingRule g on {w : V // w ≠ v₂}
by having v₁'s ballot also count as v₂'s ballot.

g(P₁, P₃, ..., Pₙ) = f(P₁, P₁, P₃, ..., Pₙ)

This is the key construction for the induction proof: we reduce from n voters to n-1.
-/
noncomputable def clonedRule {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (f : VotingRule) (v₁ v₂ : V) (hne : v₁ ≠ v₂) :
    Profile {w : V // w ≠ v₂} A → Finset A :=
  fun P' => f (expandProfile v₁ v₂ hne P')

/-! ## Property Preservation -/

/-- The cloned rule is resolute if the original is. -/
lemma clonedRule_resolute {V A : Type} [Fintype V] [Fintype A] [Nonempty A] [DecidableEq V]
    (f : VotingRule) (hf : Resolute f) (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (P' : Profile {w : V // w ≠ v₂} A) : (clonedRule f v₁ v₂ hne P').card = 1 := by
  unfold clonedRule
  exact hf (expandProfile v₁ v₂ hne P')

/-- Helper: TopRank is preserved through expandProfile for non-v₂ voters. -/
lemma topRank_expandProfile_of_ne {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) (P' : Profile {w : V // w ≠ v₂} A) (c : A)
    (w : {w : V // w ≠ v₂}) (htop : TopRank P' w c) :
    TopRank (expandProfile v₁ v₂ hne P') w.val c := by
  have hb : (expandProfile v₁ v₂ hne P').pref w.val = P'.pref w :=
    expandProfile_pref_of_ne v₁ v₂ hne P' w.prop
  exact (topRank_congr_ballot _ _ _ _ hb c).mpr htop

/-- Helper: TopRank at v₂ in expanded profile equals TopRank at v₁ in reduced profile. -/
lemma topRank_expandProfile_v2 {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) (P' : Profile {w : V // w ≠ v₂} A) (c : A)
    (htop : TopRank P' ⟨v₁, hne⟩ c) :
    TopRank (expandProfile v₁ v₂ hne P') v₂ c := by
  have hb : (expandProfile v₁ v₂ hne P').pref v₂ = P'.pref ⟨v₁, hne⟩ :=
    expandProfile_pref_v2 v₁ v₂ hne P'
  exact (topRank_congr_ballot _ _ _ _ hb c).mpr htop

/-- If f is unanimous, then the cloned rule is unanimous. -/
lemma clonedRule_unanimity {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (f : VotingRule) (hf_unan : Unanimity f)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) :
    ∀ P' : Profile {w : V // w ≠ v₂} A, ∀ c : A,
      (∀ w : {w : V // w ≠ v₂}, TopRank P' w c) →
      clonedRule f v₁ v₂ hne P' = {c} := by
  intro P' c htop
  unfold clonedRule
  let _ : Nonempty V := ⟨v₂⟩
  apply hf_unan
  intro v
  by_cases hv : v = v₂
  · -- v₂ uses v₁'s ballot, which has c on top
    subst hv
    exact topRank_expandProfile_v2 v₁ v hne P' c (htop ⟨v₁, hne⟩)
  · -- Other voters directly use their ballot from P'
    exact topRank_expandProfile_of_ne v₁ v₂ hne P' c ⟨v, hv⟩ (htop ⟨v, hv⟩)

/-! ## Strategy-Proofness Preservation -/

/-- Helper: The expanded profile after updating voter w in P' equals
    the update of the expanded profile at w.val. -/
lemma expandProfile_updateProfile_eq {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (P' : Profile {w : V // w ≠ v₂} A)
    (w : {u : V // u ≠ v₂}) (hw : w.val ≠ v₁)
    (ballot : LinearOrder A) :
    expandProfile v₁ v₂ hne (updateProfile P' w ballot) =
    updateProfile (expandProfile v₁ v₂ hne P') w.val ballot := by
  ext u
  by_cases huv₂ : u = v₂
  · rw [huv₂]
    have hne_w : (⟨v₁, hne⟩ : {u : V // u ≠ v₂}) ≠ w := by
      intro heq; exact hw (congrArg Subtype.val heq.symm)
    rw [expandProfile_pref_v2, updateProfile_pref_of_ne _ _ _ hne_w,
        updateProfile_pref_of_ne _ _ _ (Ne.symm w.prop), expandProfile_pref_v2]
  · rw [expandProfile_pref_of_ne _ _ _ _ huv₂]
    by_cases huw : u = w.val
    · have hwv : (⟨u, huv₂⟩ : {u : V // u ≠ v₂}) = w := Subtype.ext huw
      rw [hwv, updateProfile_pref_self, huw, updateProfile_pref_self]
    · have hne_w : (⟨u, huv₂⟩ : {u : V // u ≠ v₂}) ≠ w :=
        fun heq => huw (congrArg Subtype.val heq)
      rw [updateProfile_pref_of_ne _ _ _ hne_w,
          updateProfile_pref_of_ne _ _ _ huw, expandProfile_pref_of_ne _ _ _ _ huv₂]

/-- Helper: When manipulator is voter 1, the expanded profile for the deviation
    "doubles up" the new ballot. -/
lemma expandProfile_updateProfile_v1_eq {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (P' : Profile {w : V // w ≠ v₂} A)
    (ballot : LinearOrder A) :
    expandProfile v₁ v₂ hne (updateProfile P' ⟨v₁, hne⟩ ballot) =
    updateProfile (updateProfile (expandProfile v₁ v₂ hne P') v₁ ballot) v₂ ballot := by
  ext u
  by_cases huv₂ : u = v₂
  · rw [huv₂]
    rw [expandProfile_pref_v2, updateProfile_pref_self, updateProfile_pref_self]
  · rw [expandProfile_pref_of_ne _ _ _ _ huv₂]
    by_cases huv₁ : u = v₁
    · have hv1 : (⟨u, huv₂⟩ : {u : V // u ≠ v₂}) = ⟨v₁, hne⟩ := Subtype.ext huv₁
      rw [hv1, updateProfile_pref_self, huv₁, updateProfile_pref_of_ne _ _ _ hne,
          updateProfile_pref_self]
    · have hne_w : (⟨u, huv₂⟩ : {u : V // u ≠ v₂}) ≠ ⟨v₁, hne⟩ :=
        fun heq => huv₁ (congrArg Subtype.val heq)
      rw [updateProfile_pref_of_ne _ _ _ hne_w, updateProfile_pref_of_ne _ _ _ huv₂,
          updateProfile_pref_of_ne _ _ _ huv₁, expandProfile_pref_of_ne _ _ _ _ huv₂]

/-- If f is resolute strategy-proof, then the cloned rule is strategy-proof.

The key insight is that any manipulation of g corresponds to a manipulation of f:
- If manipulator w ≠ v₁: direct lifting to f
- If manipulator w = v₁: either v₁ or v₂ can manipulate f -/
lemma clonedRule_strategyproof {V A : Type} [Fintype V] [Fintype A] [Nonempty A] [DecidableEq V]
    (f : VotingRule) (hf : Resolute f) (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) :
    ∀ P' : Profile {w : V // w ≠ v₂} A,
    ∀ w : {w : V // w ≠ v₂},
    ∀ ballot : LinearOrder A,
    ∀ x y : A,
      clonedRule f v₁ v₂ hne P' = {x} →
      clonedRule f v₁ v₂ hne (updateProfile P' w ballot) = {y} →
      ¬ Prefers P' w y x := by
  intro P' w ballot x y hx hy hpref
  unfold clonedRule at hx hy
  -- Case split: is w.val = v₁ or w.val ∈ {3, ..., n}?
  by_cases hw : w.val = v₁
  · -- Case: w is voter 1 (the cloned voter)
    -- If g is manipulable by voter 1 at P' via ballot,
    -- then f is manipulable by voter 1 or voter 2.
    -- Key insight: in the expanded profile, both v₁ and v₂ have the same ballot.
    -- After the deviation, only v₁'s ballot changes in g, but this means
    -- in the expanded profile, v₁ changes but v₂ still has the old ballot.
    -- We need to show this leads to a contradiction.

    -- The expanded profile for the deviation is:
    -- expandProfile v₁ v₂ hne (updateProfile P' w ballot)
    -- where w = ⟨v₁, hne⟩.

    have hw' : w = ⟨v₁, hne⟩ := by ext; exact hw

    -- Let's denote:
    -- P_full = expandProfile v₁ v₂ hne P'  -- original full profile
    -- The cloned deviation profile expands to something where both v₁ and v₂ use ballot
    let P_full := expandProfile v₁ v₂ hne P'

    -- In the cloned rule, when w = v₁ deviates to ballot:
    -- g(P'[w := ballot]) = f(expandProfile(P'[w := ballot]))
    -- = f(profile where v₁ has ballot, v₂ has ballot, others unchanged)

    -- Rewrite to use the helper lemma
    rw [hw'] at hy

    -- The expanded deviation profile has both v₁ and v₂ with the new ballot
    have hexp : expandProfile v₁ v₂ hne (updateProfile P' ⟨v₁, hne⟩ ballot) =
        updateProfile (updateProfile P_full v₁ ballot) v₂ ballot :=
      expandProfile_updateProfile_v1_eq v₁ v₂ hne P' ballot

    rw [hexp] at hy

    -- Now we have:
    -- f P_full = {x}
    -- f (updateProfile (updateProfile P_full v₁ ballot) v₂ ballot) = {y}
    -- and Prefers P' w y x, meaning v₁ prefers y to x (under P'.pref w)

    -- Consider the intermediate profile where only v₁ deviates
    let P_v1 := updateProfile P_full v₁ ballot
    -- And let z be the outcome of f at P_v1
    let z := theWinner f P_v1 hf
    have hz : f P_v1 = {z} := (eq_singleton_iff_theWinner_eq f P_v1 hf z).mpr rfl

    -- Now apply strategy-proofness arguments:
    -- If z = x: then from P_full to P_v1, outcome stays at x (no manipulation by v₁)
    --           then from P_v1 to final, v₂ changes ballot to get y from x
    --           If v₂ prefers y over x, this is manipulation of f by v₂
    -- If z ≠ x: then v₁ got z ≠ x by deviating; we need to check preferences

    by_cases hzx : z = x
    · -- z = x: the intermediate outcome is still x
      -- Then from P_v1 (with outcome x) to the final profile, v₂ deviates to get y
      -- This means v₂ manipulates f if y is preferred by v₂
      rw [hzx] at hz
      -- The final profile is updateProfile P_v1 v₂ ballot
      -- f P_v1 = {x}, f (updateProfile P_v1 v₂ ballot) = {y}
      -- Need to show v₂ doesn't prefer y over x in P_v1
      have hnot_v2 : ¬ Prefers P_v1 v₂ y x :=
        hf_sp P_v1 v₂ ballot x y hz hy
      -- But P_v1.pref v₂ = P_full.pref v₂ = P'.pref ⟨v₁, hne⟩ (since v₂ uses v₁'s ballot)
      -- And P'.pref ⟨v₁, hne⟩ = P'.pref w (since w = ⟨v₁, hne⟩)
      -- So Prefers P_v1 v₂ y x ↔ Prefers P' w y x
      have hpref_eq : Prefers P_v1 v₂ y x ↔ Prefers P' w y x := by
        have h1 : P_v1.pref v₂ = P_full.pref v₂ :=
          updateProfile_pref_of_ne P_full v₁ ballot (Ne.symm hne)
        have h2 : P_full.pref v₂ = P'.pref ⟨v₁, hne⟩ := expandProfile_pref_v2 v₁ v₂ hne P'
        have hb : P_v1.pref v₂ = P'.pref w := by rw [h1, h2, hw']
        exact prefers_congr_ballot _ _ _ _ hb y x
      rw [hpref_eq] at hnot_v2
      exact hnot_v2 hpref
    · -- z ≠ x: the intermediate outcome changed
      -- From P_full (outcome x) to P_v1 (outcome z), v₁ changed their ballot
      -- Apply strategy-proofness: v₁ shouldn't prefer z over x in P_full
      have hnot_v1 : ¬ Prefers P_full v₁ z x :=
        hf_sp P_full v₁ ballot x z hx hz

      -- We also know that going from P_v1 to final, the outcome goes from z to y
      -- Apply strategy-proofness: v₂ shouldn't prefer y over z in P_v1
      have hnot_v2 : ¬ Prefers P_v1 v₂ y z :=
        hf_sp P_v1 v₂ ballot z y hz hy

      -- Now we use that in P_full, v₁ and v₂ have the SAME ballot (v₁'s original)
      -- and in P_v1, v₁ has ballot but v₂ still has v₁'s original ballot
      -- The preferences of v₂ in P_v1 equal the preferences of v₁ in P_full

      -- Prefers P_full v₁ = using P'.pref ⟨v₁, hne⟩
      -- Prefers P_v1 v₂ = using P'.pref ⟨v₁, hne⟩ (since v₂ still has original)
      have hpref_v1_full : Prefers P_full v₁ y x ↔ Prefers P' w y x := by
        have h2 : P_full.pref v₁ = P'.pref ⟨v₁, hne⟩ := expandProfile_pref_of_ne v₁ v₂ hne P' hne
        have hb : P_full.pref v₁ = P'.pref w := by rw [h2, hw']
        exact prefers_congr_ballot _ _ _ _ hb y x
      have hpref_v2_pv1 : Prefers P_v1 v₂ y z ↔ Prefers P_full v₂ y z := by
        have hb : P_v1.pref v₂ = P_full.pref v₂ :=
          updateProfile_pref_of_ne P_full v₁ ballot (Ne.symm hne)
        exact prefers_congr_ballot _ _ _ _ hb y z
      have hpref_full_v2_v1 : Prefers P_full v₂ y z ↔ Prefers P_full v₁ y z := by
        have ha : P_full.pref v₂ = P'.pref ⟨v₁, hne⟩ := expandProfile_pref_v2 v₁ v₂ hne P'
        have hc : P_full.pref v₁ = P'.pref ⟨v₁, hne⟩ := expandProfile_pref_of_ne v₁ v₂ hne P' hne
        have hb : P_full.pref v₂ = P_full.pref v₁ := by rw [ha, hc]
        exact prefers_congr_ballot _ _ _ _ hb y z

      -- We have:
      -- ¬ Prefers P_full v₁ z x (from hnot_v1)
      -- ¬ Prefers P_v1 v₂ y z ↔ ¬ Prefers P_full v₁ y z (from hnot_v2 and equivalences)
      -- Prefers P' w y x (our assumption hpref)

      -- In P_full, v₁'s order is P'.pref w
      -- We assumed y is preferred to x in this order.
      -- We need to derive a contradiction.

      -- By transitivity reasoning on the linear order:
      -- If y > x and ¬(z > x) and ¬(y > z), we should get a contradiction.
      -- ¬(z > x) means x ≥ z, i.e., x > z or x = z
      -- ¬(y > z) means z ≥ y, i.e., z > y or z = y
      -- If x > z and z > y, then x > y, contradicting y > x
      -- If x > z and z = y, then x > y, contradicting y > x
      -- If x = z and z > y, then x > y, contradicting y > x
      -- If x = z and z = y, then x = y = z, but we know z ≠ x, contradiction

      rw [hpref_v2_pv1, hpref_full_v2_v1] at hnot_v2

      -- Transform to use the same linear order
      have hpref' : Prefers P_full v₁ y x := by
        rw [hpref_v1_full]
        exact hpref

      -- Get the linear order
      letI ord := (expandProfile v₁ v₂ hne P').pref v₁

      -- Use linear order properties
      unfold Prefers at hnot_v1 hnot_v2 hpref'

      -- hnot_v1: ¬ (z < x)  means x ≤ z
      -- hnot_v2: ¬ (y < z)  means z ≤ y
      -- hpref': y < x

      have hxz : ord.le x z := not_lt.mp hnot_v1
      have hzy : ord.le z y := not_lt.mp hnot_v2
      have hxy : ord.lt y x := hpref'

      -- By transitivity: x ≤ z ≤ y, but y < x
      have hxy' : ord.le x y := le_trans hxz hzy
      -- This contradicts y < x
      exact not_lt.mpr hxy' hxy

  · -- Case: w is voter i ≠ v₁ (corresponds to direct lifting)
    -- Any manipulation in g corresponds directly to manipulation in f by voter w.val

    -- The expanded profile for P' is expandProfile v₁ v₂ hne P'
    -- The expanded profile for updateProfile P' w ballot is
    --   updateProfile (expandProfile v₁ v₂ hne P') w.val ballot
    -- by the helper lemma (since w.val ≠ v₁)

    have hexp : expandProfile v₁ v₂ hne (updateProfile P' w ballot) =
        updateProfile (expandProfile v₁ v₂ hne P') w.val ballot :=
      expandProfile_updateProfile_eq v₁ v₂ hne P' w hw ballot

    rw [hexp] at hy

    -- Now we have:
    -- f (expandProfile v₁ v₂ hne P') = {x}
    -- f (updateProfile (expandProfile v₁ v₂ hne P') w.val ballot) = {y}
    -- Apply strategy-proofness of f
    have hnot : ¬ Prefers (expandProfile v₁ v₂ hne P') w.val y x :=
      hf_sp (expandProfile v₁ v₂ hne P') w.val ballot x y hx hy

    -- Show that Prefers in expanded profile equals Prefers in P' for w
    have hpref_eq : Prefers (expandProfile v₁ v₂ hne P') w.val y x ↔ Prefers P' w y x := by
      have hb : (expandProfile v₁ v₂ hne P').pref w.val = P'.pref w :=
        expandProfile_pref_of_ne v₁ v₂ hne P' w.prop
      exact prefers_congr_ballot _ _ _ _ hb y x

    rw [hpref_eq] at hnot
    exact hnot hpref

end SocialChoice
