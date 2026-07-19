import SocialChoice.Impossibilities.GibbardSatterthwaite.BaseCase
import SocialChoice.Impossibilities.GibbardSatterthwaite.InductionStepCase1
import SocialChoice.Impossibilities.GibbardSatterthwaite.InductionStepCase2
import Mathlib.Data.Fintype.Card

namespace SocialChoice

open Finset

/-- A `VotingRule` that agrees with `clonedRule f v₁ v₂ hne` on the electorate
`{w : V // w ≠ v₂}` and candidate type `A`, and agrees with `f` on all other
type instantiations.

This wrapper exists so we can apply an induction hypothesis stated for
polymorphic `VotingRule`s to the (monomorphic) cloned rule.
-/
noncomputable def clonedVotingRule
    {V A0 : Type} [Fintype V] [Fintype A0] [DecidableEq V]
    (f : VotingRule) (v₁ v₂ : V) (hne : v₁ ≠ v₂) : VotingRule := by
  classical
  intro V' A' instV' instA'
  letI : Fintype V' := instV'
  letI : Fintype A' := instA'
  by_cases hV : V' = {w : V // w ≠ v₂}
  · cases hV
    by_cases hA : A' = A0
    · cases hA
      -- normalize the fintype instance on the subtype (it is a parameter of `Profile`)
      cases (Subsingleton.elim instV' (Subtype.fintype (fun w : V => w ≠ v₂)))
      exact clonedRule (V := V) (A := A0) f v₁ v₂ hne
    · exact fun P => f P
  · exact fun P => f P

@[simp] lemma clonedVotingRule_apply_cloned
    {V A0 : Type} [Fintype V] [Fintype A0] [DecidableEq V]
    (f : VotingRule) (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (P' : Profile {w : V // w ≠ v₂} A0) :
    (@clonedVotingRule V A0 _ _ _ f v₁ v₂ hne)
        (V := {w : V // w ≠ v₂}) (A := A0) P' =
      clonedRule (V := V) (A := A0) f v₁ v₂ hne P' := by
  classical
  simp [clonedVotingRule]

lemma clonedVotingRule_resolute
    {V A0 : Type} [Fintype V] [Fintype A0] [Nonempty A0] [DecidableEq V]
    (f : VotingRule) (hf : Resolute f) (v₁ v₂ : V) (hne : v₁ ≠ v₂) :
    Resolute (@clonedVotingRule V A0 _ _ _ f v₁ v₂ hne) := by
  intro V' A' instV' instA' instNonemptyA' P
  letI : Fintype V' := instV'
  letI : Fintype A' := instA'
  letI : Nonempty A' := instNonemptyA'
  classical
  by_cases hV : V' = {w : V // w ≠ v₂}
  · cases hV
    by_cases hA : A' = A0
    · cases hA
      cases (Subsingleton.elim instV' (Subtype.fintype (fun w : V => w ≠ v₂)))
      simpa [clonedVotingRule] using
        clonedRule_resolute (V := V) (A := A0) (f := f) hf v₁ v₂ hne P
    · simpa [clonedVotingRule, hA] using hf P
  · simpa [clonedVotingRule, hV] using hf P

lemma clonedVotingRule_unanimity
    {V A0 : Type} [Fintype V] [Fintype A0] [DecidableEq V]
    (f : VotingRule) (hf_unan : Unanimity f) (v₁ v₂ : V) (hne : v₁ ≠ v₂) :
    Unanimity (@clonedVotingRule V A0 _ _ _ f v₁ v₂ hne) := by
  intro V' A' instV' instA' _ P c htop
  letI : Fintype V' := instV'
  letI : Fintype A' := instA'
  classical
  by_cases hV : V' = {w : V // w ≠ v₂}
  · cases hV
    by_cases hA : A' = A0
    · cases hA
      cases (Subsingleton.elim instV' (Subtype.fintype (fun w : V => w ≠ v₂)))
      simpa [clonedVotingRule] using
        clonedRule_unanimity (V := V) (A := A0) (f := f) hf_unan v₁ v₂ hne P c htop
    · simpa [clonedVotingRule, hA] using hf_unan P c htop
  · simpa [clonedVotingRule, hV] using hf_unan P c htop

lemma clonedVotingRule_strategyproof
    {V A0 : Type} [Fintype V] [Fintype A0] [Nonempty A0] [DecidableEq V]
    (f : VotingRule) (hf : Resolute f) (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂) :
    ResoluteStrategyproofness
      (@clonedVotingRule V A0 _ _ _ f v₁ v₂ hne)
      (clonedVotingRule_resolute (V := V) (A0 := A0) f hf v₁ v₂ hne) := by
  intro V' A' instV' instA' P v ballot x y hx hy
  letI : Fintype V' := instV'
  letI : Fintype A' := instA'
  classical
  by_cases hV : V' = {w : V // w ≠ v₂}
  · cases hV
    by_cases hA : A' = A0
    · cases hA
      cases (Subsingleton.elim instV' (Subtype.fintype (fun w : V => w ≠ v₂)))
      have hx' : clonedRule f v₁ v₂ hne P = {x} := by
        simpa [clonedVotingRule] using hx
      have hy' : clonedRule f v₁ v₂ hne (updateProfile P v ballot) = {y} := by
        simpa [clonedVotingRule] using hy
      exact clonedRule_strategyproof (V := V) (A := A0) (f := f) hf hf_sp v₁ v₂ hne P v ballot x y hx' hy'
    ·
      have hx' : f P = {x} := by
        simpa [clonedVotingRule, hA] using hx
      have hy' : f (updateProfile P v ballot) = {y} := by
        simpa [clonedVotingRule, hA] using hy
      exact hf_sp P v ballot x y hx' hy'
  ·
    have hx' : f P = {x} := by
      simpa [clonedVotingRule, hV] using hx
    have hy' : f (updateProfile P v ballot) = {y} := by
      simpa [clonedVotingRule, hV] using hy
    exact hf_sp P v ballot x y hx' hy'

/-- Resoluteness specialized to fixed voter/candidate types. -/
def ResoluteVA {V A : Type} [Fintype V] [Fintype A]
    (f : Profile V A → Finset A) : Prop :=
  ∀ P : Profile V A, (f P).card = 1

/-- Unanimity specialized to fixed voter/candidate types. -/
def UnanimityVA {V A : Type} [Fintype V] [Fintype A]
    (f : Profile V A → Finset A) : Prop :=
  ∀ P : Profile V A, ∀ c : A, (∀ v : V, TopRank P v c) → f P = {c}

/-- Strategy-proofness specialized to fixed voter/candidate types. -/
def StrategyproofVA {V A : Type} [Fintype V] [Fintype A]
    (f : Profile V A → Finset A) : Prop :=
  ∀ P : Profile V A, ∀ v : V, ∀ ballot : LinearOrder A, ∀ x y : A,
    f P = {x} →
    f (updateProfile P v ballot) = {y} →
    ¬ Prefers P v y x

/-- Strong-induction version of Gibbard–Satterthwaite on fixed voter and
candidate types. The rule `f` only needs to be defined on these types. -/
theorem gibbard_satterthwaite
    {V A : Type} [Fintype V] [Nonempty V] [Fintype A] [Nonempty A]
    (hcardA : 3 ≤ Fintype.card A)
    (f : VotingRule)
    (hf_res : Resolute f)
    (hf_unan : Unanimity f)
    (hf_sp : ResoluteStrategyproofness f hf_res) :
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d} := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ {V A : Type} [Fintype V] [Nonempty V] [Fintype A] [Nonempty A],
      Fintype.card V = n →
      3 ≤ Fintype.card A →
      ∀ (f : VotingRule),
        ∀ (hf_res : Resolute f),
        Unanimity f →
        ResoluteStrategyproofness f hf_res →
        ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}

  have hStrong : motive (Fintype.card V) := by
    classical
    refine Nat.strong_induction_on (p := motive) (n := Fintype.card V) ?step
    intro n ih V A _ _ _ _ hV hcardA f hf_res hf_unan hf_sp
    cases n with
    | zero =>
        -- impossible: nonempty finite type has positive cardinality
        cases (Fintype.card_ne_zero (α := V)) (by simp [hV])
    | succ n1 =>
        cases n1 with
        | zero =>
            -- n = 1: base case
            have hcard1 : Fintype.card V = 1 := by simpa using hV
            exact gs_base_case (V := V) (A := A) hcard1 f hf_res hf_unan
        | succ n2 =>
            -- inductive step: at least two voters
            have hgt1 : 1 < Fintype.card V := by
              have : 1 < n2.succ.succ := Nat.succ_lt_succ (Nat.succ_pos n2)
              exact lt_of_lt_of_eq this hV.symm

            -- pick two distinct voters
            letI : DecidableEq V := Classical.decEq V
            rcases exists_pair_of_one_lt_card (α := V) hgt1 with ⟨v₁, v₂, hne⟩

            -- package the cloned rule as a VotingRule for the IH
            let fClone : VotingRule := clonedVotingRule (V := V) (A0 := A) f v₁ v₂ hne
            have hfClone_unan : Unanimity fClone :=
              clonedVotingRule_unanimity (V := V) (A0 := A) f hf_unan v₁ v₂ hne

            -- cardinality strictly decreases
            have hg_card : Fintype.card {w : V // w ≠ v₂} < n2.succ.succ := by
              have h : Fintype.card {w : V // w ≠ v₂} < Fintype.card V :=
                card_subtype_ne_lt (α := V) (x := v₂)
              exact lt_of_lt_of_eq h hV

            -- IH on the cloned rule
            haveI : Nonempty {w : V // w ≠ v₂} := ⟨⟨v₁, hne⟩⟩
            have hg_dict : ∃ d : {w : V // w ≠ v₂},
                ∀ P' : Profile {w : V // w ≠ v₂} A,
                  clonedRule f v₁ v₂ hne P' = {topChoice P' d} := by
              have hM : motive (Fintype.card {w : V // w ≠ v₂}) :=
                ih (Fintype.card {w : V // w ≠ v₂}) hg_card
              have hdict :=
                hM (V := {w : V // w ≠ v₂}) (A := A) rfl hcardA
                  fClone
                  (clonedVotingRule_resolute (V := V) (A0 := A) f hf_res v₁ v₂ hne)
                  hfClone_unan
                  (clonedVotingRule_strategyproof (V := V) (A0 := A) f hf_res hf_sp v₁ v₂ hne)
              rcases hdict with ⟨d, hd⟩
              refine ⟨d, ?_⟩
              intro P'
              -- on this electorate/candidate type, fClone coincides with clonedRule
              simpa [fClone] using hd P'

            rcases hg_dict with ⟨i, hi⟩

            -- case split on whether dictator is v₁
            by_cases hi1 : i.val = v₁
            · -- dictator corresponds to v₁ → use case 2
              have hdict_v1 : ∀ P' : Profile {w : V // w ≠ v₂} A,
                  clonedRule f v₁ v₂ hne P' = {topChoice P' ⟨v₁, hne⟩} := by
                intro P'
                have : i = ⟨v₁, hne⟩ := by ext; exact hi1
                simpa [this] using hi P'
              cases gs_case2 hcardA (f := f) hf_res hf_sp v₁ v₂ hne hdict_v1 with
              | inl hv1 => exact ⟨v₁, hv1⟩
              | inr hv2 => exact ⟨v₂, hv2⟩
            · -- dictator is some other voter ≠ v₁
              have hi_ne : i.val ≠ v₁ := hi1
              have hf_dict := gs_case1 (f := f) hf_res hf_sp v₁ v₂ hne i hi_ne hi
              exact ⟨i.val, hf_dict⟩

  -- apply to the actual inputs
  exact hStrong (V := V) (A := A) rfl hcardA f hf_res hf_unan hf_sp

end SocialChoice
