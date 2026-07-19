import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Order.Basic

namespace SocialChoice

open Finset


structure Profile (V A : Type) [Fintype V] [Fintype A] where
  pref : V → LinearOrder A

-- Constant profile where every voter has the same ballot.
def constantProfile {V A : Type} [Fintype V] [Fintype A]
    (r : LinearOrder A) : Profile V A :=
  { pref := fun _ => r }

@[ext] lemma Profile.ext {V A : Type} [Fintype V] [Fintype A]
    {P Q : Profile V A} (h : ∀ v, P.pref v = Q.pref v) : P = Q := by
  cases P with
  | mk prefP =>
      cases Q with
      | mk prefQ =>
          have hfun : prefP = prefQ := funext h
          cases hfun
          rfl

abbrev VotingRule :=
  ∀ {V A : Type} [Fintype V] [Fintype A], Profile V A → Finset A

def IsVotingRule (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty A] (P : Profile V A), (f P).Nonempty

-- Basic preference predicates.
def Prefers {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (a b : A) : Prop :=
  (P.pref v).lt a b

def TopRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) : Prop :=
  ∀ d : A, d ≠ c → Prefers P v c d

def BottomRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) : Prop :=
  ∀ d : A, d ≠ c → Prefers P v d c

-- Permute voters by relabeling the electorate.
def permuteVoters {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) : Profile V A :=
  { pref := fun v => P.pref (σ v) }

-- Relabel a linear order along a permutation.
-- Atlas package has warningAsError; class-valued defs need reducible (4.31).
@[reducible] noncomputable def relabelBallot {α : Type} (r : LinearOrder α) (σ : Equiv.Perm α) : LinearOrder α := by
  classical
  let _ := r
  exact LinearOrder.lift' σ σ.injective

-- Relabel a linear order along an equivalence.
@[reducible] noncomputable def relabelBallotEquiv {A B : Type} (r : LinearOrder A) (e : A ≃ B) :
    LinearOrder B := by
  classical
  let _ := r
  exact LinearOrder.lift' e.symm e.symm.injective

-- Permute candidates by relabeling each ballot.
noncomputable def permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) : Profile V A :=
  { pref := fun v => relabelBallot (P.pref v) σ.symm }

noncomputable def relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) : Profile V B :=
  { pref := fun v => relabelBallotEquiv (P.pref v) e }

-- Add a voter via a sum type.
def addVoter {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) : Profile (V ⊕ Unit) A :=
  { pref := fun v =>
      match v with
      | Sum.inl v => P.pref v
      | Sum.inr _ => ballot }

-- Union of profiles on disjoint electorates using a sum type.
def unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P₁ : Profile V A) (P₂ : Profile W A) : Profile (V ⊕ W) A :=
  { pref := fun v =>
      match v with
      | Sum.inl v => P₁.pref v
      | Sum.inr w => P₂.pref w }

-- Restrict the agenda by a predicate.
@[reducible] noncomputable def restrictBallot {A : Type} (r : LinearOrder A)
    (p : A → Prop) [DecidablePred p] : LinearOrder {a // p a} := by
  classical
  let _ := r
  infer_instance

noncomputable def restrictCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p] : Profile V {a // p a} :=
  { pref := fun v => restrictBallot (P.pref v) p }

@[simp] lemma prefers_restrictCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p] (v : V)
    (a b : {x : A // p x}) :
    Prefers (restrictCandidates P p) v a b ↔ Prefers P v a b := by
  rfl

noncomputable def castCandidates {V A : Type} [Fintype V] [Fintype A]
    {p q : A → Prop} [DecidablePred p] [DecidablePred q]
    (h : p = q) (P : Profile V {a // p a}) : Profile V {a // q a} := by
  classical
  cases h
  rename_i instP instQ
  have hinst : instP = instQ := Subsingleton.elim _ _
  cases hinst
  exact P

@[simp] lemma castCandidates_rfl {V A : Type} [Fintype V] [Fintype A]
    {p : A → Prop} [DecidablePred p]
    (P : Profile V {a // p a}) : castCandidates (p := p) (q := p) rfl P = P := by
  classical
  simp [castCandidates]

@[simp] lemma castCandidates_restrictCandidates {V A : Type} [Fintype V] [Fintype A]
    {p q : A → Prop} [DecidablePred p] [DecidablePred q]
    (P : Profile V A) (h : p = q) :
    castCandidates (p := p) (q := q) h (restrictCandidates P p) = restrictCandidates P q := by
  classical
  cases h
  rename_i instP instQ
  have hinst : instP = instQ := Subsingleton.elim _ _
  cases hinst
  rfl

-- Helper instance for restricted candidate types
noncomputable instance instFintypeNeq {A : Type} [Fintype A] [DecidableEq A] (c : A) :
    Fintype {x : A // x ≠ c} := by
  classical
  infer_instance

-- Restrict a profile by removing one candidate
noncomputable def restrictProfile {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (c : A) : Profile V {x : A // x ≠ c} :=
  restrictCandidates P (fun x => x ≠ c)

@[simp] lemma prefers_restrictProfile_iff {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (c : A) (v : V) (a b : {x : A // x ≠ c}) :
    Prefers (restrictProfile P c) v a b ↔ Prefers P v a b := by
  rfl

-- Tie back to ℕ via finite subtypes.
abbrev NatElectorate (S : Finset Nat) := {n // n ∈ S}
abbrev NatAgenda (S : Finset Nat) := {n // n ∈ S}

instance (S : Finset Nat) : Fintype (NatElectorate S) := by
  classical
  simpa [NatElectorate] using (Fintype.subtype S (by intro x; rfl))

instance (S : Finset Nat) : Fintype (NatAgenda S) := by
  classical
  simpa [NatAgenda] using (Fintype.subtype S (by intro x; rfl))

abbrev ProfileOnNat (V A : Finset Nat) := Profile (NatElectorate V) (NatAgenda A)

-- Helpers for counting voters.
noncomputable def votersPreferring {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Prefers P v a b)

noncomputable def votersTop {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => TopRank P v c)

noncomputable def votersBottom {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => BottomRank P v c)

def StrictMajority {V : Type} [Fintype V] (S : Finset V) : Prop :=
  2 * S.card > Fintype.card V

-- Candidate renaming on winner sets.
noncomputable def permuteWinners {A : Type} (σ : Equiv.Perm A) (s : Finset A) : Finset A := by
  classical
  exact s.map σ.toEmbedding

-- Ballot-level predicates used in variable-electorate axioms.
def BallotTop {A : Type} (r : LinearOrder A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → r.lt c d

def BallotBottom {A : Type} (r : LinearOrder A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → r.lt d c

-- Variable-agenda helpers.
noncomputable def liftWinners {A : Type}
    {p : A → Prop} [DecidablePred p]
    (s : Finset {a // p a}) : Finset A := by
  classical
  exact s.image (fun a => a.1)

lemma cardinality_lemma {V : Type} [Fintype V]
    (p q : V → Prop) [DecidablePred p] [DecidablePred q] :
    (∀ v, p v → q v) →
      (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card := by
  classical
  intro pq
  refine Finset.card_le_card ?_
  intro v hv
  have hv' : p v := (Finset.mem_filter.mp hv).2
  exact (Finset.mem_filter.mpr ⟨mem_univ v, pq v hv'⟩)

lemma cardinality_lemma2 {V : Type} [Fintype V]
    (p q : V → Prop) [DecidablePred p] [DecidablePred q] :
    (∀ v, p v ↔ q v) →
      (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  classical
  intro pq
  have hset : (Finset.univ.filter p) = (Finset.univ.filter q) := by
    ext v
    simp [pq v]
  simp [hset]

/-! ## Cardinality Lemmas for Subtypes -/

/-- Cardinality strictly decreases when removing one element. -/
lemma card_subtype_ne_lt {α : Type} [Fintype α] [DecidableEq α] (x : α) :
    Fintype.card {y : α // y ≠ x} < Fintype.card α :=
  Fintype.card_subtype_lt (x := x) (by simp)

/-- Cardinality of {y // y ≠ x} equals card α - 1. -/
lemma card_subtype_ne_eq {α : Type} [Fintype α] [DecidableEq α] (x : α) :
    Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 := by
  classical
  have h := (Fintype.card_subtype (α := α) (p := fun y => y ≠ x))
  have hfilter : ({y : α | y ≠ x} : Finset α) = (Finset.univ.erase x) := by
    ext y
    by_cases hy : y = x <;> simp [hy]
  have h' : Fintype.card {y : α // y ≠ x} = (Finset.univ.erase x).card := by
    rw [hfilter] at h
    exact h
  have herase : (Finset.univ.erase x).card = (Finset.univ : Finset α).card - 1 :=
    Finset.card_erase_of_mem (s := (Finset.univ : Finset α)) (a := x) (by simp)
  calc
    Fintype.card {y : α // y ≠ x} = (Finset.univ.erase x).card := h'
    _ = (Finset.univ : Finset α).card - 1 := herase
    _ = Fintype.card α - 1 := by simp [Finset.card_univ]

/-- If there are at least 2 elements, there exist two distinct elements. -/
lemma exists_pair_of_one_lt_card {α : Type} [Fintype α]
    (h : 1 < Fintype.card α) : ∃ x y : α, x ≠ y := by
  classical
  have hne : ¬ Subsingleton α := by
    intro hsub
    have hcard := Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  rw [not_subsingleton_iff_nontrivial] at hne
  exact Nontrivial.exists_pair_ne

lemma one_lt_card_subtype_ne {A : Type} [Fintype A] [DecidableEq A] {c : A}
    (h : 2 < Fintype.card A) : 1 < Fintype.card {x : A // x ≠ c} := by
  have hpred : 1 < (Fintype.card A).pred := by
    have hle : 2 ≤ (Fintype.card A).pred := Nat.le_pred_of_lt h
    exact lt_of_lt_of_le (by decide : (1 : Nat) < 2) hle
  simpa [card_subtype_ne_eq c, Nat.pred_eq_sub_one] using hpred

lemma two_elems_eq_or_eq {A : Type} [Fintype A] (hcard : Fintype.card A = 2) (a b : A) (hab : a ≠ b) (c : A) :
    c = a ∨ c = b := by
  classical
  have hpair : ({a, b} : Finset A).card = 2 := Finset.card_pair hab
  have hsub : ({a, b} : Finset A) ⊆ (Finset.univ : Finset A) := by
    intro x _
    exact Finset.mem_univ x
  have hcard_univ : (Finset.univ : Finset A).card = 2 := by
    simpa [Finset.card_univ] using hcard
  have hpair_eq : ({a, b} : Finset A) = (Finset.univ : Finset A) := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hcard_univ, hpair]
  have huniv : (Finset.univ : Finset A) = {a, b} := hpair_eq.symm
  have hc : c ∈ ({a, b} : Finset A) := by
    simpa [huniv] using Finset.mem_univ c
  simpa using hc

end SocialChoice
