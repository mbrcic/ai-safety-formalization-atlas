/-
Vendored classical Gibbard–Satterthwaite from DominikPeters/SocialChoiceLean
via mbrcic/SocialChoiceLean `port/lean-4.31` revision `74f491b` (MIT).

Single-module packaging (Arrow-style) so the GS proof can `unfold`/defeq across
what were separate upstream files, while remaining importable from the
AISafetyAtlas public-module package. Upstream multi-file layout is preserved
as section comments; source SHA list in vendor/SocialChoiceLean/PROVENANCE.md.

Atlas adaptations:
* single `module` file under AISafetyAtlas.Upstream
* drop Meta.lean / `@[scAxiom]`
* Unanimity def only; Strategyproofness = updateProfile + ResoluteStrategyproofness
* `@[reducible]` on class-valued ballot constructors (package warningAsError)
* 4.31 GSShim ballot-congruence helpers from the port
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin

namespace SocialChoice

set_option linter.unusedSectionVars false


/-! ### Vendored fragment: SocialChoice/Profile.lean -/



open Finset


public structure Profile (V A : Type) [Fintype V] [Fintype A] where
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

public abbrev VotingRule :=
  ∀ {V A : Type} [Fintype V] [Fintype A], Profile V A → Finset A

def IsVotingRule (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty A] (P : Profile V A), (f P).Nonempty

-- Basic preference predicates.
public def Prefers {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (a b : A) : Prop :=
  (P.pref v).lt a b

public def TopRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) : Prop :=
  ∀ d : A, d ≠ c → Prefers P v c d

public def BottomRank {V A : Type} [Fintype V] [Fintype A]
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


/-! ### Vendored fragment: SocialChoice/Rank.lean -/



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
public noncomputable def topChoice {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
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


/-! ### Vendored fragment: SocialChoice/GSShim.lean -/


/-!
# Ballot-level shim for the Gibbard–Satterthwaite port

Root cause of the 4.27 -> 4.31 breakage: a ballot is a bundled `LinearOrder A`
(`Profile.pref : V -> LinearOrder A`).  Proofs discharge preference goals with
`simp [Prefers, ...]`, which unfolds `Prefers P v a b = (P.pref v).lt a b` down
the `LinearOrder -> PartialOrder -> Preorder -> LT` instance chain.  Between
Mathlib versions that chain's *syntactic* spelling changes, so two defeq terms
stop unifying ("Type mismatch after simplification" / "simp made no progress").

Fix: reason at the **ballot** level and keep `Prefers` sealed.  `Prefers P v a b`
depends on `P.pref v` only, so ballot equality transports it without ever
touching the `.lt` instance path.  These lemmas are version-stable: they mention
only function equality of ballots, never `LinearOrder`'s internal fields.
-/


variable {V W A : Type} [Fintype V] [Fintype W] [Fintype A]

/-- The workhorse: transport `Prefers` across ballot equality without unfolding
`.lt`.  Replaces every `simpa [Prefers, <constructor>] using h`. -/
theorem prefers_congr_ballot (P : Profile V A) (Q : Profile W A)
    (v : V) (w : W) (h : P.pref v = Q.pref w) (a b : A) :
    Prefers P v a b ↔ Prefers Q w a b := by
  unfold Prefers; rw [h]

/-- `TopRank` transported across ballot equality. -/
theorem topRank_congr_ballot (P : Profile V A) (Q : Profile W A)
    (v : V) (w : W) (h : P.pref v = Q.pref w) (c : A) :
    TopRank P v c ↔ TopRank Q w c := by
  unfold TopRank
  constructor <;> intro htop d hd <;>
    [exact (prefers_congr_ballot P Q v w h c d).mp (htop d hd);
     exact (prefers_congr_ballot P Q v w h c d).mpr (htop d hd)]

/-- `BottomRank` transported across ballot equality. -/
theorem bottomRank_congr_ballot (P : Profile V A) (Q : Profile W A)
    (v : V) (w : W) (h : P.pref v = Q.pref w) (c : A) :
    BottomRank P v c ↔ BottomRank Q w c := by
  unfold BottomRank
  constructor <;> intro hbot d hd <;>
    [exact (prefers_congr_ballot P Q v w h d c).mp (hbot d hd);
     exact (prefers_congr_ballot P Q v w h d c).mpr (hbot d hd)]

/-! ## Ballot projections for the `Profile` constructors

Each rewrites `(constructor ...).pref v` to the selected ballot at the *data*
level (no `.lt`).  Feed the resulting equality into `prefers_congr_ballot`. -/

@[simp] theorem constantProfile_pref (r : LinearOrder A) (v : V) :
    (constantProfile (V := V) r).pref v = r := rfl

@[simp] theorem addVoter_pref_old (P : Profile V A) (ballot : LinearOrder A)
    (v : V) : (addVoter P ballot).pref (Sum.inl v) = P.pref v := rfl

@[simp] theorem addVoter_pref_new (P : Profile V A) (ballot : LinearOrder A)
    (u : Unit) : (addVoter P ballot).pref (Sum.inr u) = ballot := rfl

@[simp] theorem unionProfiles_pref_left (P₁ : Profile V A) (P₂ : Profile W A)
    (v : V) : (unionProfiles P₁ P₂).pref (Sum.inl v) = P₁.pref v := rfl

@[simp] theorem unionProfiles_pref_right (P₁ : Profile V A) (P₂ : Profile W A)
    (w : W) : (unionProfiles P₁ P₂).pref (Sum.inr w) = P₂.pref w := rfl

@[simp] theorem permuteVoters_pref (P : Profile V A) (σ : Equiv.Perm V) (v : V) :
    (permuteVoters P σ).pref v = P.pref (σ v) := rfl


/-! ### Vendored fragment: SocialChoice/Axioms/Resolute.lean -/



/-!
# Resolute Voting Rules

A voting rule is **resolute** if it always returns exactly one winner.
This file provides the definition and helper lemmas for working with resolute rules.
-/

open Finset

/-- A voting rule is resolute if it always returns exactly one winner. -/
public def Resolute (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty A] (P : Profile V A), (f P).card = 1

/-! ## Extracting the Unique Winner -/

/-- Extract the unique winner from a resolute voting rule's output. -/
noncomputable def theWinner {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) : A := by
  have h : ∃! x, x ∈ f P := by
    have hcard := hf P
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, hx⟩ := hcard
    exact ⟨x, by simp [hx], fun y hy => by simp [hx] at hy; exact hy⟩
  exact Classical.choose h

/-- The winner is a member of f P. -/
lemma theWinner_mem {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) :
    theWinner f P hf ∈ f P := by
  unfold theWinner
  have h : ∃! x, x ∈ f P := by
    have hcard := hf P
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, hx⟩ := hcard
    exact ⟨x, by simp [hx], fun y hy => by simp [hx] at hy; exact hy⟩
  exact (Classical.choose_spec h).1

/-- If f P = {c}, then the winner is c. -/
lemma theWinner_eq_of_eq_singleton {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) (c : A)
    (hc : f P = {c}) : theWinner f P hf = c := by
  have hmem : theWinner f P hf ∈ f P := theWinner_mem f P hf
  simp only [hc, Finset.mem_singleton] at hmem
  exact hmem

/-- f P = {c} iff theWinner is c. -/
lemma eq_singleton_iff_theWinner_eq {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) (c : A) :
    f P = {c} ↔ theWinner f P hf = c := by
  constructor
  · exact theWinner_eq_of_eq_singleton f P hf c
  · intro hw
    have hcard := hf P
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, hx⟩ := hcard
    have hmem : theWinner f P hf ∈ f P := theWinner_mem f P hf
    simp only [hx, Finset.mem_singleton] at hmem
    -- hmem : theWinner f P hf = x
    -- hw : theWinner f P hf = c
    -- hx : f P = {x}
    -- Goal: f P = {c}
    rw [hmem] at hw
    simp only [hx, hw]


/-! ### Vendored fragment: SocialChoice/Axioms/Core.lean -/



/-- A voting rule is non-trivial if some candidate can lose. -/
def NonTrivial (f : VotingRule) : Prop :=
  ∃ (V A : Type) (instV : Fintype V) (instA : Fintype A),
    let _ := instV
    let _ := instA
    ∃ (P : Profile V A) (c : A), c ∉ f P

/-- A voting rule is onto if every candidate can win. -/
def Onto (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (c : A), ∃ P : Profile V A, f P = {c}


/-! ### Vendored fragment: SocialChoice/Axioms/Unanimity.lean -/



/-- If every voter ranks `c` uniquely first, then `c` is the unique winner. -/
public def Unanimity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty V] (P : Profile V A) (c : A),
    (∀ v : V, TopRank P v c) → f P = {c}


/-! ### Vendored fragment: SocialChoice/Axioms/Strategyproofness.lean -/



/-- Replace one voter's ballot with a new linear order. -/
public noncomputable def updateProfile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (ballot : LinearOrder A) : Profile V A := by
  classical
  exact { pref := fun w => if w = v then ballot else P.pref w }

/-- Strategyproofness for resolute rules: no voter can gain by misreporting. -/
public def ResoluteStrategyproofness (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (v : V) (ballot : LinearOrder A) (x y : A),
    f P = {x} →
    f (updateProfile P v ballot) = {y} →
    ¬ Prefers P v y x


/-! ### Vendored fragment: SocialChoice/Axioms/Dictatorship.lean -/



/-!
# Dictatorship Axiom

A voting rule is **dictatorial** if some voter's top choice always uniquely wins.
-/

/-- A voting rule is dictatorial if some voter's top choice always uniquely wins.
    This is the fully quantified version over all voter/candidate types. -/
def Dictatorial (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty A],
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}

/-- A voting rule is dictatorial for a fixed voter type if some voter's
    top choice always uniquely wins, for all candidate sets. -/
def DictatorialV {V : Type} [Fintype V] (f : VotingRule) : Prop :=
  ∃ d : V, ∀ {A : Type} [Fintype A] [Nonempty A] (P : Profile V A),
    f P = {topChoice P d}

/-- A voting rule is dictatorial for fixed voter and candidate types. -/
def DictatorialVA {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : Profile V A → Finset A) : Prop :=
  ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}


/-! ### Vendored fragment: SocialChoice/Impossibilities/GibbardSatterthwaite/BaseCase.lean -/



/-!
# Gibbard-Satterthwaite Base Case

The base case of the induction proof: for a single voter, any resolute,
unanimous, strategy-proof voting rule is dictatorial.

This is trivially true because with one voter, unanimity forces the rule
to select that voter's top choice.
-/

open Finset

/-- Base case: For a single voter (Unit type), any resolute, unanimous voting rule
    selects the unique voter's top choice. -/
theorem gs_base_case_unit {A : Type} [Fintype A] [Nonempty A]
    (f : VotingRule) (_hf : Resolute f)
    (hf_unan : Unanimity f) :
    ∀ P : Profile Unit A, f P = {topChoice P ()} := by
  intro P
  -- The single voter unanimously ranks topChoice P () first
  have htop : ∀ v : Unit, TopRank P v (topChoice P ()) := by
    intro v
    cases v
    exact topChoice_topRank P ()
  exact hf_unan P (topChoice P ()) htop

/-- Base case with explicit cardinality condition. -/
theorem gs_base_case {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (hcard_V : Fintype.card V = 1)
    (f : VotingRule) (_hf : Resolute f)
    (hf_unan : Unanimity f) :
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d} := by
  -- There's exactly one voter, so pick it
  classical
  have hnonempty : Nonempty V := by
    refine Fintype.card_pos_iff.mp ?_
    simp [hcard_V]
  let _ : Nonempty V := hnonempty
  have hunique := Fintype.card_eq_one_iff.mp hcard_V
  obtain ⟨d, hd⟩ := hunique
  use d
  intro P
  -- All voters equal d, so TopRank P v (topChoice P d) for all v
  have htop : ∀ v : V, TopRank P v (topChoice P d) := by
    intro v
    have hveq := hd v
    rw [hveq]
    exact topChoice_topRank P d
  exact hf_unan P (topChoice P d) htop


/-! ### Vendored fragment: SocialChoice/Impossibilities/GibbardSatterthwaite/Common.lean -/



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


/-! ### Vendored fragment: SocialChoice/Impossibilities/GibbardSatterthwaite/InductionStepCase1.lean -/



/-!
# Gibbard-Satterthwaite Induction Step: Case 1

Case 1 of the induction step: If the dictator in the cloned rule g is
voter i ∈ {3, ..., n} (i.e., i ≠ v₁), then i is also the dictator in f.

## Main Result

* `gs_case1`: If i ≠ v₁ is the dictator in g, then i.val is the dictator in f.
-/

open Finset

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [Nonempty A]

/-- Case 1: If dictator in g is voter i ∈ {3,...,n} (i.e., i.val ≠ v₁),
    then i.val is also a dictator in f. -/
theorem gs_case1
    (f : VotingRule) (hf : Resolute f)
    (hf_sp : ResoluteStrategyproofness f hf)
    (v₁ v₂ : V) (hne : v₁ ≠ v₂)
    (i : {w : V // w ≠ v₂}) (hi : i.val ≠ v₁)
    (hdict_g : ∀ P' : Profile {w : V // w ≠ v₂} A,
        clonedRule f v₁ v₂ hne P' = {topChoice P' i}) :
    ∀ P : Profile V A, f P = {topChoice P i.val} := by
  intro P

  -- The key insight: we can derive f(P) = topChoice(P, i) from the fact that
  -- g dictates for i, combined with strategy-proofness.

  -- Define the reduced profile P' by restricting P to {w : V // w ≠ v₂}
  -- where v₂ is simply dropped.
  let P'_v1 : Profile {w : V // w ≠ v₂} A :=
    { pref := fun w => P.pref w.val }

  let P'_v2 : Profile {w : V // w ≠ v₂} A :=
    { pref := fun w => if w.val = v₁ then P.pref v₂ else P.pref w.val }

  -- From the cloned rule definition:
  -- g(P'_v1) = f(expanded profile where v₂ copies v₁)
  --          = f(P₁, P₁, P₃, ..., Pₙ) [using notation from the paper]

  -- By dictatorship of g at P'_v1: g(P'_v1) = {topChoice P'_v1 i}
  have hg_v1 : clonedRule f v₁ v₂ hne P'_v1 = {topChoice P'_v1 i} := hdict_g P'_v1

  -- By dictatorship of g at P'_v2: g(P'_v2) = {topChoice P'_v2 i}
  have hg_v2 : clonedRule f v₁ v₂ hne P'_v2 = {topChoice P'_v2 i} := hdict_g P'_v2

  -- Note that topChoice P'_v1 i = topChoice P i.val (since P'_v1.pref i = P.pref i.val)
  have htop_v1 : topChoice P'_v1 i = topChoice P i.val := by
    unfold topChoice
    congr 1

  -- And topChoice P'_v2 i = topChoice P i.val (since i.val ≠ v₁, so P'_v2.pref i = P.pref i.val)
  have htop_v2 : topChoice P'_v2 i = topChoice P i.val := by
    unfold topChoice
    congr 1
    simp only [P'_v2, hi, ite_false]

  -- Let a = topChoice P i.val (the dictator's choice)
  let a := topChoice P i.val

  -- So g(P'_v1) = {a} and g(P'_v2) = {a}
  rw [htop_v1] at hg_v1
  rw [htop_v2] at hg_v2

  -- Now unfold the cloned rule:
  -- clonedRule f v₁ v₂ hne P'_v1 = f(expandProfile v₁ v₂ hne P'_v1)
  -- The expanded profile of P'_v1 has:
  --   - v₁ → P.pref v₁
  --   - v₂ → P.pref v₁ (copies v₁)
  --   - w ≠ v₂ → P.pref w
  -- This is the profile (P₁, P₁, P₃, ..., Pₙ)

  -- Similarly for P'_v2, the expanded profile has:
  --   - v₁ → P.pref v₂ (since P'_v2.pref ⟨v₁, hne⟩ = P.pref v₂)
  --   - v₂ → P.pref v₂ (copies v₁'s ballot which is P.pref v₂)
  --   - w ≠ v₂ → P.pref w
  -- This is the profile (P₂, P₂, P₃, ..., Pₙ)

  -- Let Q₁₁ = expandProfile v₁ v₂ hne P'_v1 (profile with v₂ copying v₁)
  -- Let Q₂₂ = expandProfile v₁ v₂ hne P'_v2 (profile with v₂ copying v₂, i.e., both equal P.pref v₂)

  let Q₁₁ := expandProfile v₁ v₂ hne P'_v1
  let Q₂₂ := expandProfile v₁ v₂ hne P'_v2

  have hQ₁₁ : f Q₁₁ = {a} := hg_v1
  have hQ₂₂ : f Q₂₂ = {a} := hg_v2

  -- Now, the actual profile P differs from both Q₁₁ and Q₂₂ only in some ballots.
  -- We need to use strategy-proofness to show f P = {a}.

  -- Strategy:
  -- 1. Q₁₁ differs from P only at v₂ (where Q₁₁ has P.pref v₁, and P has P.pref v₂)
  -- 2. By strategy-proofness, starting from Q₁₁, if we change v₂'s ballot to P.pref v₂,
  --    the outcome should either stay at a or move to something v₂ doesn't prefer over a (in Q₁₁).

  -- Note: Q₁₁ differs from P at v₂:
  -- Q₁₁.pref v₂ = P.pref v₁
  -- P.pref v₂ = P.pref v₂
  -- For w ≠ v₂: Q₁₁.pref w = P.pref w

  -- Actually let's check: expandProfile v₁ v₂ hne P'_v1 at v:
  -- if v = v₂: P'_v1.pref ⟨v₁, hne⟩ = P.pref v₁
  -- if v ≠ v₂: P'_v1.pref ⟨v, _⟩ = P.pref v

  -- So Q₁₁.pref v = if v = v₂ then P.pref v₁ else P.pref v

  -- Let's denote the outcome of f P as b
  let b := theWinner f P hf
  have hfP : f P = {b} := (eq_singleton_iff_theWinner_eq f P hf b).mpr rfl

  -- We want to show b = a

  -- Claim: P = updateProfile Q₁₁ v₂ (P.pref v₂)
  have hP_from_Q₁₁ : P = updateProfile Q₁₁ v₂ (P.pref v₂) := by
    ext w
    by_cases hwv₂ : w = v₂
    · rw [hwv₂, updateProfile_pref_self]
    · rw [updateProfile_pref_of_ne _ _ _ hwv₂]
      have h2 : Q₁₁.pref w = P.pref w := expandProfile_pref_of_ne v₁ v₂ hne P'_v1 hwv₂
      rw [h2]

  -- By strategy-proofness of f applied at Q₁₁:
  -- f Q₁₁ = {a}, f P = {b}
  -- => ¬ Prefers Q₁₁ v₂ b a
  have hfP1 : f (updateProfile Q₁₁ v₂ (P.pref v₂)) = {b} := by
    simpa [hP_from_Q₁₁.symm] using hfP
  have hsp1 : ¬ Prefers Q₁₁ v₂ b a := hf_sp Q₁₁ v₂ (P.pref v₂) a b hQ₁₁ hfP1

  -- Note: Prefers Q₁₁ v₂ uses Q₁₁.pref v₂ = P.pref v₁
  -- So hsp1 says: ¬ (b <_{P.pref v₁} a), i.e., a ≤_{P.pref v₁} b

  -- Similarly, we have Q₂₂ differs from P at v₁:
  -- Q₂₂.pref v = if v = v₂ then P.pref v₂ else (if v = v₁ then P.pref v₂ else P.pref v)
  -- So Q₂₂.pref v₁ = P.pref v₂, Q₂₂.pref v₂ = P.pref v₂, Q₂₂.pref w = P.pref w for w ≠ v₁, v₂

  -- Claim: P = updateProfile Q₂₂ v₁ (P.pref v₁)
  have hP_from_Q₂₂ : P = updateProfile Q₂₂ v₁ (P.pref v₁) := by
    ext w
    by_cases hwv₁ : w = v₁
    · rw [hwv₁, updateProfile_pref_self]
    · have h1 : (updateProfile Q₂₂ v₁ (P.pref v₁)).pref w = Q₂₂.pref w :=
        updateProfile_pref_of_ne Q₂₂ v₁ (P.pref v₁) hwv₁
      by_cases hwv₂ : w = v₂
      · have h2 : Q₂₂.pref w = P.pref w := by
          have hb : Q₂₂.pref w = P'_v2.pref ⟨v₁, hne⟩ := by
            rw [hwv₂]; exact expandProfile_pref_v2 v₁ v₂ hne P'_v2
          rw [hb, hwv₂]; exact if_pos rfl
        rw [h1, h2]
      · have h2 : Q₂₂.pref w = P.pref w := by
          have hb : Q₂₂.pref w = P'_v2.pref ⟨w, hwv₂⟩ := expandProfile_pref_of_ne v₁ v₂ hne P'_v2 hwv₂
          rw [hb]; exact if_neg hwv₁
        rw [h1, h2]

  have hfP2 : f (updateProfile Q₂₂ v₁ (P.pref v₁)) = {b} := by
    simpa [hP_from_Q₂₂.symm] using hfP
  have hsp2 : ¬ Prefers Q₂₂ v₁ b a := hf_sp Q₂₂ v₁ (P.pref v₁) a b hQ₂₂ hfP2

  -- Note: Prefers Q₂₂ v₁ uses Q₂₂.pref v₁ = P.pref v₂
  -- So hsp2 says: ¬ (b <_{P.pref v₂} a), i.e., a ≤_{P.pref v₂} b

  -- Now we have:
  -- - a ≤_{P.pref v₁} b  (from hsp1)
  -- - a ≤_{P.pref v₂} b  (from hsp2)

  -- But we need to show a = b.

  -- The key insight is to use strategy-proofness in the other direction too.
  -- Consider changing v₂'s ballot in P to match v₁ (going backwards):

  -- f P = {b}, and if we change v₂'s ballot to P.pref v₁:
  have hQ₁₁_from_P : Q₁₁ = updateProfile P v₂ (P.pref v₁) := by
    ext v
    by_cases hv : v = v₂
    · rw [hv]
      have h1 : Q₁₁.pref v₂ = P.pref v₁ := expandProfile_pref_v2 v₁ v₂ hne P'_v1
      rw [h1, updateProfile_pref_self]
    · have h1 : Q₁₁.pref v = P.pref v := expandProfile_pref_of_ne v₁ v₂ hne P'_v1 hv
      have h2 : (updateProfile P v₂ (P.pref v₁)).pref v = P.pref v :=
        updateProfile_pref_of_ne P v₂ (P.pref v₁) hv
      rw [h1, h2]

  -- Actually we need P without the rewriting
  have hfP_orig : f P = {b} := hfP

  rw [hQ₁₁_from_P] at hQ₁₁
  have hsp3 : ¬ Prefers P v₂ a b := hf_sp P v₂ (P.pref v₁) b a hfP_orig hQ₁₁

  -- Similarly in the other direction for v₁:
  have hQ₂₂_from_P : Q₂₂ = updateProfile P v₁ (P.pref v₂) := by
    ext v
    by_cases hv₁ : v = v₁
    · rw [hv₁]
      have h1 : Q₂₂.pref v₁ = P.pref v₂ := by
        have hb : Q₂₂.pref v₁ = P'_v2.pref ⟨v₁, hne⟩ := expandProfile_pref_of_ne v₁ v₂ hne P'_v2 hne
        rw [hb]; exact if_pos rfl
      rw [h1, updateProfile_pref_self]
    · by_cases hv₂ : v = v₂
      · rw [hv₂]
        have h1 : Q₂₂.pref v₂ = P.pref v₂ := by
          have hb : Q₂₂.pref v₂ = P'_v2.pref ⟨v₁, hne⟩ := expandProfile_pref_v2 v₁ v₂ hne P'_v2
          rw [hb]; exact if_pos rfl
        have h2 : (updateProfile P v₁ (P.pref v₂)).pref v₂ = P.pref v₂ :=
          updateProfile_pref_of_ne P v₁ (P.pref v₂) (hv₂ ▸ hv₁)
        rw [h1, h2]
      · have h1 : Q₂₂.pref v = P.pref v := by
          have hb : Q₂₂.pref v = P'_v2.pref ⟨v, hv₂⟩ := expandProfile_pref_of_ne v₁ v₂ hne P'_v2 hv₂
          rw [hb]; exact if_neg hv₁
        have h2 : (updateProfile P v₁ (P.pref v₂)).pref v = P.pref v :=
          updateProfile_pref_of_ne P v₁ (P.pref v₂) hv₁
        rw [h1, h2]

  rw [hQ₂₂_from_P] at hQ₂₂
  have hsp4 : ¬ Prefers P v₁ a b := hf_sp P v₁ (P.pref v₂) b a hfP_orig hQ₂₂

  -- Now hsp3 says: ¬ (a <_{P.pref v₂} b), i.e., b ≤_{P.pref v₂} a
  -- Combined with hsp2: a ≤_{P.pref v₂} b
  -- This gives a = b under P.pref v₂

  -- Similarly for v₁'s preferences

  -- From hsp1: ¬ (b <_{P.pref v₁} a), so a ≤_{P.pref v₁} b
  -- From hsp4: ¬ (a <_{P.pref v₁} b), so b ≤_{P.pref v₁} a
  -- Together: a = b under P.pref v₁

  -- Use linear order antisymmetry to show b = a, then rewrite the outcome
  unfold Prefers at hsp1 hsp4
  have hQ₁₁_v₂ : Q₁₁.pref v₂ = P.pref v₁ := by
    simp [Q₁₁, expandProfile, P'_v1]

  have hsp1' : ¬ (P.pref v₁).lt b a := by
    rw [hQ₁₁_v₂] at hsp1
    exact hsp1

  have hsp4' : ¬ (P.pref v₁).lt a b := by
    simpa using hsp4

  letI := P.pref v₁
  have hle1 : a ≤ b := not_lt.mp hsp1'
  have hle2 : b ≤ a := not_lt.mp hsp4'
  have hba : a = b := le_antisymm hle1 hle2

  have hba' : b = a := hba.symm
  -- Conclude
  simpa [hba'] using hfP_orig


/-! ### Vendored fragment: SocialChoice/Impossibilities/GibbardSatterthwaite/InductionStepCase2.lean -/



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
@[reducible] noncomputable def someLinearOrder (A : Type) [Fintype A] : LinearOrder A := by
  classical
  let e := Fintype.equivFin A
  exact LinearOrder.lift' e e.injective

@[reducible] noncomputable def ballotWithTop {A : Type} [Fintype A] (c : A) : LinearOrder A := by
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
@[reducible] noncomputable def ballotWithTopTwo {A : Type} [Fintype A] (a b : A)
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


/-! ### Vendored fragment: SocialChoice/Impossibilities/GibbardSatterthwaite/Main.lean -/



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
public theorem gibbard_satterthwaite
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
