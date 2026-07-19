/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/


module

public import AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Uncomputability

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Chaitin's Incompleteness Theorem

This module formalizes Chaitin's Incompleteness Theorem within an abstract formal system.
We define a formal system by its provability relation, its computable enumerator of theorems,
and its ability to express statements of the form "K(x) > L".

The main result proves that for any sound, recursively enumerable formal system,
there exists a constant `c` such that the system cannot prove any true statement
of the form `K(x) > L` for `L > c`. This serves as an information-theoretic equivalent
to Gödel's First Incompleteness Theorem.
-/

namespace Kolmogorov

/-! ### Abstract Formal Systems -/

/-- An abstract formal system capable of expressing statements about Kolmogorov complexity.
    It requires a computable enumerator of theorems and a computable parser for statements
    of the form `K(x) > L`. -/
public structure FormalSystem (U : Map) where
  /-- The type of formulas in the formal system. -/
  Formula : Type
  enc : Primcodable Formula
  /-- The provability relation for formulas. -/
  provable : Formula → Prop
  /-- The enumerator for theorems in the system. -/
  enumThm : ℕ → Option Formula
  hEnumComp : Computable enumThm
  hEnumExact : ∀ φ, provable φ ↔ ∃ i, enumThm i = some φ
  /-- Formula representing the statement that K(x) > L. -/
  exprKGt : ℕ → ℕ → Formula
  /-- Parser that attempts to extract `(x, L)` from a formula asserting `K(x) > L`. -/
  parseKGt : Formula → Option (ℕ × ℕ)
  hParseComp : Computable parseKGt
  hParseForward : ∀ x L, parseKGt (exprKGt x L) = some (x, L)
  hParseInv : ∀ φ x L, parseKGt φ = some (x, L) → φ = exprKGt x L
  hSound : ∀ x L, provable (exprKGt x L) → (L : ENat) < plainKNat U x

attribute [instance] FormalSystem.enc

/-! ### Enumerator Construction -/

namespace FormalSystem

variable {U : Map} (F : FormalSystem U)

/-- Combines the theorem enumerator with the parser to directly enumerate proven
bounds `(x, L)`. -/
@[expose]
public def enumBounds (i : ℕ) : Option (ℕ × ℕ) :=
  (F.enumThm i).bind F.parseKGt

/-- A boolean check answering whether the `i`-th enumerated bound asserts `L > M`. -/
@[expose]
public def isBoundGt (M i : ℕ) : Bool :=
  match F.enumBounds i with
  | some (_, L) => decide (L > M)
  | none => false

/-- The bound enumerator is computable since it is a composition of computable functions. -/
public lemma enumBoundsComputable : Computable F.enumBounds := by
  have h_eq : F.enumBounds = fun i ↦ Option.casesOn (F.enumThm i) none F.parseKGt := by
    funext i
    dsimp [enumBounds, Option.bind]
    cases F.enumThm i <;> rfl
  rw [h_eq]
  exact Computable.option_casesOn F.hEnumComp
    (Computable.const none)
    (F.hParseComp.comp (@Computable.snd ℕ F.Formula _ _))

/-- The threshold checker is computable. -/
public lemma isBoundGtComputable : Computable (fun p : ℕ × ℕ ↦ F.isBoundGt p.1 p.2) := by
  have h_eq : (fun p : ℕ × ℕ ↦ F.isBoundGt p.1 p.2) =
    fun p ↦ Option.casesOn (F.enumBounds p.2) false (fun xL ↦ decide (p.1 < xL.2)) := by
    funext p
    dsimp [isBoundGt]
    cases F.enumBounds p.2 <;> rfl
  rw [h_eq]
  have h_opt : Computable (fun p : ℕ × ℕ ↦ F.enumBounds p.2) := by
    change Computable (F.enumBounds ∘ Prod.snd)
    exact F.enumBoundsComputable.comp Computable.snd
  have h_def : Computable (fun p : ℕ × ℕ ↦ false) :=
    Computable.const false
  have h_fst_fst : Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ p.1.1) := by
    change Computable (Prod.fst ∘ Prod.fst)
    exact Computable.fst.comp Computable.fst
  have h_snd_snd : Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ p.2.2) := by
    change Computable (Prod.snd ∘ Prod.snd)
    exact Computable.snd.comp Computable.snd
  have h_pair : Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ (p.1.1, p.2.2)) :=
    h_fst_fst.pair h_snd_snd
  have h_some : Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ decide (p.1.1 < p.2.2)) := by
    let Lt := fun q : ℕ × ℕ ↦ decide (q.1 < q.2)
    let Pair := fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ (p.1.1, p.2.2)
    change Computable (Lt ∘ Pair)
    exact Computable.natLt.comp h_pair
  exact Computable.option_casesOn h_opt h_def h_some

/-- Extracting the first component from the bound enumerator along a computable
search function is computable. -/
public lemma enumBoundsFirstComputable (F : FormalSystem U) (search : ℕ → ℕ)
    (hsearch : Computable search) :
    Computable (fun k : ℕ ↦
      Option.casesOn (motive := fun _ ↦ ℕ) (F.enumBounds (search k)) 0
        (fun xL : ℕ × ℕ ↦ xL.1)) := by
  have h_opt : Computable (fun k : ℕ ↦ F.enumBounds (search k)) := by
    change Computable (F.enumBounds ∘ search)
    exact F.enumBoundsComputable.comp hsearch
  have h_def : Computable (fun _ : ℕ ↦ 0) := Computable.const 0
  have h_some : Computable (fun p : ℕ × (ℕ × ℕ) ↦ p.2.1) := by
    change Computable (Prod.fst ∘ Prod.snd)
    exact Computable.fst.comp Computable.snd
  exact Computable.option_casesOn h_opt h_def h_some

/-- If the enumerator outputs a bound, that bound is sound (true) in the underlying metric. -/
public lemma enumBoundsSound (i x L : ℕ) (h : F.enumBounds i = some (x, L)) :
    (L : ENat) < plainKNat U x := by
  unfold enumBounds at h
  cases h_thm : F.enumThm i with
  | none =>
    rw [h_thm] at h
    contradiction
  | some phi =>
    rw [h_thm] at h
    change F.parseKGt phi = some (x, L) at h
    have h_eq : phi = F.exprKGt x L := F.hParseInv phi x L h
    have h_prov : F.provable phi := (F.hEnumExact phi).mpr ⟨i, h_thm⟩
    rw [h_eq] at h_prov
    exact F.hSound x L h_prov

public lemma Computable.decide_eq_true {α : Type*} [Primcodable α] {f : α → Bool} (hf : Computable f) :
  Computable (fun a ↦ decide (f a = true)) :=
  hf.of_eq (fun a ↦ (Bool.decide_coe (f a)).symm)

-- The decidable predicate used in the Chaitin diagonal search is computable.
public lemma isBoundGtSearchPredicateComputable :
    Computable (fun p : ℕ × ℕ ↦ F.isBoundGt (2 ^ p.1) p.2) := by
  have hpair : Computable (fun p : ℕ × ℕ ↦ (2 ^ p.1, p.2)) :=
    (Computable.pow2.comp Computable.fst).pair Computable.snd
  apply Computable.comp
    (f := fun p : ℕ × ℕ ↦ F.isBoundGt p.1 p.2)
    (g := fun p : ℕ × ℕ ↦ (2 ^ p.1, p.2))
  · exact F.isBoundGtComputable
  · exact hpair

public lemma isBoundGtSearchComputable
    (h_exists : ∀ M : ℕ, ∃ i, F.isBoundGt M i = true) :
    Computable (fun k : ℕ ↦ Nat.find (h_exists (2 ^ k))) := by
  exact Computable.natFind
    (Computable.decide_eq_true (isBoundGtSearchPredicateComputable F))
    (fun k ↦ h_exists (2 ^ k))

/-! ### Chaitin's Bound -/

-- The large unbounded-search / diagonalization argument elaborates many composed
-- computability facts; the heaviest search/extractor parts are factored into
-- named lemmas above so the main diagonalization proof remains predictable.
/-- Every sound formal system has a constant `c` such that it cannot prove
    any statement of the form `K(x) > L` for `L > c`. -/
public theorem chaitinBound (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ i x L, F.enumBounds i = some (x, L) → L ≤ c := by
  by_contra h_unb_inf
  -- Push the negation inward: `¬ ∀ …, L ≤ c` becomes `∃ …, c < L`.
  push Not at h_unb_inf
  have h_exists (M : ℕ) : ∃ i, F.isBoundGt M i = true := by
    obtain ⟨i, x, L, h_eq, h_gt⟩ := h_unb_inf M
    refine ⟨i, ?_⟩
    unfold isBoundGt
    rw [h_eq]
    exact decide_eq_true h_gt
  let search (k : ℕ) : ℕ := Nat.find (h_exists (2^k))
  let g (k : ℕ) : ℕ :=
    match F.enumBounds (search k) with
    | some (x, _) => x
    | none => 0
  -- 1. Computability of the search function
  have h_search_comp : Computable search :=
    F.isBoundGtSearchComputable h_exists
  -- 2. Computability of the final extractor function
  have hg_comp : Computable g := by
    have h_eq : g = fun k : ℕ ↦
        Option.casesOn (motive := fun _ ↦ ℕ) (F.enumBounds (search k)) 0
          (fun xL : ℕ × ℕ ↦ xL.1) := by
      funext k; dsimp [g]; cases F.enumBounds (search k) <;> rfl
    rw [h_eq]
    exact F.enumBoundsFirstComputable search h_search_comp
  -- 3. Constructing the paradox
  let fMap := fun s ↦ Nat.bits (g (decodeBits s))
  have hf_comp : Computable fMap := natBitsComputable.comp (hg_comp.comp decodeBitsComputable)
  obtain ⟨cG, h_bound_g⟩ := plainKMapLe U hU fMap hf_comp
  obtain ⟨cLen, h_bound_len⟩ := plainKNatLeLength U hU
  let cTotal := cG + cLen
  obtain ⟨k, hk⟩ := growthLemma cTotal
  have h_spec : F.isBoundGt (2^k) (search k) = true := Nat.find_spec (h_exists (2^k))
  unfold isBoundGt at h_spec
  cases h_match : F.enumBounds (search k) with
  | none =>
    rw [h_match] at h_spec
    contradiction
  | some res =>
    obtain ⟨x, L⟩ := res
    have h_gt : 2^k < L := by
      rw [h_match] at h_spec
      exact of_decide_eq_true h_spec
    have h_sound := F.enumBoundsSound (search k) x L h_match
    have hg_val : g k = x := by
      dsimp [g]
      rw [h_match]
    have h_low : (2^k : ENat) < plainKNat U (g k) := by
      rw [hg_val]
      exact lt_trans (ENat.coe_lt_coe.mpr h_gt) h_sound
    have h_top :
        plainKNat U (g k) ≤ (programLength (Nat.bits k) : ENat) + (cTotal : ENat) := by
      have h1 := h_bound_g (Nat.bits k)
      dsimp [fMap] at h1
      rw [decodeBits_natBits] at h1
      have h2 := h_bound_len k
      calc plainKNat U (g k)
        ≤ plainKNat U k + (cG : ENat) := h1
        _ ≤ ((programLength (Nat.bits k) : ENat) + cLen) + cG := add_le_add h2 le_rfl
        _ = (programLength (Nat.bits k) : ENat) + (cTotal : ENat) := by
          dsimp [cTotal]
          push_cast
          rw [add_assoc, add_comm (cLen : ENat)]
    exact lt_irrefl _ (lt_of_le_of_lt h_top (lt_trans hk h_low))

/-! ### The Incompleteness Theorem -/

/-- Chaitin's Incompleteness Theorem:
    In any sufficiently strong, sound, and computably enumerable formal system,
    there exist numbers `x` and thresholds `L` such that `K(x) > L` is true,
    but cannot be proven by the system. -/
public theorem chaitinIncompleteness (hU : isOptimalConditional U) :
    ∃ x L : ℕ,
      (L : ENat) < plainKNat U x ∧
      ¬ F.provable (F.exprKGt x L) := by
  obtain ⟨c, hc⟩ := F.chaitinBound hU
  let L := c + 1
  obtain ⟨x, hx⟩ := existsPlainKNatGt U L
  refine ⟨x, L, hx, ?_⟩
  intro h_prov
  obtain ⟨i, hi⟩ := (F.hEnumExact _).mp h_prov
  have h_eb : F.enumBounds i = some (x, L) := by
    unfold enumBounds
    rw [hi]
    exact F.hParseForward x L
  have h_le_c := hc i x L h_eb
  omega

end FormalSystem
end Kolmogorov
