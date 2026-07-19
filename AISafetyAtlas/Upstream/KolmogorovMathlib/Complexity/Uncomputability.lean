/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/


module

public import AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.NatComplexity
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Properties
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Core.Basic
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.NatEncoding
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.UnboundedSearch
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.PartrecCode
public import Mathlib.Order.Lattice

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Uncomputability of Kolmogorov Complexity

This module proves that Kolmogorov Complexity is not computable.
Instead of just proving that `plainK` is uncomputable, we prove a much stronger,
generalized result: **There exists no computable, unbounded lower bound for `plainK`**.

The proof relies on Berry's Paradox: if such a bound existed, we could compute
a number with "too much" complexity for its small description length.
-/

namespace Kolmogorov

/-! ### Growth Lemma & Paradox Base -/

/-- Helper for the growth lemma to isolate the induction step.
    Proves that linear growth cannot keep up with exponential growth. -/
private lemma growthArithmeticHelper (n : ℕ) : n + 5 + n < 2 ^ (n + 5) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- Growth Lemma: `2^k` eventually dominates any logarithmic description.
    For any constant `c`, there exists a `k` such that `|k| + c < 2^k`. -/
public lemma growthLemma (c : ℕ) :
    ∃ k, (programLength (Nat.bits k) : ENat) + (c : ENat) < (2^k : ENat) := by
  let k := c + 5
  refine ⟨k, ?_⟩
  have h_len := length_natBits_le k
  have h_arith : (programLength (Nat.bits k) : ENat) + c ≤ (k : ENat) + c := by
    dsimp [programLength]
    exact add_le_add (ENat.coe_le_coe.mpr h_len) (le_refl (c : ENat))
  have h_exp : (k : ENat) + c < (2^k : ENat) := by
    apply ENat.coe_lt_coe.mpr
    dsimp [k]
    exact growthArithmeticHelper c
  exact lt_of_le_of_lt h_arith h_exp

/-! ### Computability Bridge Integration -/

/-- The unbounded search function (Berry's algorithm) is computable
    because we are searching over a computable lower bound `f`. -/
public lemma Computable.findComplex (f : ℕ → ℕ) (h_f_comp : Computable f)
    (h_unb : ∀ M, ∃ n, f n > M) :
    Computable (fun k ↦ Nat.find (h_unb (2^k))) := by
  exact Computable.searchCore f h_f_comp (fun k ↦ 2^k) Computable.pow2 (fun _ _ ↦ Iff.rfl) (fun k ↦ h_unb (2^k))

/-- Computable functions on natural numbers do not increase complexity by more than a constant. -/
public lemma plainKNatCompLe (U : Map) (hU : isOptimalConditional U)
    (g : ℕ → ℕ) (hg : Computable g) :
    ∃ c_g : ℕ, ∀ k, plainKNat U (g k) ≤ plainKNat U k + (c_g : ENat) := by
  let f_str : BitString → BitString := fun s ↦ Nat.bits (g (decodeBits s))
  have hf_comp : Computable f_str :=
    natBitsComputable.comp (hg.comp decodeBitsComputable)
  obtain ⟨c_g, hc⟩ := plainKMapLe U hU f_str hf_comp
  refine ⟨c_g, ?_⟩
  intro k
  have h_bound := hc (Nat.bits k)
  dsimp [f_str] at h_bound
  rw [decodeBits_natBits] at h_bound
  exact h_bound

/-- Final assembly: the complexity of Berry's algorithm output is bounded by `|k| + c`. -/
public lemma plainKNatFindComplexLe (U : Map) (hU : isOptimalConditional U)
    (f : ℕ → ℕ) (h_f_comp : Computable f) (h_unb : ∀ M, ∃ n, f n > M) :
    ∃ c : ℕ, ∀ k, plainKNat U (Nat.find (h_unb (2^k))) ≤
      (programLength (Nat.bits k) : ENat) + (c : ENat) := by
  let g := fun k ↦ Nat.find (h_unb (2^k))
  have hg_comp : Computable g := Computable.findComplex f h_f_comp h_unb
  obtain ⟨c_g, h_bound_g⟩ := plainKNatCompLe U hU g hg_comp
  obtain ⟨c_len, h_bound_len⟩ := plainKNatLeLength U hU
  refine ⟨c_g + c_len, ?_⟩
  intro k
  calc
    plainKNat U (g k)
      ≤ plainKNat U k + (c_g : ENat) := h_bound_g k
    _ ≤ ((programLength (Nat.bits k) : ENat) + c_len) + c_g := add_le_add (h_bound_len k) le_rfl
    _ = (programLength (Nat.bits k) : ENat) + ((c_g + c_len : ℕ) : ENat) := by
      push_cast
      rw [add_assoc, add_comm (c_len : ENat)]

/-! ### Main Theorems -/

/-- General Uncomputability Theorem:
    There is no computable, unbounded lower bound for Kolmogorov Complexity. -/
public theorem noComputableUnboundedLowerBound (U : Map) (hU : isOptimalConditional U) :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧
      (∀ n, (f n : ENat) ≤ plainKNat U n) ∧
      (∀ M, ∃ n, f n > M) := by
  rintro ⟨f, h_f_comp, h_lower, h_unb⟩
  let g (k : ℕ) := Nat.find (h_unb (2^k))
  obtain ⟨c, hc⟩ := plainKNatFindComplexLe U hU f h_f_comp h_unb
  obtain ⟨k, hk⟩ := growthLemma c
  have h_top := hc k
  have h_find : 2^k < f (g k) := Nat.find_spec (h_unb (2^k))
  have h_find_enat : (2^k : ENat) < (f (g k) : ENat) := ENat.coe_lt_coe.mpr h_find
  have h_chain_1 : (2^k : ENat) < plainKNat U (g k) :=
    lt_of_lt_of_le h_find_enat (h_lower (g k))
  have h_chain_2 : plainKNat U (g k) < (2^k : ENat) :=
    lt_of_le_of_lt h_top hk
  exact lt_irrefl _ (lt_trans h_chain_1 h_chain_2)

/-- Main Theorem (Corollary): Kolmogorov complexity is not computable. -/
public theorem notComputablePlainKNat (U : Map) (hU : isOptimalConditional U) :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧ ∀ n, plainKNat U n = (f n : ENat) := by
  rintro ⟨f, h_f_comp, h_f_eq⟩
  apply noComputableUnboundedLowerBound U hU
  refine ⟨f, h_f_comp, fun n ↦ le_of_eq (h_f_eq n).symm, fun M ↦ ?_⟩
  obtain ⟨n, hn⟩ := existsPlainKNatGt U M
  refine ⟨n, ?_⟩
  rw [h_f_eq n] at hn
  exact ENat.coe_lt_coe.mp hn

end Kolmogorov
