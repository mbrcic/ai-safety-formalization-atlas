/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/


module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Unbounded Search Computability (The Mu-Operator)

This module provides the "Computability Bridge" for unbounded search.
It proves that if a predicate `P` is decidable and computable, and if an answer
is guaranteed to exist for every input, then the search for the minimal such answer
(`Nat.find`) is a total computable function.
-/

namespace Kolmogorov

/-! ### Basic Math Computability -/

/-- Auxiliary lemma: Exponentiation `2^k` is a computable function. -/
public lemma Computable.pow2 : Computable (fun k : ℕ ↦ 2 ^ k) := by
  apply Primrec.to_comp
  rw [Primrec.nat_iff]
  have h_eq : (fun k ↦ (Nat.pair 2 k).unpair.1 ^ (Nat.pair 2 k).unpair.2) =
              (fun k ↦ 2 ^ k) := by
    funext k
    simp only [Nat.unpair_pair]
  rw [← h_eq]
  exact Nat.Primrec.pow.comp (Nat.Primrec.pair (Nat.Primrec.const 2) Nat.Primrec.id)

/-! ### General Unbounded Search -/

/-- **General unbounded search.** If a predicate `P a n` is decidable and the
uncurried decision procedure is computable, and if for every `a` there exists an
`n` with `P a n`, then the minimal-witness function `a ↦ Nat.find (h a)` is total
computable. This is the key bridge `Nat.find = Nat.rfind` for total decidable
computable predicates. -/
public lemma Computable.natFind {α : Type*} [Primcodable α] {P : α → ℕ → Prop}
    [∀ a n, Decidable (P a n)]
    (hP : Computable (fun p : α × ℕ ↦ decide (P p.1 p.2)))
    (h : ∀ a, ∃ n, P a n) :
    Computable (fun a ↦ Nat.find (h a)) := by
  have hp2 : Partrec₂ (fun (a : α) (n : ℕ) ↦ (Part.some (decide (P a n)) : Part Bool)) := by
    have : Computable₂ (fun (a : α) (n : ℕ) ↦ decide (P a n)) := hP
    exact this.partrec₂
  have hr := Partrec.rfind hp2
  refine hr.of_eq (fun a ↦ ?_)
  change (Nat.rfind fun n ↦ Part.some (decide (P a n))) = Part.some (Nat.find (h a))
  rw [Part.eq_some_iff, Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · simp only [Part.mem_some_iff]
    exact (decide_eq_true (Nat.find_spec (h a))).symm
  · intro m hm
    simp only [Part.mem_some_iff]
    exact (decide_eq_false (Nat.find_min (h a) hm)).symm

/-! ### Corollaries -/

/-- Equality Search: If a function `f` is computable and surjective,
its inverse search function is computable. -/
public lemma Computable.inverse (f : ℕ → ℕ) (hf_comp : Computable f)
    (h_surj : ∀ y, ∃ x, f x = y) :
    Computable (fun y ↦ Nat.find (h_surj y)) := by
  apply Computable.natFind (P := fun y x ↦ f x = y)
  have h_pair : Computable (fun p : ℕ × ℕ ↦ (f p.2, p.1)) :=
    (hf_comp.comp Computable.snd).pair Computable.fst
  obtain ⟨_, h_eq⟩ := Primrec.eq (α := ℕ)
  refine Computable.of_eq ((Primrec.to_comp h_eq).comp h_pair) (fun p ↦ ?_)
  exact congrArg (fun inst ↦ @decide _ inst) (Subsingleton.elim _ _)

/-- Isolates the strict inequality comparison operator on natural numbers. -/
public lemma Computable.natLt : Computable (fun p : ℕ × ℕ ↦ decide (p.1 < p.2)) := by
  obtain ⟨_, h_prim⟩ := Primrec.nat_lt
  convert Primrec.to_comp h_prim

/-- Proves the computability of a predicate `P` defined by a strict inequality
between two computable functions. -/
public lemma Computable.testP {P : ℕ → ℕ → Prop}
    {f g : ℕ → ℕ} (hf : Computable f) (hg : Computable g)
    (h_equiv : ∀ k n, P k n ↔ f n > g k) :
    ComputablePred (fun p : ℕ × ℕ ↦ P p.1 p.2) := by
  letI : DecidableRel P := fun k n ↦ decidable_of_iff _ (h_equiv k n).symm
  let h_pair := (hg.comp Computable.fst).pair (hf.comp Computable.snd)
  let h_alg := Computable.natLt.comp h_pair
  have h_comp : Computable (fun p : ℕ × ℕ ↦ decide (P p.1 p.2)) :=
    Computable.of_eq h_alg (fun p ↦ by
      have h : P p.1 p.2 ↔ g p.1 < f p.2 := h_equiv p.1 p.2
      cases h_dec : decide (g p.1 < f p.2)
      · have h_not : ¬ (g p.1 < f p.2) := of_decide_eq_false h_dec
        exact (decide_eq_false (mt h.mp h_not)).symm
      · have h_yes : g p.1 < f p.2 := of_decide_eq_true h_dec
        exact (decide_eq_true (h.mpr h_yes)).symm)
  exact Computable.computablePred h_comp

/-- Inequality Search: A modular search function over a predicate defined
by a strict inequality between two computable functions. -/
public lemma Computable.searchCore {P : ℕ → ℕ → Prop} [DecidableRel P]
    (f : ℕ → ℕ) (hf_comp : Computable f)
    (g : ℕ → ℕ) (hg_comp : Computable g)
    (h_equiv : ∀ k n, P k n ↔ f n > g k)
    (h_unbounded : ∀ k, ∃ n, P k n) :
    Computable (fun k ↦ Nat.find (h_unbounded k)) := by
  have hcomp : Computable (fun p : ℕ × ℕ ↦ decide (P p.1 p.2)) := by
    have h_pair := (hg_comp.comp Computable.fst).pair (hf_comp.comp Computable.snd)
    have h_alg := Computable.natLt.comp h_pair
    refine Computable.of_eq h_alg (fun p ↦ ?_)
    have h : P p.1 p.2 ↔ g p.1 < f p.2 := by rw [h_equiv]
    exact decide_eq_decide.mpr h.symm
  exact Computable.natFind hcomp h_unbounded

end Kolmogorov
