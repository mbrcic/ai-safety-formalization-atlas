/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/


module

public import AISafetyAtlas.Upstream.KolmogorovMathlib.Core.Basic
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.RecursivelyEnumerable
public import AISafetyAtlas.Upstream.KolmogorovMathlib.Foundation.UnboundedSearch
public import Mathlib.Computability.Partrec
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.List.Basic

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Basic Properties of Kolmogorov Complexity

This module establishes the foundational inequalities of algorithmic information theory
using an optimal universal decompressor `U`. It proves that:
* `plainK(x) ≤ |x| + c` (strings can be compressed no worse than their literal length).
* `condK(x|x) ≤ c` (knowing the answer gives constant complexity).
* `condK(x|y) ≤ plainK(x) + c` (conditioning only reduces complexity).
* `condK(f(x)|y) ≤ condK(x|y) + c` (computable functions do not add information).

It also establishes the computability properties (RE and co-RE) of the complexity metric.
-/

namespace Kolmogorov

/-! ### Boundary API -/

/-- The conditional complexity is infinite (`⊤`) if and only if
    there is no program that produces `x` given context `y` on map `D`. -/
public lemma condKEqTopIff (D : Map) (x y : BitString) :
    condK D x y = ⊤ ↔ ¬ ∃ p, x ∈ D (p, y) := by
  constructor
  · intro h ⟨p, hp⟩
    have h_mem : (programLength p : ENat) ∈ candidateLengths D x y := ⟨p, hp, rfl⟩
    have h_le : condK D x y ≤ (programLength p : ENat) := sInf_le h_mem
    rw [h] at h_le
    have h_not_top : ¬ (⊤ ≤ (programLength p : ENat)) := by simp
    exact h_not_top h_le
  · intro h_none
    have h_empty : candidateLengths D x y = ∅ := by
      ext n; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨p', hp', rfl⟩
      exact h_none ⟨p', hp'⟩
    change sInf (candidateLengths D x y) = ⊤
    rw [h_empty]
    exact sInf_empty

/-! ### Fundamental Inequalities -/

/-- Plain complexity of a string is bounded by its length plus a constant. -/
public theorem plainKLeLength (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, plainK U x ≤ (programLength x : ENat) + c := by
  let id_decompressor : Map := fun (p, _) ↦ Part.some p
  obtain ⟨c, hc⟩ := hU.2 id_decompressor (Computable.partrec Computable.fst)
  use c; intro x
  apply le_trans (hc x [])
  gcongr
  apply sInf_le
  exact ⟨x, ⟨trivial, rfl⟩, rfl⟩

/-- The conditional complexity of a string given itself is bounded by a constant. -/
public theorem condKSelf (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, condK U x x ≤ (c : ENat) := by
  let ctx_decompressor : Map := fun (_, y) ↦ Part.some y
  obtain ⟨c, hc⟩ := hU.2 ctx_decompressor (Computable.partrec Computable.snd)
  use c; intro x
  calc
    condK U x x ≤ condK ctx_decompressor x x + c := hc x x
    _           ≤ 0 + c                            := by
      gcongr
      apply sInf_le
      exact ⟨[], ⟨trivial, rfl⟩, rfl⟩
    _           = c                                := zero_add _

/-- Conditioning only reduces complexity. -/
public theorem condKLePlainK (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y, condK U x y ≤ plainK U x + (c : ENat) := by
  let D : Map := fun p ↦ U (p.1, [])
  have hD : isDecompressor D :=
    Partrec.comp hU.1 (Computable.pair Computable.fst (Computable.const []))
  obtain ⟨c, hc⟩ := hU.2 D hD
  use c; intro x y
  exact le_trans (hc x y) le_rfl

/-- The conditional complexity of `f(x)` given `x` is bounded by a constant. -/
public theorem condKComp (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, condK U (f x) x ≤ (c : ENat) := by
  let f_decompressor : Map := fun (_, y) ↦ Part.some (f y)
  have hF : isDecompressor f_decompressor :=
    Computable.partrec (Computable.comp hf Computable.snd)
  obtain ⟨c, hc⟩ := hU.2 f_decompressor hF
  use c; intro x
  calc
    condK U (f x) x ≤ condK f_decompressor (f x) x + c := hc (f x) x
    _               ≤ 0 + c                            := by
      gcongr
      apply sInf_le
      exact ⟨[], ⟨trivial, rfl⟩, rfl⟩
    _               = c                                := zero_add _

/-- Applying a computable function does not increase conditional complexity. -/
public theorem condKMapLe (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x y, condK U (f x) y ≤ condK U x y + (c : ENat) := by
  let D : Map := fun pair ↦ (U pair).map f
  have hD : isDecompressor D := Partrec.map hU.1 (Computable.comp hf Computable.snd)
  obtain ⟨c, hc⟩ := hU.2 D hD
  use c; intro x y
  apply le_trans (hc (f x) y)
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, ⟨h_dom, h_eq⟩, rfl⟩
  exact ⟨p, ⟨h_dom, congrArg f h_eq⟩, rfl⟩

/-- Applying a computable function does not increase plain complexity. -/
public theorem plainKMapLe (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x, plainK U (f x) ≤ plainK U x + (c : ENat) := by
  let D : Map := fun pair ↦ (U (pair.1, [])).map f
  have hD : isDecompressor D := Partrec.map
    (Partrec.comp hU.1 (Computable.pair Computable.fst (Computable.const [])))
    (Computable.comp hf Computable.snd)
  obtain ⟨c, hc⟩ := hU.2 D hD
  use c; intro x
  apply le_trans (hc (f x) [])
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, ⟨h_dom, h_eq⟩, rfl⟩
  exact ⟨p, ⟨h_dom, congrArg f h_eq⟩, rfl⟩

/-! ### Computability and Enumerability (RE / co-RE) -/

/-- `K(x|y) ≤ N` iff there exists a program of length `≤ N` that produces `x`. -/
public lemma condKLeIff (D : Map) (x y : BitString) (N : ℕ) :
    condK D x y ≤ (N : ENat) ↔ ∃ p, programLength p ≤ N ∧ produces D p y x := by
  constructor
  · intro h_le
    by_contra h_not
    push Not at h_not
    have h_bound : ∀ n ∈ candidateLengths D x y, ((N + 1 : ℕ) : ENat) ≤ n := by
      rintro _ ⟨p, hp_prod, rfl⟩
      have h_gt : N + 1 ≤ programLength p := by
        have h_contra : ¬ (programLength p ≤ N) := fun hp_len ↦ h_not p hp_len hp_prod
        omega
      exact_mod_cast h_gt
    have h_le_inf : ((N + 1 : ℕ) : ENat) ≤ sInf (candidateLengths D x y) := le_sInf h_bound
    have h_contra : ((N + 1 : ℕ) : ENat) ≤ (N : ENat) := le_trans h_le_inf h_le
    replace h_contra : N + 1 ≤ N := by exact_mod_cast h_contra
    omega
  · rintro ⟨p, hp_len, hp_prod⟩
    have h_mem : (programLength p : ENat) ∈ candidateLengths D x y := ⟨p, hp_prod, rfl⟩
    exact le_trans (sInf_le h_mem) (by exact_mod_cast hp_len)

/-- The strict inequality `N < K(x|y)` iff no program of length `≤ N` produces `x`. -/
public lemma condKGtIff (D : Map) (x y : BitString) (N : ℕ) :
    (N : ENat) < condK D x y ↔ ∀ p, programLength p ≤ N → ¬ produces D p y x := by
  rw [← not_le]
  rw [condKLeIff]
  push Not
  rfl

/-! ### Auxiliary structures for Dovetailing / Bounded Search -/

/-- The underlying relation `produces` is RE over the full tuple of arguments. -/
public lemma producesIsRe (U : Map) (hU_partrec : Partrec U) :
    IsRE (fun (args : (BitString × BitString × ℕ) × BitString) ↦
      produces U args.2 args.1.2.1 args.1.1) := by
  obtain ⟨f, hf_partrec, hf_dom⟩ := Partrec.graphIsRe U hU_partrec
  use fun args ↦ f ((args.2, args.1.2.1), args.1.1)
  constructor
  · have h_trans : Computable (fun (args : (BitString × BitString × ℕ) × BitString) ↦
        ((args.2, args.1.2.1), args.1.1)) :=
      Computable.pair
        (Computable.pair Computable.snd (Computable.fst.comp (Computable.snd.comp Computable.fst)))
        (Computable.fst.comp Computable.fst)
    exact Partrec.comp hf_partrec h_trans
  · intro args
    change (f ((args.2, args.1.2.1), args.1.1)).Dom ↔ args.1.1 ∈ U (args.2, args.1.2.1)
    rw [hf_dom]

/-! ### Main Computability Theorems -/

/-- The set of triples `(x, y, N)` such that `K_U(x|y) ≤ N` is computably enumerable. -/
public theorem condKLeIsRe (U : Map) (hU : isOptimalConditional U) :
    IsRE (fun (trip : BitString × BitString × ℕ) ↦
    condK U trip.1 trip.2.1 ≤ (trip.2.2 : ENat)) := by
  have h_equiv : (fun (trip : BitString × BitString × ℕ) ↦
      condK U trip.1 trip.2.1 ≤ (trip.2.2 : ENat)) =
      (fun trip ↦ ∃ p ∈ boundedPrograms trip.2.2, produces U p trip.2.1 trip.1) := by
    ext ⟨x, y, N⟩
    simp only
    rw [condKLeIff]
    constructor
    · rintro ⟨p, hlen, hprod⟩
      exact ⟨p, (mem_boundedPrograms_iff p N).mpr hlen, hprod⟩
    · rintro ⟨p, hmem, hprod⟩
      exact ⟨p, (mem_boundedPrograms_iff p N).mp hmem, hprod⟩
  rw [h_equiv]
  have h_bound_comp : Computable (fun (trip : BitString × BitString × ℕ) ↦
      boundedPrograms trip.2.2) :=
    Computable.boundedPrograms.comp (Computable.snd.comp Computable.snd)
  exact IsRE.existsInList (producesIsRe U hU.1) _ h_bound_comp

/-- The set of pairs `(x, N)` such that `K_U(x) > N` is co-computably enumerable. -/
public theorem plainKGtIsCore (U : Map) (hU : isOptimalConditional U) :
    IsCoRE (fun (pair : BitString × ℕ) ↦ (pair.2 : ENat) < plainK U pair.1) := by
  unfold IsCoRE
  have h_equiv : (fun (pair : BitString × ℕ) ↦ ¬((pair.2 : ENat) < plainK U pair.1)) =
                 (fun (pair : BitString × ℕ) ↦ plainK U pair.1 ≤ (pair.2 : ENat)) := by
    ext pair
    simp only [not_lt]
  rw [h_equiv]
  obtain ⟨f, hf_partrec, hf_dom⟩ := condKLeIsRe U hU
  let f_plain : BitString × ℕ →. Unit := fun p ↦ f (p.1, [], p.2)
  use f_plain
  constructor
  · have h_tuple : Computable (fun (p : BitString × ℕ) ↦ (p.1, ([] : BitString), p.2)) :=
      Computable.pair Computable.fst
        (Computable.pair (Computable.const ([] : BitString)) Computable.snd)
    exact Partrec.comp hf_partrec h_tuple
  · intro p
    change (f (p.1, [], p.2)).Dom ↔ plainK U p.1 ≤ ↑p.2
    rw [hf_dom (p.1, [], p.2)]
    rfl

end Kolmogorov
