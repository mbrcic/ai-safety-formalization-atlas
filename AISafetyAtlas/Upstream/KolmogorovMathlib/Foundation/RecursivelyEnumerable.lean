/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/


module

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
# Computably Enumerable Sets

This module establishes the abstract definitions of Computably Enumerable (RE) and co-RE sets,
along with their closure properties (like bounded existential search), and standard
utilities for generating bounded lists of booleans.
-/

namespace Kolmogorov

/-! ### Computably Enumerable (RE) Relations -/

/-- A relation is Computably Enumerable (RE) if it is the domain of a partial recursive function. -/
@[expose]
public def IsRE {α : Type*} [Primcodable α] (R : α → Prop) : Prop :=
  ∃ f : α →. Unit, Partrec f ∧ ∀ a, (f a).Dom ↔ R a

/-- A relation is co-RE if its complement is RE. -/
@[expose]
public def IsCoRE {α : Type*} [Primcodable α] (R : α → Prop) : Prop :=
  IsRE (fun a ↦ ¬ R a)

/-- The graph of a partial recursive function is an RE relation. -/
public lemma Partrec.graphIsRe {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α →. β) (hf : Partrec f) :
    IsRE (fun (p : α × β) ↦ p.2 ∈ f p.1) := by
  classical
  refine ⟨fun p ↦ (f p.1).bind (fun c ↦ ↑(if c = p.2 then some () else none)), ?_, ?_⟩
  · apply Partrec.bind (hf.comp Computable.fst)
    have h : Partrec (fun q : (α × β) × β ↦
        (↑(if q.2 = q.1.2 then some () else none) : Part Unit)) :=
      Computable.ofOption ((Computable.cond
        ((Primrec.to_comp Primrec.beq).comp
          (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)))
        (Computable.const (some ()))
        (Computable.const none)).of_eq (fun q ↦ by simp [beq_iff_eq]))
    exact h.to₂
  · intro ⟨a, b⟩
    dsimp only
    rw [Part.mem_eq]
    constructor
    · intro h
      rw [Part.bind_dom] at h
      obtain ⟨hdom, hstep⟩ := h
      refine ⟨hdom, ?_⟩
      by_cases heq : (f a).get hdom = b
      · exact heq
      · exfalso
        rw [if_neg heq] at hstep
        cases hstep
    · rintro ⟨hdom, heq⟩
      rw [Part.bind_dom]
      refine ⟨hdom, ?_⟩
      rw [if_pos heq]
      trivial

/-! ### Bounded Search and Dovetailing -/

/-- Auxiliary lemma: Establishes the equivalence between the domain of a partial
recursive function and the existence of a finite step count `k` for which the
evaluation of its code halts (`isSome = true`). -/
private lemma partrecCodeDom {α : Type*} [Primcodable α]
    (g : α →. Unit) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := α) n)).bind
        (fun a ↦ Part.map Encodable.encode (g a)))
    (a : α) :
    (g a).Dom ↔ ∃ k, (Nat.Partrec.Code.evaln k c (Encodable.encode a)).isSome := by
  have h_eval : (c.eval (Encodable.encode a)).Dom ↔ (g a).Dom := by aesop
  convert h_eval.symm using 1
  simp only [Part.dom_iff_mem, Nat.Partrec.Code.evaln_complete]
  constructor
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k c (Encodable.encode a) <;> aesop
  · rintro ⟨y, k, hk⟩
    exact ⟨k, by aesop⟩

/-- Helper 1: Computability of looking up the item in the list -/
private lemma dovetailLookupComputable {α β : Type*} [Primcodable α] [Primcodable β]
    (bound : α → List β) (h_bound : Computable bound) :
    Computable (fun p : α × ℕ ↦ (bound p.1)[p.2.unpair.1]?) := by
  have h_fst : Computable (fun p : α × ℕ ↦ bound p.1) :=
    Computable.comp h_bound Computable.fst
  have h_idx : Computable (fun p : α × ℕ ↦ p.2.unpair.1) :=
    Computable.comp Computable.fst (Computable.comp Computable.unpair Computable.snd)
  exact Computable.comp Computable.list_getElem? (Computable.pair h_fst h_idx)

/-- Helper 2: Core computability of evaln with a fixed code -/
private lemma evalnCoreComputable (c : Nat.Partrec.Code) :
    Computable (fun p : ℕ × ℕ ↦ Nat.Partrec.Code.evaln p.1 c p.2) := by
  have h_prim : Primrec (fun p : ℕ × ℕ ↦ Nat.Partrec.Code.evaln p.1 c p.2) := by
    convert Nat.Partrec.Code.primrec_evaln using 1
    constructor <;> intro h
    · convert Nat.Partrec.Code.primrec_evaln using 1
    · convert h.comp (show Primrec (fun p : ℕ × ℕ ↦ ((p.1, c), p.2)) from ?_) using 1
      exact Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd
  exact Primrec.to_comp h_prim

/-- Helper 3: Computability of advancing the machine state -/
private lemma dovetailStepComputable {α β : Type*} [Primcodable α] [Primcodable β]
    (c : Nat.Partrec.Code) :
    Computable₂ (fun (p : α × ℕ) (b : β) ↦
      Nat.Partrec.Code.evaln (p.2.unpair.2 + 1) c (Encodable.encode (p.1, b))) := by
  have h_steps : Computable (fun q : (α × ℕ) × β ↦ q.1.2.unpair.2 + 1) := by
    have hp : Primrec (fun q : (α × ℕ) × β ↦ q.1.2.unpair.2 + 1) :=
      Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
    exact Primrec.to_comp hp
  have h_input : Computable (fun q : (α × ℕ) × β ↦ Encodable.encode (q.1.1, q.2)) := by
    have hp : Primrec (fun q : (α × ℕ) × β ↦ (q.1.1, q.2)) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
    exact Computable.comp Computable.encode (Primrec.to_comp hp)
  exact Computable.comp (evalnCoreComputable c) (Computable.pair h_steps h_input)

/-- The dovetailing check function is computable. It unpairs the index `n` into
a candidate index and step count, retrieves the candidate, and runs the evaluation. -/
private lemma dovetailCheckComputable {α β : Type*} [Primcodable α] [Primcodable β]
    (bound : α → List β) (h_bound : Computable bound) (c : Nat.Partrec.Code) :
    Computable₂ (fun (a : α) (n : ℕ) ↦
      match (bound a)[n.unpair.1]? with
      | some b =>
        (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
      | none => false) := by
  have h_lookup := dovetailLookupComputable bound h_bound
  have h_step := dovetailStepComputable (α := α) (β := β) c
  have h_bind := Computable.option_bind h_lookup h_step
  have h_isSome : Computable (fun o : Option ℕ ↦ o.isSome) :=
    Primrec.to_comp Primrec.option_isSome
  have h_full : Computable (fun p : α × ℕ ↦
      ((bound p.1)[p.2.unpair.1]?.bind (fun b ↦
        Nat.Partrec.Code.evaln (p.2.unpair.2 + 1) c (Encodable.encode (p.1, b)))).isSome) :=
    Computable.comp h_isSome h_bind
  exact Computable.of_eq h_full (by
    intro p
    dsimp only
    cases h : (bound p.1)[p.2.unpair.1]? <;> rfl)

/-- Master Lemma for Bounded Existential Search over RE sets.
If a two-argument relation `R(a, b)` is RE, and `bound : α → List β` is a computable function
generating a finite list of candidates for each `a`, then the relation
`∃ b ∈ bound a, R a b` is also RE. Proven via dovetailing over the candidate list. -/
public lemma IsRE.existsInList {α β : Type*} [Primcodable α] [Primcodable β]
    {R : α → β → Prop} (hR : IsRE (fun p : α × β ↦ R p.1 p.2))
    (bound : α → List β) (h_bound : Computable bound) :
    IsRE (fun a ↦ ∃ b ∈ bound a, R a b) := by
  obtain ⟨g, hg_partrec, hg_dom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg_partrec
  let check : α → ℕ → Bool := fun a n ↦
    match (bound a)[n.unpair.1]? with
    | some b =>
      (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
    | none => false
  have hcheck : Computable₂ check := dovetailCheckComputable bound h_bound c
  have h_rfind : Partrec (fun a ↦ Nat.rfind (fun n ↦ Part.some (check a n))) :=
    Partrec.rfind hcheck.partrec
  refine ⟨fun a ↦ (Nat.rfind (fun n ↦ Part.some (check a n))).map (fun _ ↦ ()),
    h_rfind.map (Computable.const ()).to₂, ?_⟩
  intro a
  change (Nat.rfind (fun n ↦ Part.some (check a n))).Dom ↔ _
  rw [Nat.rfind_dom]; simp_rw [Part.mem_some_iff]
  have hrfind_simp : (∃ n, true = check a n ∧ ∀ {m : ℕ}, m < n →
      (Part.some (check a m)).Dom) ↔ (∃ n, check a n = true) := by
    constructor
    · rintro ⟨n, hn, _⟩; exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn.symm, fun _ ↦ Part.some_dom _⟩
  rw [hrfind_simp]
  have code_dom := partrecCodeDom g c hc
  constructor
  · rintro ⟨n, hn⟩
    simp only [check] at hn
    generalize n.unpair.1 = i at hn
    generalize n.unpair.2 = k at hn
    cases hget : (bound a)[i]? with
    | none =>
      simp only [hget] at hn
      contradiction
    | some b =>
      simp only [hget] at hn
      refine ⟨b, List.mem_of_getElem? hget, ?_⟩
      exact (hg_dom (a, b)).mp ((code_dom (a, b)).mpr ⟨k + 1, hn⟩)
  · rintro ⟨b, hb_mem, hR_ab⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb_mem
    have hdom : (g (a, b)).Dom := (hg_dom (a, b)).mpr hR_ab
    obtain ⟨k, hk⟩ := (code_dom (a, b)).mp hdom
    refine ⟨Nat.pair i k, ?_⟩
    simp only [check, Nat.unpair_pair, hi]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    exact Option.isSome_iff_exists.mpr
      ⟨x, Option.mem_def.mp (Nat.Partrec.Code.evaln_mono
        (Nat.le_succ k) (Option.mem_def.mpr hx))⟩

/-! ### Bounded Generators (For Bitstrings) -/

/-- Generates all bitstrings (lists of booleans) of exactly length n. -/
@[expose]
public def exactLengthPrograms : ℕ → List (List Bool)
  | 0 => [[]]
  | (n + 1) => (exactLengthPrograms n).flatMap fun s ↦ [false :: s, true :: s]

/-- Generates all bitstrings of length ≤ N. -/
@[expose]
public def boundedPrograms (N : ℕ) : List (List Bool) :=
  (List.range (N + 1)).flatMap exactLengthPrograms

/-- Helper: programs generated by `exactLengthPrograms n` have length `n`. -/
private lemma exactLengthPrograms_length (n : ℕ) (p : List Bool) :
    p ∈ exactLengthPrograms n → p.length = n := by
  induction n generalizing p with
  | zero =>
    intro h
    have : p = [] := by simpa [exactLengthPrograms] using h
    rw [this]
    rfl
  | succ n ih =>
    intro h
    have : ∃ s ∈ exactLengthPrograms n, p = false :: s ∨ p = true :: s := by
      simpa [exactLengthPrograms] using h
    rcases this with ⟨s, hs_mem, rfl | rfl⟩
    · simp [ih s hs_mem]
    · simp [ih s hs_mem]

/-- Helper: any list belongs to `exactLengthPrograms` of its own length. -/
private lemma mem_exactLengthPrograms_self (p : List Bool) :
    p ∈ exactLengthPrograms p.length := by
  induction p with
  | nil => simp [exactLengthPrograms]
  | cons b tail ih =>
    simp only [exactLengthPrograms, List.length_cons, List.mem_flatMap]
    refine ⟨tail, ih, ?_⟩
    cases b <;> simp

/-- Members of `exactLengthPrograms n` all have length `n` (public restatement of the
private helper). -/
public lemma exactLengthPrograms_length_eq (n : ℕ) (p : List Bool)
    (hp : p ∈ exactLengthPrograms n) : p.length = n :=
  exactLengthPrograms_length n p hp

/-
`exactLengthPrograms n` has no duplicates.
-/
public lemma exactLengthPrograms_nodup (n : ℕ) : (exactLengthPrograms n).Nodup := by
  refine Nat.recOn n ?_ ?_ <;> simp +decide [ exactLengthPrograms ];
  grind

/-
`boundedPrograms N` has no duplicates.
-/
-- Closes the indexed disjointness goal after extracting exact lengths from both
-- sides, via a squeezed `simp_all only` over the range-index rewrites.
public lemma boundedPrograms_nodup (N : ℕ) : (boundedPrograms N).Nodup := by
  refine List.nodup_flatMap.mpr ?_;
  refine ⟨ fun x hx ↦ exactLengthPrograms_nodup x, ?_ ⟩;
  refine List.pairwise_iff_get.mpr ?_;
  intros i j hij; rw [ Function.onFun, List.disjoint_left ]; intros x hx hy; have := exactLengthPrograms_length_eq _ _ hx; have := exactLengthPrograms_length_eq _ _ hy; simp_all +decide only [List.get_eq_getElem, List.getElem_range];
  exact hij.ne ( Fin.ext ‹_› ▸ rfl )

/-- A bitstring is in `boundedPrograms N` if and only if its length is at most `N`. -/
public lemma mem_boundedPrograms_iff (p : List Bool) (N : ℕ) :
    p ∈ boundedPrograms N ↔ p.length ≤ N := by
  constructor
  · intro hp
    unfold boundedPrograms at hp
    simp only [List.mem_flatMap, List.mem_range] at hp
    obtain ⟨n, hn_lt, hp_mem⟩ := hp
    have h_len := exactLengthPrograms_length n p hp_mem
    omega
  · intro h_len
    unfold boundedPrograms
    simp only [List.mem_flatMap, List.mem_range]
    refine ⟨p.length, by omega, mem_exactLengthPrograms_self p⟩

/-- The exact-length generator is primitive recursive. -/
public lemma primrec_exactLengthPrograms : Primrec exactLengthPrograms := by
  have hrec : exactLengthPrograms = fun n ↦
      Nat.rec ([[]] : List (List Bool))
        (fun _ ih ↦ List.flatMap (fun s ↦ [false :: s, true :: s]) ih) n := by
    funext n; induction n with
    | zero => rfl
    | succ n ih => simp [exactLengthPrograms, ih]
  rw [hrec]
  have hStep : Primrec₂ (fun (_ : Unit) (p : ℕ × List (List Bool)) ↦
      List.flatMap (fun s ↦ [false :: s, true :: s]) p.2) := by
    change Primrec (fun (q : Unit × (ℕ × List (List Bool))) ↦
      List.flatMap (fun s ↦ [false :: s, true :: s]) q.2.2)
    exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (show Primrec₂ (fun (_ : Unit × (ℕ × List (List Bool))) (s : List Bool) ↦
          [false :: s, true :: s]) from
        Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
          (Primrec.list_cons.comp
            (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
            (Primrec.const [])))
  exact (Primrec.nat_rec (Primrec.const [[]]) hStep).comp (Primrec.const ()) Primrec.id

/-- The bounded-program generator is primitive recursive. -/
public lemma primrec_boundedPrograms : Primrec boundedPrograms := by
  change Primrec (fun N ↦ List.flatMap exactLengthPrograms (List.range (N + 1)))
  exact Primrec.list_flatMap
    (Primrec.list_range.comp Primrec.succ)
    (primrec_exactLengthPrograms.comp Primrec.snd)

/-- The generator function itself is computable. -/
public lemma Computable.boundedPrograms : Computable boundedPrograms :=
  primrec_boundedPrograms.to_comp

end Kolmogorov
