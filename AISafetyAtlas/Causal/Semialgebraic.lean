module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Semialgebraic subsets of a finite-dimensional real coordinate space

MAIS-A2 `prob:exact` opens *"Let `𝒩 ⊆ 𝕄(sk, λ)` be a **compact semialgebraic**
class …"*. Neither word can be dropped, and Mathlib at the pinned revision has
no semialgebraic sets at all — the word occurs nowhere in the library, and there
is no o-minimality development either — so the notion is built here.
Compactness is Mathlib's.

The definition is the standard one (Bochnak–Coste–Roy §2.1): a finite union of
sets each cut out by finitely many polynomial sign conditions. Allowing `≥`
alongside `=` and `>` is redundant — `p ≥ 0` is `p > 0 ∨ p = 0`, so the class of
sets is unchanged — and it is kept because the objects `prob:exact` actually
names, closed boxes and closed margin conditions, are then basic rather than
unions of exponentially many pieces. Keeping `≥` earns its place a second time
under complementation: the negation of a strict inequality is a single `≥`
condition, so without it every negated `>` would split into two pieces.

BCR §2.1 also establishes that these sets form a **Boolean algebra**, closed
under finite union, finite intersection, and complement. All three are proved
below. Only the union is exercised by `prob:exact` itself, since a class is
presented as a union of boxes; a caller who cuts one class down by another needs
the other two, and `IsSemialgebraic.sdiff` is what they write.

What is deliberately absent is Tarski–Seidenberg. Nothing here concludes that
the projection of a semialgebraic set, its topological closure, or a set defined
by a quantified first-order formula is semialgebraic.

Nothing here is specific to causal models; `ι` is any index type and the
coordinate space is `ι → ℝ`. The causal use instantiates `ι := ChartIndex G`.
-/

namespace AISafetyAtlas.Causal

open MvPolynomial

variable {ι : Type*}

/-- One of the three sign conditions a polynomial may be required to satisfy. -/
public inductive PolySign
  | zero
  | pos
  | nonneg
  deriving DecidableEq

/-- What a sign condition asserts of a real number. -/
@[expose] public def PolySign.Holds : PolySign → ℝ → Prop
  | .zero, r => r = 0
  | .pos, r => 0 < r
  | .nonneg, r => 0 ≤ r

/-- A **basic** semialgebraic set: finitely many polynomial sign conditions,
required simultaneously.

The conditions are carried as a `Finset` rather than a `Fin n`-indexed family so
that a union of two semialgebraic sets is a union of two `Finset`s. Indexing by
`Fin n` makes the piece count a dependent parameter and every union proof a
sequence of casts. -/
@[expose] public def BasicSemialgebraic
    (ps : Finset (MvPolynomial ι ℝ × PolySign)) : Set (ι → ℝ) :=
  {x | ∀ p ∈ ps, p.2.Holds (eval x p.1)}

/-- **Semialgebraic**: a finite union of basic semialgebraic sets. -/
@[expose] public def IsSemialgebraic (s : Set (ι → ℝ)) : Prop :=
  ∃ pieces : Set (Finset (MvPolynomial ι ℝ × PolySign)),
    pieces.Finite ∧ s = ⋃ ps ∈ pieces, BasicSemialgebraic ps

/-- The empty set is semialgebraic: the empty union. -/
public theorem isSemialgebraic_empty : IsSemialgebraic (∅ : Set (ι → ℝ)) :=
  ⟨∅, Set.finite_empty, by simp⟩

/-- A basic semialgebraic set is semialgebraic. -/
public theorem IsSemialgebraic.basic (ps : Finset (MvPolynomial ι ℝ × PolySign)) :
    IsSemialgebraic (BasicSemialgebraic ps) :=
  ⟨{ps}, Set.finite_singleton _, by simp⟩

/-- The whole space is semialgebraic: one basic piece with no conditions. -/
public theorem isSemialgebraic_univ : IsSemialgebraic (Set.univ : Set (ι → ℝ)) := by
  have h : (Set.univ : Set (ι → ℝ)) = BasicSemialgebraic (ι := ι) ∅ := by
    ext x
    simp [BasicSemialgebraic]
  rw [h]
  exact IsSemialgebraic.basic _

/-- A union of semialgebraic sets is semialgebraic. -/
public theorem IsSemialgebraic.union {s t : Set (ι → ℝ)}
    (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) :
    IsSemialgebraic (s ∪ t) := by
  obtain ⟨p₁, hp₁, rfl⟩ := hs
  obtain ⟨p₂, hp₂, rfl⟩ := ht
  refine ⟨p₁ ∪ p₂, hp₁.union hp₂, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro (⟨ps, hps, hx⟩ | ⟨ps, hps, hx⟩)
    · exact ⟨ps, Or.inl hps, hx⟩
    · exact ⟨ps, Or.inr hps, hx⟩
  · rintro ⟨ps, hps | hps, hx⟩
    · exact Or.inl ⟨ps, hps, hx⟩
    · exact Or.inr ⟨ps, hps, hx⟩

/-! ## The Boolean algebra

BCR §2.1's closure statement is that the semialgebraic subsets of a real
coordinate space form a **Boolean algebra of sets**: closed under finite union,
finite intersection, and complement. `IsSemialgebraic.union` above is one third
of it. The rest follows here, because a caller who cuts one class down by
another — a margin class minus a degenerate locus, an identified set met with a
box — needs the other two thirds and gets no help from the union alone.

None of these carries a hypothesis on `ι`. The finiteness that makes them work
is the finiteness already present in `BasicSemialgebraic`'s `Finset` and in
`IsSemialgebraic`'s `pieces.Finite`, never finiteness of the coordinate index.
-/

/-- Conditions imposed simultaneously by two `Finset`s are the conditions
imposed by their union. This is the pointwise core of closure under
intersection: two basic sets meet in a basic set. -/
public theorem basicSemialgebraic_union [DecidableEq (MvPolynomial ι ℝ × PolySign)]
    (ps qs : Finset (MvPolynomial ι ℝ × PolySign)) :
    BasicSemialgebraic (ps ∪ qs)
      = BasicSemialgebraic ps ∩ BasicSemialgebraic qs := by
  ext x
  simp only [BasicSemialgebraic, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun p hp ↦ h p (Or.inl hp), fun p hp ↦ h p (Or.inr hp)⟩
  · rintro ⟨h₁, h₂⟩ p (hp | hp)
    · exact h₁ p hp
    · exact h₂ p hp

/-- An intersection of semialgebraic sets is semialgebraic: distribute the two
unions and meet the pieces pairwise. -/
public theorem IsSemialgebraic.inter {s t : Set (ι → ℝ)}
    (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) :
    IsSemialgebraic (s ∩ t) := by
  classical
  obtain ⟨p₁, hp₁, rfl⟩ := hs
  obtain ⟨p₂, hp₂, rfl⟩ := ht
  refine ⟨(fun pq : Finset (MvPolynomial ι ℝ × PolySign) ×
      Finset (MvPolynomial ι ℝ × PolySign) ↦ pq.1 ∪ pq.2) '' (p₁ ×ˢ p₂),
    (hp₁.prod hp₂).image _, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop, Set.mem_image,
    Set.mem_prod]
  constructor
  · rintro ⟨⟨ps, hps, hx⟩, qs, hqs, hy⟩
    refine ⟨ps ∪ qs, ⟨(ps, qs), ⟨hps, hqs⟩, rfl⟩, ?_⟩
    rw [basicSemialgebraic_union]
    exact ⟨hx, hy⟩
  · rintro ⟨rs, ⟨⟨ps, qs⟩, ⟨hps, hqs⟩, rfl⟩, hx⟩
    rw [basicSemialgebraic_union] at hx
    exact ⟨⟨ps, hps, hx.1⟩, qs, hqs, hx.2⟩

/-- A **finite** union of semialgebraic sets is semialgebraic. BCR's closure
statement is for finite unions; the binary case above is the two-piece
instance. -/
public theorem isSemialgebraic_biUnion {α : Type*} (t : Finset α)
    {f : α → Set (ι → ℝ)} (hf : ∀ a ∈ t, IsSemialgebraic (f a)) :
    IsSemialgebraic (⋃ a ∈ t, f a) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using isSemialgebraic_empty
  | insert a t _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (hf a (Finset.mem_insert_self a t)).union
      (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

/-- A **finite** intersection of semialgebraic sets is semialgebraic.

Proved directly from `IsSemialgebraic.inter`, not as a complemented union: the
De Morgan route would make this lemma depend on the negation table below, which
has nothing to do with intersection. -/
public theorem isSemialgebraic_biInter {α : Type*} (t : Finset α)
    {f : α → Set (ι → ℝ)} (hf : ∀ a ∈ t, IsSemialgebraic (f a)) :
    IsSemialgebraic (⋂ a ∈ t, f a) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using isSemialgebraic_univ
  | insert a t _ ih =>
    rw [Finset.set_biInter_insert]
    exact (hf a (Finset.mem_insert_self a t)).inter
      (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

/-- The set where one sign condition **fails** is semialgebraic.

This is the negation table, and the reason `PolySign` needs no fourth
constructor: negating any of the three conditions on `p` lands back inside
`{zero, pos, nonneg}`, applied to `p` or to `-p`.

| condition | negation |
|---|---|
| `p = 0` | `0 < p` or `0 < -p` — the only case that splits |
| `0 < p` | `0 ≤ -p` |
| `0 ≤ p` | `0 < -p` |

The middle row is why `nonneg` is kept even though it adds no sets: without it
the negation of a strict inequality would itself split, and the piece count of a
complement would grow exponentially in the number of conditions. -/
public theorem isSemialgebraic_not_holds (p : MvPolynomial ι ℝ × PolySign) :
    IsSemialgebraic {x : ι → ℝ | ¬ p.2.Holds (eval x p.1)} := by
  obtain ⟨q, sg⟩ := p
  cases sg with
  | zero =>
    have h : {x : ι → ℝ | ¬ PolySign.zero.Holds (eval x q)}
        = BasicSemialgebraic {(q, PolySign.pos)}
            ∪ BasicSemialgebraic {(-q, PolySign.pos)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, BasicSemialgebraic,
        Finset.mem_singleton, PolySign.Holds, forall_eq, map_neg]
      constructor
      · intro hx
        rcases lt_trichotomy (eval x q) 0 with h | h | h
        · exact Or.inr (by linarith)
        · exact absurd h hx
        · exact Or.inl h
      · rintro (h | h) hx <;> linarith
    rw [h]
    exact (IsSemialgebraic.basic _).union (IsSemialgebraic.basic _)
  | pos =>
    have h : {x : ι → ℝ | ¬ PolySign.pos.Holds (eval x q)}
        = BasicSemialgebraic {(-q, PolySign.nonneg)} := by
      ext x
      simp only [Set.mem_setOf_eq, BasicSemialgebraic, Finset.mem_singleton,
        PolySign.Holds, forall_eq, map_neg]
      constructor
      · intro hx
        linarith [not_lt.mp hx]
      · intro hx h
        linarith
    rw [h]
    exact IsSemialgebraic.basic _
  | nonneg =>
    have h : {x : ι → ℝ | ¬ PolySign.nonneg.Holds (eval x q)}
        = BasicSemialgebraic {(-q, PolySign.pos)} := by
      ext x
      simp only [Set.mem_setOf_eq, BasicSemialgebraic, Finset.mem_singleton,
        PolySign.Holds, forall_eq, map_neg]
      constructor
      · intro hx
        linarith [not_le.mp hx]
      · intro hx h
        linarith
    rw [h]
    exact IsSemialgebraic.basic _

/-- The complement of a basic semialgebraic set is semialgebraic: a point escapes
exactly when it fails one of the finitely many conditions. -/
public theorem isSemialgebraic_compl_basic
    (ps : Finset (MvPolynomial ι ℝ × PolySign)) :
    IsSemialgebraic (BasicSemialgebraic ps)ᶜ := by
  have h : (BasicSemialgebraic ps)ᶜ
      = ⋃ p ∈ ps, {x : ι → ℝ | ¬ p.2.Holds (eval x p.1)} := by
    ext x
    simp only [Set.mem_compl_iff, BasicSemialgebraic, Set.mem_setOf_eq,
      Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      by_contra hc
      exact hx fun p hp ↦ by
        by_contra hn
        exact hc ⟨p, hp, hn⟩
    · rintro ⟨p, hp, hn⟩ hall
      exact hn (hall p hp)
  rw [h]
  exact isSemialgebraic_biUnion ps fun p _ ↦ isSemialgebraic_not_holds p

/-- The complement of a semialgebraic set is semialgebraic.

The pieces are turned into a `Finset` rather than inducted over as a
`Set.Finite`: the set is *defined* from its pieces, so an induction holding the
set fixed has no motive to move, and generalizing it is more work than
transporting the finiteness. -/
public theorem IsSemialgebraic.compl {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic sᶜ := by
  obtain ⟨pieces, hfin, rfl⟩ := hs
  have h : (⋃ ps ∈ pieces, BasicSemialgebraic ps)ᶜ
      = ⋂ ps ∈ hfin.toFinset, (BasicSemialgebraic ps)ᶜ := by
    ext x
    simp [hfin.mem_toFinset]
  rw [h]
  exact isSemialgebraic_biInter _ fun ps _ ↦ isSemialgebraic_compl_basic ps

/-- A difference of semialgebraic sets is semialgebraic. This is the shape a
caller cutting one class down by another actually writes, and it is the first
thing that closure under union alone cannot supply. -/
public theorem IsSemialgebraic.sdiff {s t : Set (ι → ℝ)}
    (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) :
    IsSemialgebraic (s \ t) := by
  rw [Set.sdiff_eq]
  exact hs.inter ht.compl

/-! ## The closed box

`prob:exact`'s richness condition asks that a class's table-parameter projection
*"contains a `K(G)`-dimensional box of side `ρ`"*. That box is the set below,
and it is basic semialgebraic — which is why `nonneg` is in `PolySign`. -/

/-- The closed box with corner `c` and side `r`: `∏ᵢ [cᵢ, cᵢ + r]`. -/
@[expose] public def ClosedBox (c : ι → ℝ) (r : ℝ) : Set (ι → ℝ) :=
  {x | ∀ i, c i ≤ x i ∧ x i ≤ c i + r}

/-- A closed box is basic semialgebraic: two `≥` conditions per coordinate,
`Xᵢ - cᵢ ≥ 0` and `cᵢ + r - Xᵢ ≥ 0`. -/
public theorem isSemialgebraic_closedBox [Fintype ι] (c : ι → ℝ) (r : ℝ) :
    IsSemialgebraic (ClosedBox c r) := by
  classical
  have hbox : ClosedBox c r =
      BasicSemialgebraic
        ((Finset.univ.image fun i : ι ↦ (X i - C (c i), PolySign.nonneg)) ∪
          (Finset.univ.image fun i : ι ↦ (C (c i + r) - X i, PolySign.nonneg))) := by
    ext x
    simp only [ClosedBox, Set.mem_setOf_eq, BasicSemialgebraic, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro hx p (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · simpa [PolySign.Holds, sub_nonneg] using (hx i).1
      · simpa [PolySign.Holds, sub_nonneg] using (hx i).2
    · intro hx i
      have h1 := hx _ (Or.inl ⟨i, rfl⟩)
      have h2 := hx _ (Or.inr ⟨i, rfl⟩)
      simp only [PolySign.Holds, map_sub, eval_X, eval_C, sub_nonneg] at h1 h2
      exact ⟨h1, h2⟩
  rw [hbox]
  exact IsSemialgebraic.basic _

/-- A closed box is compact. Paired with `isSemialgebraic_closedBox` this makes
the box **compact semialgebraic**, which is the conjunction `prob:exact` asks of
the class it quantifies over. -/
public theorem isCompact_closedBox [Fintype ι] (c : ι → ℝ) (r : ℝ) :
    IsCompact (ClosedBox c r) := by
  have hpi : ClosedBox c r = Set.univ.pi fun i ↦ Set.Icc (c i) (c i + r) := by
    ext x
    simp only [ClosedBox, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  rw [hpi]
  exact isCompact_univ_pi fun _ ↦ isCompact_Icc

end AISafetyAtlas.Causal
