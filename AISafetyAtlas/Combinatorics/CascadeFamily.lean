module

public import AISafetyAtlas.Combinatorics.Cascade
public import AISafetyAtlas.Combinatorics.KruskalKatona
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Colex rank, and what still stands between the cascade and the theorem

`AISafetyAtlas.Combinatorics.Cascade` carries the cascade representation and its
two Kruskal-Katona shifts as arithmetic. Turning them into a statement about set
families needs one more object: the **colex rank** of a finite set, which counts
the sets of the same size strictly below it in colexicographic order.

`colexRank` is that count's closed form, and `colexRank_erase_max` is the
recursion it satisfies — strip the largest element and the rank drops by exactly
the binomial that element contributes. Read the other way, this is the
**combinatorial number system**: the digits of `colexRank s` in the cascade
representation are the elements of `s`.

**And it finishes the theorem.** `card_initSeg` says the cardinality of a colex
initial segment is one more than the rank, `cascadeShadow_colexRank_succ` carries
`cascadeShadow` across the erasure of a least element, and Mathlib's
shadow-of-an-initial-segment lemma closes it: `cascadeShadow_le_card_shadow'` is
Kruskal-Katona in cascade form over an arbitrary ground type, which Mathlib's own
file records as an open task. The identity is not a digit-by-digit match — for
`s = {2, 3}` the count is `6`, whose leading cascade digit is `4` and not `3` —
so it runs by induction on the set, splitting on whether the part below the
greatest element is itself the largest of its size.

A search recorded in `benchmark-facet-atlas/findings/` found this counting in no
proof assistant before this module: not in Mathlib, AddCombi, PFR or batteries, not in the Lean 3
development Mathlib's Kruskal-Katona file was ported from, not in the Isabelle
AFP, HOL Light, HOL4, Agda or Rocq, and not on Formalpedia. The nearest thing is
`Vilin97/lean-pool`, whose Boolean-isoperimetry tree proves an upper-shadow
minimisation for the cube; its numeric function is Harper's boundary function against layer offsets rather than a cascade at a fixed level, it is indexed by
the ground-set size, and it sits on a different toolchain. It is a neighbour and
not this.

Source and scope: the colex rank is classical, and is the combinatorial number
system of Lehmer 1964. Nothing here is coverage of a printed result.
-/

namespace AISafetyAtlas.Combinatorics

open Finset
open scoped FinsetFamily

/--
**The colex rank of a finite set of naturals.** Each element contributes the
binomial in its own value and its position, counting from one.

For `s = {a₁ < a₂ < ⋯ < a_r}` this is `C(a₁,1) + C(a₂,2) + ⋯ + C(a_r,r)`, which
is the number of `r`-element sets strictly below `s` in colexicographic order.
-/
@[expose] public def colexRank (s : Finset ℕ) : ℕ :=
  ∑ a ∈ s, a.choose (s.filter (· ≤ a)).card

/-- The empty set is first. -/
@[simp] public theorem colexRank_empty : colexRank ∅ = 0 := by
  simp [colexRank]

/-- A singleton's rank is its element: `C(a, 1) = a`. -/
@[simp] public theorem colexRank_singleton (a : ℕ) : colexRank {a} = a := by
  rw [colexRank, Finset.sum_singleton, Finset.filter_singleton, if_pos le_rfl,
    Finset.card_singleton, Nat.choose_one_right]

/--
**The rank recursion.** Removing the largest element drops the rank by exactly
that element's own binomial.

The positions of the remaining elements are unchanged, because they are all below
the one removed. Iterating this is what identifies the cascade digits of
`colexRank s` with the elements of `s`.
-/
public theorem colexRank_erase_max (s : Finset ℕ) (hs : s.Nonempty) :
    colexRank s = (s.max' hs).choose s.card + colexRank (s.erase (s.max' hs)) := by
  classical
  set m := s.max' hs with hm
  have hmem : m ∈ s := s.max'_mem hs
  have hfilt : s.filter (· ≤ m) = s := by
    refine Finset.filter_true_of_mem fun a ha => ?_
    exact s.le_max' a ha
  have hkey : ∀ a ∈ s.erase m, (s.erase m).filter (· ≤ a) = s.filter (· ≤ a) := by
    intro a ha
    have hane : a ≠ m := (Finset.mem_erase.mp ha).1
    have has : a ∈ s := (Finset.mem_erase.mp ha).2
    have halt : a < m := lt_of_le_of_ne (s.le_max' a has) hane
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hbs⟩, hba⟩
      exact ⟨hbs, hba⟩
    · rintro ⟨hbs, hba⟩
      exact ⟨⟨fun h => absurd (h ▸ hba) (by omega), hbs⟩, hba⟩
  have hsum : ∑ x ∈ s.erase m, x.choose (s.filter (· ≤ x)).card = colexRank (s.erase m) := by
    rw [colexRank]
    exact Finset.sum_congr rfl fun a ha => by rw [hkey a ha]
  rw [colexRank, ← Finset.sum_erase_add s _ hmem, hfilt]
  omega

/-- The remainder after one greedy cascade step is strictly under the next
binomial down, which is what makes the representation terminate. -/
public theorem sub_cascadeTop_choose_lt (r a : ℕ)
    (ha : (cascadeTop (r + 1) a).choose (r + 1) ≤ a) :
    a - (cascadeTop (r + 1) a).choose (r + 1) < (cascadeTop (r + 1) a).choose r := by
  have h := lt_succ_cascadeTop_choose r a
  rw [Nat.choose_succ_succ'] at h
  omega

/-!
## The rank is an order embedding

Two facts carry `colexRank` from a formula to a counting principle: it is bounded
by the binomial in whatever bound the set's elements respect, and it is strictly
monotone along the colexicographic order. Together they make it an injection of
the `r`-subsets of `Fin n` into `range (n.choose r)`, which by cardinality is a
bijection.
-/

/--
**The rank is bounded by the ground set.** A set whose elements are all below `n`
ranks below `n.choose` its own cardinality.

The proof is the recursion plus Pascal: the largest element contributes
`C(m, k+1)`, and everything under it contributes less than `C(m, k)`.
-/
public theorem colexRank_lt_choose :
    ∀ (k : ℕ) (s : Finset ℕ), s.card = k → ∀ n : ℕ, (∀ a ∈ s, a < n) →
      colexRank s < n.choose k := by
  intro k
  induction k with
  | zero =>
    intro s hs n _
    rw [Finset.card_eq_zero.mp hs]
    simp
  | succ k ih =>
    intro s hs n hn
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hmem : s.max' hne ∈ s := s.max'_mem hne
    have hmn : s.max' hne < n := hn _ hmem
    have hcard : (s.erase (s.max' hne)).card = k := by
      rw [Finset.card_erase_of_mem hmem, hs]
      omega
    have hsub : ∀ a ∈ s.erase (s.max' hne), a < s.max' hne := fun a ha =>
      lt_of_le_of_ne (s.le_max' a (Finset.mem_erase.mp ha).2) (Finset.mem_erase.mp ha).1
    have hih := ih (s.erase (s.max' hne)) hcard (s.max' hne) hsub
    have hrec := colexRank_erase_max s hne
    rw [hs] at hrec
    have hpascal : (s.max' hne + 1).choose (k + 1)
        = (s.max' hne).choose k + (s.max' hne).choose (k + 1) := Nat.choose_succ_succ' _ _
    have hle : (s.max' hne + 1).choose (k + 1) ≤ n.choose (k + 1) :=
      Nat.choose_le_choose _ (by omega)
    omega

/--
**The rank respects colex.** Among sets of one size, a colexicographically
smaller set has a strictly smaller rank.

The two cases are the two ways one set can precede another: a smaller largest
element, where `colexRank_lt_choose` separates them outright, or the same largest
element, where the comparison passes to what is left after erasing it.
-/
public theorem colexRank_lt_colexRank :
    ∀ (k : ℕ) (s t : Finset ℕ), s.card = k → t.card = k →
      toColex s < toColex t → colexRank s < colexRank t := by
  intro k
  induction k with
  | zero =>
    intro s t hs ht hlt
    rw [Finset.card_eq_zero.mp hs, Finset.card_eq_zero.mp ht] at hlt
    exact absurd hlt (lt_irrefl _)
  | succ k ih =>
    intro s t hs ht hlt
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    have htne : t.Nonempty := Finset.card_pos.mp (by omega)
    have hab : s.max' hsne ≤ t.max' htne := by
      have := Finset.Colex.forall_le_mono (a := t.max' htne) hlt.le
        (fun b hb => t.le_max' b hb)
      exact this _ (s.max'_mem hsne)
    have hsmem : s.max' hsne ∈ s := s.max'_mem hsne
    have htmem : t.max' htne ∈ t := t.max'_mem htne
    have hsrec := colexRank_erase_max s hsne
    have htrec := colexRank_erase_max t htne
    rw [hs] at hsrec
    rw [ht] at htrec
    rcases hab.lt_or_eq with hab | hab
    · have hscard : (s.erase (s.max' hsne)).card = k := by
        rw [Finset.card_erase_of_mem hsmem, hs]
        omega
      have hbound : colexRank s < (s.max' hsne + 1).choose (k + 1) := by
        refine colexRank_lt_choose (k + 1) s hs _ ?_
        intro a ha
        exact Nat.lt_succ_of_le (s.le_max' a ha)
      have hmono : (s.max' hsne + 1).choose (k + 1) ≤ (t.max' htne).choose (k + 1) :=
        Nat.choose_le_choose _ (by omega)
      omega
    · have hins : ({s.max' hsne} : Finset ℕ) ⊆ s := Finset.singleton_subset_iff.mpr hsmem
      have hint : ({s.max' hsne} : Finset ℕ) ⊆ t := by
        rw [hab]
        exact Finset.singleton_subset_iff.mpr htmem
      have hsdiff : toColex (s \ {s.max' hsne}) < toColex (t \ {s.max' hsne}) :=
        (Finset.Colex.toColex_sdiff_lt_toColex_sdiff hins hint).mpr hlt
      rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase] at hsdiff
      have hscard : (s.erase (s.max' hsne)).card = k := by
        rw [Finset.card_erase_of_mem hsmem, hs]
        omega
      have htcard : (t.erase (s.max' hsne)).card = k := by
        rw [hab, Finset.card_erase_of_mem htmem, ht]
        omega
      have hih := ih _ _ hscard htcard hsdiff
      rw [← hab] at htrec
      omega

/-!
## The initial family of a given size

Over a finite ground set the rank becomes a bijection onto an interval, so
filtering by it produces a colexicographic initial segment of any requested size.
That is what Mathlib's Kruskal-Katona theorem asks to be handed.
-/

variable {n : ℕ}

/-- The colex rank of a set of `Fin n`, read through its values. -/
@[expose] public def finRank (s : Finset (Fin n)) : ℕ := colexRank (s.image Fin.val)

/-- Ranking through values does not change the cardinality. -/
public theorem card_image_val (s : Finset (Fin n)) : (s.image Fin.val).card = s.card :=
  Finset.card_image_of_injective _ Fin.val_injective

/-- **The rank lands below the binomial.** -/
public theorem finRank_lt (s : Finset (Fin n)) : finRank s < n.choose s.card := by
  rw [finRank, ← card_image_val s]
  refine colexRank_lt_choose _ _ rfl n ?_
  intro a ha
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
  exact x.isLt

/-- **And it respects colex**, exactly as over the naturals. -/
public theorem finRank_lt_finRank {s t : Finset (Fin n)} (hst : s.card = t.card)
    (h : toColex s < toColex t) : finRank s < finRank t := by
  refine colexRank_lt_colexRank s.card _ _ (card_image_val s) ?_ ?_
  · rw [card_image_val t, hst]
  · exact (Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono).mpr h

/-- So the rank is injective on each layer. -/
public theorem finRank_injOn (r : ℕ) :
    Set.InjOn (finRank (n := n))
      ((Finset.univ.powersetCard r : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
  intro s hs t ht heq
  have hsc : s.card = r := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hs)).2
  have htc : t.card = r := (Finset.mem_powersetCard.mp (Finset.mem_coe.mp ht)).2
  rcases lt_trichotomy (toColex s) (toColex t) with h | h | h
  · exact absurd heq (Nat.ne_of_lt (finRank_lt_finRank (hsc.trans htc.symm) h))
  · exact toColex.injective h
  · exact absurd heq.symm (Nat.ne_of_lt (finRank_lt_finRank (htc.trans hsc.symm) h))

/--
**The first `m` sets of size `r`**, cut out by the rank rather than constructed.
-/
@[expose] public def initFamily (n r m : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard r).filter (fun t => finRank t < m)

/-- Membership, unfolded. -/
public theorem mem_initFamily_iff {r m : ℕ} {s : Finset (Fin n)} :
    s ∈ initFamily n r m ↔ s.card = r ∧ finRank s < m := by
  rw [initFamily, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Finset.subset_univ _, h.1⟩, h.2⟩⟩

/--
**It is a colexicographic initial segment.** Anything of the same size below a
member ranks lower still, so it is a member too.
-/
public theorem isInitSeg_initFamily (r m : ℕ) :
    Finset.Colex.IsInitSeg (initFamily n r m) r := by
  constructor
  · intro s hs
    exact (mem_initFamily_iff.mp (Finset.mem_coe.mp hs)).1
  · rintro s u hs ⟨hlt, hcard⟩
    obtain ⟨hsc, hsr⟩ := mem_initFamily_iff.mp hs
    exact mem_initFamily_iff.mpr
      ⟨hcard, lt_of_lt_of_le (finRank_lt_finRank (hcard.trans hsc.symm) hlt) (le_of_lt hsr)⟩

/-- The ranks of a whole layer are exactly an initial interval. -/
public theorem image_finRank_powersetCard (r : ℕ) :
    (Finset.univ.powersetCard r : Finset (Finset (Fin n))).image finRank
      = Finset.range (n.choose r) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    have hsc : s.card = r := (Finset.mem_powersetCard.mp hs).2
    exact Finset.mem_range.mpr (hsc ▸ finRank_lt s)
  · rw [Finset.card_range, Finset.card_image_of_injOn (finRank_injOn r),
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/--
**The family really has the size asked for.** For every `m` up to the size of the
layer there is a colexicographic initial segment with exactly `m` members.

This is the unranking half of the combinatorial number system, and it is what
lets a numeric statement be fed to a theorem about families.
-/
public theorem card_initFamily (r m : ℕ) (hm : m ≤ n.choose r) :
    (initFamily n r m).card = m := by
  have himg : (initFamily n r m).image finRank = Finset.range m := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (mem_initFamily_iff.mp hs).2
    · intro hj
      have hjr : j ∈ Finset.range (n.choose r) := Finset.mem_range.mpr (lt_of_lt_of_le hj hm)
      rw [← image_finRank_powersetCard r] at hjr
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hjr
      exact ⟨s, mem_initFamily_iff.mpr ⟨(Finset.mem_powersetCard.mp hs).2, hj⟩, rfl⟩
  have hinj : Set.InjOn finRank ((initFamily n r m : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
    intro s hs t ht heq
    refine finRank_injOn r ?_ ?_ heq
    · exact Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (mem_initFamily_iff.mp (Finset.mem_coe.mp hs)).1⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (mem_initFamily_iff.mp (Finset.mem_coe.mp ht)).1⟩)
  rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_range]

/-!
## The combinatorial number system

Mathlib's `Finset.Colex.initSeg` is the initial segment generated by a set. It is
the family this file cuts out by rank, and so its cardinality is one more than
that rank: the statement that the colex rank *is* the position.
-/

/-- Mathlib's generated initial segment is this file's, cut at one past the rank. -/
public theorem initSeg_eq_initFamily (s : Finset (Fin n)) :
    Finset.Colex.initSeg s = initFamily n s.card (finRank s + 1) := by
  ext u
  rw [Finset.Colex.mem_initSeg, mem_initFamily_iff]
  constructor
  · rintro ⟨hcard, hle⟩
    refine ⟨hcard.symm, ?_⟩
    rcases hle.lt_or_eq with hlt | heq
    · exact Nat.lt_succ_of_lt (finRank_lt_finRank hcard.symm hlt)
    · rw [toColex.injective heq]
      exact Nat.lt_succ_self _
  · rintro ⟨hcard, hlt⟩
    refine ⟨hcard.symm, ?_⟩
    by_contra hcon
    have hsu : toColex s < toColex u := lt_of_not_ge hcon
    exact absurd (finRank_lt_finRank hcard.symm hsu) (by omega)

/--
**The colex rank is the position.** An initial segment holds one more set than
the rank of the set that generates it.

This is the combinatorial number system stated as a counting principle, and it is
the step that carries the cascade arithmetic over to families.
-/
public theorem card_initSeg (s : Finset (Fin n)) :
    (Finset.Colex.initSeg s).card = finRank s + 1 := by
  rw [initSeg_eq_initFamily s]
  exact card_initFamily s.card (finRank s + 1) (finRank_lt s)

/-!
## The arithmetic that closes the loop

What is left is a statement about `colexRank` alone: erasing the least element of
a set drops the count in exactly the way `cascadeShadow` says. The identity is
not a digit-by-digit match, so it is proved by two inductions — one for the
generic step and one for the case where the set is the largest of its size.
-/

/--
**The largest set of its size, and what erasing its least element does.**

If `v` ranks last among the `k`-sets below `b`, then dropping its least element
leaves the last `(k-1)`-set below `b`. This is the boundary case the main
induction cannot reach by stripping one digit.
-/
public theorem colexRank_erase_min_of_maximal :
    ∀ (k : ℕ) (v : Finset ℕ) (b : ℕ), v.card = k + 1 → (∀ x ∈ v, x < b) →
      colexRank v + 1 = b.choose (k + 1) →
      ∀ hv : v.Nonempty, colexRank (v.erase (v.min' hv)) + 1 = b.choose k := by
  intro k
  induction k with
  | zero =>
    intro v b hcard _ _ hv
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Finset.min'_singleton, Finset.erase_singleton, colexRank_empty, Nat.choose_zero_right]
  | succ k ih =>
    intro v b hcard hlt hrank hv
    have hmem : v.max' hv ∈ v := v.max'_mem hv
    have hcmax : v.max' hv < b := hlt _ hmem
    have hcard2 : v.card = k + 2 := hcard
    have hvcard : (v.erase (v.max' hv)).card = k + 1 := by
      rw [Finset.card_erase_of_mem hmem, hcard2]
      omega
    have hv'ne : (v.erase (v.max' hv)).Nonempty := Finset.card_pos.mp (by omega)
    have hrec : colexRank v
        = (v.max' hv).choose (k + 2) + colexRank (v.erase (v.max' hv)) := by
      have h := colexRank_erase_max v hv
      rwa [hcard2] at h
    have hrank2 : colexRank v + 1 = b.choose (k + 2) := hrank
    have hsub : ∀ x ∈ v.erase (v.max' hv), x < v.max' hv := fun x hx =>
      lt_of_le_of_ne (v.le_max' x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1
    have hbound := colexRank_lt_choose (k + 1) _ hvcard _ hsub
    have hpascal : (v.max' hv + 1).choose (k + 2)
        = (v.max' hv).choose (k + 1) + (v.max' hv).choose (k + 2) := Nat.choose_succ_succ' _ _
    have hbeq : v.max' hv + 1 = b := by
      by_contra hne
      have hmono2 : (v.max' hv + 2).choose (k + 2) ≤ b.choose (k + 2) :=
        Nat.choose_le_choose _ (by omega)
      have hp2 : (v.max' hv + 2).choose (k + 2)
          = (v.max' hv + 1).choose (k + 1) + (v.max' hv + 1).choose (k + 2) :=
        Nat.choose_succ_succ' _ _
      have hpos : (v.max' hv).choose (k + 1) ≤ (v.max' hv + 1).choose (k + 1) :=
        Nat.choose_le_choose _ (by omega)
      omega
    have hrank' : colexRank (v.erase (v.max' hv)) + 1 = (v.max' hv).choose (k + 1) := by
      rw [← hbeq] at hrank2
      omega
    have hih := ih _ _ hvcard hsub hrank' hv'ne
    have hmm : v.min' hv < v.max' hv := v.min'_lt_max'_of_card (by omega)
    have hminmem : v.min' hv ∈ v.erase (v.max' hv) :=
      Finset.mem_erase.mpr ⟨ne_of_lt hmm, v.min'_mem hv⟩
    have hminv : (v.erase (v.max' hv)).min' hv'ne = v.min' hv :=
      le_antisymm (Finset.min'_le _ _ hminmem)
        (Finset.le_min' _ _ _ fun y hy => v.min'_le y (Finset.mem_of_mem_erase hy))
    -- the set with its least element removed still has the same greatest element
    have hwne : (v.erase (v.min' hv)).Nonempty :=
      ⟨v.max' hv, Finset.mem_erase.mpr ⟨ne_of_gt hmm, hmem⟩⟩
    have hwcard : (v.erase (v.min' hv)).card = k + 1 := by
      rw [Finset.card_erase_of_mem (v.min'_mem hv), hcard2]
      omega
    have hwmax : (v.erase (v.min' hv)).max' hwne = v.max' hv :=
      le_antisymm
        (Finset.max'_le _ _ _ fun y hy => v.le_max' y (Finset.mem_of_mem_erase hy))
        (Finset.le_max' _ _ (Finset.mem_erase.mpr ⟨ne_of_gt hmm, hmem⟩))
    have hwrec : colexRank (v.erase (v.min' hv))
        = (v.max' hv).choose (k + 1)
          + colexRank ((v.erase (v.min' hv)).erase (v.max' hv)) := by
      have h := colexRank_erase_max (v.erase (v.min' hv)) hwne
      rw [hwcard, hwmax] at h
      exact h
    have hswap : (v.erase (v.min' hv)).erase (v.max' hv)
        = (v.erase (v.max' hv)).erase ((v.erase (v.max' hv)).min' hv'ne) := by
      rw [hminv, Finset.erase_right_comm]
    rw [hwrec, hswap]
    have hpascal2 : b.choose (k + 1)
        = (v.max' hv).choose k + (v.max' hv).choose (k + 1) := by
      rw [← hbeq]
      exact Nat.choose_succ_succ' _ _
    omega

/--
**The identity that closes the loop.** Counting the sets at or below `u` and then
applying the cascade's downward shift gives the count at or below `u` with its
least element removed.

This is Kruskal-Katona's numeric content, isolated from any family: the cascade
of a *count* and the elements of the set that realises it need not agree digit by
digit — for `u = {2, 3}` the count is `6`, whose leading digit is `4` — and the
proof therefore runs on the set, splitting on whether the part below the greatest
element is itself the largest of its size.
-/
public theorem cascadeShadow_colexRank_succ :
    ∀ (k : ℕ) (u : Finset ℕ), u.card = k + 1 → ∀ hu : u.Nonempty,
      cascadeShadow (k + 1) (colexRank u + 1)
        = colexRank (u.erase (u.min' hu)) + 1 := by
  intro k
  induction k with
  | zero =>
    intro u hcard hu
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    have htop : cascadeTop 1 (a + 1) = a + 1 :=
      cascadeTop_eq (r := 0) (by simp) (by simp)
    rw [Finset.min'_singleton, Finset.erase_singleton, colexRank_empty,
      colexRank_singleton, cascadeShadow, if_neg (by omega), htop]
    simp [cascadeShadow]
  | succ k ih =>
    intro u hcard hu
    have hmem : u.max' hu ∈ u := u.max'_mem hu
    have hvcard : (u.erase (u.max' hu)).card = k + 1 := by
      rw [Finset.card_erase_of_mem hmem, hcard]
      omega
    have hu'ne : (u.erase (u.max' hu)).Nonempty := Finset.card_pos.mp (by omega)
    have hrec : colexRank u
        = (u.max' hu).choose (k + 1 + 1) + colexRank (u.erase (u.max' hu)) := by
      have h := colexRank_erase_max u hu
      rwa [hcard] at h
    have hsub : ∀ x ∈ u.erase (u.max' hu), x < u.max' hu := fun x hx =>
      lt_of_le_of_ne (u.le_max' x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1
    have hbound := colexRank_lt_choose (k + 1) _ hvcard _ hsub
    have hmm : u.min' hu < u.max' hu := u.min'_lt_max'_of_card (by omega)
    have hminmem : u.min' hu ∈ u.erase (u.max' hu) :=
      Finset.mem_erase.mpr ⟨ne_of_lt hmm, u.min'_mem hu⟩
    have hminv : (u.erase (u.max' hu)).min' hu'ne = u.min' hu :=
      le_antisymm (Finset.min'_le _ _ hminmem)
        (Finset.le_min' _ _ _ fun y hy => u.min'_le y (Finset.mem_of_mem_erase hy))
    have hwne : (u.erase (u.min' hu)).Nonempty :=
      ⟨u.max' hu, Finset.mem_erase.mpr ⟨ne_of_gt hmm, hmem⟩⟩
    have hwcard : (u.erase (u.min' hu)).card = k + 1 := by
      rw [Finset.card_erase_of_mem (u.min'_mem hu), hcard]
      omega
    have hwmax : (u.erase (u.min' hu)).max' hwne = u.max' hu :=
      le_antisymm
        (Finset.max'_le _ _ _ fun y hy => u.le_max' y (Finset.mem_of_mem_erase hy))
        (Finset.le_max' _ _ (Finset.mem_erase.mpr ⟨ne_of_gt hmm, hmem⟩))
    have hswap : (u.erase (u.min' hu)).erase (u.max' hu)
        = (u.erase (u.max' hu)).erase ((u.erase (u.max' hu)).min' hu'ne) := by
      rw [hminv, Finset.erase_right_comm]
    -- the right-hand side, computed once for both cases
    have hRHS : colexRank (u.erase (u.min' hu))
        = (u.max' hu).choose (k + 1)
          + colexRank ((u.erase (u.max' hu)).erase ((u.erase (u.max' hu)).min' hu'ne)) := by
      have h := colexRank_erase_max (u.erase (u.min' hu)) hwne
      rw [hwcard, hwmax, hswap] at h
      exact h
    have hpascal : (u.max' hu + 1).choose (k + 1 + 1)
        = (u.max' hu).choose (k + 1) + (u.max' hu).choose (k + 1 + 1) := Nat.choose_succ_succ' _ _
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hbound) with hcase | hcase
    · -- the part below the greatest element is not the largest of its size
      have htop : cascadeTop (k + 1 + 1) (colexRank u + 1) = u.max' hu :=
        cascadeTop_eq (r := k + 1) (by omega) (by rw [hpascal]; omega)
      rw [cascadeShadow, if_neg (by omega), htop, hRHS]
      have harg : colexRank u + 1 - (u.max' hu).choose (k + 1 + 1)
          = colexRank (u.erase (u.max' hu)) + 1 := by omega
      rw [harg]
      have hstep := ih (u.erase (u.max' hu)) hvcard hu'ne
      omega
    · -- it is, and the cascade rolls over to the next digit
      have hmax := colexRank_erase_min_of_maximal k (u.erase (u.max' hu)) (u.max' hu)
        hvcard hsub (by omega) hu'ne
      have hpascal2 : (u.max' hu + 1).choose (k + 1)
          = (u.max' hu).choose k + (u.max' hu).choose (k + 1) := Nat.choose_succ_succ' _ _
      have hpascal3 : (u.max' hu + 1 + 1).choose (k + 1 + 1)
          = (u.max' hu + 1).choose (k + 1) + (u.max' hu + 1).choose (k + 1 + 1) :=
        Nat.choose_succ_succ' _ _
      have htop : cascadeTop (k + 1 + 1) (colexRank u + 1) = u.max' hu + 1 := by
        refine cascadeTop_eq (r := k + 1) (by omega) ?_
        have hpos : 0 < (u.max' hu + 1).choose (k + 1) := by omega
        omega
      rw [cascadeShadow, if_neg (by omega), htop, hRHS]
      have hzero : colexRank u + 1 - (u.max' hu + 1).choose (k + 1 + 1) = 0 := by omega
      rw [hzero, cascadeShadow_zero_right]
      omega

/-!
## Kruskal-Katona in cascade form

Everything above assembles. The initial family of a given size is a colex initial
segment, Mathlib says its shadow is the initial segment generated by erasing a
least element, the rank counts both, and the identity above says the cascade's
downward shift is exactly that change of count.
-/

/-- Erasing the least element commutes with reading a set through its values. -/
public theorem image_val_erase_min (s : Finset (Fin n)) (hs : s.Nonempty) :
    (s.erase (s.min' hs)).image Fin.val
      = (s.image Fin.val).erase ((s.image Fin.val).min' (hs.image _)) := by
  have hmin : (s.image Fin.val).min' (hs.image _) = ((s.min' hs : Fin n) : ℕ) := by
    refine le_antisymm (Finset.min'_le _ _ (Finset.mem_image_of_mem _ (s.min'_mem hs))) ?_
    refine Finset.le_min' _ _ _ fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Fin.le_def.mp (s.min'_le x hx)
  rw [hmin, Finset.image_erase Fin.val_injective]

/--
**The shadow of an initial family, counted.** The colexicographically first `m`
sets of size `r` touch exactly `cascadeShadow r m` sets of size `r - 1`.
-/
public theorem card_shadow_initFamily (r m : ℕ) (hm : m ≤ n.choose r) :
    (∂ (initFamily n r m)).card = cascadeShadow r m := by
  induction r with
  | zero =>
    have hsub : initFamily n 0 m ⊆ {∅} := by
      intro s hs
      rw [Finset.mem_singleton, ← Finset.card_eq_zero]
      exact (mem_initFamily_iff.mp hs).1
    have : ∂ (initFamily n 0 m) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
      rw [Finset.mem_shadow_iff] at hs
      obtain ⟨A, hA, a, ha, _⟩ := hs
      rw [Finset.mem_singleton.mp (hsub hA)] at ha
      exact absurd ha (Finset.notMem_empty a)
    rw [this, Finset.card_empty, cascadeShadow]
  | succ k _ =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have : initFamily n (k + 1) 0 = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
        exact absurd (mem_initFamily_iff.mp hs).2 (Nat.not_lt_zero _)
      rw [this, Finset.shadow_empty, Finset.card_empty, cascadeShadow, if_pos rfl]
    · have hne : (initFamily n (k + 1) m).Nonempty := by
        rw [← Finset.card_pos, card_initFamily _ _ hm]
        exact hpos
      obtain ⟨s, hscard, hseq⟩ :=
        (isInitSeg_initFamily (n := n) (k + 1) m).exists_initSeg hne
      have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
      have hcards : (Finset.Colex.initSeg s).card = m := by
        rw [← hseq]; exact card_initFamily _ _ hm
      have hrank : finRank s + 1 = m := by rw [← card_initSeg s, hcards]
      rw [hseq, Finset.Colex.shadow_initSeg hsne, card_initSeg, ← hrank]
      rw [finRank, finRank, image_val_erase_min s hsne]
      refine (cascadeShadow_colexRank_succ k (s.image Fin.val) ?_ (hsne.image _)).symm
      rw [card_image_val, hscard]

/--
**Kruskal-Katona, in cascade form.** A family of `r`-sets has a shadow at least
as large as the cascade's downward shift of its own size.

This is the statement Mathlib records as an open task. Mathlib supplies the hard
half — that colexicographic initial segments minimise the shadow — and everything
between that and a number is the ranking above.
-/
public theorem cascadeShadow_le_card_shadow {r : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r) :
    cascadeShadow r 𝒜.card ≤ (∂ 𝒜).card := by
  have hsub : 𝒜 ⊆ Finset.univ.powersetCard r := by
    intro s hs
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h𝒜 (Finset.mem_coe.mpr hs)⟩
  have hcard : 𝒜.card ≤ n.choose r := by
    refine (Finset.card_le_card hsub).trans_eq ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← card_shadow_initFamily r 𝒜.card hcard]
  refine Finset.kruskal_katona h𝒜 ?_ (isInitSeg_initFamily r 𝒜.card)
  exact le_of_eq (card_initFamily r 𝒜.card hcard)

/--
**Kruskal-Katona in cascade form, over an arbitrary ground type.**

The same transport `AISafetyAtlas.Combinatorics.KruskalKatona` performs for the
Lovasz form: carry the family back along an embedding of `Fin s.card` into a
finite `s`, apply the statement there, and push the shadow forward again.

This is the tight bound. `choose_le_card_shadow_iterate` is the loose one, and on
realistic inputs the two differ by a few percent.
-/
public theorem cascadeShadow_le_card_shadow' {α : Type*} [DecidableEq α]
    {𝒜 : Finset (Finset α)} {s : Finset α} {r : ℕ}
    (hsub : ∀ A ∈ 𝒜, A ⊆ s) (hsized : (𝒜 : Set (Finset α)).Sized r) :
    cascadeShadow r 𝒜.card ≤ (∂ 𝒜).card := by
  classical
  obtain ⟨f, hf⟩ := exists_embedding_range_eq s
  set B : Finset α → Finset (Fin s.card) := fun A => Finset.univ.filter (fun j => f j ∈ A)
    with hBdef
  have hBmap : ∀ A ∈ 𝒜, (B A).map f = A := by
    intro A hA
    ext a
    simp only [hBdef, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro ha
      obtain ⟨j, rfl⟩ := (hf a).mp (hsub A hA ha)
      exact ⟨j, ha, rfl⟩
  have hinj : Set.InjOn B 𝒜 := by
    intro A hA A' hA' h
    rw [← hBmap A hA, ← hBmap A' hA', h]
  have hcardB : (𝒜.image B).card = 𝒜.card := Finset.card_image_of_injOn hinj
  have hsizedB : ((𝒜.image B : Finset (Finset (Fin s.card))) :
      Set (Finset (Fin s.card))).Sized r := by
    intro C hC
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hC
    obtain ⟨A, hA, rfl⟩ := hC
    have hmapA : ((B A).map f).card = A.card := by rw [hBmap A hA]
    rw [← Finset.card_map f, hmapA]
    exact hsized hA
  have hshadow :
      ((∂ (𝒜.image B)).map ⟨Finset.map f, Finset.map_injective f⟩) ⊆ ∂ 𝒜 := by
    intro T hT
    rw [Finset.mem_map] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    rw [Finset.mem_shadow_iff_exists_sdiff] at hT₀ ⊢
    obtain ⟨S, hS, hTS, hcard'⟩ := hT₀
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
    refine ⟨A, hA, ?_, ?_⟩
    · rw [← hBmap A hA]
      exact Finset.map_subset_map.mpr hTS
    · rw [← hBmap A hA]
      show (Finset.map f (B A) \ Finset.map f T₀).card = 1
      rw [← Finset.map_sdiff, Finset.card_map]
      exact hcard'
  have hle : (∂ (𝒜.image B)).card ≤ (∂ 𝒜).card := by
    have h := Finset.card_le_card hshadow
    rwa [Finset.card_map] at h
  refine le_trans ?_ hle
  rw [← hcardB]
  exact cascadeShadow_le_card_shadow hsizedB

/--
**The cap is attained, so it is tight.** Given a level of size `a` at order
`r + 1`, there really is a family of `cascadeUpper (r + 1) a` sets of size
`r + 2` whose shadow is no larger than `a`.

`cascadeShadow_le_card_shadow'` and
`cascadeShadow_le_iff_le_cascadeUpper` together say no family does better than
the cap. This says the cap is not merely an upper bound that happens to hold: it
is reached, by the colexicographically first family of that size. Without it the
word "tight" is an assertion about a number rather than a statement about
families, and a corpus at 40% of the cap could in principle be at 40% of
something unreachable.

The hypothesis is the ground set: the witness lives inside `Fin n`, so `n` has
to be wide enough to hold it.
-/
public theorem exists_card_eq_cascadeUpper_of_le {r a : ℕ}
    (hn : cascadeUpper (r + 1) a ≤ n.choose (r + 2)) :
    ∃ 𝔅 : Finset (Finset (Fin n)),
      (𝔅 : Set (Finset (Fin n))).Sized (r + 2) ∧
        𝔅.card = cascadeUpper (r + 1) a ∧ (∂ 𝔅).card ≤ a := by
  refine ⟨initFamily n (r + 2) (cascadeUpper (r + 1) a), ?_, ?_, ?_⟩
  · intro A hA
    exact (mem_initFamily_iff.mp hA).1
  · exact card_initFamily _ _ hn
  · rw [card_shadow_initFamily _ _ hn]
    exact cascadeShadow_cascadeUpper_le (r + 1) a

end AISafetyAtlas.Combinatorics
