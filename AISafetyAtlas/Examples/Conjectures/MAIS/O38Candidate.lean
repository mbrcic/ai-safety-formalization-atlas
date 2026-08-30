module

public import AISafetyAtlas.Analysis.MaximalMinor
public import AISafetyAtlas.Analysis.NullImage
public import AISafetyAtlas.Conjectures.MAIS.O38
public import AISafetyAtlas.Examples.Conjectures.MAIS.O38

/-!
# MAIS-O38: the submitted candidate, proved

`AISafetyAtlas.Conjectures.MAIS.o38PolynomialSampleCandidate` transcribes the
theorem submitted as MAIS issue #30 by `26david26`, and
`o38PolynomialSampleCandidate_holds` **proves it**. The theorem
`maisO38_polynomialSamplesSuffice_holds` then resolves MAIS-O38 at every
`2 ≤ m`, `1 ≤ k < m`, while retaining print's growth hypotheses.

**The mathematics is not the atlas's.** The construction and the argument are the
issue's: `N = m³ + 2m` codes — `m` blocks of `L = m² + 1` codes carried on the
**cyclic windows** `Sₜ = {t, …, t+k-1}` of `[m]`, plus the `m` standard basis
vectors as anchors. The issue stated that it had been produced and checked
entirely by AI systems with no human verification; what this module adds is that
verification, and it found no gap.

## The route

| the note's step | here |
|---|---|
| Lemma 7, the window combinatorics | `cyclicWindow_injective`, `card_windows_containing`, `card_windows_containing_pair` |
| Lemma 6, the dimension count | `exists_subset_windowSpan_le_of_not_badBlock`, `volume_badBlock_eq_zero`, `forcing_of_windowSpan_le` |
| Lemma 8, fixing the codes first | `ae_ae_not_badBlock` |
| Theorem 3, Steps 1/3/4 | `col_mem_span_of_anchors`, `colDegree_eq`, `exists_perm_smul_col`, packaged as `uniquelyCoded_of_forcing` |

Lemma 7 is where `k < m` is spent, and it is false at `k = m` — the note's own
control, and the same boundary the atlas records at
`not_uniquelyCoded_of_full_sparsity_spark`.

Four facts Mathlib does not carry were written for this and are domain-neutral:
`AISafetyAtlas.Analysis.ae_eval_ne_zero_fintype`,
`AISafetyAtlas.Analysis.exists_det_ne_zero_of_linearIndependent`,
`AISafetyAtlas.Analysis.volume_setOf_exists_forall_dotProduct_eq_zero` — which
replaces the semialgebraic dimension count the note phrases the argument in,
since Mathlib has no semialgebraic sets — and
`AISafetyAtlas.Analysis.measurableSet_exists_of_isClosed`, which is what makes
Lemma 8's Tonelli step legitimate without the universal measurability of analytic
sets.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open Finset

/-! ## Cyclic windows -/

/-- The cyclic window of length `k` starting at `t`: print's `Sₜ`, read through
the characterisation `p ∈ Sₜ ↔ (p - t) < k` in `Fin m`, which is the form every
proof below uses. -/
@[expose] public def cyclicWindow {m : ℕ} [NeZero m] (k : ℕ) (t : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun p => ((p - t : Fin m) : ℕ) < k

@[simp]
public theorem mem_cyclicWindow {m : ℕ} [NeZero m] {k : ℕ} {t p : Fin m} :
    p ∈ cyclicWindow k t ↔ ((p - t : Fin m) : ℕ) < k := by
  simp [cyclicWindow]

/-- The `k` residues below `k` are `k` of them, once `k ≤ m`. -/
private theorem card_filter_val_lt (m k : ℕ) [NeZero m] (hk : k ≤ m) :
    (Finset.univ.filter fun s : Fin m => (s : ℕ) < k).card = k := by
  classical
  rw [show (Finset.univ.filter fun s : Fin m => (s : ℕ) < k)
      = (Finset.range k).attachFin (fun i hi => lt_of_lt_of_le (Finset.mem_range.1 hi) hk) by
    ext s
    simp [Finset.mem_attachFin]]
  simp

/-- Every window has exactly `k` elements. -/
public theorem card_cyclicWindow {m k : ℕ} [NeZero m] (hk : k ≤ m) (t : Fin m) :
    (cyclicWindow k t).card = k := by
  classical
  have hbij : (cyclicWindow k t).card
      = (Finset.univ.filter fun s : Fin m => (s : ℕ) < k).card := by
    refine Finset.card_bij' (fun p _ => p - t) (fun s _ => s + t) ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp_all
  rw [hbij, card_filter_val_lt m k hk]

/-- **Lemma 7(b).** Every index lies in exactly `k` of the windows.

This is the equality half of the incidence count: it is what makes the classical
binomial factor disappear, since it bounds the count by `mk` from below at every
column of a rival dictionary that sits on a single atom. -/
public theorem card_windows_containing {m k : ℕ} [NeZero m] (hk : k ≤ m) (p : Fin m) :
    (Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t).card = k := by
  classical
  have hbij : (Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t).card
      = (Finset.univ.filter fun s : Fin m => (s : ℕ) < k).card := by
    refine Finset.card_bij' (fun t _ => p - t) (fun s _ => p - s) ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp_all
  rw [hbij, card_filter_val_lt m k hk]

/-- The predecessor of `0` in `Fin m` is `m - 1`. This is what makes `t - 1` land
*outside* a window of length `k < m`, which is the whole of Lemma 7(a). -/
private theorem val_neg_one (m : ℕ) [NeZero m] : ((-1 : Fin m) : ℕ) = m - 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne m) with ⟨n, rfl⟩
  simp [Fin.coe_neg_one]

/-- **Lemma 7(a).** Distinct starts give distinct windows.

`t` is recoverable from `Sₜ` as its unique element whose predecessor is outside:
`t ∈ Sₜ` needs `1 ≤ k`, and `t - 1 ∉ Sₜ` needs `k < m`. Both hypotheses are
spent here, and at `k = m` the conclusion is false — every window is all of
`[m]`, which is the note's own control and the boundary the atlas records at
`not_uniquelyCoded_of_full_sparsity_spark`. -/
public theorem cyclicWindow_injective {m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m) :
    Function.Injective (cyclicWindow (m := m) k) := by
  intro t s h
  have hself : ((t - s : Fin m) : ℕ) < k := by
    have hmem : t ∈ cyclicWindow k t := by simp; omega
    rw [h] at hmem
    simpa using hmem
  have hpred : ¬ ((t - 1 - s : Fin m) : ℕ) < k := by
    have hnot : (t - 1) ∉ cyclicWindow k t := by
      simp only [mem_cyclicWindow, not_lt, show (t - 1 - t : Fin m) = -1 by abel, val_neg_one]
      omega
    rw [h] at hnot
    simpa using hnot
  by_contra hne
  have ha : (t - s : Fin m) ≠ 0 := sub_ne_zero.mpr hne
  have hav : ((t - s : Fin m) : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using ha
  rw [show (t - 1 - s : Fin m) = (t - s) - 1 by abel, Fin.val_sub_one_of_ne_zero ha] at hpred
  omega

/-- **Lemma 7(c).** Two distinct indices lie together in at most `k - 1` windows.

This is the strict half of the incidence count, and the reason a rival column
supported on two or more atoms is *cheaper* than one supported on a single atom.
The witness is print's: some window containing `p` omits `q`. -/
public theorem card_windows_containing_pair {m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m)
    {p q : Fin m} (hpq : p ≠ q) :
    (Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t).card < k := by
  classical
  have hd0 : ((q - p : Fin m) : ℕ) ≠ 0 := by
    simp only [ne_eq, Fin.val_eq_zero_iff, sub_eq_zero]
    exact fun hc => hpq hc.symm
  -- print's witness: some window catches `p` and misses `q`
  obtain ⟨t₀, hp₀, hq₀⟩ :
      ∃ t₀ : Fin m, p ∈ cyclicWindow k t₀ ∧ q ∉ cyclicWindow k t₀ := by
    by_cases hcase : k ≤ ((q - p : Fin m) : ℕ)
    · refine ⟨p, by simp; omega, ?_⟩
      simp only [mem_cyclicWindow, not_lt]
      exact hcase
    · rw [not_le] at hcase
      have hlt : k - ((q - p : Fin m) : ℕ) < m := by omega
      refine ⟨p - ⟨k - ((q - p : Fin m) : ℕ), hlt⟩, ?_, ?_⟩
      · simp only [mem_cyclicWindow,
          show (p - (p - ⟨k - ((q - p : Fin m) : ℕ), hlt⟩) : Fin m)
            = ⟨k - ((q - p : Fin m) : ℕ), hlt⟩ from by abel]
        show k - ((q - p : Fin m) : ℕ) < k
        omega
      · simp only [mem_cyclicWindow, not_lt,
          show (q - (p - ⟨k - ((q - p : Fin m) : ℕ), hlt⟩) : Fin m)
            = (q - p) + ⟨k - ((q - p : Fin m) : ℕ), hlt⟩ from by abel]
        rw [Fin.val_add]
        show k ≤ (((q - p : Fin m) : ℕ) + (k - ((q - p : Fin m) : ℕ))) % m
        rw [show ((q - p : Fin m) : ℕ) + (k - ((q - p : Fin m) : ℕ)) = k by omega,
          Nat.mod_eq_of_lt hkm]
  have hsub : (Finset.univ.filter
        fun t : Fin m => p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t)
      ⊆ Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t := by
    intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩
  have hne : (Finset.univ.filter
        fun t : Fin m => p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t)
      ≠ Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t := by
    intro heq
    have h0 : t₀ ∈ Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t :=
      Finset.mem_filter.2 ⟨Finset.mem_univ t₀, hp₀⟩
    rw [← heq] at h0
    exact hq₀ (Finset.mem_filter.1 h0).2.2
  exact lt_of_lt_of_le (Finset.card_lt_card (lt_of_le_of_ne hsub hne))
    (le_of_eq (card_windows_containing hkm.le p))

/-! ## Sparse vectors are determined by their image

The note's *"one consequence used repeatedly"* of the spark condition, and the
only property of `A` that Steps 3 and 4 of its Theorem 3 use besides the window
construction. The atlas already carries the special case `m ≤ 2k`
(`SparkCondition.mulVec_injective`); this is the version that bites at every `m`,
because the two vectors are separately `k`-sparse rather than unconstrained. -/

/-- `A *ᵥ v` as a combination of the columns `A` actually uses. -/
private theorem mulVec_eq_sum_of_support {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (v : Fin m → ℝ) (S : Finset (Fin m)) (hv : ∀ j, j ∉ S → v j = 0) :
    A.mulVec v = ∑ j ∈ S, v j • A.col j := by
  rw [Matrix.mulVec_eq_sum,
    ← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hv j hj])]
  simp [Matrix.col]

open AISafetyAtlas.Conjectures.MAIS in
/-- Under the spark condition of order `k`, two `k`-sparse vectors with the same
image are equal: their difference is supported on at most `2k` indices, so the
spark condition makes the corresponding columns independent. -/
public theorem sparse_eq_of_mulVec_eq {k n m : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (hA : SparkCondition k A) {r r' : Fin m → ℝ}
    (hr : IsKSparse k r) (hr' : IsKSparse k r') (h : A.mulVec r = A.mulVec r') : r = r' := by
  classical
  set S : Finset (Fin m) :=
    (Function.support r).toFinset ∪ (Function.support r').toFinset with hS
  have hcard : S.card ≤ 2 * k := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : (Function.support r).toFinset.card ≤ k := by
      rw [← Set.ncard_eq_toFinset_card']; exact hr
    have h2 : (Function.support r').toFinset.card ≤ k := by
      rw [← Set.ncard_eq_toFinset_card']; exact hr'
    omega
  have hind := hA S hcard
  have houts : ∀ j, j ∉ S → (r - r') j = 0 := by
    intro j hj
    simp only [hS, Finset.mem_union, Set.mem_toFinset, Function.mem_support, not_or,
      not_not] at hj
    simp [hj.1, hj.2]
  have hmul : A.mulVec (r - r') = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hsum : ∑ j ∈ S, (r - r') j • A.col j = 0 := by
    rw [← mulVec_eq_sum_of_support A (r - r') S houts, hmul]
  have hcoe : ∑ j : S, (r - r') (j : Fin m) • A.col (j : Fin m) = 0 := by
    rw [Finset.sum_coe_sort S (fun j => (r - r') j • A.col j)]
    exact hsum
  have hzero := Fintype.linearIndependent_iff.1 hind (fun j : S => (r - r') (j : Fin m)) hcoe
  funext j
  by_cases hj : j ∈ S
  · have := hzero ⟨j, hj⟩
    simpa [sub_eq_zero] using this
  · have := houts j hj
    simpa [sub_eq_zero] using this

/-! ## Column spans and their coefficient vectors -/

/-- The span of a set of columns, as the set of images of vectors supported
there. This is the bridge between the geometric side of the note's Step 3 — a
rival column lying in a *window subspace* — and the arithmetic side, a coefficient
vector the spark condition can pin down. -/
public theorem mem_span_col_iff {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (S : Finset (Fin m))
    (b : Fin n → ℝ) :
    b ∈ Submodule.span ℝ (Set.range fun j : S => A.col (j : Fin m)) ↔
      ∃ r : Fin m → ℝ, (∀ j, j ∉ S → r j = 0) ∧ A.mulVec r = b := by
  classical
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun j => if h : j ∈ S then c ⟨j, h⟩ else 0, fun j hj => by simp [hj], ?_⟩
    rw [mulVec_eq_sum_of_support A _ S (fun j hj => by simp [hj]), ← hc,
      ← Finset.sum_coe_sort S (fun j => (if h : j ∈ S then c ⟨j, h⟩ else 0) • A.col j)]
    exact Finset.sum_congr rfl (fun j _ => by simp)
  · rintro ⟨r, hr, rfl⟩
    refine ⟨fun j => r (j : Fin m), ?_⟩
    rw [Finset.sum_coe_sort S (fun j => r j • A.col j)]
    exact (mulVec_eq_sum_of_support A r S hr).symm

/-! ## Window subspaces -/

open AISafetyAtlas.Conjectures.MAIS in
/-- Print's **window subspace** `Uₜ`: the span of the atoms indexed by the cyclic
window at `t`. -/
@[expose] public def windowSpan {n m : ℕ} [NeZero m] (k : ℕ) (A : Matrix (Fin n) (Fin m) ℝ)
    (t : Fin m) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range fun j : (cyclicWindow k t) => A.col (j : Fin m))

public theorem mem_windowSpan_iff {n m : ℕ} [NeZero m] {k : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    {t : Fin m} {b : Fin n → ℝ} :
    b ∈ windowSpan k A t ↔
      ∃ r : Fin m → ℝ, (∀ j, j ∉ cyclicWindow k t → r j = 0) ∧ A.mulVec r = b :=
  mem_span_col_iff A _ b

open AISafetyAtlas.Conjectures.MAIS in
/-- A vector supported on at most `k` indices is `k`-sparse. -/
public theorem isKSparse_of_support_subset {k m : ℕ} (S : Finset (Fin m)) (hS : S.card ≤ k)
    {r : Fin m → ℝ} (hr : ∀ j, j ∉ S → r j = 0) : IsKSparse k r := by
  classical
  have hsub : Function.support r ⊆ (S : Set (Fin m)) := by
    intro j hj
    by_contra hc
    exact hj (hr j (by simpa using hc))
  calc (Function.support r).ncard
      ≤ ((S : Set (Fin m))).ncard := Set.ncard_le_ncard hsub S.finite_toSet
    _ = S.card := by simp
    _ ≤ k := hS

open AISafetyAtlas.Conjectures.MAIS in
/-- **The coefficient vector on a window is unique, across all windows.**

Two window representations of the same vector are `k`-sparse, so the spark
condition of order `k` identifies them. This is what lets the note speak of *the*
support `R_j` of a rival column rather than one support per window. -/
public theorem windowRep_unique {k n m : ℕ} [NeZero m] (hkm : k ≤ m)
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) {r r' : Fin m → ℝ} {t s : Fin m}
    (hr : ∀ j, j ∉ cyclicWindow k t → r j = 0)
    (hr' : ∀ j, j ∉ cyclicWindow k s → r' j = 0)
    (h : A.mulVec r = A.mulVec r') : r = r' :=
  sparse_eq_of_mulVec_eq hA
    (isKSparse_of_support_subset _ (le_of_eq (card_cyclicWindow hkm t)) hr)
    (isKSparse_of_support_subset _ (le_of_eq (card_cyclicWindow hkm s)) hr') h

open AISafetyAtlas.Conjectures.MAIS in
/-- **Print's (15).** Once a rival column has a window representation, the windows
containing it are exactly the windows containing that representation's support. -/
public theorem mem_windowSpan_iff_support_subset {k n m : ℕ} [NeZero m] (hkm : k ≤ m)
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) {r : Fin m → ℝ} {t s : Fin m}
    (hr : ∀ j, j ∉ cyclicWindow k t → r j = 0) :
    A.mulVec r ∈ windowSpan k A s ↔ ∀ j, r j ≠ 0 → j ∈ cyclicWindow k s := by
  constructor
  · intro hmem
    obtain ⟨r', hr', hrr'⟩ := mem_windowSpan_iff.1 hmem
    have : r' = r := windowRep_unique hkm hA hr' hr hrr'
    subst this
    intro j hj
    by_contra hc
    exact hj (hr' j hc)
  · intro hsupp
    exact mem_windowSpan_iff.2 ⟨r, fun j hj => by
      by_contra hc; exact hj (hsupp j hc), rfl⟩

/-! ## The incidence count

Print's Step 3. Each nonzero rival column that meets a window subspace has a
*degree*: the number of windows containing it. Lemma 7(b) caps that degree at
`k`, with equality only when the column sits on a single atom, and Lemma 7(c) is
what makes a column spread over two or more atoms strictly cheaper. Since the
forcing lemma supplies `k` incidences per window, the total is `mk` from below
and `mk` from above, so every column is on a single atom. -/

/-- Membership in a window subspace is not decidable, so the incidence count runs
on `Set.ncard`; these bridge the two Lemma 7 bounds across. -/
private theorem ncard_setOf_eq_card_filter {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] : {a | P a}.ncard = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext a
  simp

private theorem ncard_windows_containing {m k : ℕ} [NeZero m] (hk : k ≤ m) (p : Fin m) :
    {t : Fin m | p ∈ cyclicWindow k t}.ncard = k := by
  classical
  rw [ncard_setOf_eq_card_filter]
  exact card_windows_containing hk p

private theorem ncard_windows_containing_pair {m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m)
    {p q : Fin m} (hpq : p ≠ q) :
    {t : Fin m | p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t}.ncard < k := by
  classical
  rw [ncard_setOf_eq_card_filter]
  exact card_windows_containing_pair hk1 hkm hpq

open AISafetyAtlas.Conjectures.MAIS in
/-- The number of window subspaces containing the `j`-th rival column. -/
@[expose] public noncomputable def colDegree {n m : ℕ} [NeZero m] (k : ℕ)
    (A B : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : ℕ :=
  {t : Fin m | B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t}.ncard

open AISafetyAtlas.Conjectures.MAIS in
/-- Every column has degree at most `k`: its window representation is supported
somewhere, and by Lemma 7(b) only `k` windows contain any given index. -/
public theorem colDegree_le {k n m : ℕ} [NeZero m] (hkm : k < m)
    {A B : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) (j : Fin m) :
    colDegree k A B j ≤ k := by
  by_cases hne : ∃ t : Fin m, B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t
  · obtain ⟨t, hb0, hbt⟩ := hne
    obtain ⟨r, hr, hrb⟩ := mem_windowSpan_iff.1 hbt
    have hr0 : r ≠ 0 := fun hc => hb0 (by rw [← hrb, hc]; simp)
    obtain ⟨p, hp⟩ : ∃ p, r p ≠ 0 := Function.ne_iff.1 hr0
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
      (le_of_eq (ncard_windows_containing hkm.le p))
    intro s hs
    exact (mem_windowSpan_iff_support_subset hkm.le hA hr (s := s)).1
      (by rw [hrb]; exact hs.2) p hp
  · have hempty : {t : Fin m | B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hs => hne ⟨s, hs⟩
    simp [colDegree, hempty]

open AISafetyAtlas.Conjectures.MAIS in
/-- **A column of full degree sits on a single atom.**

If two distinct indices carried the representation, Lemma 7(c) would cap the
degree at `k - 1`. So the support is a single index, and the column is a nonzero
multiple of that atom — print's (17). -/
public theorem exists_smul_col_of_colDegree_eq {k n m : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m)
    {A B : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) {j : Fin m}
    (hdeg : colDegree k A B j = k) :
    ∃ (p : Fin m) (μ : ℝ), μ ≠ 0 ∧ B.col j = μ • A.col p := by
  have hpos : 0 < colDegree k A B j := by omega
  obtain ⟨t, hb0, hbt⟩ : ∃ t : Fin m, B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t := by
    by_contra hc
    have hempty : {t : Fin m | B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hs => hc ⟨s, hs⟩
    rw [colDegree, hempty] at hpos
    simp at hpos
  obtain ⟨r, hr, hrb⟩ := mem_windowSpan_iff.1 hbt
  have hr0 : r ≠ 0 := fun hc => hb0 (by rw [← hrb, hc]; simp)
  obtain ⟨p, hp⟩ : ∃ p, r p ≠ 0 := Function.ne_iff.1 hr0
  -- the support is exactly `{p}`
  have hsingle : ∀ q, r q ≠ 0 → q = p := by
    intro q hq
    by_contra hqp
    have hsub : {s : Fin m | B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A s}
        ⊆ {s : Fin m | q ∈ cyclicWindow k s ∧ p ∈ cyclicWindow k s} := by
      intro s hs
      have hmem := (mem_windowSpan_iff_support_subset hkm.le hA hr (s := s)).1
        (by rw [hrb]; exact hs.2)
      exact ⟨hmem q hq, hmem p hp⟩
    have hlt := lt_of_le_of_lt (Set.ncard_le_ncard hsub (Set.toFinite _))
      (ncard_windows_containing_pair hk1 hkm hqp)
    rw [← colDegree] at hlt
    omega
  refine ⟨p, r p, hp, ?_⟩
  rw [← hrb, mulVec_eq_sum_of_support A r ({p} : Finset (Fin m)) ?_]
  · simp
  · intro q hq
    simp only [Finset.mem_singleton] at hq
    by_contra hc
    exact hq (hsingle q hc)

open AISafetyAtlas.Conjectures.MAIS in
/-- **The lower half of the incidence count.** Each window subspace is spanned by
`k` nonzero rival columns, so counting incidences by window gives `mk`. -/
public theorem sum_colDegree_ge {k n m : ℕ} [NeZero m] {A B : Matrix (Fin n) (Fin m) ℝ}
    (hforce : ∀ t : Fin m, ∃ T : Finset (Fin m), T.card = k ∧
      ∀ j ∈ T, B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t) :
    m * k ≤ ∑ j, colDegree k A B j := by
  classical
  have hcol : ∀ j : Fin m, colDegree k A B j
      = (Finset.univ.filter fun t : Fin m => B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t).card :=
    fun j => ncard_setOf_eq_card_filter _
  simp_rw [hcol, Finset.card_filter]
  rw [Finset.sum_comm]
  have hrow : ∀ t : Fin m,
      k ≤ ∑ j : Fin m, if (B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t) then 1 else 0 := by
    intro t
    obtain ⟨T, hT, hTmem⟩ := hforce t
    calc k = T.card := hT.symm
      _ = ∑ _j ∈ T, 1 := by simp
      _ = ∑ j ∈ T, (if (B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t) then 1 else 0) :=
          Finset.sum_congr rfl (fun j hj => by rw [if_pos (hTmem j hj)])
      _ ≤ ∑ j : Fin m, (if (B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t) then 1 else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun _ _ _ => Nat.zero_le _)
  calc m * k = ∑ _t : Fin m, k := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun t _ => hrow t)

open AISafetyAtlas.Conjectures.MAIS in
/-- **The incidence count is tight**, so every rival column has full degree. -/
public theorem colDegree_eq {k n m : ℕ} [NeZero m] (hkm : k < m)
    {A B : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A)
    (hforce : ∀ t : Fin m, ∃ T : Finset (Fin m), T.card = k ∧
      ∀ j ∈ T, B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t) (j : Fin m) :
    colDegree k A B j = k := by
  classical
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), colDegree k A B j ≤ k :=
    fun j _ => colDegree_le hkm hA j
  have hupper : ∑ j : Fin m, colDegree k A B j ≤ m * k := by
    calc ∑ j : Fin m, colDegree k A B j ≤ ∑ _j : Fin m, k := Finset.sum_le_sum hle
      _ = m * k := by simp [mul_comm]
  have hsum : ∑ j : Fin m, colDegree k A B j = ∑ _j : Fin m, k := by
    have := sum_colDegree_ge hforce
    have hconst : ∑ _j : Fin m, k = m * k := by simp [mul_comm]
    omega
  exact (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)

/-! ## Step 4: the permutation and the rescaling -/

open AISafetyAtlas.Conjectures.MAIS in
/-- **What the forcing lemma delivers**, and all of it that Steps 3 and 4 use: at
every window, `k` linearly independent rival columns lying in that window's
subspace. Isolating it this way is deliberate — everything below is independent
of *how* the forcing lemma is proved. -/
@[expose] public def ForcingData {n m : ℕ} [NeZero m] (k : ℕ)
    (A B : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ t : Fin m, ∃ T : Finset (Fin m), T.card = k ∧
    (∀ j ∈ T, B.col j ∈ windowSpan k A t) ∧ LinearIndependent ℝ fun j : T => B.col j

open AISafetyAtlas.Conjectures.MAIS in
/-- The columns the forcing lemma names are nonzero, being members of a linearly
independent family. -/
public theorem ForcingData.ne_zero {k n m : ℕ} [NeZero m] {A B : Matrix (Fin n) (Fin m) ℝ}
    (hforce : ForcingData k A B) (t : Fin m) : ∃ T : Finset (Fin m), T.card = k ∧
      ∀ j ∈ T, B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t := by
  obtain ⟨T, hT, hmem, hind⟩ := hforce t
  exact ⟨T, hT, fun j hj => ⟨by simpa using hind.ne_zero ⟨j, hj⟩, hmem j hj⟩⟩

open AISafetyAtlas.Conjectures.MAIS in
/-- A one-index coefficient vector realises a rescaled atom. -/
private theorem mulVec_single {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (p : Fin m) (c : ℝ) :
    A.mulVec (fun q => if q = p then c else 0) = c • A.col p := by
  rw [mulVec_eq_sum_of_support A _ ({p} : Finset (Fin m)) (by
    intro q hq; simp only [Finset.mem_singleton] at hq; simp [hq])]
  simp

open AISafetyAtlas.Conjectures.MAIS in
/-- **Print's Steps 3 and 4 together.** Given what the forcing lemma delivers, a
rival dictionary is the original up to a permutation of the atoms and a nonzero
rescaling of each.

Every column sits on a single atom by the incidence count; the map it induces
sends each window's spanning set onto that window, so it is injective on each
window and its image covers `[m]`; a surjective self-map of a finite type is a
bijection. -/
public theorem exists_perm_smul_col {k n m : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m)
    {A B : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A)
    (hforce : ForcingData k A B) :
    ∃ (π : Equiv.Perm (Fin m)) (μ : Fin m → ℝ), (∀ j, μ j ≠ 0) ∧
      ∀ j, B.col j = μ j • A.col (π j) := by
  classical
  -- every column is a nonzero multiple of a single atom
  have hex : ∀ j : Fin m, ∃ pc : Fin m × ℝ, pc.2 ≠ 0 ∧ B.col j = pc.2 • A.col pc.1 := by
    intro j
    obtain ⟨p, c, hc, hb⟩ := exists_smul_col_of_colDegree_eq hk1 hkm hA
      (colDegree_eq hkm hA (fun t => hforce.ne_zero t) j)
    exact ⟨(p, c), hc, hb⟩
  choose f hf0 hfb using hex
  -- the atom of a column lying in a window subspace belongs to that window
  have hmemwin : ∀ (j t : Fin m), B.col j ∈ windowSpan k A t → (f j).1 ∈ cyclicWindow k t := by
    intro j t hmem
    obtain ⟨r, hr, hrb⟩ := mem_windowSpan_iff.1 hmem
    have hone : A.mulVec (fun q => if q = (f j).1 then (f j).2 else 0) = B.col j := by
      rw [mulVec_single]; exact (hfb j).symm
    have heq : (fun q => if q = (f j).1 then (f j).2 else 0) = r :=
      sparse_eq_of_mulVec_eq hA
        (isKSparse_of_support_subset ({(f j).1} : Finset (Fin m)) (by simpa using hk1)
          (by intro q hq; simp only [Finset.mem_singleton] at hq; simp [hq]))
        (isKSparse_of_support_subset _ (le_of_eq (card_cyclicWindow hkm.le t)) hr)
        (by rw [hone, ← hrb])
    by_contra hc
    have hz := hr ((f j).1) hc
    rw [← heq] at hz
    simp at hz
    exact hf0 j hz
  -- the induced atom map is surjective: each window's spanning set maps onto it
  have hsurj : Function.Surjective (fun j => (f j).1) := by
    intro p
    obtain ⟨t, ht⟩ : ∃ t : Fin m, p ∈ cyclicWindow k t := by
      by_contra hc
      have hempty : {t : Fin m | p ∈ cyclicWindow k t} = ∅ := by
        ext s; simpa using fun hs => hc ⟨s, hs⟩
      have := ncard_windows_containing (m := m) (k := k) hkm.le p
      rw [hempty] at this
      simp at this
      omega
    obtain ⟨T, hT, hmem, hind⟩ := hforce t
    -- the atom map is injective on `T`
    have hinjT : ∀ j ∈ T, ∀ j' ∈ T, (f j).1 = (f j').1 → j = j' := by
      intro j hj j' hj' hpp
      by_contra hne
      have hpair : LinearIndependent ℝ ![B.col j, B.col j'] := by
        have hcomp := hind.comp ![(⟨j, hj⟩ : T), ⟨j', hj'⟩] (by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [Subtype.ext_iff])
        convert hcomp using 1
        funext a
        fin_cases a <;> simp
      have hzero : (f j').2 • B.col j + (-((f j).2)) • B.col j' = 0 := by
        rw [hfb j, hfb j', ← hpp, smul_smul, smul_smul, ← add_smul,
          show (f j').2 * (f j).2 + -(f j).2 * (f j').2 = 0 by ring]
        simp
      have hcoef := (LinearIndependent.pair_iff.1 hpair) ((f j').2) (-((f j).2)) hzero
      exact hf0 j' hcoef.1
    -- the image of `T` is contained in `Sₜ`, both of size `k`, so they agree
    have himg : T.image (fun j => (f j).1) ⊆ cyclicWindow k t := by
      intro q hq
      simp only [Finset.mem_image] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      exact hmemwin j t (hmem j hj)
    have hcard : (T.image (fun j => (f j).1)).card = k := by
      rw [Finset.card_image_of_injOn (fun a ha b hb => hinjT a ha b hb), hT]
    have heq : T.image (fun j => (f j).1) = cyclicWindow k t :=
      Finset.eq_of_subset_of_card_le himg (by rw [hcard, card_cyclicWindow hkm.le])
    rw [← heq] at ht
    simp only [Finset.mem_image] at ht
    obtain ⟨j, _, hj⟩ := ht
    exact ⟨j, hj⟩
  have hbij : Function.Bijective (fun j => (f j).1) :=
    ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  exact ⟨Equiv.ofBijective _ hbij, fun j => (f j).2, hf0, hfb⟩

/-! ## From the column identity to print's conclusion -/

private theorem permMatrix_mul_diagonal_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ)
    (a b : Fin m) : (σ.permMatrix ℝ * Matrix.diagonal d) a b = if σ a = b then d b else 0 := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Finset.sum_ite_eq']

private theorem mul_permMatrix_diagonal_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ) (i : Fin n) (b : Fin m) :
    (A * σ.permMatrix ℝ * Matrix.diagonal d) i b = A i (σ.symm b) * d b := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [permMatrix_mul_diagonal_apply, Equiv.apply_eq_iff_eq_symm_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The column identity of Step 4, as the matrix factorisation print asks for. -/
public theorem eq_mul_permMatrix_diagonal {n m : ℕ} {A B : Matrix (Fin n) (Fin m) ℝ}
    (π : Equiv.Perm (Fin m)) (μ : Fin m → ℝ) (h : ∀ j, B.col j = μ j • A.col (π j)) :
    B = A * (Equiv.Perm.permMatrix ℝ π.symm) * Matrix.diagonal μ := by
  ext i j
  rw [mul_permMatrix_diagonal_apply, Equiv.symm_symm]
  have hij := congrFun (h j) i
  simp only [Matrix.col, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul] at hij
  rw [hij, mul_comm]

open AISafetyAtlas.Conjectures.MAIS in
/-- A permuted rescaling preserves `k`-sparsity: this is what lets the final step
compare `x i` with `P D *ᵥ x' i` under the spark condition. -/
private theorem isKSparse_permScale {k m : ℕ} (π : Equiv.Perm (Fin m)) (μ : Fin m → ℝ)
    {v : Fin m → ℝ} (hv : IsKSparse k v) :
    IsKSparse k (fun a => μ (π.symm a) * v (π.symm a)) := by
  classical
  have hsub : Function.support (fun a => μ (π.symm a) * v (π.symm a))
      ⊆ (fun a => π a) '' Function.support v := by
    intro a ha
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at ha
    exact ⟨π.symm a, by simpa using ha.2, by simp⟩
  calc (Function.support (fun a => μ (π.symm a) * v (π.symm a))).ncard
      ≤ ((fun a => π a) '' Function.support v).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (Function.support v).ncard := Set.ncard_image_of_injective _ π.injective
    _ ≤ k := hv

open AISafetyAtlas.Conjectures.MAIS in
/-- **Print's Definition 1 discharged**, given only what the forcing lemma
delivers at every rival dictionary the data admits.

This is Steps 1, 3 and 4 of the note's Theorem 3, with Step 2 — the forcing
lemma itself — taken as the hypothesis `hforce`. -/
public theorem uniquelyCoded_of_forcing {k n m N : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m)
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A)
    {x : Fin N → (Fin m → ℝ)} (hx : ∀ i, IsKSparse k (x i))
    (hforce : ∀ (B : Matrix (Fin n) (Fin m) ℝ) (x' : Fin N → (Fin m → ℝ)),
      (∀ i, IsKSparse k (x' i)) → (∀ i, B.mulVec (x' i) = A.mulVec (x i)) →
        ForcingData k A B) :
    UniquelyCoded k A x := by
  intro B x' hsparse heq
  obtain ⟨π, μ, hμ, hcol⟩ := exists_perm_smul_col hk1 hkm hA (hforce B x' hsparse heq)
  set P : Matrix (Fin m) (Fin m) ℝ := Equiv.Perm.permMatrix ℝ π.symm with hP
  set D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal μ with hD
  have hPperm : IsPermutationMatrix P := ⟨π.symm, rfl⟩
  have hDdiag : IsInvertibleDiagonal D := ⟨μ, hμ, rfl⟩
  have hBfac : B = A * P * D := eq_mul_permMatrix_diagonal π μ hcol
  refine ⟨P, D, hPperm, hDdiag, hBfac, ?_⟩
  intro i
  -- `P * D` applied to a vector is a permuted rescaling, hence `k`-sparse
  have hPD : ∀ v : Fin m → ℝ, (P * D).mulVec v = fun a => μ (π.symm a) * v (π.symm a) := by
    intro v
    funext a
    simp only [Matrix.mulVec, dotProduct, hP, hD, permMatrix_mul_diagonal_apply]
    rw [Finset.sum_eq_single (π.symm a)]
    · simp
    · intro b _ hb
      rw [if_neg (fun hc => hb hc.symm)]
      ring
    · intro h
      simp at h
  have hsparsePD : IsKSparse k ((P * D).mulVec (x' i)) := by
    rw [hPD]; exact isKSparse_permScale π μ (hsparse i)
  -- the spark condition identifies the two `k`-sparse preimages
  have hmul : A.mulVec ((P * D).mulVec (x' i)) = A.mulVec (x i) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← hBfac]
    exact heq i
  have hkey : (P * D).mulVec (x' i) = x i :=
    sparse_eq_of_mulVec_eq hA hsparsePD (hx i) hmul
  -- invert
  have hPu : IsUnit P := hPperm.isUnit
  have hDu : IsUnit D := hDdiag.isUnit
  have hinv : (D⁻¹ * P⁻¹) * (P * D) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹ P D,
      Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det P |>.1 hPu), Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det D |>.1 hDu)]
  calc x' i = ((D⁻¹ * P⁻¹) * (P * D)).mulVec (x' i) := by rw [hinv, Matrix.one_mulVec]
    _ = (D⁻¹ * P⁻¹).mulVec ((P * D).mulVec (x' i)) := by rw [Matrix.mulVec_mulVec]
    _ = (D⁻¹ * P⁻¹).mulVec (x i) := by rw [hkey]

/-! ## The design

Print's construction: `m` blocks of `L = m² + 1` codes carried on the cyclic
windows, together with the `m` standard basis vectors as anchors. The count is
`m·(m² + 1) + m = m³ + 2m`, which is the candidate's `N`. -/

/-- Place a coefficient vector on the window at `t`, and zero elsewhere: print's
`ιₜ`. Supported on `cyclicWindow k t` by construction. -/
@[expose] public def windowPlace {m : ℕ} [NeZero m] {k : ℕ} (t : Fin m) (c : Fin k → ℝ) :
    Fin m → ℝ :=
  fun p => if h : ((p - t : Fin m) : ℕ) < k then c ⟨_, h⟩ else 0

public theorem support_windowPlace {m k : ℕ} [NeZero m] (t : Fin m) (c : Fin k → ℝ) :
    ∀ p, p ∉ cyclicWindow k t → windowPlace t c p = 0 := by
  intro p hp
  simp only [mem_cyclicWindow, not_lt] at hp
  simp [windowPlace, Nat.not_lt.2 hp]

open AISafetyAtlas.Conjectures.MAIS in
public theorem isKSparse_windowPlace {m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m)
    (c : Fin k → ℝ) : IsKSparse k (windowPlace t c) :=
  isKSparse_of_support_subset _ (le_of_eq (card_cyclicWindow hkm t)) (support_windowPlace t c)

/-- The design's index set: `m × L` window codes and `m` anchors. -/
public noncomputable def designEquiv (m : ℕ) :
    ((Fin m × Fin (m ^ 2 + 1)) ⊕ Fin m) ≃ Fin (m ^ 3 + 2 * m) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_sum, Fintype.card_prod]; ring)

open AISafetyAtlas.Conjectures.MAIS in
/-- **Print's design**, at a given coefficient array. -/
@[expose] public noncomputable def o38Design {m : ℕ} [NeZero m] (k : ℕ)
    (c : Fin m → Fin (m ^ 2 + 1) → (Fin k → ℝ)) : Fin (m ^ 3 + 2 * m) → (Fin m → ℝ) :=
  fun i =>
    match (designEquiv m).symm i with
    | .inl tl => windowPlace tl.1 (c tl.1 tl.2)
    | .inr j => Pi.single j (1 : ℝ)

open AISafetyAtlas.Conjectures.MAIS in
/-- Every code in the design is `k`-sparse: the window codes by construction, the
anchors because `1 ≤ k`. -/
public theorem isKSparse_o38Design {m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (c : Fin m → Fin (m ^ 2 + 1) → (Fin k → ℝ)) (i : Fin (m ^ 3 + 2 * m)) :
    IsKSparse k (o38Design k c i) := by
  rw [o38Design]
  cases h : (designEquiv m).symm i with
  | inl tl => exact isKSparse_windowPlace hkm _ _
  | inr j =>
    refine isKSparse_of_support_subset ({j} : Finset (Fin m)) (by simpa using hk1) ?_
    intro q hq
    simp only [Finset.mem_singleton] at hq
    exact Pi.single_eq_of_ne (by simpa using hq) 1

/-! ## The window in coordinates

The forcing lemma runs in the `k` coordinates of a window subspace, so the datum
a block of codes produces has to be written as an explicit combination of the `k`
atoms the window names. -/

/-- The `j`-th atom of the window at `t`. -/
@[expose] public def windowAtom {m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m) (j : Fin k) :
    Fin m :=
  t + ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkm⟩

public theorem windowAtom_mem {m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m) (j : Fin k) :
    windowAtom hkm t j ∈ cyclicWindow k t := by
  simp only [mem_cyclicWindow, windowAtom, add_sub_cancel_left]
  exact j.isLt

public theorem windowAtom_injective {m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m) :
    Function.Injective (windowAtom hkm t) := by
  intro j j' h
  simp only [windowAtom, add_right_inj, Fin.mk.injEq] at h
  exact Fin.ext h

public theorem cyclicWindow_eq_image {m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m) :
    cyclicWindow k t = Finset.univ.image (windowAtom hkm t) := by
  ext p
  simp only [mem_cyclicWindow, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hp
    refine ⟨⟨((p - t : Fin m) : ℕ), hp⟩, ?_⟩
    simp only [windowAtom]
    rw [show (⟨((p - t : Fin m) : ℕ), lt_of_lt_of_le hp hkm⟩ : Fin m) = p - t from Fin.ext rfl]
    abel
  · rintro ⟨j, rfl⟩
    simp [windowAtom]

public theorem windowPlace_windowAtom {m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m)
    (c : Fin k → ℝ) (j : Fin k) : windowPlace t c (windowAtom hkm t j) = c j := by
  have hval : ((windowAtom hkm t j - t : Fin m) : ℕ) = (j : ℕ) := by
    simp [windowAtom]
  simp only [windowPlace]
  rw [dif_pos (by rw [hval]; exact j.isLt)]
  congr 1
  exact Fin.ext hval

/-- **The datum of a window code, as a combination of the window's atoms.** -/
public theorem mulVec_windowPlace {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (c : Fin k → ℝ) :
    A.mulVec (windowPlace t c) = fun i => ∑ j : Fin k, c j * A.col (windowAtom hkm t j) i := by
  classical
  rw [mulVec_eq_sum_of_support A _ (cyclicWindow k t) (support_windowPlace t c),
    cyclicWindow_eq_image hkm t,
    Finset.sum_image (fun a _ b _ hab => windowAtom_injective hkm t hab)]
  funext i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [windowPlace_windowAtom hkm t c j]

/-! ## Step 1: the anchors put the rival inside `im A`

Print's Step 1, and the only role the `m` anchors play. It is what makes the
forcing lemma applicable at all, because the dimension count there is against
`im A` — of dimension at most `m`, however large `n` is — and not against `ℝⁿ`. -/

/-- Any image of `A` lies in the span of its columns. -/
private theorem mulVec_mem_span_col {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ) :
    A.mulVec v ∈ Submodule.span ℝ (Set.range A.col) := by
  rw [← Matrix.range_mulVecLin]
  exact ⟨v, rfl⟩

/-- If every atom of `A` is reachable from `B`, the atoms lie in `B`'s column
span. This is what the anchors give. -/
public theorem col_mem_span_of_exists_mulVec {n m : ℕ} {A B : Matrix (Fin n) (Fin m) ℝ}
    (h : ∀ j, ∃ w, B.mulVec w = A.col j) (j : Fin m) :
    A.col j ∈ Submodule.span ℝ (Set.range B.col) := by
  obtain ⟨w, hw⟩ := h j
  rw [← hw]
  exact mulVec_mem_span_col B w

/-- **Print's Step 1.** Once `A` has maximal rank and every atom of `A` is
reachable from `B`, the rival's columns lie in `im A`.

Both cases of print's dimension comparison appear: at `n ≤ m` the span of `A`'s
columns is already everything, and at `n > m` it has dimension `m`, which `B`'s
column span cannot exceed. -/
public theorem col_mem_span_of_anchors {n m : ℕ} {A B : Matrix (Fin n) (Fin m) ℝ}
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) = min n m)
    (hanchor : ∀ j, A.col j ∈ Submodule.span ℝ (Set.range B.col)) (j : Fin m) :
    B.col j ∈ Submodule.span ℝ (Set.range A.col) := by
  classical
  have hle : Submodule.span ℝ (Set.range A.col) ≤ Submodule.span ℝ (Set.range B.col) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hanchor i)
  by_cases hnm : n ≤ m
  · have htop : Submodule.span ℝ (Set.range A.col) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hrank, min_eq_left hnm]
      simp
    rw [htop]
    trivial
  · rw [not_le] at hnm
    have hBle : Module.finrank ℝ (Submodule.span ℝ (Set.range B.col)) ≤ m := by
      have h1 := finrank_span_le_card (R := ℝ) (Set.range B.col)
      have h2 : (Set.range B.col).toFinset.card ≤ m := by
        rw [Set.toFinset_range]
        exact le_trans Finset.card_image_le (by simp)
      exact le_trans h1 h2
    have heq : Submodule.span ℝ (Set.range A.col) = Submodule.span ℝ (Set.range B.col) := by
      refine Submodule.eq_of_le_of_finrank_le hle ?_
      rw [hrank, min_eq_right hnm.le]
      exact hBle
    rw [heq]
    exact Submodule.subset_span ⟨j, rfl⟩

open AISafetyAtlas.Conjectures.MAIS in
/-- The design's anchors, read off: the `j`-th anchor's datum is the `j`-th atom
of `A`, so a rival reproducing the data reaches every atom. -/
public theorem exists_mulVec_of_design {m k : ℕ} [NeZero m] {n : ℕ}
    {A B : Matrix (Fin n) (Fin m) ℝ} {c : Fin m → Fin (m ^ 2 + 1) → (Fin k → ℝ)}
    {x' : Fin (m ^ 3 + 2 * m) → (Fin m → ℝ)}
    (heq : ∀ i, B.mulVec (x' i) = A.mulVec (o38Design k c i)) (j : Fin m) :
    ∃ w, B.mulVec w = A.col j := by
  refine ⟨x' (designEquiv m (.inr j)), ?_⟩
  rw [heq]
  have hval : o38Design k c (designEquiv m (.inr j)) = Pi.single j (1 : ℝ) := by
    rw [o38Design]
    simp
  rw [hval, show (Pi.single j (1 : ℝ)) = fun q => if q = j then (1 : ℝ) else 0 from by
    funext q; simp [Pi.single_apply], mulVec_single]
  simp

/-! ## Lemma 6: the parameters of a rival, and the minors that cut it down

A rival whose columns lie in `im A` is `A · C`, so the rivals form an
`m²`-parameter family — and `L = m² + 1` clears that by exactly one. That is the
whole reason the count works, and it is why no basis of `im A` is ever needed. -/

/-- A rival with columns in `im A` is `A * C`. -/
public theorem exists_matrix_of_col_mem_span {n m : ℕ} {A B : Matrix (Fin n) (Fin m) ℝ}
    (h : ∀ j, B.col j ∈ Submodule.span ℝ (Set.range A.col)) :
    ∃ C : Matrix (Fin m) (Fin m) ℝ, B = A * C := by
  have h' : ∀ j, ∃ w, A.mulVec w = B.col j := by
    intro j
    have hj := h j
    rw [← Matrix.range_mulVecLin] at hj
    exact hj
  choose v hv using h'
  refine ⟨Matrix.of fun p q => v q p, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  have hij := congrFun (hv j) i
  simp only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply] at hij
  simpa [Matrix.of_apply] using hij.symm

/-- The discrete data one minor witness needs: how many rival columns to use,
which ones, and which rows to read. Finitely many, so a union over them is a
finite union. -/
@[expose] public def MinorChoice (k m n : ℕ) : Type :=
  Σ r : Fin (k + 1), (Fin (r : ℕ) → Fin m) × (Option (Fin (r : ℕ)) → Fin n)

public instance instFintypeMinorChoice (k m n : ℕ) : Fintype (MinorChoice k m n) := by
  unfold MinorChoice
  infer_instance

open AISafetyAtlas.Analysis in
/-- The normal vector a single choice contributes: the minor of the chosen rival
columns bordered by the window's `j`-th atom. Polynomial in `C`. -/
@[expose] public noncomputable def choiceNormal {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (d : MinorChoice k m n)
    (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin k) : ℝ :=
  borderedMinor (fun i : Fin (d.1 : ℕ) => ((A * C).col (d.2.1 i))) d.2.2
    (A.col (windowAtom hkm t j))

open AISafetyAtlas.Analysis in
/-- **The weighted sum of the normals is the minor at the block's datum.** This
is what makes the forcing condition a linear condition on the coefficients. -/
public theorem sum_choiceNormal {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (d : MinorChoice k m n)
    (C : Matrix (Fin m) (Fin m) ℝ) (c : Fin k → ℝ) :
    ∑ j, c j * choiceNormal hkm A t d C j
      = borderedMinor (fun i : Fin (d.1 : ℕ) => ((A * C).col (d.2.1 i))) d.2.2
          (A.mulVec (windowPlace t c)) := by
  rw [mulVec_windowPlace hkm]
  exact (borderedMinor_sum _ _ c (fun j => A.col (windowAtom hkm t j))).symm

open AISafetyAtlas.Conjectures.MAIS in
/-- The window subspace, spanned by the window's atoms listed in order. -/
public theorem windowSpan_eq_span_atoms {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) :
    windowSpan k A t
      = Submodule.span ℝ (Set.range fun j : Fin k => A.col (windowAtom hkm t j)) := by
  rw [windowSpan]
  congr 1
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    have hp : (((p : Fin m) - t : Fin m) : ℕ) < k := mem_cyclicWindow.1 p.2
    refine ⟨⟨(((p : Fin m) - t : Fin m) : ℕ), hp⟩, ?_⟩
    congr 1
    simp only [windowAtom]
    rw [show (⟨(((p : Fin m) - t : Fin m) : ℕ), lt_of_lt_of_le hp hkm⟩ : Fin m)
      = (p : Fin m) - t from Fin.ext rfl]
    abel
  · rintro ⟨j, rfl⟩
    exact ⟨⟨windowAtom hkm t j, windowAtom_mem hkm t j⟩, rfl⟩

/-- **The coefficient blocks the forcing lemma has to exclude.** A block is bad
when some rival, with some choice of witnessing minors, makes every one of the
`L` linear conditions vanish while all the minors are alive. -/
@[expose] public noncomputable def BadBlock {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (c : Fin (m ^ 2 + 1) → Fin k → ℝ) : Prop :=
  ∃ (D : Fin (m ^ 2 + 1) → MinorChoice k m n) (C : Matrix (Fin m) (Fin m) ℝ),
    (∀ ℓ, ∃ j, choiceNormal hkm A t (D ℓ) C j ≠ 0) ∧
      ∀ ℓ, ∑ j, c ℓ j * choiceNormal hkm A t (D ℓ) C j = 0

open AISafetyAtlas.Analysis AISafetyAtlas.Conjectures.MAIS in
/-- **Lemma 6, the logical half.** For a block that is not bad, every rival
admitting the data has some `≤ k` of its columns spanning the window subspace.

This is print's Step 2 with the measure-theoretic content factored out: the only
thing used about the block is that it escapes `BadBlock`. -/
public theorem exists_subset_windowSpan_le_of_not_badBlock {n m k : ℕ} [NeZero m]
    (hkm : k ≤ m) {A : Matrix (Fin n) (Fin m) ℝ} (t : Fin m)
    {c : Fin (m ^ 2 + 1) → Fin k → ℝ} (hgood : ¬ BadBlock hkm A t c)
    {B : Matrix (Fin n) (Fin m) ℝ}
    (hBcol : ∀ j, B.col j ∈ Submodule.span ℝ (Set.range A.col))
    (hy : ∀ ℓ, ∃ T : Finset (Fin m), T.card ≤ k ∧
      A.mulVec (windowPlace t (c ℓ))
        ∈ Submodule.span ℝ (Set.range fun j : T => B.col (j : Fin m))) :
    ∃ T : Finset (Fin m), T.card ≤ k ∧
      windowSpan k A t ≤ Submodule.span ℝ (Set.range fun j : T => B.col (j : Fin m)) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC⟩ := exists_matrix_of_col_mem_span hBcol
  subst hC
  refine hgood ?_
  -- for each block index, pick a witnessing minor
  have hchoice : ∀ ℓ : Fin (m ^ 2 + 1), ∃ d : MinorChoice k m n,
      (∃ j, choiceNormal hkm A t d C j ≠ 0) ∧
        ∑ j, c ℓ j * choiceNormal hkm A t d C j = 0 := by
    intro ℓ
    obtain ⟨T, hTcard, hyT⟩ := hy ℓ
    -- an independent subfamily of the chosen rival columns, with the same span
    obtain ⟨r, σ', hrle, hind, hspan⟩ :=
      exists_independent_spanning_subfamily (fun i : T => (A * C).col (i : Fin m))
    have hrk : r ≤ k := le_trans hrle (by simpa using hTcard)
    -- some window atom escapes that span
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin k,
        A.col (windowAtom hkm t j₀)
          ∉ Submodule.span ℝ (Set.range ((fun i : T => (A * C).col (i : Fin m)) ∘ σ')) := by
      by_contra hall
      push Not at hall
      refine hcon T hTcard ?_
      rw [windowSpan_eq_span_atoms hkm]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      rw [← hspan]
      exact hall j
    -- border it and take a nonzero minor
    have hopt : (fun b : Option (Fin r) =>
          Option.elim b (A.col (windowAtom hkm t j₀))
            ((fun i : T => (A * C).col (i : Fin m)) ∘ σ'))
        = fun o : Option (Fin r) => o.casesOn' (A.col (windowAtom hkm t j₀))
            ((fun i : T => (A * C).col (i : Fin m)) ∘ σ') := by
      funext o
      cases o <;> rfl
    obtain ⟨f, hf⟩ := exists_borderedMinor_ne_zero
      ((fun i : T => (A * C).col (i : Fin m)) ∘ σ') (hopt ▸ hind.option hj₀)
    refine ⟨⟨⟨r, by omega⟩, ((fun i => (σ' i : Fin m)), f)⟩, ⟨j₀, ?_⟩, ?_⟩
    · simp only [choiceNormal]
      exact hf
    · rw [sum_choiceNormal hkm]
      refine borderedMinor_eq_zero_of_mem_span _ _ ?_
      rw [show (Set.range fun i : Fin (⟨r, by omega⟩ : Fin (k + 1)).1 =>
          (A * C).col ((σ' i : Fin m)))
          = Set.range ((fun i : T => (A * C).col (i : Fin m)) ∘ σ') from rfl, hspan]
      exact hyT
  choose D hD1 hD2 using hchoice
  exact ⟨D, C, hD1, hD2⟩

open AISafetyAtlas.Conjectures.MAIS in
/-- The window subspace has dimension `k`: its atoms are `k` columns, and the
spark condition of order `k` makes any `2k` of them independent. -/
public theorem finrank_windowSpan {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) (t : Fin m) :
    Module.finrank ℝ (windowSpan k A t) = k := by
  classical
  have hind : LinearIndependent ℝ fun j : (cyclicWindow k t) => A.col (j : Fin m) :=
    hA _ (by rw [card_cyclicWindow hkm]; omega)
  rw [windowSpan, finrank_span_eq_card hind, Fintype.card_coe]
  exact card_cyclicWindow hkm t

open AISafetyAtlas.Conjectures.MAIS in
/-- **Lemma 6, the linear-algebra half.** Print's *"`k = dim U ≤ dim V_T ≤ |T| ≤ k`,
so all of these are equalities"*. -/
public theorem forcing_of_windowSpan_le {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    {A B : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) (t : Fin m)
    {T : Finset (Fin m)} (hTcard : T.card ≤ k)
    (hle : windowSpan k A t ≤ Submodule.span ℝ (Set.range fun j : T => B.col (j : Fin m))) :
    T.card = k ∧ (∀ j ∈ T, B.col j ∈ windowSpan k A t) ∧
      LinearIndependent ℝ fun j : T => B.col (j : Fin m) := by
  classical
  have hcardT : Fintype.card T = T.card := by simp
  have hup : Module.finrank ℝ (Submodule.span ℝ (Set.range fun j : T => B.col (j : Fin m)))
      ≤ T.card := by
    rw [← hcardT]
    exact finrank_range_le_card (fun j : T => B.col (j : Fin m))
  have hdown : k ≤ Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun j : T => B.col (j : Fin m))) := by
    rw [← finrank_windowSpan hkm hA t]
    exact Submodule.finrank_mono hle
  have hTk : T.card = k := le_antisymm hTcard (le_trans hdown hup)
  have hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range fun j : T => B.col (j : Fin m)))
      = Fintype.card T := le_antisymm (by simpa [hcardT] using hup) (by
        rw [hcardT, hTk]; exact hdown)
  have hindB : LinearIndependent ℝ fun j : T => B.col (j : Fin m) := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    simpa [Set.finrank] using hrank.symm
  have heq : windowSpan k A t
      = Submodule.span ℝ (Set.range fun j : T => B.col (j : Fin m)) := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_windowSpan hkm hA t, hrank, hcardT, hTk]
  refine ⟨hTk, ?_, hindB⟩
  intro j hj
  rw [heq]
  exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

open AISafetyAtlas.Analysis in
/-- The normals are polynomial in the rival's parameters, hence `C¹`. -/
public theorem contDiff_choiceNormal {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (d : MinorChoice k m n) (j : Fin k) :
    ContDiff ℝ 1 fun C : Fin m × Fin m → ℝ =>
      choiceNormal hkm A t d (Matrix.of fun p q => C (p, q)) j := by
  simp only [choiceNormal]
  refine contDiff_borderedMinor _ (fun i r => ?_) (fun r => contDiff_const)
  simp only [Matrix.col, Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun p _ => contDiff_const.mul (contDiff_apply ℝ ℝ (p, d.2.1 i))

open AISafetyAtlas.Analysis in
/-- **Lemma 6, the measure half.** The bad coefficient blocks form a null set.

This is the dimension count. The rivals with columns in `im A` are `A · C`, an
`m²`-parameter family; each of the `L = m² + 1` blocks costs its own factor one
dimension; and `m² < L` is exactly the margin. -/
public theorem volume_badBlock_eq_zero {n m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) :
    MeasureTheory.volume {c : Fin (m ^ 2 + 1) × Fin k → ℝ |
      ∃ (D : Fin (m ^ 2 + 1) → MinorChoice k m n) (C : Fin m × Fin m → ℝ),
        (∀ ℓ, ∃ j, choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j ≠ 0) ∧
          ∀ ℓ, ∑ j, c (ℓ, j)
            * choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j = 0} = 0 := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set S : (Fin (m ^ 2 + 1) → MinorChoice (k' + 1) m n) →
      Set (Fin (m ^ 2 + 1) × Fin (k' + 1) → ℝ) := fun D =>
    {c | ∃ C : Fin m × Fin m → ℝ,
      (∀ ℓ, ∃ j, choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j ≠ 0) ∧
        ∀ ℓ, ∑ j, c (ℓ, j)
          * choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j = 0} with hSdef
  have hcover : {c : Fin (m ^ 2 + 1) × Fin (k' + 1) → ℝ |
      ∃ (D : Fin (m ^ 2 + 1) → MinorChoice (k' + 1) m n) (C : Fin m × Fin m → ℝ),
        (∀ ℓ, ∃ j, choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j ≠ 0) ∧
          ∀ ℓ, ∑ j, c (ℓ, j)
            * choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j = 0}
      ⊆ ⋃ D, S D := by
    rintro c ⟨D, C, h1, h2⟩
    exact Set.mem_iUnion.2 ⟨D, ⟨C, h1, h2⟩⟩
  refine MeasureTheory.measure_mono_null hcover
    (MeasureTheory.measure_iUnion_null fun D => ?_)
  rw [hSdef]
  refine volume_setOf_exists_forall_dotProduct_eq_zero
      (w := fun C q => choiceNormal hkm A t (D q.1) (Matrix.of fun p q' => C (p, q')) q.2)
      (P := fun C => ∀ ℓ, ∃ j, choiceNormal hkm A t (D ℓ)
        (Matrix.of fun p q' => C (p, q')) j ≠ 0) ?_ (fun a hPa ℓ => hPa ℓ) ?_
  · exact contDiff_pi.2 fun q => contDiff_choiceNormal hkm A t (D q.1) q.2
  · simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith [Nat.zero_le k', Nat.zero_le m]

/-! ## Lemma 8: fixing the codes before the dictionary

Print's Lemma 8. For each dictionary the bad blocks are null; Tonelli turns that
into *for almost every array of blocks, the bad dictionaries are null*, which is
the quantifier order the printed question demands. The step that needs care is
measurability of the bad set in the product, since it is stated with an
existential over rivals; `AISafetyAtlas.Analysis.measurableSet_exists_of_isClosed`
is what discharges it. -/

open AISafetyAtlas.Analysis in
/-- The normal, as a function of the dictionary and the rival's parameters
jointly. Polynomial in both, hence `C¹`. -/
public theorem contDiff_pairNormal {n m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m)
    (d : MinorChoice k m n) (j : Fin k) :
    ContDiff ℝ 1 fun x : (Fin m × Fin m → ℝ) ×
        ((Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ))) =>
      choiceNormal hkm (Matrix.of x.2.1) t d (Matrix.of fun p q => x.1 (p, q)) j := by
  simp only [choiceNormal]
  refine contDiff_borderedMinor _ (fun i r => ?_) (fun r => ?_)
  · simp only [Matrix.col, Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply]
    refine ContDiff.sum fun p _ => ContDiff.mul ?_ ?_
    · exact (contDiff_apply ℝ ℝ p).comp
        ((contDiff_apply ℝ (Fin m → ℝ) r).comp (contDiff_fst.comp contDiff_snd))
    · exact (contDiff_apply ℝ ℝ (p, d.2.1 i)).comp contDiff_fst
  · simp only [Matrix.col, Matrix.transpose_apply, Matrix.of_apply]
    exact (contDiff_apply ℝ ℝ (windowAtom hkm t j)).comp
      ((contDiff_apply ℝ (Fin m → ℝ) r).comp (contDiff_fst.comp contDiff_snd))

open AISafetyAtlas.Analysis in
/-- **The bad set is measurable in the product.** Stated per window, per discrete
choice, per witnessing coordinate and per lower bound on the witnessing minor —
the countable union of those is the bad set itself. -/
public theorem measurableSet_badPiece {n m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m)
    (D : Fin (m ^ 2 + 1) → MinorChoice k m n) (jj : Fin (m ^ 2 + 1) → Fin k) (ε : ℝ) :
    MeasurableSet {x : (Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ)) |
      ∃ C : Fin m × Fin m → ℝ,
        (∀ ℓ, ε ≤ |choiceNormal hkm (Matrix.of x.1) t (D ℓ)
            (Matrix.of fun p q => C (p, q)) (jj ℓ)|) ∧
          ∀ ℓ, ∑ j, x.2 t (ℓ, j)
            * choiceNormal hkm (Matrix.of x.1) t (D ℓ) (Matrix.of fun p q => C (p, q)) j = 0} := by
  have hcont : ∀ (ℓ : Fin (m ^ 2 + 1)) (j : Fin k),
      Continuous fun p : (Fin m × Fin m → ℝ) ×
          ((Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ))) =>
        choiceNormal hkm (Matrix.of p.2.1) t (D ℓ) (Matrix.of fun a b => p.1 (a, b)) j :=
    fun ℓ j => (contDiff_pairNormal hkm t (D ℓ) j).continuous
  refine measurableSet_exists_of_isClosed (F := {p : (Fin m × Fin m → ℝ) ×
      ((Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ))) |
      (∀ ℓ, ε ≤ |choiceNormal hkm (Matrix.of p.2.1) t (D ℓ)
          (Matrix.of fun a b => p.1 (a, b)) (jj ℓ)|) ∧
        ∀ ℓ, ∑ j, p.2.2 t (ℓ, j)
          * choiceNormal hkm (Matrix.of p.2.1) t (D ℓ)
              (Matrix.of fun a b => p.1 (a, b)) j = 0}) ?_
  have h1 : IsClosed {p : (Fin m × Fin m → ℝ) ×
      ((Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ))) |
      ∀ ℓ, ε ≤ |choiceNormal hkm (Matrix.of p.2.1) t (D ℓ)
        (Matrix.of fun a b => p.1 (a, b)) (jj ℓ)|} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun ℓ => isClosed_le continuous_const (hcont ℓ (jj ℓ)).abs
  have h2 : IsClosed {p : (Fin m × Fin m → ℝ) ×
      ((Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ))) |
      ∀ ℓ, ∑ j, p.2.2 t (ℓ, j)
        * choiceNormal hkm (Matrix.of p.2.1) t (D ℓ)
            (Matrix.of fun a b => p.1 (a, b)) j = 0} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun ℓ => isClosed_eq (continuous_finsetSum _ fun j _ => ?_)
      continuous_const
    exact Continuous.mul
      ((continuous_apply (ℓ, j)).comp
        ((continuous_apply t).comp (continuous_snd.comp continuous_snd)))
      (hcont ℓ j)
  exact h1.inter h2

open AISafetyAtlas.Analysis in
/-- `BadBlock` with its coefficient block and rival parameters flattened, which is
the shape both the measure statement and the Tonelli step use. -/
public theorem badBlock_iff_flat {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (c : Fin (m ^ 2 + 1) × Fin k → ℝ) :
    BadBlock hkm A t (fun ℓ j => c (ℓ, j)) ↔
      ∃ (D : Fin (m ^ 2 + 1) → MinorChoice k m n) (C : Fin m × Fin m → ℝ),
        (∀ ℓ, ∃ j, choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j ≠ 0) ∧
          ∀ ℓ, ∑ j, c (ℓ, j)
            * choiceNormal hkm A t (D ℓ) (Matrix.of fun p q => C (p, q)) j = 0 := by
  constructor
  · rintro ⟨D, C, h1, h2⟩
    exact ⟨D, fun pq => C pq.1 pq.2, h1, h2⟩
  · rintro ⟨D, C, h1, h2⟩
    exact ⟨D, Matrix.of fun p q => C (p, q), h1, h2⟩

open AISafetyAtlas.Analysis in
/-- **The bad set in the product is measurable.** The existential over rivals is
made measurable by `measurableSet_exists_of_isClosed`; the remaining quantifiers
— the window, the discrete choice, which coordinate witnesses, and how large the
witnessing minor is — are all countable. -/
public theorem measurableSet_badPair {n m k : ℕ} [NeZero m] (hkm : k ≤ m) :
    MeasurableSet {x : (Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ)) |
      ∃ t, BadBlock hkm (Matrix.of x.1) t (fun ℓ j => x.2 t (ℓ, j))} := by
  classical
  have hrw : {x : (Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ)) |
      ∃ t, BadBlock hkm (Matrix.of x.1) t (fun ℓ j => x.2 t (ℓ, j))}
      = ⋃ t : Fin m, ⋃ D : Fin (m ^ 2 + 1) → MinorChoice k m n,
          ⋃ jj : Fin (m ^ 2 + 1) → Fin k, ⋃ i : ℕ,
            {x : (Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ)) |
              ∃ C : Fin m × Fin m → ℝ,
                (∀ ℓ, (1 : ℝ) / (i + 1) ≤ |choiceNormal hkm (Matrix.of x.1) t (D ℓ)
                    (Matrix.of fun p q => C (p, q)) (jj ℓ)|) ∧
                  ∀ ℓ, ∑ j, x.2 t (ℓ, j)
                    * choiceNormal hkm (Matrix.of x.1) t (D ℓ)
                        (Matrix.of fun p q => C (p, q)) j = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, hbad⟩
      obtain ⟨D, C, h1, h2⟩ := (badBlock_iff_flat hkm _ t (fun q => x.2 t q)).1 hbad
      choose jj hjj using h1
      obtain ⟨i, hi⟩ : ∃ i : ℕ, ∀ ℓ, (1 : ℝ) / (i + 1)
          ≤ |choiceNormal hkm (Matrix.of x.1) t (D ℓ)
              (Matrix.of fun p q => C (p, q)) (jj ℓ)| := by
        have hne : (Finset.univ : Finset (Fin (m ^ 2 + 1))).Nonempty :=
          ⟨0, Finset.mem_univ _⟩
        have hminpos : (0 : ℝ) < Finset.univ.inf' hne (fun ℓ =>
            |choiceNormal hkm (Matrix.of x.1) t (D ℓ)
              (Matrix.of fun p q => C (p, q)) (jj ℓ)|) := by
          rw [Finset.lt_inf'_iff]
          exact fun ℓ _ => abs_pos.2 (hjj ℓ)
        obtain ⟨i, hi⟩ := exists_nat_one_div_lt hminpos
        exact ⟨i, fun ℓ => le_trans hi.le (Finset.inf'_le _ (Finset.mem_univ ℓ))⟩
      exact ⟨t, D, jj, i, C, hi, h2⟩
    · rintro ⟨t, D, jj, i, C, h1, h2⟩
      refine ⟨t, (badBlock_iff_flat hkm _ t (fun q => x.2 t q)).2 ⟨D, C, fun ℓ => ⟨jj ℓ, ?_⟩, h2⟩⟩
      intro hz
      have hcon := h1 ℓ
      rw [hz, abs_zero] at hcon
      have hpos : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
      linarith
  rw [hrw]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun D =>
    MeasurableSet.iUnion fun jj => MeasurableSet.iUnion fun i =>
      measurableSet_badPiece hkm t D jj _

open MeasureTheory AISafetyAtlas.Analysis in
/-- **Lemma 8.** For almost every array of coefficient blocks, almost every
dictionary is good for it — the quantifier order print's question demands, with
the codes fixed before the dictionary and before the number of rows. -/
public theorem ae_ae_not_badBlock {n m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    ∀ᵐ cs : Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ),
      ∀ᵐ A : Fin n → Fin m → ℝ,
        ∀ t, ¬ BadBlock hkm (Matrix.of A) t (fun ℓ j => cs t (ℓ, j)) := by
  classical
  set S : Set ((Fin n → Fin m → ℝ) × (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ))) :=
    {x | ∃ t, BadBlock hkm (Matrix.of x.1) t (fun ℓ j => x.2 t (ℓ, j))} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_badPair hkm
  -- every dictionary's section is null: that is Lemma 6's measure half
  have hsection : ∀ A : Fin n → Fin m → ℝ, volume (Prod.mk A ⁻¹' S) = 0 := by
    intro A
    have hsub : Prod.mk A ⁻¹' S
        ⊆ ⋃ t : Fin m, (Function.eval t) ⁻¹'
            {c : Fin (m ^ 2 + 1) × Fin k → ℝ |
              ∃ (D : Fin (m ^ 2 + 1) → MinorChoice k m n) (C : Fin m × Fin m → ℝ),
                (∀ ℓ, ∃ j, choiceNormal hkm (Matrix.of A) t (D ℓ)
                    (Matrix.of fun p q => C (p, q)) j ≠ 0) ∧
                  ∀ ℓ, ∑ j, c (ℓ, j)
                    * choiceNormal hkm (Matrix.of A) t (D ℓ)
                        (Matrix.of fun p q => C (p, q)) j = 0} := by
      rintro cs ⟨t, hbad⟩
      exact Set.mem_iUnion.2 ⟨t, (badBlock_iff_flat hkm _ t _).1 hbad⟩
    refine measure_mono_null hsub (measure_iUnion_null fun t => ?_)
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ (volume_badBlock_eq_zero hk1 hkm (Matrix.of A) t)
  -- so the bad set is null in the product
  have hprod : (volume : Measure ((Fin n → Fin m → ℝ) ×
      (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ)))) S = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.measure_prod_null_of_ae_null hSmeas
      (Filter.Eventually.of_forall hsection)
  -- and Tonelli reads it in the other order
  have hswap : (volume : Measure ((Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ)) ×
      (Fin n → Fin m → ℝ))) (Prod.swap ⁻¹' S) = 0 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_swap,
      Measure.map_apply measurable_swap (measurable_swap hSmeas),
      show Prod.swap ⁻¹' (Prod.swap ⁻¹' S) = S from rfl, ← Measure.volume_eq_prod]
    exact hprod
  have hae := (Measure.measure_prod_null (measurable_swap hSmeas)).1
    (by rw [← Measure.volume_eq_prod]; exact hswap)
  filter_upwards [hae] with cs hcs
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hcs
  intro A hA
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hA
  exact hA

open MeasureTheory AISafetyAtlas.Conjectures.MAIS in
/-- Almost every dictionary has maximal rank — the other half of print's `Ωₙ`. -/
public theorem ae_finrank_span_col {n m : ℕ} :
    ∀ᵐ A : Fin n → Fin m → ℝ,
      Module.finrank ℝ (Submodule.span ℝ (Set.range (Matrix.of A).col)) = min n m := by
  classical
  obtain ⟨S, -, hScard⟩ : ∃ S : Finset (Fin m), S ⊆ Finset.univ ∧ S.card = min n m :=
    Finset.exists_subset_card_eq (by simp)
  filter_upwards [ae_linearIndependent_col S (by rw [hScard]; exact Nat.min_le_left n m)]
    with A hA
  refine le_antisymm (le_min ?_ ?_) ?_
  · exact le_trans (Submodule.finrank_le _) (by simp)
  · exact le_trans (finrank_range_le_card (Matrix.of A).col) (by simp)
  · have hsub : Submodule.span ℝ (Set.range fun j : S => (Matrix.of A).col (j : Fin m))
        ≤ Submodule.span ℝ (Set.range (Matrix.of A).col) :=
      Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨(j : Fin m), rfl⟩)
    calc min n m = Fintype.card S := by simp [hScard]
      _ = Module.finrank ℝ (Submodule.span ℝ
            (Set.range fun j : S => (Matrix.of A).col (j : Fin m))) :=
        (finrank_span_eq_card hA).symm
      _ ≤ _ := Submodule.finrank_mono hsub

open AISafetyAtlas.Conjectures.MAIS in
/-- The design's window codes, read off. -/
public theorem o38Design_inl {m k : ℕ} [NeZero m]
    (c : Fin m → Fin (m ^ 2 + 1) → (Fin k → ℝ)) (t : Fin m) (ℓ : Fin (m ^ 2 + 1)) :
    o38Design k c (designEquiv m (.inl (t, ℓ))) = windowPlace t (c t ℓ) := by
  rw [o38Design]
  simp

/-! ## What is left

Everything above is Steps 1, 3 and 4 of the note's Theorem 3, and none of it
depends on how the forcing lemma is proved. The reduction below makes the
remaining gap a single statement: a design of `m³ + 2m` `k`-sparse codes for
which, at every `n ≥ 2k` and almost every spark-condition dictionary, every rival
admitting the data satisfies `ForcingData`. That is exactly the note's Lemma 6
(the dimension count) together with its Lemma 8 (the Tonelli argument fixing the
codes before the dictionary), and nothing else. -/

open AISafetyAtlas.Conjectures.MAIS in
/-- **The candidate follows from a design whose rivals are forced.**

Chained through `o38PolynomialSampleCandidate_holds`, this says: supply the
design and the forcing lemma, and CONJ-025 is resolved affirmatively at every
non-degenerate `m`. The
hypothesis is stated at the note's own quantifier order — codes first, then every
`n`, then almost every `A` — so discharging it is discharging Lemmas 6 and 8. -/
public theorem o38PolynomialSampleCandidate_of_forcing
    (h : ∀ m k : ℕ, (hm : 2 ≤ m) → 1 ≤ k → k < m →
      ∃ x : Fin (m ^ 3 + 2 * m) → (Fin m → ℝ),
        (∀ i, IsKSparse k (x i)) ∧
          ∀ n : ℕ, 2 * k ≤ n →
            ∀ᵐ A : Fin n → Fin m → ℝ, SparkCondition k (Matrix.of A) →
              ∀ (B : Matrix (Fin n) (Fin m) ℝ) (x' : Fin (m ^ 3 + 2 * m) → (Fin m → ℝ)),
                (∀ i, IsKSparse k (x' i)) →
                (∀ i, B.mulVec (x' i) = (Matrix.of A).mulVec (x i)) →
                  haveI : NeZero m := ⟨by omega⟩
                  ForcingData k (Matrix.of A) B) :
    o38PolynomialSampleCandidate := by
  intro m k hm hk1 hkm
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨x, hx, hae⟩ := h m k hm hk1 hkm
  refine ⟨x, hx, fun n hn => ?_⟩
  filter_upwards [hae n hn] with A hforce hspark
  exact uniquelyCoded_of_forcing hk1 hkm hspark hx (hforce hspark)

/-! ## Theorem 3 -/

open MeasureTheory AISafetyAtlas.Analysis AISafetyAtlas.Conjectures.MAIS in
/-- **MAIS issue #30's Theorem 3, proved.**

`m³ + 2m` codes, depending only on `m` and `k`, whose dataset is uniquely coded
at almost every dictionary satisfying the spark condition, for every `n ≥ 2k`. -/
public theorem o38PolynomialSampleCandidate_holds : o38PolynomialSampleCandidate := by
  classical
  refine o38PolynomialSampleCandidate_of_forcing ?_
  intro m k hm hk1 hkm
  haveI : NeZero m := ⟨by omega⟩
  -- Lemma 8: one coefficient array serves every `n` and almost every dictionary
  obtain ⟨cs, hcs⟩ : ∃ cs : Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ), ∀ n : ℕ,
      ∀ᵐ A : Fin n → Fin m → ℝ,
        ∀ t, ¬ BadBlock hkm.le (Matrix.of A) t (fun ℓ j => cs t (ℓ, j)) := by
    haveI : (MeasureTheory.ae
        (volume : Measure (Fin m → (Fin (m ^ 2 + 1) × Fin k → ℝ)))).NeBot :=
      MeasureTheory.ae_neBot.2 (volume_ne_zero_pi_pi _ _)
    exact (MeasureTheory.ae_all_iff.2
      fun n => ae_ae_not_badBlock (n := n) hk1 hkm.le).exists
  refine ⟨o38Design k (fun t ℓ j => cs t (ℓ, j)),
    isKSparse_o38Design hk1 hkm.le _, fun n hn => ?_⟩
  filter_upwards [hcs n, ae_sparkCondition (k := k) (n := n) (m := m) hn,
    ae_finrank_span_col (n := n) (m := m)] with A hgood _ hrank
  intro _ B x' hsparse heq t
  -- Step 1: the anchors put the rival inside `im A`
  have hBcol : ∀ j, B.col j ∈ Submodule.span ℝ (Set.range (Matrix.of A).col) :=
    col_mem_span_of_anchors hrank
      (fun j => col_mem_span_of_exists_mulVec (exists_mulVec_of_design heq) j)
  -- the data of each window block lies in a `≤ k`-column span of the rival
  have hy : ∀ ℓ : Fin (m ^ 2 + 1), ∃ T : Finset (Fin m), T.card ≤ k ∧
      (Matrix.of A).mulVec (windowPlace t (fun j => cs t (ℓ, j)))
        ∈ Submodule.span ℝ (Set.range fun j : T => B.col (j : Fin m)) := by
    intro ℓ
    set i : Fin (m ^ 3 + 2 * m) := designEquiv m (.inl (t, ℓ)) with hi
    refine ⟨(Function.support (x' i)).toFinset, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card']
      exact hsparse i
    · rw [← o38Design_inl (fun t ℓ j => cs t (ℓ, j)) t ℓ, ← hi, ← heq i]
      exact (mem_span_col_iff B _ _).2 ⟨x' i, fun j hj => by simpa using hj, rfl⟩
  -- Lemma 6
  obtain ⟨T, hTcard, hle⟩ :=
    exists_subset_windowSpan_le_of_not_badBlock hkm.le t (hgood t) hBcol hy
  obtain ⟨hTk, hmem, hind⟩ := forcing_of_windowSpan_le hkm.le ‹_› t hTcard hle
  exact ⟨T, hTk, hmem, hind⟩

open AISafetyAtlas.Conjectures.MAIS in
/--
**MAIS-O38 is true**, at print's own hypotheses and at every `m` where the printed
sentence has content.

The candidate submitted as MAIS issue #30 already supplies the pointwise
conclusion, and this proof does not discard it: no `filter_upwards`, no threshold.
The polynomial witness is `X³ + 2X`, which dominates `N = m³ + 2m` at every `m`
with equality, so the candidate's bound is exactly a polynomial bound in print's
sense.

The two guards are discharged from each other: `1 ≤ k m` and `k m < m` give
`2 ≤ m`, which is the candidate's own lower bound on the dimension.

`hk : Filter.Tendsto k Filter.atTop Filter.atTop` is print's and is **not used**.
See `maisO38_polynomialSamplesSuffice` for why it is nonetheless part of the
statement. -/
public theorem maisO38_polynomialSamplesSuffice_holds :
    maisO38_polynomialSamplesSuffice := by
  intro k n _ hn
  refine ⟨fun m => m ^ 3 + 2 * m, Polynomial.X ^ 3 + 2 * Polynomial.X, fun m => by simp, ?_⟩
  intro m hone hlt
  obtain ⟨x, hsparse, hae⟩ :=
    o38PolynomialSampleCandidate_holds m (k m) (by omega) hone hlt
  exact ⟨x, hsparse, hae (n m) (hn m)⟩

end AISafetyAtlas.Examples.Conjectures.MAIS
