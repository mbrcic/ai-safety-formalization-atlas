module

public import AISafetyAtlas.Compositional.Hyperproperties
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Finset.Sort

/-!
# Synchronized self-composition, and its relation to the batch form

Clarkson and Schneider state Theorem 2 for the `k`-fold *synchronized product*
`S^k`, whose members are ordered `k`-tuples of traces.  The reduction in
`AISafetyAtlas.Compositional.Hyperproperties` instead uses unordered batches of
at most `k` traces.  This module supplies the product presentation, the
translations between the two, and the boundary conditions the translation needs.

## Where the translation is total, and where it is not

`toBatch` sends a tuple to the finite set of traces it mentions.  It is total
and always lands in the batch self-composition.

Going back requires padding, and padding is where the assumptions live.

* **Nonempty batch.**  Enumerate it and pad by repeating one of its own
  members, so `toBatch` recovers it exactly (`toBatch_padBatch`).
* **Empty batch with `k > 0`.**  There is no preimage at all.  A total function
  into a nonempty index type mentions at least one trace, so `toBatch` is never
  `∅`.  `productSelfComposition_empty` and `finiteSelfComposition_empty` record
  the resulting asymmetry over an empty system.

Consequently the transfer theorem below is **not** stated for an arbitrary
predicate on batches; for such a predicate the two quantifications genuinely
differ at the empty batch.  It is stated for `SelfCompositionSafe`, where
`selfCompositionSafe_empty_of_any` shows the empty batch is subsumed by any
other: an observation realized by the empty batch must itself be empty, and an
empty observation is realized by every batch.

## Coalescing and order

`toBatch` discards multiplicity and order.  Both are harmless for the reduction,
because the source's witnesses are *sets* of at most `k` prefixes and `Realizes`
quantifies over membership only.  `card_toBatch_le` and `toBatch_perm` record
the two facts.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties

variable {Prefix Trace : Type*}

/-- The synchronized `k`-fold self-composition: ordered `k`-tuples of traces
drawn from the system.  This is the source's `S^k`. -/
@[expose] public def productSelfComposition (k : ℕ) (S : TraceSystem Trace) :
    Set (Fin k → Trace) :=
  {tup | ∀ i, tup i ∈ S}

open scoped Classical in
/-- The finite set of traces a tuple mentions. -/
@[expose] public noncomputable def toBatch {k : ℕ} (tup : Fin k → Trace) :
    Finset Trace :=
  Finset.image tup Finset.univ

/-- Membership in the batch of a tuple is exactly being one of its entries. -/
public theorem mem_toBatch {k : ℕ} (tup : Fin k → Trace) (t : Trace) :
    t ∈ toBatch tup ↔ ∃ i, tup i = t := by
  classical
  simp [toBatch]

/-- A tuple mentions at most `k` distinct traces; duplicates are coalesced. -/
public theorem card_toBatch_le {k : ℕ} (tup : Fin k → Trace) :
    (toBatch tup).card ≤ k := by
  classical
  calc (toBatch tup).card ≤ (Finset.univ : Finset (Fin k)).card :=
        Finset.card_image_le
    _ = k := by simp

/-- Reordering a tuple does not change the traces it mentions. -/
public theorem toBatch_perm {k : ℕ} (tup : Fin k → Trace) (σ : Equiv.Perm (Fin k)) :
    toBatch (tup ∘ σ) = toBatch tup := by
  classical
  ext t
  simp only [mem_toBatch, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨σ.symm i, by simpa using hi⟩

/-- The batch of a product tuple lies in the batch self-composition. -/
public theorem toBatch_mem_finiteSelfComposition {k : ℕ} {S : TraceSystem Trace}
    {tup : Fin k → Trace} (h : tup ∈ productSelfComposition k S) :
    toBatch tup ∈ FiniteSelfComposition k S := by
  classical
  refine ⟨?_, card_toBatch_le tup⟩
  intro t ht
  obtain ⟨i, rfl⟩ := (mem_toBatch tup t).mp ht
  exact h i

/-! ### Padding -/

/--
Pad a batch to a tuple by enumerating it and repeating a designated member.

The designated member is what forces the nonemptiness side condition.
-/
@[expose] public noncomputable def padBatch {k : ℕ} (batch : Finset Trace)
    (d : Trace) : Fin k → Trace :=
  fun i => batch.toList.getD i d

/-- Every entry of a padded tuple belongs to the batch. -/
public theorem padBatch_mem {k : ℕ} {batch : Finset Trace} {d : Trace}
    (hd : d ∈ batch) (i : Fin k) : padBatch (k := k) batch d i ∈ batch := by
  unfold padBatch
  by_cases hi : (i : ℕ) < batch.toList.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact Finset.mem_toList.mp (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hd

/-- Padding recovers the batch exactly, provided the designated member is drawn
from the batch itself and the batch fits inside `k`. -/
public theorem toBatch_padBatch {k : ℕ} {batch : Finset Trace} {d : Trace}
    (hd : d ∈ batch) (hcard : batch.card ≤ k) :
    toBatch (padBatch (k := k) batch d) = batch := by
  classical
  ext t
  rw [mem_toBatch]
  constructor
  · rintro ⟨i, rfl⟩
    exact padBatch_mem hd i
  · intro ht
    have htl : t ∈ batch.toList := Finset.mem_toList.mpr ht
    obtain ⟨j, hj, hjt⟩ := List.mem_iff_getElem.mp htl
    have hlen : batch.toList.length = batch.card := Finset.length_toList batch
    have hjk : j < k := by omega
    refine ⟨⟨j, hjk⟩, ?_⟩
    unfold padBatch
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    exact hjt

/-- The padded tuple stays inside the product self-composition. -/
public theorem padBatch_mem_productSelfComposition {k : ℕ} {S : TraceSystem Trace}
    {batch : Finset Trace} {d : Trace} (hd : d ∈ batch)
    (hsub : (batch : Set Trace) ⊆ S) :
    padBatch (k := k) batch d ∈ productSelfComposition k S :=
  fun i => hsub (padBatch_mem hd i)

/-! ### The boundary at the empty batch -/

/-- With `k > 0` there is no product tuple over an empty system. -/
public theorem productSelfComposition_empty {k : ℕ} (hk : 0 < k) :
    productSelfComposition k (∅ : TraceSystem Trace) = ∅ := by
  ext tup
  simp only [productSelfComposition, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_forall]
  exact ⟨⟨0, hk⟩, by simp⟩

/-- The batch self-composition over an empty system still contains the empty
batch, at every `k`.  This is the asymmetry padding cannot repair. -/
public theorem finiteSelfComposition_empty {k : ℕ} :
    (∅ : Finset Trace) ∈ FiniteSelfComposition k (∅ : TraceSystem Trace) :=
  ⟨by simp, by simp⟩

/--
An observation realized by the empty batch is itself empty.

This is why the empty batch imposes the weakest safety condition of all.
-/
public theorem eq_empty_of_realizes_empty (prefixOf : Prefix → Trace → Prop)
    {M : Observation Prefix}
    (h : Realizes prefixOf M ((∅ : Finset Trace) : Set Trace)) : M = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨t, ht, _⟩ := h p hp
  simp at ht

/--
Safety of *any* batch implies safety of the empty batch.

An observation realized by `∅` must be empty, and the empty observation is
realized by every batch, so a bad empty observation would already refute the
given batch.
-/
public theorem selfCompositionSafe_empty_of_any (prefixOf : Prefix → Trace → Prop)
    (k : ℕ) (H : Hyperproperty Trace) {batch : Finset Trace}
    (h : SelfCompositionSafe prefixOf k H batch) :
    SelfCompositionSafe prefixOf k H (∅ : Finset Trace) := by
  rintro ⟨M, hcard, hreal, hbad⟩
  have hM : M = ∅ := eq_empty_of_realizes_empty prefixOf hreal
  subst hM
  exact h ⟨∅, by simp, by simp [Realizes], hbad⟩

/-! ### Transfer between the two presentations -/

/--
For the induced safety predicate, quantifying over the batch self-composition
and over the synchronized product agree.

The nonemptiness hypothesis supplies a padding element.  It cannot be dropped:
`productSelfComposition_empty` and `finiteSelfComposition_empty` show the two
index sets differ over an empty system when `k > 0`.  Note also that this is
stated for `SelfCompositionSafe` rather than for an arbitrary predicate, since
an arbitrary predicate can distinguish the empty batch, which has no product
preimage.
-/
public theorem forall_batch_iff_forall_product (prefixOf : Prefix → Trace → Prop)
    {k : ℕ} {S : TraceSystem Trace} (H : Hyperproperty Trace) (hS : S.Nonempty) :
    (∀ batch ∈ FiniteSelfComposition k S, SelfCompositionSafe prefixOf k H batch) ↔
      (∀ tup ∈ productSelfComposition k S,
        SelfCompositionSafe prefixOf k H (toBatch tup)) := by
  classical
  constructor
  · intro h tup htup
    exact h _ (toBatch_mem_finiteSelfComposition htup)
  · intro h batch hbatch
    obtain ⟨hsub, hcard⟩ := hbatch
    rcases Finset.eq_empty_or_nonempty batch with rfl | ⟨d, hd⟩
    · obtain ⟨s, hs⟩ := hS
      exact selfCompositionSafe_empty_of_any prefixOf k H
        (h (fun _ => s) (fun _ => hs))
    · have hpad := h _ (padBatch_mem_productSelfComposition (k := k) hd hsub)
      rwa [toBatch_padBatch hd hcard] at hpad

/--
**Clarkson-Schneider Theorem 2, synchronized-product form.**

For a `k`-safety hyperproperty and a nonempty system, satisfaction is equivalent
to the induced ordinary safety predicate holding on every member of the
synchronized `k`-fold self-composition.
-/
public theorem k_safety_iff_product_self_composition
    (prefixOf : Prefix → Trace → Prop) (k : ℕ) (H : Hyperproperty Trace)
    (hk : IsKSafety prefixOf k H) {S : TraceSystem Trace} (hS : S.Nonempty) :
    S ∈ H ↔
      ∀ tup ∈ productSelfComposition k S,
        SelfCompositionSafe prefixOf k H (toBatch tup) :=
  (k_safety_iff_finite_self_composition prefixOf k H hk S).trans
    (forall_batch_iff_forall_product prefixOf H hS)

end AISafetyAtlas.Compositional.Hyperproperties
