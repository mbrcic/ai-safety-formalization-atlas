module

public import Mathlib.Data.Finset.Image
public import Mathlib.Topology.Closure

/-!
# Hyperproperties, finite witnesses, and self-composition

The definitions follow Clarkson and Schneider, *Hyperproperties* (JCS 2010):
a hyperproperty is a set of systems (sets of traces), and a `k`-safety
violation has a bad finite observation of at most `k` trace prefixes.

`k_safety_iff_finite_self_composition` is a set-based presentation of their
Theorem 2.  A member of the self-composition is an unordered batch of at most
`k` traces; this avoids artificial padding and duplicate coordinates while
retaining exactly the finite witnesses used by the proof.

The final decomposition theorem reproduces the generic topological theorem used
by Abate et al., *Journey Beyond Full Abstraction* (CSF 2019), in their Rocq
development.  The specialization to hypersafety/hyperliveness depends on the
chosen topology and is therefore not silently asserted here.

`AISafetyAtlas.Compositional.Hyperproperties.PrefixTopology` supplies the
observation topology that earns the operational reading: there `IsClosed` is
proved equivalent to Clarkson-Schneider hypersafety, `Dense` to hyperliveness,
and `IsKSafety` is shown to imply hypersafety, which connects the reduction
below to the decomposition.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties

/-- A system is a set of complete traces. -/
public abbrev TraceSystem (Trace : Type*) := Set Trace

/-- A hyperproperty is a set of systems. -/
public abbrev Hyperproperty (Trace : Type*) := Set (TraceSystem Trace)

/-- A finite observation is a finite set of finite trace prefixes. -/
public abbrev Observation (Prefix : Type*) := Finset Prefix

/-- A system realizes an observation when every observed prefix extends to
some complete trace in the system. -/
@[expose] public def Realizes {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (M : Observation Prefix) (S : TraceSystem Trace) : Prop :=
  ∀ p ∈ M, ∃ t ∈ S, prefixOf p t

/-- `M` is a bad observation for `H`: every system realizing it violates `H`. -/
@[expose] public def IsBadObservation {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (H : Hyperproperty Trace) (M : Observation Prefix) : Prop :=
  ∀ S, Realizes prefixOf M S → S ∉ H

/--
A `k`-safety hyperproperty.  Every violating system exhibits a bad observation
containing at most `k` finite prefixes.
-/
@[expose] public def IsKSafety {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (k : ℕ) (H : Hyperproperty Trace) : Prop :=
  ∀ S, S ∉ H → ∃ M : Observation Prefix,
    M.card ≤ k ∧ Realizes prefixOf M S ∧ IsBadObservation prefixOf H M

/-- Unordered finite `k`-fold self-composition: batches of at most `k` traces
drawn from `S`. -/
@[expose] public def FiniteSelfComposition {Trace : Type*}
    (k : ℕ) (S : TraceSystem Trace) : Set (Finset Trace) :=
  {batch | (batch : Set Trace) ⊆ S ∧ batch.card ≤ k}

/-- The safety predicate produced by the reduction: a trace batch contains no
bad observation of size at most `k`. -/
@[expose] public def SelfCompositionSafe {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (k : ℕ) (H : Hyperproperty Trace) (batch : Finset Trace) : Prop :=
  ¬ ∃ M : Observation Prefix,
    M.card ≤ k ∧
    Realizes prefixOf M (batch : Set Trace) ∧
    IsBadObservation prefixOf H M

/-- Ordinary finite-observation safety for a predicate on trace batches. -/
@[expose] public def IsSafetyPredicate {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (P : Finset Trace → Prop) : Prop :=
  ∀ batch, ¬ P batch → ∃ M : Observation Prefix,
    Realizes prefixOf M (batch : Set Trace) ∧
    ∀ batch' : Finset Trace,
      Realizes prefixOf M (batch' : Set Trace) → ¬ P batch'

/-- The predicate constructed by the reduction is an ordinary safety
predicate: its violation is preserved by every batch realizing the same finite
bad observation. -/
public theorem self_composition_is_safety
    {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (k : ℕ) (H : Hyperproperty Trace) :
    IsSafetyPredicate prefixOf (SelfCompositionSafe prefixOf k H) := by
  classical
  intro batch hbatch
  have hexists :
      ∃ M : Observation Prefix,
        M.card ≤ k ∧
        Realizes prefixOf M (batch : Set Trace) ∧
        IsBadObservation prefixOf H M := by
    by_contra h
    exact hbatch h
  obtain ⟨M, hMk, hreal, hbad⟩ := hexists
  refine ⟨M, hreal, ?_⟩
  intro batch' hreal'
  exact fun hsafety => hsafety ⟨M, hMk, hreal', hbad⟩

/--
**Clarkson–Schneider `k`-safety reduction (finite-set representation).**

For a `k`-safety hyperproperty, a system satisfies `H` exactly when every batch
in its finite `k`-self-composition satisfies the induced ordinary safety
predicate.
-/
public theorem k_safety_iff_finite_self_composition
    {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (k : ℕ) (H : Hyperproperty Trace)
    (hk : IsKSafety prefixOf k H)
    (S : TraceSystem Trace) :
    S ∈ H ↔
      ∀ batch ∈ FiniteSelfComposition k S,
        SelfCompositionSafe prefixOf k H batch := by
  classical
  constructor
  · intro hS batch hbatch
    rintro ⟨M, hMk, hreal, hbad⟩
    apply hbad S
    intro p hp
    obtain ⟨t, ht, hpt⟩ := hreal p hp
    exact ⟨t, hbatch.1 ht, hpt⟩
    exact hS
  · intro hall
    by_contra hS
    obtain ⟨M, hMk, hreal, hbad⟩ := hk S hS
    let pick : {p // p ∈ M} → Trace :=
      fun p => Classical.choose (hreal p p.property)
    let batch : Finset Trace := M.attach.image pick
    have pick_mem (p : {p // p ∈ M}) : pick p ∈ S :=
      (Classical.choose_spec (hreal p p.property)).1
    have pick_extends (p : {p // p ∈ M}) : prefixOf p (pick p) :=
      (Classical.choose_spec (hreal p p.property)).2
    have hbatchS : (batch : Set Trace) ⊆ S := by
      intro t ht
      change t ∈ batch at ht
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
      exact pick_mem p
    have hbatchCard : batch.card ≤ k := by
      calc
        batch.card ≤ M.attach.card := by
          exact Finset.card_image_le
        _ = M.card := Finset.card_attach
        _ ≤ k := hMk
    have hrealBatch : Realizes prefixOf M (batch : Set Trace) := by
      intro p hp
      let q : {p // p ∈ M} := ⟨p, hp⟩
      refine ⟨pick q, ?_, pick_extends q⟩
      change pick q ∈ batch
      exact Finset.mem_image.mpr ⟨q, Finset.mem_attach M q, rfl⟩
    exact (hall batch ⟨hbatchS, hbatchCard⟩)
      ⟨M, hMk, hrealBatch, hbad⟩

/--
Every subset of a topological space is the intersection of a closed set and a
dense set.

This is the classical decomposition used by the reproduced Rocq development:
take `C = closure S` and `D = S ∪ Cᶜ`.
-/
public theorem topological_decomposition
    {X : Type*} [TopologicalSpace X] (S : Set X) :
    ∃ C D : Set X, IsClosed C ∧ Dense D ∧ S = C ∩ D := by
  let C := closure S
  let D := S ∪ Cᶜ
  refine ⟨C, D, isClosed_closure, ?_, ?_⟩
  · rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ C
    · exact closure_mono Set.subset_union_left hx
    · exact subset_closure (Set.mem_union_right S hx)
  · apply Set.Subset.antisymm
    · intro x hx
      exact ⟨subset_closure hx, Set.mem_union_left Cᶜ hx⟩
    · rintro x ⟨_, hxS | hxC⟩
      · exact hxS
      · exact False.elim (hxC ‹x ∈ C›)

/--
Hyperproperty specialization of `topological_decomposition`.  A topology on
systems must be supplied explicitly; no topology, and hence no interpretation
as hypersafety/hyperliveness, is smuggled into the statement.
-/
public theorem hyperproperty_decomposition
    {Trace : Type*} [TopologicalSpace (TraceSystem Trace)]
    (H : Hyperproperty Trace) :
    ∃ closedPart densePart : Hyperproperty Trace,
      IsClosed closedPart ∧ Dense densePart ∧
      H = closedPart ∩ densePart :=
  topological_decomposition H

/-- Topological hypersafety predicate for an explicitly supplied topology. -/
public abbrev IsHyperSafety {Trace : Type*}
    [TopologicalSpace (TraceSystem Trace)]
    (H : Hyperproperty Trace) : Prop :=
  IsClosed H

/-- Topological hyperliveness predicate for an explicitly supplied topology. -/
public abbrev IsHyperLiveness {Trace : Type*}
    [TopologicalSpace (TraceSystem Trace)]
    (H : Hyperproperty Trace) : Prop :=
  Dense H

/--
Every hyperproperty is the intersection of a hypersafety part and a
hyperliveness part, relative to the supplied system topology.
-/
public theorem hypersafety_hyperliveness_decomposition
    {Trace : Type*} [TopologicalSpace (TraceSystem Trace)]
    (H : Hyperproperty Trace) :
    ∃ safetyPart livenessPart : Hyperproperty Trace,
      IsHyperSafety safetyPart ∧ IsHyperLiveness livenessPart ∧
      H = safetyPart ∩ livenessPart :=
  hyperproperty_decomposition H

end AISafetyAtlas.Compositional.Hyperproperties
