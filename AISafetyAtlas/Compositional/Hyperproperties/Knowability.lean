module

public import AISafetyAtlas.Compositional.Hyperproperties
public import AISafetyAtlas.Knowledge

/-!
# Finite-observation safety, in the shared knowability vocabulary

## Statement intent

- **Objects.** A trace batch as the world, the set of finite observations the
  batch realizes as the observation, and the safety predicate as the hidden
  property.
- **Conclusion.** `knowable_of_isSafetyPredicate`: an ordinary finite-observation
  safety predicate factors through the batch's realized observations. So the
  predicate is `Knowledge.Knowable` from that observation, and the kernel's laws
  apply to it.
- **Mechanism.** `IsSafetyPredicate` gives, for each violating batch, one finite
  observation whose every realizer also violates. Two batches realizing exactly
  the same observations therefore agree, which is the no-collision condition
  `Knowledge.knowable_iff_no_collision` asks for.

## Why this direction

`Hyperproperties` already states its own safety notions and proves the
Clarkson–Schneider reduction over them. What it did not have was any edge to the
rest of the tree: nothing in this cluster referred to `AISafetyAtlas.Knowledge`,
and nothing outside `Compositional` referred to these definitions. The adapter
lives here rather than in `Knowledge`, so the dependency runs downstream only and
the kernel stays free of trace vocabulary.

## Explicit non-claims

- **Not new mathematics.** `IsSafetyPredicate` is unchanged and its consequences
  are unchanged; `knowable_of_isSafetyPredicate` derives nothing the definition
  did not already say. What is new is that it is said in the vocabulary
  `Knowledge` shares with `Oversight`, `Preference` and `Wireheading`.
- **Not a converse.** Knowability from `realizedSet` does **not** give back
  `IsSafetyPredicate`. Factorization says the predicate is constant on batches
  with equal realized-observation sets; safety says more, that each violation is
  witnessed by a *single finite* observation all of whose realizers violate.
  Finiteness and the per-violation witness are lost on the way in, and no attempt
  is made to recover them.
- **Not a trace producer.** This connects the *consumer* side of the trace theory
  to the kernel, and nothing here produces a trace. The producer is
  `AISafetyAtlas.Compositional.NetworkTraces`, which reads one of the four
  execution-generating modules as a `TraceSystem`; the other three —
  `Compositional.Symmetry`, `Wireheading.CRMDP` and
  `Wireheading.GoalPreservation` — still have no trace consumer.
- **Not** a claim about `IsKSafety`, `IsHyperSafety` or `IsHyperLiveness`. Only
  the ordinary batch-predicate notion is routed.

## Scope boundary

The property lands in `Prop`, so `knowable_iff_no_collision`'s `[Nonempty Y]` is
discharged by `Prop` being inhabited, and the collision step closes with
`propext`. Nothing here needs `prefixOf` to be decidable, or `Prefix` and `Trace`
to be finite.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties

universe u v

variable {Prefix : Type u} {Trace : Type v}

/--
The finite observations a batch realizes.

This is the observation map: everything a finite-observation safety argument may
read about a batch, and nothing else. Two batches with the same realized set are
indistinguishable to every such argument.
-/
@[expose] public def realizedSet (prefixOf : Prefix → Trace → Prop)
    (batch : Finset Trace) : Set (Observation Prefix) :=
  {M | Realizes prefixOf M (batch : Set Trace)}

/--
**Finite-observation safety is a factorization.**

An ordinary safety predicate on trace batches is recoverable from the set of
finite observations the batch realizes.

`IsSafetyPredicate` supplies, for each violating batch, one observation whose
realizers all violate. Two batches realizing the same observations therefore
cannot differ: a violation of one transfers along the shared observation to the
other. That is exactly `knowable_iff_no_collision` at `Y := Prop`.
-/
public theorem knowable_of_isSafetyPredicate
    (prefixOf : Prefix → Trace → Prop) (P : Finset Trace → Prop)
    (hP : IsSafetyPredicate prefixOf P) :
    Knowledge.Knowable (realizedSet prefixOf) P := by
  refine (Knowledge.knowable_iff_no_collision _ _).mpr ?_
  intro b₁ b₂ hobs
  have key : ∀ c₁ c₂ : Finset Trace,
      realizedSet prefixOf c₁ = realizedSet prefixOf c₂ → ¬ P c₁ → ¬ P c₂ := by
    intro c₁ c₂ h hnc
    obtain ⟨M, hreal, hall⟩ := hP c₁ hnc
    have hmem : M ∈ realizedSet prefixOf c₁ := hreal
    exact hall c₂ ((Set.ext_iff.mp h M).mp hmem)
  exact propext
    ⟨fun h => by by_contra hn; exact key b₂ b₁ hobs.symm hn h,
     fun h => by by_contra hn; exact key b₁ b₂ hobs hn h⟩

/--
The contrapositive, in the kernel's certificate form: two batches realizing the
same finite observations but disagreeing on `P` refute safety of `P`.

Stated because it is the shape a consumer holding a counterexample has, and it
needs no safety hypothesis to be useful — it refutes `Knowable`, from which
`knowable_of_isSafetyPredicate` refutes `IsSafetyPredicate`.
-/
public theorem not_knowable_of_realizedSet_collision
    {prefixOf : Prefix → Trace → Prop} {P : Finset Trace → Prop}
    {b₁ b₂ : Finset Trace}
    (hobs : realizedSet prefixOf b₁ = realizedSet prefixOf b₂)
    (hP : P b₁ ≠ P b₂) :
    ¬ Knowledge.Knowable (realizedSet prefixOf) P :=
  Knowledge.not_knowable_of_collision hobs hP

/-- Consequently such a pair refutes the safety of `P` outright. -/
public theorem not_isSafetyPredicate_of_realizedSet_collision
    {prefixOf : Prefix → Trace → Prop} {P : Finset Trace → Prop}
    {b₁ b₂ : Finset Trace}
    (hobs : realizedSet prefixOf b₁ = realizedSet prefixOf b₂)
    (hP : P b₁ ≠ P b₂) :
    ¬ IsSafetyPredicate prefixOf P :=
  fun hs => not_knowable_of_realizedSet_collision hobs hP
    (knowable_of_isSafetyPredicate prefixOf P hs)

end AISafetyAtlas.Compositional.Hyperproperties
