module

public import Mathlib.Logic.Function.Basic

/-!
# Exact knowability — the observation-factorization kernel

Nothing here is *embedded*: `observation` is an arbitrary map, and no result
below makes it a projection of a state containing the observer. Embedding starts
in `AISafetyAtlas.Knowledge.Embedded`; the self-referential case, where the
observer's model is a component of the state, is `Knowledge.SelfReference`. Any
title for this module carrying "embedded" or "self-knowledge" would contradict
its own non-claims section below.

`AISafetyAtlas.SelfAwareness` shares the registry group *limits of self-knowledge
and reflection* with the modules above and shares no machinery with them: its
obstruction is a cost law over a semilattice of composites, not a decoder against
observation fibres. Neither module imports the other, and neither should be moved
under the other on thematic grounds.

When can a property of a system be recovered from what an observer is able to
read? `Knowable` answers with a **decoder**: one rule on observations, uniform in
the state, that reproduces the property everywhere. The characterization against
observation fibres is then a theorem, not the definition.

## The definitional commitment

`Knowable observation property` is *deliberately not* defined as "no collision
exists", and not as `Function.FactorsThrough`. Defining it either way would
collapse `knowable_iff_no_collision` — the statement this file exists to prove —
into definitional unfolding, and would leave the artifact with no statement
connecting an observation's *informational content* to a *usable decoder*. The
same commitment is made, for the same reason, by
`AISafetyAtlas.Oversight.JointObservation.Covers`.

Quantifier order is part of that commitment: one decoder, uniform in the state.
Swapping the quantifiers gives a vacuous per-state statement.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `Knowable` | A decoder on observations reproduces the property everywhere |
| **Model** | `IndistinguishabilityWitness` | Two states the observation cannot separate, with different property values |
| **Model** | `Determines` | One observation is at least as informative as another |
| **Law** | `knowable_iff_factorsThrough` | Bridge to Mathlib's `Function.FactorsThrough` |
| **Law** | `knowable_iff_no_collision` | Knowability ⟺ the property is constant on observation fibres |
| **Law** | `not_knowable_of_collision` | A colliding pair refutes knowability |
| **Law** | `exists_witness_of_not_knowable` | Failure yields a concrete colliding pair |
| **Boundary** | `Knowable.mono` | Knowability transfers to any more informative observation |
| **Boundary** | `not_knowable_comp` | Post-processing an unchanged observation cannot create knowability |
| **Whole state** | `knowable_id_iff_injective` | Knowing the entire state ⟺ the observation is injective |
| **Whole state** | `not_knowable_state_of_nontrivial_remainder` | A `Read × Rest` state with two remainder values is not recoverable from `Prod.fst` |
| **Whole state** | `remainderWitness` | The same obstruction as an inspectable certificate |

## Constructivity

`not_knowable_of_collision`, `not_knowable_of_witness`, `Knowable.mono` and
`not_knowable_comp` depend on **no axioms at all** (`#print axioms`): each
transports a decoder or a colliding pair directly.

`knowable_iff_factorsThrough`, `knowable_iff_no_collision` and
`exists_witness_of_not_knowable` are classical. The first two assemble a decoder
fibrewise through Mathlib's `Function.extend`, which needs a junk value on
observations nothing realizes — hence the `[Nonempty Y]` hypothesis, discharged
automatically for `Bool`-valued properties. The third extracts a colliding pair
from a negated universal statement.

## Explicit non-claims

The factorization content is standard and is Mathlib's; what is packaged here is
the decoder-form statement, the witness interface, and monotonicity. Nothing here
asserts an AI-system interpretation, an embedded-observer model, a temporal
claim, or a consciousness claim. `observation` is an arbitrary map; no result
below makes it a projection of a state containing the observer.

No survey coverage row is claimed here; this is workbench infrastructure.
-/

namespace AISafetyAtlas.Knowledge

universe u v w x

/-! ## Knowability -/

/--
The property is **knowable** from the observation: one decoder on observations
reproduces it at every state.
-/
@[expose] public def Knowable {Ω : Sort u} {I : Sort v} {Y : Sort w}
    (observation : Ω → I) (property : Ω → Y) : Prop :=
  ∃ decoder : I → Y, ∀ ω, property ω = decoder (observation ω)

/--
An **indistinguishability witness**: two states the observation cannot separate,
yet on which the property differs. This is the negative certificate a consumer
inspects to see *which* pair the current observation fails to resolve.
-/
public structure IndistinguishabilityWitness {Ω : Sort u} {I : Sort v} {Y : Sort w}
    (observation : Ω → I) (property : Ω → Y) where
  /-- One side of the indistinguishable pair. -/
  left : Ω
  /-- The other side. -/
  right : Ω
  /-- The observation cannot tell them apart. -/
  sameObservation : observation left = observation right
  /-- Yet the property differs. -/
  propertyDiffers : property left ≠ property right

/-! ## The characterization -/

/--
Bridge to Mathlib: the decoder form agrees with `Function.FactorsThrough`.

This is where the fibrewise construction is discharged, once, by
`Function.factorsThrough_iff`.
-/
public theorem knowable_iff_factorsThrough {Ω : Sort u} {I : Sort v} {Y : Sort w}
    [Nonempty Y] (observation : Ω → I) (property : Ω → Y) :
    Knowable observation property ↔ Function.FactorsThrough property observation := by
  rw [Function.factorsThrough_iff property]
  constructor
  · rintro ⟨decoder, hdec⟩
    exact ⟨decoder, funext hdec⟩
  · rintro ⟨decoder, hdec⟩
    exact ⟨decoder, fun ω => congrFun hdec ω⟩

/--
**The characterization.** Knowability is equivalent to the property being
constant on the observation's fibres.

This is what licenses reading an indistinguishability witness as a genuine
informational obstruction rather than the failure of one particular decoder.
-/
public theorem knowable_iff_no_collision {Ω : Sort u} {I : Sort v} {Y : Sort w}
    [Nonempty Y] (observation : Ω → I) (property : Ω → Y) :
    Knowable observation property ↔
      ∀ ω τ, observation ω = observation τ → property ω = property τ := by
  rw [knowable_iff_factorsThrough observation property]
  exact ⟨fun h _ _ hobs => h hobs, fun h _ _ hobs => h _ _ hobs⟩

/-- A colliding pair refutes knowability. Constructive. -/
public theorem not_knowable_of_collision {Ω : Sort u} {I : Sort v} {Y : Sort w}
    {observation : Ω → I} {property : Ω → Y} {ω₁ ω₂ : Ω}
    (sameObservation : observation ω₁ = observation ω₂)
    (propertyDiffers : property ω₁ ≠ property ω₂) :
    ¬ Knowable observation property := by
  rintro ⟨decoder, hdec⟩
  exact propertyDiffers (by rw [hdec ω₁, hdec ω₂, sameObservation])

/-- A witness refutes knowability. Constructive. -/
public theorem not_knowable_of_witness {Ω : Sort u} {I : Sort v} {Y : Sort w}
    {observation : Ω → I} {property : Ω → Y}
    (w : IndistinguishabilityWitness observation property) :
    ¬ Knowable observation property :=
  not_knowable_of_collision w.sameObservation w.propertyDiffers

/--
Conversely, failure of knowability yields a concrete colliding pair. Stated
existentially: extracting it from a negated universal statement is classical.
-/
public theorem exists_witness_of_not_knowable {Ω : Sort u} {I : Sort v} {Y : Sort w}
    [Nonempty Y] {observation : Ω → I} {property : Ω → Y}
    (h : ¬ Knowable observation property) :
    Nonempty (IndistinguishabilityWitness observation property) := by
  classical
  by_contra hempty
  refine h ((knowable_iff_no_collision observation property).mpr ?_)
  intro ω τ hobs
  by_contra hne
  exact hempty ⟨{ left := ω, right := τ,
                  sameObservation := hobs, propertyDiffers := hne }⟩

/-! ## Informativeness -/

/--
`Determines finer coarser` — the `finer` observation is **at least as
informative**: what `coarser` reveals is recoverable from it.

Direction is part of the freeze: the more informative observation is the *first*
argument, and it is the one that determines the other.
-/
@[expose] public def Determines {Ω : Sort u} {I : Sort v} {J : Sort x}
    (finer : Ω → J) (coarser : Ω → I) : Prop :=
  ∃ k : J → I, ∀ ω, coarser ω = k (finer ω)

/--
**Monotonicity.** Knowability transfers to any more informative observation.
Constructive: the decoder is composed, not reassembled.
-/
public theorem Knowable.mono {Ω : Sort u} {I : Sort v} {J : Sort x} {Y : Sort w}
    {finer : Ω → J} {coarser : Ω → I} {property : Ω → Y}
    (hd : Determines finer coarser)
    (h : Knowable coarser property) :
    Knowable finer property := by
  obtain ⟨k, hk⟩ := hd
  obtain ⟨decoder, hdec⟩ := h
  exact ⟨fun j => decoder (k j), fun ω => by rw [hdec ω, hk ω]⟩

/--
**The repair boundary.** Post-processing an unchanged observation cannot create
knowability: if the property is not knowable from the observation, it is not
knowable from any computation over that observation's output either.

Constructive, and the contrapositive of `Knowable.mono` at `finer := observation`.
-/
public theorem not_knowable_comp {Ω : Sort u} {I : Sort v} {K : Sort x} {Y : Sort w}
    {observation : Ω → I} {property : Ω → Y}
    (g : I → K)
    (h : ¬ Knowable observation property) :
    ¬ Knowable (fun ω => g (observation ω)) property := by
  intro hk
  exact h (Knowable.mono (finer := observation) ⟨g, fun _ => rfl⟩ hk)

/-! ## Self-measurement -/

/--
Knowing the **whole state** is exactly injectivity of the observation: a decoder
for `id` is a left inverse of the observation.
-/
public theorem knowable_id_iff_injective {Ω : Sort u} {I : Sort v}
    [Nonempty Ω] (observation : Ω → I) :
    Knowable observation (id : Ω → Ω) ↔ Function.Injective observation := by
  rw [knowable_iff_factorsThrough observation id]
  exact ⟨fun h _ _ hobs => h hobs, fun h _ _ hobs => h hobs⟩

/--
**Self-measurement fails whenever anything outside the read can differ.**

The global state splits into the part the observer reads and a remainder. If the
remainder can take two values, two global states collide at the observation while
being distinct, so the global state is not knowable from inside.

Axiom-free: the proof exhibits the colliding pair rather than reasoning about
injectivity.

This is the *information-theoretic skeleton* of Breuer's self-measurement
argument, not that argument. Non-triviality of the remainder is a hypothesis
here; deriving it from physical containment, and the measurement dynamics,
classical/quantum cases and apparatus model, are all outside this statement.
-/
public theorem not_knowable_state_of_nontrivial_remainder
    {Read : Type u} {Rest : Type v} [Nonempty Read]
    {rest₁ rest₂ : Rest} (hne : rest₁ ≠ rest₂) :
    ¬ Knowable (Prod.fst : Read × Rest → Read) id := by
  obtain ⟨r⟩ := ‹Nonempty Read›
  exact not_knowable_of_collision
    (ω₁ := (r, rest₁)) (ω₂ := (r, rest₂)) rfl
    (fun heq => hne (congrArg Prod.snd heq))

/--
The same obstruction as an inspectable certificate rather than a negation.
-/
public def remainderWitness
    {Read : Type u} {Rest : Type v} (r : Read)
    {rest₁ rest₂ : Rest} (hne : rest₁ ≠ rest₂) :
    IndistinguishabilityWitness (Prod.fst : Read × Rest → Read) id where
  left := (r, rest₁)
  right := (r, rest₂)
  sameObservation := rfl
  propertyDiffers := fun heq => hne (congrArg Prod.snd heq)

end AISafetyAtlas.Knowledge
