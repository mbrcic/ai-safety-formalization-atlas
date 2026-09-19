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
| **Model** | `Determines` | One observation is at least as informative as another — the same proposition as `Knowable`, named for a different use |
| **Law** | `Determines.refl` | Every observation is as informative as itself |
| **Law** | `Determines.trans` | Informativeness composes, across three codomains |
| **Law** | `knowable_iff_factorsThrough` | Bridge to Mathlib's `Function.FactorsThrough` |
| **Law** | `knowable_iff_no_collision` | Knowability ⟺ the property is constant on observation fibres |
| **Law** | `not_knowable_of_collision` | A colliding pair refutes knowability |
| **Law** | `not_knowable_of_invariant_transform` | An observation-preserving map that moves the property refutes knowability |
| **Law** | `exists_witness_of_not_knowable` | Failure yields a concrete colliding pair |
| **Boundary** | `Knowable.mono` | Knowability transfers to any more informative observation |
| **Boundary** | `not_knowable_comp` | Post-processing an unchanged observation cannot create knowability |
| **Whole state** | `knowable_id_iff_injective` | Knowing the entire state ⟺ the observation is injective |
| **Whole state** | `not_knowable_state_of_nontrivial_remainder` | A `Read × Rest` state with two remainder values is not recoverable from `Prod.fst` |
| **Whole state** | `remainderWitness` | The same obstruction as an inspectable certificate |

## `Determines` is `Knowable`, and that is deliberate

`Determines finer coarser` unfolds to `∃ k, ∀ ω, coarser ω = k (finer ω)`, which
is `Knowable finer coarser`. The equality is between the two *applied* at the
same arguments, at full universe generality — the bare constants are not
interchangeable, because they take their type parameters in a different order,
and nothing here needs them to be. So `Determines.trans` and `Knowable.mono` are
one theorem: `Determines.trans` is defined as `Knowable.mono`, with no tactic and
no second proof. `Knowable.mono`'s
own statement writes both names, taking a `Determines` and a `Knowable` as its
two hypotheses, which is the clearest evidence that the split is about intent.

Two names are kept because a factorization is read two ways — as *a property
recovered from an observation* and as *one observation refining another* — and a
consumer holding one question should not have to translate into the other. The
same body appears twice more outside this file, as
`Oversight.JointObservation.Covers` and `Refines`, where the intent is coverage
and evidence refinement. Four names, one proposition. Nothing here proves a law
about `Determines` that is not already a law about `Knowable`, and nothing
should: a genuinely new law would mean the collapse had been broken.

## Constructivity

`not_knowable_of_collision`, `not_knowable_of_witness`,
`not_knowable_of_invariant_transform`, `Knowable.mono`, `not_knowable_comp`,
`Determines.refl` and `Determines.trans` depend on **no axioms at all**
(`#print axioms`): each transports a decoder or a colliding pair directly.

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

universe u v w x y

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
A transformation that leaves the observation fixed and moves the property
refutes knowability.

This is `not_knowable_of_collision` packaged for the case where the colliding
pair is produced by a map rather than found: `σ` is a symmetry of the
observation, and any point it moves in the property is a witness. It states no
new law — the proof is the collision lemma applied to `σ ω` and `ω`.

`σ` is an arbitrary endomap. It is deliberately not a relation, a monoid action
or a group: the two call sites in this tree supply a bare function, and nothing
here needs `σ` to be invertible or to iterate.
-/
public theorem not_knowable_of_invariant_transform {Ω : Sort u} {I : Sort v} {Y : Sort w}
    {observation : Ω → I} {property : Ω → Y}
    (σ : Ω → Ω) (invariantObservation : ∀ ω, observation (σ ω) = observation ω)
    (ω : Ω) (propertyMoves : property (σ ω) ≠ property ω) :
    ¬ Knowable observation property :=
  not_knowable_of_collision (invariantObservation ω) propertyMoves

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
**Reflexivity.** Every observation is at least as informative as itself: the
recovery map is the identity.
-/
public theorem Determines.refl {Ω : Sort u} {I : Sort v} (observation : Ω → I) :
    Determines observation observation :=
  ⟨id, fun _ => rfl⟩

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
**Transitivity.** Informativeness composes: if `f` recovers `g` and `g` recovers
`h`, then `f` recovers `h`.

This *is* `Knowable.mono`, and the proof says so rather than repeating it:
`Determines` and `Knowable` are the same proposition, so composing two
recoveries and transporting a decoder along a coarsening are one operation seen
from two directions. It sits here rather than beside `Determines.refl` for that
reason — the name belongs to the relation, the theorem belongs to the transport.

Stated with three independent codomains, because the whole point of the relation
is to compare observations that do not share a type.
-/
public theorem Determines.trans {Ω : Sort u} {I : Sort v} {J : Sort x} {K : Sort y}
    {f : Ω → J} {g : Ω → I} {h : Ω → K}
    (hfg : Determines f g) (hgh : Determines g h) :
    Determines f h :=
  Knowable.mono hfg hgh

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
