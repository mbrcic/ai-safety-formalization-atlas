module

public import AISafetyAtlas.Knowledge
public import Mathlib.Order.Defs.PartialOrder

/-!
# Time-indexed knowability

`AISafetyAtlas.Knowledge` asks whether a property factors through an
observation. This module adds the one thing that question is missing when the
observer runs inside a process: **when**.

## The distinction the whole module exists for

Two statements that prose conflates and that must not be one definition:

* *knowing the state as of time `s`, from evidence available at time `t`*, and
* *knowing the current state at time `t`.*

`KnowableFrom … t s` is the first. The second is `KnowableAt … t`, which is
`KnowableFrom … t t`. Chandy–Lamport (`LAND-CL-001`) is precisely the fact that
the first is achievable in a distributed system while the computation continues.
So an impossibility stated as "a system cannot know its own global state" is
false at useful resolutions; the defensible obstruction is contemporaneous. The
non-implication is *exhibited*, not asserted — see
`AISafetyAtlas.Examples.Knowledge.Temporal`.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `KnowableFrom` | The target as of time `s` is decodable from evidence at time `t` |
| **Model** | `KnowableAt` | The *contemporaneous* case, `KnowableFrom t t` |
| **Model** | `EvidenceMonotone` | Later evidence determines earlier evidence |
| **Model** | `CollisionAt` | Two histories agreeing on evidence at `t`, differing in the target at `t` |
| **Model** | `DelayedKnowable` | `t ≤ t'`, not knowable when current, knowable from evidence at `t'` |
| **Law** | `knowableFrom_mono` | Under cumulative evidence, knowability transfers forward in time |
| **Boundary** | `not_knowableAt_of_collisionAt` | A collision at `t` refutes contemporaneous knowledge at `t` |
| **Law** | `collisionAt_of_not_knowableAt` | The converse: failure yields a concrete colliding pair |

## What carries the content

Nothing here re-proves a factorization argument. `knowableFrom_mono` is
`Knowable.mono` at `finer := observe t'`, and
`not_knowableAt_of_collisionAt` is `not_knowable_of_collision`. The content
of this module is the **indexing**: separating the time the evidence is read from
the time the target refers to, so that the two statements above stop being the
same sentence.

## Prior art: this is a measure-free shadow of a filtration

The indexing is not new. Mathlib's `ProbabilityTheory.Filtration`
(`Mathlib/Probability/Process/Filtration.lean`) is an increasing family of
sub-σ-algebras over the same `[Preorder ι]`, and the surrounding development
already names every distinction this module draws:

| Here | Mathlib |
|---|---|
| `EvidenceMonotone observe` | `Filtration`, via `mono'` |
| `∀ t, KnowableAt observe target t` | `Adapted` |
| knowable from strictly earlier evidence | `Predictable` |
| `DelayedKnowable` | `ℱ t'`-measurable but not `ℱ t`-measurable |

So no novelty is claimed for time-indexed information as such; the recorded
search is `NC-007`. What this module has that a filtration does not is that it
needs **no measurable structure at all** — `Ω`, the evidence types and the target
are bare types, examples stay `decide`-able, and cumulativity is stated as
`Determines` rather than σ-algebra inclusion **because the evidence types at
different times are different types**, which a filtration over one fixed `Ω`
cannot express. Those are the reasons to have it, not priority.

## Explicit non-claims

`observe` is an arbitrary indexed family; nothing here makes it a projection of a
state containing the observer, and nothing makes `T` physical time — it is any
preorder, and the results hold for logical clocks and causal orders equally.
There is no dynamics, no transition relation, no probability, and no rate. No
AI-system reading follows without a separate reviewed bridge.

No survey coverage row is claimed here; this is workbench infrastructure.
-/

namespace AISafetyAtlas.Knowledge.Temporal

universe u v w x

variable {T : Type x} {Ω : Type u} {I : T → Type v} {Y : Type w}

/-! ## Indexed knowability -/

/--
The target **as of time `s`** is knowable **from the evidence available at time
`t`**: one decoder on time-`t` evidence reproduces the time-`s` target at every
history.

Keeping the two indices apart is the whole point. Collapsing them to one is
`KnowableAt`, and the two are not interchangeable.
-/
@[expose] public def KnowableFrom
    (observe : ∀ t, Ω → I t) (target : T → Ω → Y) (t s : T) : Prop :=
  Knowable (observe t) (target s)

/--
The **contemporaneous** case: the target as of `t` is knowable from evidence at
`t`. This is the statement an impossibility result may defensibly deny.
-/
@[expose] public def KnowableAt
    (observe : ∀ t, Ω → I t) (target : T → Ω → Y) (t : T) : Prop :=
  KnowableFrom observe target t t

/-! ## Cumulative evidence -/

/--
Evidence is **cumulative**: whatever an earlier reading reveals is recoverable
from a later one. Stated as `Determines` rather than as set inclusion because the
evidence types at different times are different types.

Without this an observer may *forget*, and knowability does not transfer forward.
-/
@[expose] public def EvidenceMonotone [Preorder T]
    (observe : ∀ t, Ω → I t) : Prop :=
  ∀ ⦃t t' : T⦄, t ≤ t' → Determines (observe t') (observe t)

/--
**Knowledge is not lost.** Under cumulative evidence, anything decodable at `t`
is decodable at any later `t'` — about the same target time `s`.

This is `Knowable.mono`; the temporal reading is the contribution, not the proof.
-/
public theorem knowableFrom_mono [Preorder T]
    {observe : ∀ t, Ω → I t} {target : T → Ω → Y} {t t' s : T}
    (hm : EvidenceMonotone observe) (hle : t ≤ t')
    (hk : KnowableFrom observe target t s) :
    KnowableFrom observe target t' s :=
  Knowable.mono (hm hle) hk

/-! ## Collisions -/

/--
**A collision at `t`**: two histories the evidence at `t` cannot separate, whose
targets at `t` already differ.

### On the name

This is deliberately **not** called `CausalInnovation`, which is the name it
invites. Nothing here is causal: there is no transition system, no dynamics, and
no notion of the target *moving*. What the definition says is that the
contemporaneous reading is ambiguous about the contemporaneous target — a
collision, indexed by time.

A genuine causal-innovation condition would be *why* such a pair exists: the
target changed between the last evidence-generating event and `t`. Stating that
requires dynamics this module deliberately does not have. When dynamics land,
innovation is what would have to **imply** `CollisionAt`; it is not what
`CollisionAt` says.

The distinction matters for a real reason. Positive propagation delay alone does
*not* defeat contemporaneous knowledge — under deterministic dynamics the current
target may already be determined by old evidence. Only a collision does.
-/
@[expose] public def CollisionAt
    (observe : ∀ t, Ω → I t) (target : T → Ω → Y) (t : T) : Prop :=
  ∃ ω ω' : Ω, observe t ω = observe t ω' ∧ target t ω ≠ target t ω'

/-- A collision at `t` refutes contemporaneous knowledge at `t`. Axiom-free. -/
public theorem not_knowableAt_of_collisionAt
    {observe : ∀ t, Ω → I t} {target : T → Ω → Y} {t : T}
    (h : CollisionAt observe target t) :
    ¬ KnowableAt observe target t := by
  obtain ⟨ω, ω', hobs, hne⟩ := h
  exact not_knowable_of_collision hobs hne

/-- Conversely, failure of contemporaneous knowledge yields a concrete colliding
pair. Classical, as the kernel's witness extraction is. -/
public theorem collisionAt_of_not_knowableAt [Nonempty Y]
    {observe : ∀ t, Ω → I t} {target : T → Ω → Y} {t : T}
    (h : ¬ KnowableAt observe target t) :
    CollisionAt observe target t := by
  obtain ⟨w⟩ := exists_witness_of_not_knowable h
  exact ⟨w.left, w.right, w.sameObservation, w.propertyDiffers⟩

/-! ## Delay -/

/--
The target as of `t` is **not** knowable when current, but **is** knowable from
the evidence at a **later** time `t'`.

`t ≤ t'` is part of the definition and not an afterthought. Without it the
predicate is satisfied by `t' < t`, which is not delay but precognition: the
target as of `t` decoded from evidence that predates it. That would be a
perfectly consistent Lean statement and a completely wrong reading of the name,
so the order lives in the definition where it cannot be forgotten at a use site.

This is the escape distributed snapshots take: relax contemporaneity, keep
exactness. `AISafetyAtlas.Examples.Knowledge.Temporal` exhibits a model
inhabiting this together with `EvidenceMonotone`, which is what stops the
contemporaneous obstruction being read as "the state is never knowable".
-/
@[expose] public def DelayedKnowable [Preorder T]
    (observe : ∀ t, Ω → I t) (target : T → Ω → Y) (t t' : T) : Prop :=
  t ≤ t' ∧ ¬ KnowableAt observe target t ∧ KnowableFrom observe target t' t

end AISafetyAtlas.Knowledge.Temporal
