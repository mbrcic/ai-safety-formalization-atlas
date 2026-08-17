module

public import AISafetyAtlas.Knowledge.Devices
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi

/-!
# Checkers that run, for the knowability kernel and the device transports

`Knowledge` and `Knowledge.Devices` state their obstructions as `Prop`s and prove
them by hand. That is the right form for a theorem and the wrong form for a
question someone wants answered about a particular finite model, which is the
shape most consumers arrive with — an architecture, a monitor, a hazard.

This module supplies the executable half, on the pattern
`Oversight.JointObservation.FiniteDecision` already sets for coverage: a function
that computes, and a theorem saying the function agrees with the `Prop`. Only the
theorem makes the output evidence rather than a report.

## What runs

* `findCollision` searches a finite state space for an indistinguishability
  witness, returning the pair. `none` is not a failure to find one — it is
  `Knowable`, by `knowable_of_findCollision_eq_none`.
* The `Decidable` instances make `WeaklyInfers`, `Realized` and
  `BlockwiseCollision` evaluate on any finite device. `decide` already settles
  them in the kernel at elaboration time; the instances are what lets a program
  settle them at runtime, on a model it read from a file.

`Examples.Inference.FinDevice` carries its own instance for enumerating *all*
devices of a shape, which is a different job — that one quantifies over devices
and needs both types pinned, while these take the device as given.

## What does not run

Nothing here decides anything about an infinite state space, and nothing here
produces a Lean proof term at runtime. A program using these gets the same answer
the kernel would give, with the theorem below as the reason to believe it; it
does not get a certificate the kernel has checked. That distinction is the whole
content of `atlas-check`'s output and is stated there too.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Checker** | `findCollision` | Search a finite state space for an indistinguishability witness |
| **Law** | `not_knowable_of_findCollision_eq_some` | A returned pair refutes knowability |
| **Law** | `knowable_of_findCollision_eq_none` | Returning nothing *is* knowability |
| **Instance** | `decidableRealized` | Setup values a finite device actually takes |
| **Instance** | `decidableWeaklyInfers` | Definition 3 on a finite device |
| **Instance** | `decidableBlockwiseCollision` | The transport hypothesis on a finite device |
-/

namespace AISafetyAtlas.Knowledge.Check

open AISafetyAtlas.Inference
open AISafetyAtlas.Knowledge

universe u v v'

/-! ## Searching for a witness -/

/--
Every ordered pair drawn from an enumeration of the states.

The enumeration is an argument rather than derived from `Fintype`, for the reason
`FiniteDecision` gives about coverage: `Finset.toList` is noncomputable, so a
checker that reaches for it states the search without running it.
-/
@[expose] public def collisionPairs {U : Type u} (enum : List U) : List (U × U) :=
  enum.flatMap fun a => enum.map fun b => (a, b)

/--
Search the enumerated states for a pair the observation cannot separate and the
property does. Returns the first such pair.
-/
@[expose] public def findCollision {U : Type u} {I : Type v} {Y : Type v'}
    [DecidableEq I] [DecidableEq Y] (enum : List U)
    (observation : U → I) (property : U → Y) : Option (U × U) :=
  (collisionPairs enum).find? fun p =>
    decide (observation p.1 = observation p.2) && !decide (property p.1 = property p.2)

/-- A returned pair is a genuine witness, whatever the enumeration was. -/
public theorem findCollision_eq_some {U : Type u} {I : Type v} {Y : Type v'}
    [DecidableEq I] [DecidableEq Y] {enum : List U}
    {observation : U → I} {property : U → Y} {p : U × U}
    (h : findCollision enum observation property = some p) :
    observation p.1 = observation p.2 ∧ property p.1 ≠ property p.2 := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] at hp
  exact hp

/-- **The checker refutes.** A returned pair is the spine's negative certificate. -/
public theorem not_knowable_of_findCollision_eq_some {U : Type u}
    {I : Type v} {Y : Type v'} [DecidableEq I] [DecidableEq Y] {enum : List U}
    {observation : U → I} {property : U → Y} {p : U × U}
    (h : findCollision enum observation property = some p) :
    ¬ Knowable observation property :=
  not_knowable_of_collision (findCollision_eq_some h).1 (findCollision_eq_some h).2

/--
**The checker confirms.** Returning nothing is not an inconclusive search *when
the enumeration is complete*: it is knowability.

Completeness is a hypothesis rather than an instance because it is the whole
content of the direction. A checker run on a partial enumeration answers a
different question, and silently treating that answer as this one is the failure
mode the hypothesis exists to block.
-/
public theorem knowable_of_findCollision_eq_none {U : Type u}
    {I : Type v} {Y : Type v'} [DecidableEq I] [DecidableEq Y] [Nonempty Y]
    {enum : List U} (hcomplete : ∀ u : U, u ∈ enum)
    {observation : U → I} {property : U → Y}
    (h : findCollision enum observation property = none) :
    Knowable observation property := by
  refine (knowable_iff_no_collision observation property).mpr fun ω τ hobs => ?_
  by_contra hne
  have hmem : (ω, τ) ∈ collisionPairs enum :=
    List.mem_flatMap.mpr ⟨ω, hcomplete ω, List.mem_map.mpr ⟨τ, hcomplete τ, rfl⟩⟩
  have hfail := List.find?_eq_none.mp h (ω, τ) hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, not_and, not_not] at hfail
  exact hne (hfail hobs)

/-- The checker and the kernel agree in both directions. -/
public theorem findCollision_eq_none_iff {U : Type u}
    {I : Type v} {Y : Type v'} [DecidableEq I] [DecidableEq Y] [Nonempty Y]
    {enum : List U} (hcomplete : ∀ u : U, u ∈ enum)
    (observation : U → I) (property : U → Y) :
    findCollision enum observation property = none ↔ Knowable observation property := by
  refine ⟨knowable_of_findCollision_eq_none hcomplete, fun hk => ?_⟩
  rcases hfind : findCollision enum observation property with _ | p
  · rfl
  · exact absurd hk (not_knowable_of_findCollision_eq_some hfind)

/-! ## The reader's relabelling changes nothing

`atlas-check` does not hand the kernel the numbers a caller wrote. It relabels
them, keeping only **which states share a value**, so that the codomain is finite
without the caller declaring its size. Until now the claim that this cannot change
a verdict was asserted in a comment, and
[`docs/guide/atlas-check.md`](../../docs/guide/atlas-check.md) named it as the one
step between a caller's JSON and a certified predicate that no theorem covered.

These are that theorem. The hypothesis is exactly what the reader guarantees —
two states share a relabelled value precisely when they shared a raw one — and the
conclusion is that knowability is the same question before and after. Neither
direction needs the relabelling to be injective, surjective, order-preserving, or
into any particular type; it needs only that the partition survives.

`knowable_congr_observation` covers the observation side and
`knowable_congr_property` the property side, so a reader that renumbers both is
covered by composing them. `knowable_comp_left_iff` is the special case a caller
is most likely to reason about: post-composing with an injection.
-/

/--
**Relabelling the observation cannot change the verdict.** If two states share a
value under the new observation exactly when they shared one under the old, then
the property is knowable from one iff it is knowable from the other.

This is the fibre-preservation the JSON reader performs, stated as a hypothesis.
-/
public theorem knowable_congr_observation {U : Type u} {I : Type v} {I' : Type v'}
    {Y : Type w} [Nonempty Y]
    {observation : U → I} {observation' : U → I'} {property : U → Y}
    (hfibres : ∀ u v : U, observation u = observation v ↔ observation' u = observation' v) :
    Knowable observation property ↔ Knowable observation' property := by
  rw [knowable_iff_no_collision observation property,
    knowable_iff_no_collision observation' property]
  exact ⟨fun h u v huv => h u v ((hfibres u v).mpr huv),
    fun h u v huv => h u v ((hfibres u v).mp huv)⟩

/--
**Relabelling the property cannot change the verdict either.** The same
hypothesis on the other argument.

`Nonempty` is required of both target types because the characterization this
runs through supplies a decoder by choosing a value on each fibre.
-/
public theorem knowable_congr_property {U : Type u} {I : Type v}
    {Y : Type w} {Y' : Type w'} [Nonempty Y] [Nonempty Y']
    {observation : U → I} {property : U → Y} {property' : U → Y'}
    (hfibres : ∀ u v : U, property u = property v ↔ property' u = property' v) :
    Knowable observation property ↔ Knowable observation property' := by
  rw [knowable_iff_no_collision observation property,
    knowable_iff_no_collision observation property']
  exact ⟨fun h u v huv => (hfibres u v).mp (h u v huv),
    fun h u v huv => (hfibres u v).mpr (h u v huv)⟩

/--
The case a caller reasons about directly: renaming observation values by an
injection is invisible to knowability.

Injectivity is stronger than the theorem above needs, which is why the general
form is the one the reader is checked against.
-/
public theorem knowable_comp_left_iff {U : Type u} {I : Type v} {I' : Type v'}
    {Y : Type w} [Nonempty Y]
    {observation : U → I} {property : U → Y} {f : I → I'} (hf : Function.Injective f) :
    Knowable (f ∘ observation) property ↔ Knowable observation property :=
  (knowable_congr_observation (observation := observation) (observation' := f ∘ observation)
    (property := property) (fun _ _ => ⟨fun h => congrArg f h, fun h => hf h⟩)).symm

/-! ## Evaluating the device predicates

Each predicate is a `def` over quantifiers that are finite once the state space
and the setup type are, and instance search works at reducible transparency, so
each is unfolded by hand. Without these a program can state the question and not
answer it.
-/

public instance decidableSurjective {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) : Decidable (Function.Surjective f) := by
  unfold Function.Surjective
  infer_instance

public instance decidableRealized {U : Type u} [Fintype U] (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (x : C.Setup) : Decidable (C.Realized x) := by
  unfold InferenceDevice.Realized
  infer_instance

public instance decidableWeaklyInfers {U : Type u} [Fintype U]
    (C : InferenceDevice.{u, v} U) [Fintype C.Setup] [DecidableEq C.Setup]
    {G : Type v'} [Fintype G] [DecidableEq G] (Γ : U → G) :
    Decidable (WeaklyInfers C Γ) := by
  unfold WeaklyInfers InferenceDevice.Realized IsProbe
  infer_instance

public instance decidableBlockwiseCollision {U : Type u} [Fintype U]
    (C : InferenceDevice.{u, v} U) [Fintype C.Setup] [DecidableEq C.Setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) (γ : G) :
    Decidable (Devices.BlockwiseCollision C Γ γ) := by
  unfold Devices.BlockwiseCollision InferenceDevice.Realized
  infer_instance

end AISafetyAtlas.Knowledge.Check
