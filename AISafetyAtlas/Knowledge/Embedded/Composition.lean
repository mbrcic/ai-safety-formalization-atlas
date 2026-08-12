module

public import AISafetyAtlas.Knowledge.Embedded

/-!
# Physical complement models for embedded measurement

`AISafetyAtlas.Knowledge.Embedded` takes proper inclusion (non-injectivity of the
restriction) as **model data**. That is faithful to Breuer: the paper does not
derive non-injectivity from set-theoretic containment alone, and Breuer's own
counterexample shows that containment need not force a collision.

This module supplies the compositional physical *bridge* that many applications
want, without rewriting the core:

* the global state is represented (possibly through an equivalence) as
  apparatus × remainder, `Ω ≃ A × R`;
* the apparatus reads by projection onto `A`;
* if the remainder has two admissible states, the restriction collides, so
  `ProperInclusion` holds and Breuer Proposition 1 applies.

## Boundary characterization

Exact whole-state recovery from the restriction is equivalent to injectivity
(`knowable_whole_state_iff_injective`), and proper inclusion is exactly failure
of injectivity (`properInclusion_iff_not_injective`). The boundary has **three**
regions, not two:

| Restriction | What holds |
|---|---|
| not injective | no meshing map measures every state — Breuer Proposition 1 |
| injective, not surjective | **no meshing map exists at all** (`not_meshing_of_not_surjective`) |
| bijective | fibre inference meshes *and* measures every state |

The middle row is easy to omit and easy to misread as an open case. It is not
open: `Meshing.restrict_surjective` empties the model there.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `ProductState` / `productRestriction` | Global state as apparatus × remainder; the apparatus reads by projection |
| **Model** | `equivalentProductRestriction` | The same reading after any representation `Ω ≃ A × R` |
| **Model** | `fibreInference` | A reading set read as the states restricting into it — the natural exact decoder |
| **Law** | `properInclusion_of_nontrivial_remainder` | Two remainder states ⇒ the projection collides. Axiom-free, no finiteness |
| **Law** | `properInclusion_of_nontrivial_remainder_of_equiv` | The same through a state-space equivalence |
| **Characterization** | `properInclusion_iff_not_injective` | Proper inclusion **is** non-injectivity |
| **Characterization** | `knowable_whole_state_iff_injective` | Exact whole-state recovery **is** injectivity — the kernel theorem at the apparatus reading |
| **Boundary** | `no_meshing_measures_all_of_nontrivial_remainder` | Breuer Proposition 1 under a nontrivial complement |
| **Boundary** | `not_meshing_of_not_surjective` | The middle row: injective-but-not-surjective admits **no** meshing map |
| **Positive** | `measuresAll_fibreInference_of_injective` | Injectivity alone measures every state |
| **Positive** | `meshing_and_measuresAll_fibreInference_of_bijective` | Bijective: fibre inference meshes *and* measures everything |

## Constructivity

The structural route is axiom-free — `properInclusion_of_nontrivial_remainder`
depends on no axioms at all. The finite route in `Embedded.Finite` is classical:
`properInclusion_of_card_lt` goes through `properInclusion_iff_not_injective`,
whose backward direction pushes a negation through a binder and so pulls
`Classical.choice`. The `fibreInference` results carry `propext`, `Quot.sound`
from set extensionality. Recorded so nobody reads constructivity off the
finiteness.

## Explicit non-claims

* **Not** “every physically contained apparatus has a nontrivial remainder.”
  A contained subsystem can in principle encode the whole state, be perfectly
  correlated with the rest, or be modelled at a resolution where the remainder
  is a singleton.
* **Not** Breuer’s theorem itself. The graded paper core remains
  `Knowledge.Embedded`. These results are atlas physical modelling, graded
  separately.
* **Not** Bekenstein, dynamics, quantum states, or AI-system conclusions.
-/

namespace AISafetyAtlas.Knowledge.Embedded.Composition

open AISafetyAtlas.Knowledge.Embedded

universe u v w

/-! ## Dichotomy: injectivity is the exact-recovery boundary -/

/--
**Boundary.** Exact whole-state knowledge from a restriction is injectivity of
that restriction. This is the kernel theorem `knowable_id_iff_injective` at the
apparatus reading; recorded here so the physical layer states the dichotomy in
one place.
-/
public theorem knowable_whole_state_iff_injective
    {Ω : Type u} {A : Type v} [Nonempty Ω] (restrict : Restriction Ω A) :
    AISafetyAtlas.Knowledge.Knowable restrict (id : Ω → Ω) ↔
      Function.Injective restrict :=
  AISafetyAtlas.Knowledge.knowable_id_iff_injective restrict

/-- Proper inclusion is exactly non-injectivity of the restriction. -/
public theorem properInclusion_iff_not_injective
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A) :
    ProperInclusion restrict ↔ ¬ Function.Injective restrict := by
  constructor
  · rintro ⟨s₁, s₂, heq, hne⟩ hinj
    exact hne (hinj heq)
  · intro h
    -- `¬ ∀ {x y}, restrict x = restrict y → x = y`
    simp only [Function.Injective] at h
    push Not at h
    exact h

/--
**The third case.** If the restriction is injective but *not* surjective, there is
no meshing inference map at all — so "no meshing map measures every state" holds,
but vacuously, and for a reason unrelated to proper inclusion.

Without this the boundary reads as a two-way split between collision and
bijection, with injective-but-not-surjective an unexplained middle. It is not a
middle: the measurement model is empty there. Contrapositive of
`Meshing.restrict_surjective`.
-/
public theorem not_meshing_of_not_surjective
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (hsurj : ¬ Function.Surjective restrict) (M : InferenceMap Ω A) :
    ¬ Meshing restrict M :=
  fun hm => hsurj (Meshing.restrict_surjective restrict M hm)

/-! ## Product / complement model -/

/-- Global state as apparatus reading paired with an independent remainder. -/
public abbrev ProductState (A : Type v) (R : Type u) := A × R

/-- The apparatus reads by projecting onto its own state. -/
@[expose] public def productRestriction (A : Type v) (R : Type u) :
    Restriction (ProductState A R) A :=
  Prod.fst

/--
Read the apparatus component after representing an arbitrary global state as a
product. This is the reusable form for applications whose global state type is
not definitionally `A × R`.
-/
@[expose] public def equivalentProductRestriction
    {Ω : Type u} {A : Type v} {R : Type w}
    (e : Ω ≃ ProductState A R) : Restriction Ω A :=
  fun s => (e s).1

/--
**Nontrivial complement ⇒ proper inclusion.**

If the remainder admits two distinct states, then for any apparatus reading `a`
the global states `(a, r₁)` and `(a, r₂)` collide under projection. No finiteness
is required: this is the structural content of “the apparatus is only part of a
larger system with an independently variable rest.”
-/
public theorem properInclusion_of_nontrivial_remainder
    {A : Type v} {R : Type u} [Nonempty A]
    {r₁ r₂ : R} (hne : r₁ ≠ r₂) :
    ProperInclusion (productRestriction A R) := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨(a, r₁), (a, r₂), rfl, by intro h; exact hne (congrArg Prod.snd h)⟩

/-- Same obstruction through the knowability kernel (LAND-SELFMEAS-001 shape).

Named for the product state rather than reusing the kernel's name: an unqualified
`not_knowable_state_of_nontrivial_remainder` would be ambiguous in any file that
opens both `Knowledge` and this namespace, which `Examples.NonVacuity` does. -/
public theorem not_knowable_productState_of_nontrivial_remainder
    {A : Type v} {R : Type u} [Nonempty A]
    {r₁ r₂ : R} (hne : r₁ ≠ r₂) :
    ¬ AISafetyAtlas.Knowledge.Knowable (productRestriction A R) id :=
  AISafetyAtlas.Knowledge.not_knowable_state_of_nontrivial_remainder hne

/--
**Breuer Proposition 1 under a nontrivial complement.**

Once the remainder can vary independently, no meshing inference map exactly
measures every product state.
-/
public theorem no_meshing_measures_all_of_nontrivial_remainder
    {A : Type v} {R : Type u} [Nonempty A]
    (M : InferenceMap (ProductState A R) A)
    {r₁ r₂ : R} (hne : r₁ ≠ r₂)
    (hm : Meshing (productRestriction A R) M) :
    ¬ MeasuresAllStates M :=
  no_meshing_inference_measures_all_states
    (productRestriction A R) M (properInclusion_of_nontrivial_remainder hne) hm

/-- A nontrivial remainder still forces proper inclusion after any state-space
equivalence `Ω ≃ A × R`. -/
public theorem properInclusion_of_nontrivial_remainder_of_equiv
    {Ω : Type u} {A : Type v} {R : Type w} [Nonempty A]
    (e : Ω ≃ ProductState A R)
    {r₁ r₂ : R} (hne : r₁ ≠ r₂) :
    ProperInclusion (equivalentProductRestriction e) := by
  obtain ⟨a⟩ := ‹Nonempty A›
  refine ⟨e.symm (a, r₁), e.symm (a, r₂), ?_, ?_⟩
  · simp [equivalentProductRestriction]
  · intro h
    apply hne
    have hpair : (a, r₁) = (a, r₂) := e.symm.injective h
    exact congrArg (fun p : ProductState A R => p.2) hpair

/-- Breuer Proposition 1 for an arbitrary state-space representation
`Ω ≃ A × R` with a nontrivial independently variable remainder. -/
public theorem no_meshing_measures_all_of_nontrivial_remainder_of_equiv
    {Ω : Type u} {A : Type v} {R : Type w} [Nonempty A]
    (e : Ω ≃ ProductState A R)
    (M : InferenceMap Ω A)
    {r₁ r₂ : R} (hne : r₁ ≠ r₂)
    (hm : Meshing (equivalentProductRestriction e) M) :
    ¬ MeasuresAllStates M :=
  no_meshing_inference_measures_all_states
    (equivalentProductRestriction e) M
    (properInclusion_of_nontrivial_remainder_of_equiv e hne) hm

/-! ## Positive side: bijective restriction measures all states -/

/--
Fibre inference: a reading set is read as the set of global states whose
restriction lands in it. This is the natural exact decoder when fibres are
singletons.
-/
public def fibreInference {Ω : Type u} {A : Type v}
    (restrict : Restriction Ω A) : InferenceMap Ω A where
  infer U := {s | restrict s ∈ U.1}
  infer_eq_union_singletons := by
    intro U
    ext s
    constructor
    · intro hs
      exact ⟨restrict s, hs, by simp [ReadingSet.singleton]⟩
    · rintro ⟨a, ha, hsa⟩
      -- `hsa : restrict s ∈ {a}`, i.e. `restrict s = a`
      change restrict s ∈ ({a} : Set A) at hsa
      have hsa' : restrict s = a := hsa
      show restrict s ∈ U.1
      simpa [hsa'] using ha

/-- Surjectivity of the restriction makes the fibre inference map mesh. -/
public theorem meshing_fibreInference_of_surjective
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (hsurj : Function.Surjective restrict) :
    Meshing restrict (fibreInference restrict) := by
  intro a
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    -- `hs : restrict s ∈ {a}` under `fibreInference`
    change restrict s ∈ ({a} : Set A) at hs
    exact hs
  · intro hx
    change x ∈ ({a} : Set A) at hx
    obtain ⟨s, hsx⟩ := hsurj x
    refine ⟨s, ?_, hsx⟩
    -- need `restrict s ∈ {a}`
    change restrict s ∈ ({a} : Set A)
    simpa [hsx] using hx

/--
**Injectivity ⇒ every state is exactly measurable** by the fibre inference map.

Surjectivity is not required for this half: each singleton reading
`{restrict s}` recovers `s` alone. Meshing still needs surjectivity
(`meshing_fibreInference_of_surjective`). Together with
`knowable_whole_state_iff_injective`, this is the constructive positive half of
the boundary for exact whole-state measurement in the Breuer model.
-/
public theorem measuresAll_fibreInference_of_injective
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (hinj : Function.Injective restrict) :
    MeasuresAllStates (fibreInference restrict) := by
  intro s
  refine ⟨ReadingSet.singleton (restrict s), ?_⟩
  ext t
  constructor
  · intro ht
    -- `restrict t ∈ {restrict s}`
    change restrict t ∈ ({restrict s} : Set A) at ht
    exact hinj ht
  · intro ht
    -- `t = s`
    change t = s at ht
    show restrict t ∈ ({restrict s} : Set A)
    simp [ht]

/-- The positive measurement boundary packaged in one theorem: a bijective
restriction makes fibre inference both meshing and exactly measurable for every
global state. -/
public theorem meshing_and_measuresAll_fibreInference_of_bijective
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (hbij : Function.Bijective restrict) :
    Meshing restrict (fibreInference restrict) ∧
      MeasuresAllStates (fibreInference restrict) :=
  ⟨meshing_fibreInference_of_surjective restrict hbij.2,
    measuresAll_fibreInference_of_injective restrict hbij.1⟩

end AISafetyAtlas.Knowledge.Embedded.Composition
