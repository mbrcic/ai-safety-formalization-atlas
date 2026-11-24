module

public import AISafetyAtlas.Knowledge.Embedded
public import Mathlib.Data.Set.Countable
public import Mathlib.Logic.Denumerable

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
| **Model** | `InferenceMap.ofFun` | A point map from readings to states, read as an inference map |
| **Positive** | `measuresAllStates_ofFun_of_surjective` | A surjective point map measures every state |
| **Boundary** | `not_meshing_ofFun_of_surjective` | Under proper inclusion, no surjective point map meshes |
| **Law** | `nonempty_equiv_of_finite_fibres` | Breuer footnote 4: countably infinite readings, finite fibres ⇒ a bijection readings ≃ states |
| **Boundary** | `nonempty_equiv_and_meshing_failure_of_finite_fibres` | Breuer footnote 4 as printed: such a bijection exists, and each one fails meshing |

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
* **Not** Breuer’s §3.5 theorems. The graded paper core remains
  `Knowledge.Embedded`, and the complement-model results above are atlas
  physical modelling, graded separately. The exception is the last section,
  which states Breuer's footnote 4 (p. 208) as printed.
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

/-! ## Point-map inference, and Breuer's footnote 4

Breuer's footnote 4 (p. 208) exhibits bijections between apparatus and global
states that do **not** mesh: *"if `𝒮_𝒜` is infinite but countable, and if for
every state `s_A ∈ 𝒮_𝒜` there are only finitely many `s ∈ 𝒮_𝒪` such that
`s|_A = s_A`, then there is a bijection `φ` between `𝒮_𝒜` and `𝒮_𝒪`. But since
`∃ s_A ∈ 𝒮_𝒜 : φ({s_A})|_A ≠ {s_A}` the meshing condition is not fulfilled."*

The failure needs proper inclusion, Breuer's §3.3 standing assumption: when every
fibre is a singleton the restriction is itself a bijection and its inverse
meshes. The failure half also needs no countability — any surjective point map
fails to mesh under proper inclusion (`not_meshing_ofFun_of_surjective`);
countability and finite fibres are what make the bijection exist. -/

end AISafetyAtlas.Knowledge.Embedded.Composition

namespace AISafetyAtlas.Knowledge.Embedded

universe u v

/-- **Point-map inference.** A map `φ` from readings to global states read as an
inference map, `θ(U) = φ(U)`: the inference map footnote 4 attaches to a
bijection `φ`, whose singleton values print writes `φ({s_A})`. Breuer's union
law holds because images commute with unions. -/
@[expose] public def InferenceMap.ofFun
    {Ω : Type u} {A : Type v} (φ : A → Ω) : InferenceMap Ω A where
  infer U := φ '' U.1
  infer_eq_union_singletons := by
    intro U
    ext s
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, a, rfl, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain rfl : b = a := hb
      exact ⟨b, ha, rfl⟩

end AISafetyAtlas.Knowledge.Embedded

namespace AISafetyAtlas.Knowledge.Embedded.Composition

open AISafetyAtlas.Knowledge.Embedded

universe u v w

/-- A point map infers, from a single reading, the single state it names. -/
public theorem ofFun_infer_singleton {Ω : Type u} {A : Type v} (φ : A → Ω) (a : A) :
    (InferenceMap.ofFun φ).infer (ReadingSet.singleton a) = {φ a} :=
  Set.image_singleton

/-- **A surjective point map measures every state**: each state is the value of
some reading, and that reading alone infers it. -/
public theorem measuresAllStates_ofFun_of_surjective {Ω : Type u} {A : Type v}
    {φ : A → Ω} (hφ : Function.Surjective φ) :
    MeasuresAllStates (InferenceMap.ofFun φ) := fun s => by
  obtain ⟨a, rfl⟩ := hφ s
  exact ⟨ReadingSet.singleton a, ofFun_infer_singleton φ a⟩

/-- **Under proper inclusion, no surjective point map meshes.** Breuer's
Corollary (`meshing_fails_of_measuresAllStates`) at a point map, which measures
every state. Wider than footnote 4: any surjection, at any cardinality. -/
public theorem not_meshing_ofFun_of_surjective {Ω : Type u} {A : Type v}
    (restrict : Restriction Ω A) (hp : ProperInclusion restrict)
    {φ : A → Ω} (hφ : Function.Surjective φ) :
    ¬ Meshing restrict (InferenceMap.ofFun φ) :=
  meshing_fails_of_measuresAllStates restrict _ hp (measuresAllStates_ofFun_of_surjective hφ)

/-- **Breuer footnote 4, the bijection.** If the apparatus states are countably
infinite, the restriction is surjective (Breuer §3.3), and every fibre is finite,
then apparatus and global states are in bijection: the global states are a
countable union of finite fibres, and infinite because they cover the readings. -/
public theorem nonempty_equiv_of_finite_fibres {Ω : Type u} {A : Type v}
    [Countable A] [Infinite A] (restrict : Restriction Ω A)
    (hsurj : Function.Surjective restrict) (hfin : ∀ a, (restrict ⁻¹' {a}).Finite) :
    Nonempty (A ≃ Ω) := by
  have hcount : (Set.univ : Set Ω).Countable := by
    have huniv : (Set.univ : Set Ω) = ⋃ a, restrict ⁻¹' {a} := by
      ext s; simp
    rw [huniv]
    exact Set.countable_iUnion fun a => (hfin a).countable
  have : Countable Ω := Set.countable_univ_iff.mp hcount
  have : Infinite Ω := Infinite.of_surjective restrict hsurj
  exact nonempty_equiv_of_countable

/-- **Breuer footnote 4, as printed.** Countably infinite apparatus states,
surjective restriction, finite fibres: there is a bijection `φ : 𝒮_𝒜 ≃ 𝒮_𝒪`,
and under proper inclusion *every* such bijection has a reading `s_A` with
`φ({s_A})|_A ≠ {s_A}` — print's witness that the meshing condition fails. -/
public theorem nonempty_equiv_and_meshing_failure_of_finite_fibres
    {Ω : Type u} {A : Type v} [Countable A] [Infinite A] (restrict : Restriction Ω A)
    (hsurj : Function.Surjective restrict) (hfin : ∀ a, (restrict ⁻¹' {a}).Finite)
    (hp : ProperInclusion restrict) :
    Nonempty (A ≃ Ω) ∧ ∀ e : A ≃ Ω, ∃ a : A,
      Set.image restrict ((InferenceMap.ofFun e).infer (ReadingSet.singleton a)) ≠ {a} := by
  refine ⟨nonempty_equiv_of_finite_fibres restrict hsurj hfin, fun e => ?_⟩
  have h := not_meshing_ofFun_of_surjective restrict hp e.surjective
  unfold Meshing at h
  push Not at h
  exact h

end AISafetyAtlas.Knowledge.Embedded.Composition
