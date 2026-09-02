module

public import AISafetyAtlas.Knowledge
public import Mathlib.Data.Set.Image

/-!
# Embedded measurement and Breuer's abstract core

This module formalizes the abstract set-theoretic core of Breuer's
self-measurement argument. A global state is restricted to an apparatus state;
an inference map assigns a set of compatible global states to every nonempty
set of possible apparatus readings; and the meshing condition requires the
inferred global states to restrict back to the readings that prompted them.

The two central results are:

* states with the same apparatus restriction cannot be distinguished by a
  meshing inference map (Proposition 2); and
* if the restriction is properly included (non-injective), no meshing
  inference map exactly measures every global state (Proposition 1).

Breuer's Corollary rearranges the second: measuring every state does not merely
fail, it makes the inference map inconsistent. That is the shape carrying his
Gödel analogy, and it is stated here as `meshing_fails_of_measuresAllStates`.

Proposition 1 is proved **twice**: derived from Proposition 2, and again by
Breuer's own direct chain. They prove the same statement and are not equal on
every axis — the derived route is axiom-free, the source-faithful one needs
`propext` and `Quot.sound`. The section *Breuer's own route to Proposition 1*
below states that trade in full; it is the reason both are kept.

The source uses an inference map on nonempty subsets of apparatus states and the
singleton meshing condition; those choices are retained here rather than replaced
by a single decoder. See `docs/provenance/self-measurement-kernel.md` for the
source mapping and the omitted parts of the paper.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `Restriction` | Global state restricted to an apparatus state |
| **Model** | `ReadingSet` | A nonempty set of possible apparatus readings |
| **Model** | `InferenceMap` | Reading sets to compatible global states, under Breuer's union law |
| **Model** | `Meshing` | Inferred states restrict back exactly to the reading that prompted them |
| **Model** | `ProperInclusion` | Two distinct global states with the same restriction |
| **Model** | `ExactlyMeasurable` / `MeasuresAllStates` | Some reading set infers a state alone / every state |
| **Model** | `Distinguishes` | Mutually separating reading sets for two states — Breuer §3.2 |
| **Law** | `Meshing.restrict_surjective` | Meshing already forces surjectivity; the paper assumes it separately |
| **Law** | `infer_singleton_eq_of_meshing` | Breuer's unnamed LEMMA, as displayed on p. 208 |
| **Boundary** | `no_meshing_inference_distinguishes` | **Proposition 2** |
| **Boundary** | `no_meshing_inference_measures_all_states` | **Proposition 1**, derived — axiom-free |
| **Boundary** | `no_meshing_inference_measures_all_states_direct` | **Proposition 1**, Breuer's own chain |
| **Boundary** | `exists_state_not_exactly_measurable` | Proposition 1 in the paper's printed existential form |
| **Boundary** | `meshing_fails_of_measuresAllStates` | **Corollary** — measuring every state makes the inference map inconsistent |
| **Boundary** | `exists_state_meshing_failure_of_measuresAllStates` | The Corollary's printed witness, under the source's §3.3 surjectivity |
| **Bridge** | `not_knowable_state_of_properInclusion` | Proper inclusion through `AISafetyAtlas.Knowledge`; strictly weaker than the measurement result |

## Explicit non-claims

This is an **abstract measurement result, not a physical model**. Classical and
quantum state spaces, dynamics, apparatus construction, and EPR correlations are
intentionally left to separate layers.

Proper inclusion is **model data**, not derived. Nothing here says that a
physically contained apparatus must have a non-injective restriction; the source
does not derive it either, and Breuer's own counterexample shows containment need
not force a collision. Deriving it under stated hypotheses is
`Knowledge.Embedded.Composition` and `.Finite`, graded separately as atlas
modelling rather than as the paper.

Nothing here concerns AI systems. No self-monitoring, introspection, or
observability reading follows without a separate reviewed bridge.

The grade against Breuer is `EQUIVALENT` (`LAND-SELFMEAS-002`). Every statement
§3.5 displays is here — Propositions 1 and 2, the LEMMA, the Corollary — over the
paper's own §3.2 abstraction, and §§4–5 display none, they apply these. Not
`EXACT`, because the hypotheses are deliberately not the source's: meshing alone
is assumed where the paper assumes meshing and surjectivity, and the Corollary's
witness form takes surjectivity back explicitly. The physical, quantum,
dynamical and EPR material of the paper is not formalized.
-/

namespace AISafetyAtlas.Knowledge.Embedded

universe u v

/-! ## Measurement model -/

/-- A nonempty set of possible apparatus readings. -/
public abbrev ReadingSet (A : Type v) := {U : Set A // U.Nonempty}

/-- Exposed: `Meshing`, `ExactlyMeasurable` and `Distinguishes` are *stated* in
terms of this constructor, so an external consumer cannot discharge any of them
without unfolding it. -/
@[expose] public def ReadingSet.singleton {A : Type v} (a : A) : ReadingSet A :=
  ⟨{a}, ⟨a, rfl⟩⟩

/-- The reading set that excludes nothing: the apparatus reports no information.
Exposed for the same reason as `singleton` — the inference-map union law and the
proofs over it are stated in terms of these two constructors. -/
@[expose] public def ReadingSet.univ {A : Type v} [Nonempty A] : ReadingSet A :=
  ⟨Set.univ, by
    obtain ⟨a⟩ := ‹Nonempty A›
    exact ⟨a, by trivial⟩⟩

/--
An inference map from possible apparatus readings to compatible global states.

The union law is Breuer's `O(S_A) = ⋃ s_A ∈ S_A, O({s_A})` convention. The
empty reading set is excluded, as in the source paper.
-/
public structure InferenceMap (Ω : Type u) (A : Type v) where
  infer : ReadingSet A → Set Ω
  infer_eq_union_singletons :
    ∀ U : ReadingSet A,
      infer U = {s | ∃ a ∈ U.1, s ∈ infer (ReadingSet.singleton a)}

/-- Restriction of a global state to the apparatus state. -/
public abbrev Restriction (Ω : Type u) (A : Type v) := Ω → A

/--
Breuer's proper-inclusion condition, expressed at the state level: two
distinct global states have the same apparatus restriction.

This is deliberately not derived from a set-theoretic claim that `A` is a
subsystem of `Ω`; the source explicitly treats the restriction map as part of
the physical model. Breuer also describes that restriction as surjective;
under `Meshing`, surjectivity is derived by `Meshing.restrict_surjective`.
-/
@[expose] public def ProperInclusion
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A) : Prop :=
  ∃ s₁ s₂, restrict s₁ = restrict s₂ ∧ s₁ ≠ s₂

/--
Breuer's singleton-state consistency, called the meshing condition.

Verbatim §3.5: *"So meshing can be written: `∀ s_A ∈ 𝒮_𝒜 : {s|_A : s ∈ θ({s_A})} = {s_A}`."*
The equality is exact — not an inclusion — and this definition is that equality,
with `Set.image restrict` for `{s|A : s ∈ ·}`.
-/
@[expose] public def Meshing
    {Ω : Type u} {A : Type v}
    (restrict : Restriction Ω A) (M : InferenceMap Ω A) : Prop :=
  ∀ a : A,
    Set.image restrict (M.infer (ReadingSet.singleton a)) = {a}

/--
Meshing forces the restriction map to be surjective.

Checked against the source. Breuer states surjectivity **separately**, as part of
the §3.3 apparatus setup — *"So `|A` describes a surjective map from the states
of O to the states of A"* — and then imposes meshing in §3.5. Here it is a
theorem rather than a second hypothesis, because the exact singleton-image
equality already entails it.

So this module's hypotheses are **no stronger** than the paper's: where Breuer
assumes surjectivity and meshing, the Lean assumes meshing alone and derives the
rest. `ProperInclusion` therefore only carries the genuinely obstructive
non-injectivity witness.
-/
public theorem Meshing.restrict_surjective
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M) :
    Function.Surjective restrict := by
  intro a
  have ha : a ∈ Set.image restrict
      (M.infer (ReadingSet.singleton a)) := by
    rw [hm a]
    exact Set.mem_singleton a
  rcases ha with ⟨s, hs, hsa⟩
  exact ⟨s, hsa⟩

/-- A state is exactly measurable when some nonempty reading set infers it alone. -/
@[expose] public def ExactlyMeasurable
    {Ω : Type u} {A : Type v} (M : InferenceMap Ω A) (s : Ω) : Prop :=
  ∃ U : ReadingSet A, M.infer U = {s}

/-- Every global state is exactly measurable by an inference map. -/
@[expose] public def MeasuresAllStates
    {Ω : Type u} {A : Type v} (M : InferenceMap Ω A) : Prop :=
  ∀ s : Ω, ExactlyMeasurable M s

/--
The inference map distinguishes two states when it has mutually separating
reading sets for them.

This is Breuer's §3.2 definition, not a paraphrase of it: an experiment *"is said
to be able to distinguish the states `s₁`, `s₂` if there is one set `S¹_A` of
final apparatus states referring to `s₁` but not `s₂`, and another set `S²_A`
referring to `s₂` but not to `s₁`"*. Proposition 2 negates exactly this
existential, which is why the theorem below concludes `¬ Distinguishes`.
-/
@[expose] public def Distinguishes
    {Ω : Type u} {A : Type v} (M : InferenceMap Ω A)
    (s₁ s₂ : Ω) : Prop :=
  ∃ U V : ReadingSet A,
    s₁ ∈ M.infer U ∧ s₂ ∉ M.infer U ∧
    s₂ ∈ M.infer V ∧ s₁ ∉ M.infer V

/-! ## Basic inference-map lemmas -/

private theorem mem_infer_univ_of_mem_infer
    {Ω : Type u} {A : Type v} [Nonempty A] (M : InferenceMap Ω A)
    {s : Ω} {U : ReadingSet A} (hs : s ∈ M.infer U) :
    s ∈ M.infer (ReadingSet.univ) := by
  rw [M.infer_eq_union_singletons U] at hs
  rcases hs with ⟨a, ha, hsa⟩
  rw [M.infer_eq_union_singletons ReadingSet.univ]
  exact ⟨a, by trivial, hsa⟩

private theorem restrict_eq_of_mem_infer_singleton
    {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M)
    {s : Ω} {a : A}
    (hsa : s ∈ M.infer (ReadingSet.singleton a)) : restrict s = a := by
  have himage : restrict s ∈ Set.image restrict
      (M.infer (ReadingSet.singleton a)) :=
    ⟨s, hsa, rfl⟩
  rw [hm a] at himage
  change restrict s = a at himage
  exact himage

private theorem mem_infer_singleton_iff_restrict_eq
    {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M)
    {s : Ω} {a : A}
    (hs : s ∈ M.infer ReadingSet.univ) :
    s ∈ M.infer (ReadingSet.singleton a) ↔ restrict s = a := by
  constructor
  · exact restrict_eq_of_mem_infer_singleton restrict M hm
  · intro hres
    rw [M.infer_eq_union_singletons ReadingSet.univ] at hs
    rcases hs with ⟨b, -, hsb⟩
    have hb : restrict s = b :=
      restrict_eq_of_mem_infer_singleton restrict M hm hsb
    have hba : b = a := hb.symm.trans hres
    simpa [hba] using hsb

/--
**Breuer's unnamed LEMMA, as displayed.** Read off page 208 at 300 dpi
(2026-08-11):

`(∀ s_A) : θ({s_A}) = {s ∈ 𝒮_O : s ∈ θ(𝒮_𝒜), s|_A = s_A}`

The inner `θ(𝒮_𝒜)` applies the inference map to the **whole apparatus state
space** — script `𝒮_𝒜`, as against roman `S_A` for an individual reading set —
so it is `M.infer ReadingSet.univ` here. The paper's own proof of the converse
inclusion settles the reading: *"let `s ∈ 𝒮_O` be such that `s|_A = s_A` for some
`s_A` and `s ∈ θ(𝒮_𝒜)`. Then there is a `s'_A ∈ 𝒮_𝒜` such that `s ∈ θ({s'_A})`"* —
that step is the union law over the full apparatus space, which only makes sense
if the argument is that space.

`Nonempty A` *is* assumed here, unlike in the two propositions. The difference is
real: there it was an artifact of how the proof was routed, while here the
statement cannot be written without it — `ReadingSet.univ` does not exist over an
empty apparatus. Every call site has the reading `a` in hand, so discharging it
is free.
-/
public theorem infer_singleton_eq_of_meshing
    {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M) (a : A) :
    M.infer (ReadingSet.singleton a)
      = {s | s ∈ M.infer ReadingSet.univ ∧ restrict s = a} := by
  ext s
  constructor
  · intro hs
    exact ⟨mem_infer_univ_of_mem_infer M hs,
      restrict_eq_of_mem_infer_singleton restrict M hm hs⟩
  · rintro ⟨huniv, hres⟩
    exact (mem_infer_singleton_iff_restrict_eq restrict M hm huniv).mpr hres

/-! ## Relation to the generic kernel -/

/--
Proper inclusion, expressed through the generic knowability kernel: the whole
global state does not factor through the restriction, so it is not
`AISafetyAtlas.Knowledge.Knowable` from the apparatus reading.

This is the bridge that makes this module a **consumer** of
`AISafetyAtlas.Knowledge` rather than a parallel development. The kernel asks
whether a property factors through an observation; `ProperInclusion` is exactly
a colliding pair for the whole-state target, so the kernel's
`not_knowable_of_collision` discharges it directly.

Note what this does *not* say. It is weaker than
`no_meshing_inference_measures_all_states`: factorization through a single
decoder is not exact measurement by an inference map over reading sets, and this
statement needs no meshing hypothesis. The measurement-model result is the one
graded against the paper.
-/
public theorem not_knowable_state_of_properInclusion
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (h : ProperInclusion restrict) :
    ¬ AISafetyAtlas.Knowledge.Knowable restrict (id : Ω → Ω) := by
  obtain ⟨s₁, s₂, heq, hne⟩ := h
  exact AISafetyAtlas.Knowledge.not_knowable_of_collision heq hne

/-! ## Breuer's central results -/

/--
**Breuer Proposition 2 (abstract form).** If two global states have the same
apparatus restriction, no meshing inference map distinguishes them.

No `Nonempty A` hypothesis, matching the printed statement: with an empty
apparatus there are no reading sets, so `Distinguishes` is uninhabitable and the
conclusion holds for free. The instance is recovered inside the proof from the
reading set the hypothesis supplies.

That removal is faithfulness rather than reach. A restriction `Ω → A` with `A`
empty forces `Ω` empty, so the newly covered case has no states to quantify over
and no consumer can reach it. What it buys is a statement with the source's
hypotheses and no others.
-/
public theorem no_meshing_inference_distinguishes
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M)
    {s₁ s₂ : Ω} (hrestrict : restrict s₁ = restrict s₂) :
    ¬ Distinguishes M s₁ s₂ := by
  rintro ⟨U, V, hs₁U, hs₂U, hs₂V, hs₁V⟩
  -- `A` is inhabited because a reading set was produced, not because the
  -- statement assumed it: `ReadingSet` carries nonemptiness. With an empty
  -- apparatus there are no reading sets and `Distinguishes` is uninhabitable,
  -- which is the case the source's statement also covers for free.
  obtain ⟨witness, -⟩ := U.2
  have : Nonempty A := ⟨witness⟩
  rw [M.infer_eq_union_singletons U] at hs₁U
  rcases hs₁U with ⟨a, ha, hs₁a⟩
  have hs₁_univ := mem_infer_univ_of_mem_infer M hs₁a
  have hs₂_univ := mem_infer_univ_of_mem_infer M hs₂V
  have hs₁res := (mem_infer_singleton_iff_restrict_eq restrict M hm hs₁_univ).mp hs₁a
  have hs₂a : s₂ ∈ M.infer (ReadingSet.singleton a) := by
    apply (mem_infer_singleton_iff_restrict_eq restrict M hm hs₂_univ).mpr
    exact hrestrict.symm.trans hs₁res
  apply hs₂U
  rw [M.infer_eq_union_singletons U]
  exact ⟨a, ha, hs₂a⟩

/--
**Breuer Proposition 1 (abstract form).** Under proper inclusion, no meshing
inference map exactly measures every global state.
-/
public theorem no_meshing_inference_measures_all_states
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hproper : ProperInclusion restrict)
    (hm : Meshing restrict M) :
    ¬ MeasuresAllStates M := by
  rintro hall
  rcases hproper with ⟨s₁, s₂, hrestrict, hne⟩
  rcases hall s₁ with ⟨U, hU⟩
  rcases hall s₂ with ⟨V, hV⟩
  apply no_meshing_inference_distinguishes restrict M hm hrestrict
  refine ⟨U, V, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    exact Set.mem_singleton s₁
  · rw [hU]
    intro h
    have : s₂ = s₁ := h
    exact hne this.symm
  · rw [hV]
    exact Set.mem_singleton s₂
  · rw [hV]
    intro h
    have : s₁ = s₂ := h
    exact hne this

/-! ## Breuer's own route to Proposition 1

The theorem above reaches Proposition 1 through Proposition 2. Breuer does not:
he proves Proposition 1 first, directly, and the LEMMA and Proposition 2 come
afterwards. His argument is a chain of rewrites,

`{s} = θ({s_A}) = θ({θ({s_A})|_A}) = θ({s|_A}) = θ({s'|_A}) = θ({θ({s'_A})|_A})`
`= θ({s'_A}) = {s'}`,

contradicting `s ≠ s'`. The two lemmas below are the steps that chain performs:
the union law picks a *single* reading out of an exact measurement, and meshing
identifies that reading as the state's restriction. Once both are available the
chain collapses, because `s` and `s'` then have the *same* singleton reading.

Both routes are kept. They prove the same statement, and having the source's
argument in the tree is what lets the provenance note claim proof-level fidelity
rather than only conclusion-level.

They are not equal on every axis, and the difference runs against the source:

| | axioms |
|---|---|
| `no_meshing_inference_measures_all_states` (via Prop 2) | *none* |
| `no_meshing_inference_measures_all_states_direct` (Breuer's) | `propext`, `Quot.sound` |

Breuer's route reasons by set extensionality at the union-law step — it must
produce an *equality of sets* `θ({s_A}) = {s}` — while the route through
Proposition 2 only ever moves elements in and out of sets, and so needs nothing.
So the derived proof is axiomatically cheaper and the direct one is
source-faithful. That is a real trade rather than a redundancy, which is why
neither is deleted. -/

/--
**The union-law step.** An exact measurement by a reading set is already achieved
by one of its singletons.

Breuer: *"Since `⋃_{s_A ∈ S_A} θ({s_A}) = θ(S_A) = {s}` there is a `s_A ∈ S_A`
such that `θ({s_A}) = {s}`."*
-/
public theorem exists_singleton_infer_eq_of_infer_eq
    {Ω : Type u} {A : Type v} (M : InferenceMap Ω A)
    {U : ReadingSet A} {s : Ω} (hU : M.infer U = {s}) :
    ∃ a ∈ U.1, M.infer (ReadingSet.singleton a) = {s} := by
  have hsU : s ∈ M.infer U := by rw [hU]; exact Set.mem_singleton s
  rw [M.infer_eq_union_singletons U] at hsU
  obtain ⟨a, haU, hsa⟩ := hsU
  refine ⟨a, haU, Set.eq_singleton_iff_unique_mem.mpr ⟨hsa, ?_⟩⟩
  intro t hta
  have htU : t ∈ M.infer U := by
    rw [M.infer_eq_union_singletons U]
    exact ⟨a, haU, hta⟩
  rw [hU] at htU
  exact htU

/--
**The meshing step.** A reading that pins a state down *is* that state's
restriction.

This is what Breuer's `θ({s_A}) = θ({θ({s_A})|_A})` rewrite accomplishes: under
meshing the reading `s_A` and the restriction `s|_A` are the same apparatus
state, so the singleton reading is a function of the state alone.
-/
public theorem eq_restrict_of_infer_singleton_eq
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M)
    {a : A} {s : Ω} (h : M.infer (ReadingSet.singleton a) = {s}) :
    a = restrict s := by
  have : Nonempty A := ⟨a⟩
  have hsa : s ∈ M.infer (ReadingSet.singleton a) := by
    rw [h]; exact Set.mem_singleton s
  exact (restrict_eq_of_mem_infer_singleton restrict M hm hsa).symm

/--
**Breuer Proposition 1, by the source's own argument.** Same statement as
`no_meshing_inference_measures_all_states`, proved directly rather than through
Proposition 2.

Given proper inclusion, take the two states `s ≠ s'` with `restrict s = restrict s'`.
Exact measurement supplies reading sets for each; the union law narrows them to
single readings `a` and `b`; meshing identifies `a = restrict s` and
`b = restrict s'`, so `a = b`. But then `{s} = θ({a}) = θ({b}) = {s'}`, which is
Breuer's contradiction.
-/
public theorem no_meshing_inference_measures_all_states_direct
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hproper : ProperInclusion restrict)
    (hm : Meshing restrict M) :
    ¬ MeasuresAllStates M := by
  rintro hall
  obtain ⟨s, s', hres, hne⟩ := hproper
  obtain ⟨U, hU⟩ := hall s
  obtain ⟨V, hV⟩ := hall s'
  obtain ⟨a, -, ha⟩ := exists_singleton_infer_eq_of_infer_eq M hU
  obtain ⟨b, -, hb⟩ := exists_singleton_infer_eq_of_infer_eq M hV
  have hab : a = b := by
    rw [eq_restrict_of_infer_singleton_eq restrict M hm ha,
      eq_restrict_of_infer_singleton_eq restrict M hm hb, hres]
  have hsingletons : ({s} : Set Ω) = {s'} := by rw [← ha, ← hb, hab]
  exact hne (Set.singleton_eq_singleton_iff.mp hsingletons)

/--
**Breuer Proposition 1, in the paper's printed form.** The source displays it as
an existential over global states:

`∃ s₀ ∈ S_O, ∀ S_A ∈ P(S_A) : θ(S_A) ≠ {s₀}`

— some state that no reading set pins down. `no_meshing_inference_measures_all_states`
states the same thing as a negated universal, which is the form the proof
produces; this is the source's shape, so a reader can cite the theorem as printed.

The two are classically equivalent and not constructively so: extracting the
witness needs `Classical.choice` via `push_neg`, whereas the negated-universal
form does not. That is the only reason both are here.
-/
public theorem exists_state_not_exactly_measurable
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hproper : ProperInclusion restrict)
    (hm : Meshing restrict M) :
    ∃ s : Ω, ∀ U : ReadingSet A, M.infer U ≠ {s} := by
  by_contra hcon
  push Not at hcon
  exact no_meshing_inference_measures_all_states restrict M hproper hm hcon

/--
**Breuer's Corollary**, the form he attaches to the Gödel analogy. §3.5, printed
directly after Proposition 2's proof:

> *"Under the assumption of proper inclusion, if all states are exactly
> measurable from inside the system then the inference map θ is contradictory
> (i.e., the meshing condition is violated)."*

Classically this is Proposition 1 rearranged — same three propositions, meshing
moved from hypothesis to conclusion — and the proof here is exactly that
rearrangement rather than the source's separate argument. It earns its own name
because the source's reading lives in this shape and not the other: an
inference map that measures everything is not merely unavailable, it is
*inconsistent*, and the apparatus state where consistency breaks is what Breuer
compares to the Gödel sentence.
-/
public theorem meshing_fails_of_measuresAllStates
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hproper : ProperInclusion restrict)
    (hall : MeasuresAllStates M) :
    ¬ Meshing restrict M := fun hm =>
  no_meshing_inference_measures_all_states restrict M hproper hm hall

/--
The Corollary with its failure witness, in the source's printed shape.

Breuer displays the conclusion as `(∃ s₀ ∈ 𝒮_O) : θ({s₀|_A})|_A ≠ {s₀|_A}` — the
offending apparatus state is exhibited as the restriction of a *global* state,
which is what makes it self-referential in his sense and available for the Gödel
comparison.

Reaching that shape needs surjectivity of the restriction as a hypothesis, and
here it cannot come from `Meshing.restrict_surjective`: meshing is the thing
being refuted. Breuer has it standing from §3.3 — *"`|A` describes a surjective
map from the states of O to the states of A"* — so requiring it here is the
source's own assumption, made explicit at the one place the module cannot derive
it. Without surjectivity the honest witness is an apparatus reading with no
global state behind it, which is `meshing_fails_of_measuresAllStates` unfolded.
-/
public theorem exists_state_meshing_failure_of_measuresAllStates
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hproper : ProperInclusion restrict)
    (hsurj : Function.Surjective restrict) (hall : MeasuresAllStates M) :
    ∃ s₀ : Ω,
      Set.image restrict (M.infer (ReadingSet.singleton (restrict s₀)))
        ≠ {restrict s₀} := by
  have hm := meshing_fails_of_measuresAllStates restrict M hproper hall
  unfold Meshing at hm
  push Not at hm
  obtain ⟨a, ha⟩ := hm
  obtain ⟨s₀, rfl⟩ := hsurj a
  exact ⟨s₀, ha⟩

end AISafetyAtlas.Knowledge.Embedded
