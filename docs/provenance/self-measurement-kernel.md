# Embedded self-measurement: knowability skeleton, Breuer abstract core, and physical bridges

This note records deliberately different in-tree artifacts. It is also a
scope ledger: a later contributor should be able to tell what has already been
formalized, what was intentionally left out, and where the source material can
be retrieved.

## Source and retrieval

| Field | Value |
|---|---|
| Paper | T. Breuer, “The Impossibility of Accurate State Self-Measurements,” *Philosophy of Science* 62(2), 197–214 (1995) |
| Stable catalogue record | [PhilPapers](https://philpapers.org/rec/BRETIO-3) |
| PDF used for the source audit | [Breuer95.pdf](https://cqi.inf.usi.ch/qic/Breuer95.pdf) |
| Registry source key | `breuer-1995-self-measurement` |
| Source audit date | 2026-08-11 |
| Formalization search | Mathlib, Isabelle/AFP, Rocq/Coq, HOL4, HOL Light, Agda stdlib, and general web; no machine-checked Breuer formalization was found |

The failed search is recorded as discovery evidence, not as a proof that no
other formalization exists. A future contributor should repeat the search
before making a stronger novelty claim.

## What is implemented

### 1. Generic knowability specialization

Module: [`AISafetyAtlas.Knowledge`](../../AISafetyAtlas/Knowledge.lean)

Artifact: [`LAND-SELFMEAS-001`](../../registry.yaml)

| Declaration | Content |
|---|---|
| `knowable_id_iff_injective` | Exact knowledge of the whole state is equivalent to injectivity of the observation |
| `not_knowable_state_of_nontrivial_remainder` | A `Read × Rest` state with two possible remainder values is not recoverable from `Prod.fst` |
| `remainderWitness` | The same obstruction as an explicit colliding-pair certificate |

This is an information-fibre skeleton. It does **not** model an apparatus,
Breuer's inference map, meshing, dynamics, quantum states, or an embedded
physical subsystem. Its relationship to Breuer is therefore not graded as
exact; the row is retained as a narrower specialization of the generic
`Knowable` kernel.

### 2. Breuer's abstract set-theoretic measurement core

Module: [`AISafetyAtlas.Knowledge.Embedded`](../../AISafetyAtlas/Knowledge/Embedded.lean)

Artifact: [`LAND-SELFMEAS-002`](../../registry.yaml)

The module follows the paper's abstract setup rather than replacing it with a
single decoder:

| Declaration | Paper role |
|---|---|
| `ReadingSet` and `ReadingSet.singleton` / `ReadingSet.univ` | Nonempty sets of possible apparatus readings |
| `Restriction` | Map from global states to apparatus states |
| `InferenceMap` | Inference map from readings to sets of compatible global states, with the union-of-singletons convention |
| `ProperInclusion` | Two distinct global states with the same restriction |
| `Meshing` | Singleton inference sets restrict back to the reading that generated them |
| `Meshing.restrict_surjective` | The exact meshing equation entails the source's surjective restriction setup |
| `ExactlyMeasurable` | Some nonempty reading set infers a singleton global state |
| `MeasuresAllStates` | Every global state is exactly measurable |
| `Distinguishes` | Mutually separating reading sets for two global states |
| `no_meshing_inference_distinguishes` | Breuer Proposition 2: equal restrictions cannot be distinguished by a meshing map |
| `no_meshing_inference_measures_all_states` | Breuer Proposition 1: proper inclusion plus meshing rules out measuring every state |

The proofs are new Lean proofs of this abstract core. They are not presented as
a full formalization of every claim in the paper.

### 3. Physical bridges (product complement and finite cardinality)

Modules: `Knowledge.Embedded.Composition`, `Knowledge.Embedded.Finite`

Artifact: [`LAND-SELFMEAS-003`](../../registry.yaml) — `RELATED` modelling layer,
not a rewrite of §2. See *Physical bridges* below for the statement table,
non-claims, and Bekenstein motivation-only policy.

### Source statements, transcribed

Verified against the PDF on 2026-08-11. Section titles confirmed:
§3.2 *Description of Measurements*, §3.3 *Measurements from Inside*,
§3.5 *A Consistency Condition and the Main Results* — the last containing the
meshing condition and both propositions.

The available PDF is a scan whose text layer renders the **prose reliably and
the mathematical notation as OCR noise**. The prose is transcribed verbatim from
the text layer; the displayed formulas were **read off the page by a human**
(2026-08-11) rather than taken from the OCR, which garbled them.

> **PROPOSITION 1:** The assumption of proper inclusion and the meshing
> condition imply that not all states of a system can be measured exactly by an
> internal observer.

> **PROPOSITION 2:** Let s₁, s₂ be two states of O fulfilling s₁|A = s₂|A. Then
> there is no inference map O, and thus no measurement using as apparatus A,
> which can distinguish s₁ and s₂.

### Displayed formulas, and how the Lean compares

Page 208, §3.5, read at 300 dpi on 2026-08-11 (`pdftoppm -r 300`). The PDF's text
layer garbles the notation, so the page is rendered as an image and the formulas
read off it. Hand transcription from the text layer is not reliable here and
should not be used.

**Notation, and the distinction the OCR destroyed.** `θ` is the inference map and
`s|_A` the restriction. Breuer uses *script* `𝒮_O` and `𝒮_𝒜` for the global and
apparatus **state spaces**, and *roman* `S_A`, `S¹_A`, `S²_A` for individual
**reading sets** — elements of `𝒫(𝒮_𝒜)`. The two collapse to the same OCR token,
which is where the confusion in this note came from.

| Source | Lean | Verdict |
|---|---|---|
| **Prop 1** `∃ s₀ ∈ 𝒮_O, ∀ S_A ∈ 𝒫(𝒮_𝒜) : θ(S_A) ≠ {s₀}` | `exists_state_not_exactly_measurable`, with `no_meshing_inference_measures_all_states` as the negated-universal form the proof produces | printed form stated directly |
| **LEMMA** `(∀ s_A) : θ({s_A}) = {s ∈ 𝒮_O : s ∈ θ(𝒮_𝒜), s\|_A = s_A}` | `infer_singleton_eq_of_meshing` | same set equality, with `θ(𝒮_𝒜) = M.infer ReadingSet.univ` |
| **Prop 2** `(∀θ) : ((∄ S¹_A, S²_A ∈ 𝒫(𝒮_𝒜)) : θ(S¹_A) ∋ s₁ ∉ θ(S²_A), θ(S²_A) ∋ s₂ ∌ θ(S¹_A))` | `¬ Distinguishes M s₁ s₂` | same, with `U := S¹_A`, `V := S²_A` |
| **Corollary** `(∀s ∈ 𝒮_O)(∃S_A) : θ({s_A}) = {s}` implies `(∃s₀ ∈ 𝒮_O) : θ({s₀\|_A})\|_A ≠ {s₀\|_A}` | `meshing_fails_of_measuresAllStates`, with `exists_state_meshing_failure_of_measuresAllStates` for the displayed witness | printed conclusion needs the §3.3 surjectivity; see below |

**The Corollary is the fourth displayed statement, and the paper has no fifth.**
Proposition 1, the LEMMA, Proposition 2 and this Corollary are the only numbered
or displayed results in the paper; §4 and §5 apply them to quantum and
universal-validity questions without adding one. Classically the Corollary is
Proposition 1 with meshing moved from hypothesis to conclusion, so its content
was already in the tree — but the *shape* was not, and the shape is what Breuer
attaches his Gödel analogy to: an inference map measuring everything is
inconsistent rather than merely unavailable, and the apparatus state where
consistency breaks is his analogue of the Gödel sentence.

Its printed conclusion localizes that state as `s₀|_A`, the restriction of a
global state. Reaching that form needs restriction surjectivity as a hypothesis,
and `Meshing.restrict_surjective` cannot supply it here because meshing is what
is being refuted. Breuer has surjectivity standing from §3.3, so
`exists_state_meshing_failure_of_measuresAllStates` takes it explicitly — the one
place in this module where a source assumption is required rather than derived.

Three things this settles that the prose alone did not.

**Prop 2 really is a negated existential.** The source writes `∄` over a pair of
reading sets with mutual separation, which is exactly `¬ Distinguishes`. Had it
been an unnegated existential, or a single separating set rather than a pair, our
conclusion would have been the wrong shape.

**The `P(S_A)` quantifier is over nonempty subsets.** The propositions write the
full powerset, but §3.2 defines θ on *"apparatus states (except the empty set)"*.
So `ReadingSet A = {U : Set A // U.Nonempty}` is faithful, not a convenience
restriction. (It would also be harmless either way: the union law forces
`θ(∅) = ∅`, which is never a singleton, so the empty case of Prop 1 is vacuous.)

**Our predicates are the paper's definitions, not paraphrases.** §3.2: a state is
*"exactly measurable if … there exists a set S_A of apparatus states referring
uniquely to the state s₀, i.e. θ(S_A) = {s₀}"* — that is `ExactlyMeasurable`. And
an experiment *"is said to be able to distinguish the states s₁, s₂ if there is
one set S¹_A … referring to s₁ but not s₂, and another set S²_A referring to s₂
but not to s₁"* — that is `Distinguishes`.

**The LEMMA's inner set is `θ(𝒮_𝒜)`, the whole apparatus space.** Not `θ(S_A)`
for an individual reading set, and not `θ(𝒮_O)` — the last cannot typecheck,
since `θ` eats sets of *apparatus* states. The rendered page reads

> `(∀ s_A) : θ({s_A}) = {s ∈ 𝒮_O : s ∈ θ(𝒮_𝒜), s|_A = s_A}`

and the paper's own proof of the converse inclusion removes any doubt:

> *"Conversely, let `s ∈ 𝒮_O` be such that `s|_A = s_A` for some `s_A` and
> `s ∈ θ(𝒮_𝒜)`. Then there is a `s'_A ∈ 𝒮_𝒜` such that `s ∈ θ({s'_A})`."*

That step is the union law applied over the full apparatus space, which is only
available if the argument *is* that space. So `θ(𝒮_𝒜)` is `M.infer ReadingSet.univ`,
which is what the Lean encodes. `infer_singleton_eq_of_meshing` states the LEMMA
publicly as the set equality the paper displays, rather than leaving only its two
halves as private helpers.

**Breuer's Prop 1 proof is direct.** The page shows him proving Proposition 1
*before* the LEMMA, by a chain of meshing rewrites:

> `{s} = θ({s_A}) = θ({θ({s_A})|_A}) = θ({s|_A}) = θ({s'|_A}) = θ({θ({s'_A})|_A})
> = θ({s'_A}) = {s'}`, contradicting `s ≠ s'`.

The LEMMA then follows and serves Proposition 2. The tree carries **both** orders:
`no_meshing_inference_measures_all_states` derives Proposition 1 from
Proposition 2 by exhibiting the two exact measurements as distinguishing reading
sets, and `no_meshing_inference_measures_all_states_direct` follows the chain
above. They prove the same statement and differ in axioms — see *Breuer's own
proof of Proposition 1* below. Proof-structure fidelity therefore holds for the
LEMMA's role in Proposition 2 *and* for Proposition 1, by the direct route only.

* Breuer's **footnote 4** supplies his own counterexample: naturals as apparatus
  states, even naturals as global states, restriction `n ↦ 2n`, inference
  `{2n} ↦ {n}` — meshing satisfied, proper inclusion violated. That is the same
  separation our second non-vacuity model exhibits, arrived at independently.

One rendering difference to note rather than hide: Proposition 2 is printed
quantifying over all inference maps, with meshing a **standing assumption of
§3.5**; the Lean statement carries `Meshing` as an explicit hypothesis. That is
the same content made explicit, which is what a formalization should do — but it
is a difference in presentation, not a transcription.

### Hypotheses and shape, against the printed statements

Two places where fidelity is easy to lose, and how the tree stands on each.

**Neither proposition assumes `Nonempty A`.** Neither printed statement has such
a side condition. The instance is recovered inside each proof from the reading
set the hypothesis already supplies, since `ReadingSet` carries nonemptiness; a
formalization routed through `ReadingSet.univ` at the top level would need it as
a hypothesis instead, and would then be stronger than the source.

Absence of the hypothesis is **faithfulness, not reach**: a restriction `Ω → A`
with `A` empty forces `Ω` empty, so the extra case has no states to quantify over
and no consumer can reach it. `Examples/NonVacuity.lean` records why no witness
for that case can exist, so nobody goes looking for one. What it buys is a
statement carrying the source's hypotheses and no others.

**Proposition 1 is stated in both shapes.** The source displays an existential —
`∃ s₀ ∈ S_O, ∀ S_A : θ(S_A) ≠ {s₀}` — while the negated universal
`¬ MeasuresAllStates` is the form the proof produces.
`exists_state_not_exactly_measurable` supplies the printed form and
`no_meshing_inference_measures_all_states` the produced one. Both are kept: they
are classically equivalent and not constructively so, since extracting the
witness needs `Classical.choice` and the negated-universal form does not.

### Method for reading the page

The PDF's text layer garbles the notation. `pdftoppm -r 300 -png` renders the
page legibly and the formulas can be read off the image directly. Every displayed
formula in this note was checked that way, on 2026-08-11. Do not transcribe from
the text layer.

### Breuer's own proof of Proposition 1

`no_meshing_inference_measures_all_states_direct` follows the source's argument
instead of routing through Proposition 2. His chain

> `{s} = θ({s_A}) = θ({θ({s_A})|_A}) = θ({s|_A}) = θ({s'|_A}) = θ({θ({s'_A})|_A}) = θ({s'_A}) = {s'}`

is carried by two lemmas, one per step it performs:

| Step | Source | Lean |
|---|---|---|
| union law narrows a reading *set* to a single reading | *"Since `⋃_{s_A∈S_A} θ({s_A}) = θ(S_A) = {s}` there is a `s_A ∈ S_A` such that `θ({s_A}) = {s}`"* | `exists_singleton_infer_eq_of_infer_eq` |
| meshing identifies that reading as the restriction | the `θ({s_A}) = θ({θ({s_A})|_A})` rewrite | `eq_restrict_of_infer_singleton_eq` |

With both in hand the chain collapses: `s` and `s'` have the *same* singleton
reading, so `{s} = {s'}`.

Both routes are kept, and the axiom profiles say why — the difference runs
against the source:

| Route | Axioms |
|---|---|
| `no_meshing_inference_measures_all_states` (via Proposition 2) | none |
| `no_meshing_inference_measures_all_states_direct` (Breuer's) | `propext`, `Quot.sound` |

Breuer's argument needs set extensionality at the union-law step, since it must
produce the set equality `θ({s_A}) = {s}`. The route through Proposition 2 only
moves elements in and out of sets and needs nothing at all. So the derived proof
is axiomatically cheaper while the direct one is source-faithful. Recorded rather
than smoothed over: it would be easy to present the direct proof as strictly
better because it is the paper's, and it is not.

### Still open (paper scope)

Nothing from §3.5 remains open in the abstract core: every statement the paper
displays is mechanized, the Corollary included. §4 and §5 display none — they
apply Propositions 1 and 2 to the quantum and universal-validity questions.

`LAND-SELFMEAS-002` is therefore graded `EQUIVALENT`. Stop rule 3 below permits
promotion above `RELATED` on two conditions — matching the source model and
recording the exact scope delta — and both are met: the Lean model *is* §3.2's
abstraction rather than a re-encoding of it, and the delta is on the row. The
promotion satisfies that rule; it does not waive it.

`EXACT` is declined, and the reason is not omission but hypotheses. Breuer
assumes surjectivity in §3.3 and meshing in §3.5; this module assumes meshing
alone and derives surjectivity, so its theorems are strictly stronger than the
printed ones. The Corollary's witness form then takes surjectivity back
explicitly, because it cannot be derived where meshing is the thing being
refuted. A grade meaning *the source statement* should not be applied to
statements that deliberately carry different hypotheses in both directions.

Physical *modelling bridges* that *derive* proper inclusion under explicit extra
hypotheses live in separate modules and a separate registry artifact
(`LAND-SELFMEAS-003`); they are not retroactively Breuer’s theorem.

### Physical bridges — §3.4 lineage

The finite-cardinality bridge is **not** an atlas invention. Breuer raises the
argument himself in §3.4,
*A First Attempt*: exact measurability of all states needs a surjection from the
apparatus states onto the system states, proper inclusion makes the system
states strictly more numerous, and — his words —

> "If [there are] finitely many possible states, this already excludes the
> possibility of exact measurement of all states from inside the observed
> system."

That is what `Knowledge.Embedded.Finite` states. What makes it a bridge rather
than the paper's result is where §3.4 goes next: Breuer treats the finite case
as a route he does not take. For infinite state spaces he considers requiring
continuity, observes that in classical mechanics this forces the phase spaces of
`A` and `O` to share a dimension — impossible under proper inclusion — concludes
that exact measurability would then need an infinite-dimensional phase space,
and drops continuity altogether: *"Instead I take an entirely different
approach."* That approach is §3.5's meshing condition, and §3.5 is what
`LAND-SELFMEAS-002` grades against.

So the honest lineage is: §3.4 finite argument reproduced in
`LAND-SELFMEAS-003`, §3.4 continuity/dimension argument not reproduced at all,
§3.5 meshing route graded separately. The product-complement layer alongside it
has no §3.4 counterpart and remains atlas modelling.

### Physical bridges (not Breuer’s §3.5 core)

Modules:

* [`AISafetyAtlas.Knowledge.Embedded.Composition`](../../AISafetyAtlas/Knowledge/Embedded/Composition.lean)
* [`AISafetyAtlas.Knowledge.Embedded.Finite`](../../AISafetyAtlas/Knowledge/Embedded/Finite.lean)

Artifact: [`LAND-SELFMEAS-003`](../../registry.yaml)

| Layer | Content |
|---|---|
| Dichotomy | Exact whole-state knowledge ⇔ restriction injective; proper inclusion ⇔ non-injective |
| Composition | `Ω ≃ A × R`, with both literal-product and arbitrary-equivalence readout; nontrivial remainder ⇒ `ProperInclusion` ⇒ Breuer Prop. 1 under meshing; bijective restriction ⇒ fibre inference is meshing and measures all states |
| Finite | Finite `|A| < |Ω|` ⇒ `ProperInclusion` (pigeonhole); corollary to Prop. 1 under meshing |

The composition layer also exposes `equivalentProductRestriction` and its two
nontrivial-remainder corollaries, so an application need not make its global
state type definitionally equal to a product. The positive boundary is packaged
by `meshing_and_measuresAll_fibreInference_of_bijective` in addition to its
separate injective and surjective halves.

**What these do not claim.** They do **not** say every physically contained
apparatus has a nontrivial remainder or a strict cardinality gap. A contained
subsystem can encode the whole state, be perfectly correlated with the rest, or
be modelled so the remainder is a singleton. The defensible universal reading is
only: every model that satisfies a nontrivial-complement or strict operational
cardinality hypothesis has an unresolvable exact self-measurement ambiguity
(under meshing, for the Breuer measurement form).

**Bekenstein.** Entropy/energy bounds (Bekenstein 1981 and later overviews)
motivate *finite operational* models in applications. They do **not** by
themselves prove `|A| < |Ω|` for every physical subsystem: the bound depends on
energy, region, and operational distinguishability assumptions
([Bekenstein 1981](https://www.osti.gov/biblio/6978647);
[Scholarpedia](https://www.scholarpedia.org/article/Bekenstein_bound);
[arXiv:1804.10623](https://arxiv.org/abs/1804.10623)). Cite for motivation;
do not encode `Bekenstein ⇒ cardinality gap` without a separate physical model.

Non-vacuity for the bridges is in `Examples/NonVacuity.lean` (product remainder
and `|Unit| < |Bool|`).

### Meshing and surjectivity — resolved against the source

The encoded `Meshing` is exactly Breuer's condition, not a bundling of two source
conditions. The proposition symbols on the scan are unreadable but **the defining
paragraph is legible**:

> §3.5: *"So meshing can be written: `∀ s_A ∈ 𝒮_𝒜 : {s|_A : s ∈ θ({s_A})} = {s_A}`."*

Script `𝒮_𝒜` is the apparatus state space; the quantifier ranges over individual
apparatus states, not over reading sets.

Exact set equality, not inclusion — which is precisely `Meshing`. And
surjectivity is not something the formalization smuggled in: Breuer states it
independently in §3.3, *"So `|A` describes a surjective map from the states of O
to the states of A"*, before meshing is introduced at all.

The consequence favours the encoding. Where the paper assumes **surjectivity and
meshing**, `Knowledge.Embedded` assumes **meshing alone** and proves surjectivity
from it (`Meshing.restrict_surjective`). The mechanized hypotheses are therefore
no stronger than the source's, so the no-go results are not weakened by a hidden
extra assumption.

### Non-vacuity witness

`AISafetyAtlas.Examples.NonVacuity` contains a compile-time witness satisfying
`Meshing` and `ProperInclusion` simultaneously: global states are `Bool`, the
apparatus has the single reading `Unit.unit`, restriction is constant, and each
nonempty reading set infers `Set.univ`. Proper inclusion is witnessed by
`false` and `true`. This confirms that the hypotheses of the two no-go results
are jointly satisfiable; the propositions are not merely vacuous consequences
of an inconsistent measurement model.

## What is intentionally omitted

The following material is available in the paper but is not in the current
Atlas module:

* a physical construction of classical apparatus and observed-system state
  spaces;
* time evolution, measurement dynamics, or a deterministic/stochastic process
  model;
* the quantum/Hilbert-space and density-operator treatment;
* the EPR-correlation application and its physical interpretation;
* the paper's broader discussion of universal validity, epistemology, and
  philosophical consequences;
* any claim that physical subsystem containment automatically implies
  non-injectivity—the implementation takes the restriction map and its
  `ProperInclusion` witness as explicit model data;
* an AI-system or consciousness interpretation. Such a reading would require a
  separate reviewed bridge and is not inherited from the Lean theorem.

These omissions are deliberate. They keep the module reusable for arbitrary
state spaces and inference maps and prevent a source-level abstract theorem
from being advertised as a quantum or real-system result.

### Menu of unformalized paper material

Three of the paper's nine subsections are mechanized: §3.2, §3.3 and §3.5, plus
§3.4's finite argument as a separate bridge row. What follows is everything
else, with the reason it was skipped and what taking it would buy. Nothing here
is scheduled; it is a menu, and an entry being listed is not a claim that it
should be cooked.

| § | Material | Why not formalized | What it would buy |
|---|---|---|---|
| §2.1–2.2 | Popper, Rothstein, Dalla Chiara, Peres–Zurek on non-self-predictability and relative universal validity | Literature critique, not theorem statements. Each cited result is its own paper and would need its own catalogue row before any relation could be typed | The comparison most likely to be assumed already true. Breuer presents his result as *explaining* why non-self-predictability holds; a typed relation would settle whether Propositions 1–2 imply it or merely rhyme with it |
| §3.1 | Self-reference in physical theories | Framing prose; no statement to grade | Nothing directly. Useful only as wording for a guide |
| §3.4 | Continuity route: continuity forces equal phase-space dimension, which proper inclusion forbids, so exact measurability needs an infinite-dimensional phase space | Breuer abandons it — *"Since this case is difficult to handle I will drop the assumption of continuity altogether"* — and it needs topology and dimension theory the tree does not carry | A second, independent obstruction for the infinite case, where the finite bridge says nothing. Would extend `LAND-SELFMEAS-003` past its cardinality hypothesis, at the cost of a real dependency |
| §4 | EPR correlations, Schmidt decomposition, quantum strengthening | Needs Hilbert spaces and density operators; and §4 opens by saying the earlier results already hold "for classical and for quantum mechanics, and irrespective of the character of the time evolution", so this layer is narrower, not more general | The paper's quantum-specific results, which the atlas currently cannot claim at all. Large dependency for a result that does not generalize the core |
| §5.1–5.2 | Universal validity revisited; universal validity of quantum mechanics | The paper's thesis rather than its engine. Formalizing it means formalizing "theory", "universally valid" and "observer" — a modelling commitment far larger than the propositions | Breuer's actual conclusion. Everything the atlas holds is the machinery underneath a claim it does not make |
| §3.2–3.5, physical layer | Construction of apparatus and observed-system state spaces; time evolution; deterministic or stochastic dynamics | The propositions are single-slice and quantify over no transition function; the paper uses dynamics only to argue the result is insensitive to it, which requires having a dynamics first | Instances rather than strength. The abstract propositions already hold for every model satisfying the hypotheses |

Two entries are worth more than the others if this is ever revisited: §2, because
the relation to non-self-predictability is the one a reader will assume without
checking; and §3.4's continuity route, because it is the only listed item that
would strengthen a *statement* the atlas already has.

## Non-vacuity

Both propositions are negative — *no* meshing map does X — so each needs
witnesses on **both** sides before it says anything. The anonymous witnesses
live in
[`Examples/NonVacuity.lean`](../../AISafetyAtlas/Examples/NonVacuity.lean).

| Side | Model | Inhabits |
|---|---|---|
| Hypotheses | `Ω := Bool`, `A := Unit`, `infer _ := Set.univ` | `Meshing`, `ProperInclusion` |
| Conclusions | `Ω := A := Bool`, `restrict := id`, `infer U := U.1` | `Meshing`, `MeasuresAllStates`, `Distinguishes`, and `¬ ProperInclusion` |

The second row is the one that matters. Had `MeasuresAllStates` or
`Distinguishes` been uninhabited, both propositions would hold for free and
`ProperInclusion` would carry no weight. The second model also shows the
hypothesis is exactly what does the work: drop proper inclusion — let the
apparatus read the whole state — and the map measures every state and
distinguishes the pair.

The source also describes the restriction map as surjective. The implementation
does not duplicate that as a conjunct of `ProperInclusion`: the exact meshing
equation already entails it, via
`Meshing.restrict_surjective`. Thus under the hypotheses of either proposition
the encoded model has the same surjective restriction condition as the source.

Adding these surfaced an API defect, now fixed: `ReadingSet.singleton` was
`public` but not `@[expose]`, and `Meshing`, `ExactlyMeasurable` and
`Distinguishes` are *stated* in terms of it, so no consumer outside the module
could discharge any of them.

## Relationship and reuse

`Knowledge.Embedded` is a stronger modeling layer **built on** the generic
`Knowable` API: it represents an observer by a restriction map and an inference
map, while `Knowledge` only asks whether a property factors through an
observation.

That dependency is real, not nominal. `not_knowable_state_of_properInclusion`
discharges proper inclusion through the kernel's `not_knowable_of_collision`,
so removing the `AISafetyAtlas.Knowledge` import breaks the build. Until that
bridge was added the import was dead and this paragraph was false: the two
modules were siblings that happened to share a namespace prefix. The bridge is
deliberately weaker than `no_meshing_inference_measures_all_states` — decoder
factorization is not exact measurement over reading sets, and it needs no
meshing hypothesis — so it connects the layers without pretending they say the
same thing.

The two artifacts can also be reused independently:

* use `Knowledge` for arbitrary observation maps, collision certificates,
  monotonicity, and later temporal/embedded knowability work;
* use `Knowledge.Embedded` when the question is specifically about state
  inference, meshing, exact measurement, or Breuer-style proper inclusion.

The faithful abstract core is recorded as `EQUIVALENT`, not `EXACT`: every
displayed §3.5 statement is present, over the paper's own model, with hypotheses
deliberately weaker than printed in the propositions and explicitly stronger in
the Corollary's witness form. The physical and quantum layers remain outside
this module. No AI-safety conclusion follows without a separately reviewed
bridge.

## Stop rules

1. Do not call `Knowledge.knowable_id_iff_injective` or the product remainder
   lemma “Breuer's theorem”; cite `Knowledge.Embedded` for the abstract core.
2. Do not add quantum, dynamical, or physical-apparatus structure to the
   generic `Knowledge` facade merely to chase source parity; add a separate
   module and artifact if a concrete consumer requires it.
3. Do not promote the relationship above `RELATED` without matching the source
   model and recording the exact scope delta.
4. Do not infer an AI-system or consciousness result from either module without
   a reviewed bridge package.
