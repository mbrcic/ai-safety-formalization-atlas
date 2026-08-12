# Knowability: what a system can learn about itself

**Status: machine-checked.** Every Lean statement referenced here compiles with no
`sorry`, `admit`, local `axiom`, `native_decide`, or `@[implemented_by]` in its
trusted path, under Lean 4.31.0. Axiom profiles are given per result below; some
are axiom-free, some depend on `propext`, `Classical.choice`, `Quot.sound`.

## The question

"A system cannot fully know itself" is one of the most repeated claims in AI
safety, and one of the least precise. Read one way it is trivial. Read another it
is false — distributed systems record consistent global states routinely. Which
reading is correct depends on three things the slogan leaves out: *what* is to be
known, *from what evidence*, and *at what time*.

This cluster makes each of those explicit, and the results follow from the
distinctions rather than from any deep theorem. There is no diagonal argument
anywhere in it. The obstruction is **indistinguishability**: two situations the
observer cannot tell apart, about which the answer differs. That is a weaker and
more common phenomenon than self-reference, and it is why these results apply to
ordinary engineered systems and not only to systems rich enough to encode
arithmetic.

## The model

[`AISafetyAtlas.Knowledge`](../../AISafetyAtlas/Knowledge.lean) fixes three
objects: a state space `Ω`, an **observation** `observation : Ω → E`, and a
**target** `property : Ω → Y`.

`Knowable observation property` says the target is recoverable from the
observation, in **decoder form**: there is one rule `d : E → Y`, uniform in the
state, with `d (observation ω) = property ω` at every `ω`.

Decoder form is a deliberate choice. The alternative — defining knowability as
"the observation fibres refine the target fibres" — would make the central
characterization true by unfolding. Stating it with a decoder keeps it a theorem:

| | |
|---|---|
| `knowable_iff_no_collision` | knowable ⟺ no two states share an observation and differ in the target |
| `knowable_iff_factorsThrough` | the same, bridged to Mathlib's `Function.FactorsThrough` |

The negative direction has a certificate. `IndistinguishabilityWitness` packages a
colliding pair; `not_knowable_of_collision` and `not_knowable_of_witness` consume
one; `exists_witness_of_not_knowable` is the classical converse. So an
impossibility in this cluster is never an abstract non-existence — it names two
states.

`Determines` orders observations by informativeness, `Knowable.mono` transfers
knowability upward along it, and `not_knowable_comp` is the repair boundary:
**post-processing an unchanged observation cannot create knowability.** No amount
of computation over the same evidence helps.

## The five things the slogan conflates

Each layer isolates one, over the same kernel.

### 1. What is being known — whole state vs. one property

`knowable_id_iff_injective`: knowing the *entire* state is exactly injectivity of
the observation. Most safety questions are not that — they ask about one property,
and a property can be knowable when the state is not. Collapsing the two is the
first way the slogan misleads.

### 2. How much is left open — counting

[`Knowledge.Ambiguity`](../../AISafetyAtlas/Knowledge/Ambiguity.lean) replaces the
yes/no question with a count. `ambiguity observation property e` is the number of
target values consistent with reading `e`.

- `knowable_iff_ambiguity_le_one` — knowability *is* ambiguity at most one.
- `card_image_le_of_knowable` — a **counting obstruction**: if the target takes
  more values than the observation can, no decoder exists. This one never names a
  colliding pair, which is exactly its use: you can refute exactness by comparing
  two cardinalities, without exhibiting anything.
- `ambiguity_le_of_comp` — coarsening never lowers ambiguity.

Finite counting only. No probability, no entropy, no rate.

### 3. When — reading time vs. target time

[`Knowledge.Temporal`](../../AISafetyAtlas/Knowledge/Temporal.lean) separates two
sentences prose treats as one:

- `KnowableFrom observe target t s` — the target **as of `s`**, from evidence **at
  `t`**;
- `KnowableAt … t` — the contemporaneous case, `KnowableFrom … t t`.

`CollisionAt` is a collision between the reading at `t` and the target at `t`;
`not_knowableAt_of_collisionAt` refutes contemporaneous knowledge from it and is
**axiom-free**, with the classical converse `collisionAt_of_not_knowableAt`.
`EvidenceMonotone` says later evidence determines earlier, and `knowableFrom_mono`
transfers knowability forward under it.

`DelayedKnowable` is the escape: not knowable when current, knowable from later
evidence. It is *inhabited* — `Examples/Knowledge/Temporal.lean` builds a two-time
model with cumulative evidence throughout where the time-0 target is unknowable
when current and exactly knowable from time-1 evidence.

**This is why the slogan is wrong as usually said.** The defensible obstruction is
contemporaneous. Chandy–Lamport snapshots recover a consistent global state while
the computation continues, by giving up contemporaneity and recording a cut rather
than an instant — machine-checked in Isabelle/AFP as `LAND-CL-001`.

Prior art, recorded as `NC-007`: this indexing is a measure-free shadow of
Mathlib's filtration theory. No novelty is claimed for time-indexed information.
What the layer has that a filtration does not is that it needs no measurable
structure, and that cumulativity is `Determines` rather than σ-algebra inclusion —
because the evidence types at different times are different types.

### 4. Accumulating over a window

[`Knowledge.Accumulation`](../../AISafetyAtlas/Knowledge/Accumulation.lean) asks
about a *window* of targets rather than one. Ambiguity is bracketed:
`ambiguity_le_pairTarget_left` (widening never reduces it) and
`ambiguity_pairTarget_le_mul` (never more than the product of the steps).
`ambiguity_le_of_evidenceMonotone` bounds it along time under cumulative evidence.

**Growth is not a theorem here.** Whether ambiguity actually grows depends on
whether each step adds a distinction the observation cannot see — a statement
about dynamics this cluster does not have. Both extremes are exhibited: a blind
observer doubling per step and hitting the product ceiling, and a fully informed
one staying at `1` forever.

### 5. Where the observer is — embedded, and self-referential

Everything above treats the observation as an arbitrary map. Two layers stop
doing that.

**[`Knowledge.Embedded`](../../AISafetyAtlas/Knowledge/Embedded.lean)** is
Breuer 1995's abstract measurement model: a restriction from global states to
apparatus states, an inference map on reading sets, and the meshing condition.
Every statement §3.5 displays — Propositions 1 and 2, the LEMMA, the Corollary —
is graded `EQUIVALENT` (`LAND-SELFMEAS-002`); source map and residuals in
[`self-measurement-kernel.md`](../provenance/self-measurement-kernel.md).

Proper inclusion — two distinct global states with the same apparatus reading — is
**model data, not derived**. Breuer's own footnote 4 gives a contained apparatus
without it. Deriving it under stated hypotheses is `.Composition` (a remainder
that varies independently) and `.Finite` (a strict cardinality gap), graded
separately as atlas modelling.

**[`Knowledge.SelfReference`](../../AISafetyAtlas/Knowledge/SelfReference.lean)**
is the self-referential case proper: the state is `Model × Rest`, and the observer
reads its own `Model` component. Self-reference is then not an added axiom — the
target `id` includes `Model`, so a complete self-model must model itself.

`selfComplete_iff_subsingleton_rest`: an embedded observer completely knows the
state it is in **iff there is nothing else in the state**. Finitely,
`card_rest_le_one_of_selfComplete` gives `|Rest| ≤ 1`, proved through the counting
obstruction rather than by a fresh argument.

Read as a design law: a system whose self-model is part of its own state buys
completeness only by having nothing to be complete about. Note this is a
**characterization**, not a denial — the degenerate case genuinely holds, which is
the precise sense in which "a system cannot model itself" is false as usually
said.

## Proved / not proved

### Proved

- Knowability is exactly no-collision, with an extractable witness on failure.
- Post-processing cannot create knowability.
- Whole-state knowledge is injectivity.
- Knowability is ambiguity ≤ 1; a cardinality gap suffices without naming a pair;
  coarsening never lowers ambiguity.
- Contemporaneous knowledge fails exactly on a contemporaneous collision, and
  delayed knowledge can succeed where contemporaneous fails — exhibited, not
  asserted.
- Window ambiguity is bracketed between non-decreasing and the product of steps.
- Under Breuer's meshing condition, proper inclusion rules out exact measurement
  of every global state — by two independent proof routes, differing in axioms.
- An embedded self-model is complete iff the remainder is a subsingleton.

### Not proved, and not claimed

- **No dynamics.** No transition relation anywhere. Nothing says *why* a collision
  arises or how a target moves between observations. A causal-innovation
  condition — the target changed since the last evidence-generating event — is
  what would have to *imply* these collisions, and it is not stateable here.
- **No achievability in Lean.** The constructive side is `LAND-CL-001`, reproduced
  in Isabelle, with no Lean surface. It is a `BOUNDARY_PARTNER`, not a formal
  dual: the two do not share a model. See
  [relations](../status/relations.md).
- **No probability, entropy, or rates.** Finite counting only.
- **No physical claim.** Nothing says a physically contained apparatus must have a
  colliding restriction. Bekenstein-style bounds motivate finite models; they do
  not yield `card A < card Ω`, and `.Finite` deliberately does not encode any such
  implication.
- **No AI-system reading.** Self-monitoring, introspection, interpretability and
  wireheading detection do not follow from anything here without a separate
  reviewed bridge. `LAND-CRMDP-KNOW-001` links wireheading to the kernel as
  *mathematics* — it is not a bridge and carries no system claim.
- **Nothing about consciousness.** Incompleteness of a self-model is a statement
  about a projection, and every partially observed embedded system has it — which
  is exactly why it cannot be evidence of anything phenomenal.

## Where this is used

`Oversight.JointObservation`'s coverage laws are this kernel applied to a
coalition's evidence: `Covers` and `Refines` are definitionally `Knowable` and
`Determines`, so the coverage and repair-boundary results discharge by calling the
kernel rather than repeating a factorization argument. See
[joint observation](joint-observation-model.md).

`Wireheading.ObservationLimits` reads the CRMDP complement pair as a collision:
the true return does not factor through the observed history, over a class
containing a return-disagreeing complement pair.

Row-by-row structure, including which results are characterizations rather than
point impossibilities, is generated in [relations](../status/relations.md).
