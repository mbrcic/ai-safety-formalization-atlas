# Knowability: what a system can learn about itself

**Status: machine-checked.** Every Lean statement referenced here compiles with no
`sorry`, `admit`, local `axiom`, `native_decide`, or `@[implemented_by]` in its
trusted path, under Lean 4.33.0. Axiom profiles are given per result below; some
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

## Related, but different: Wolpert's physical knowledge

[`Inference.PhysicalKnowledge`](../../AISafetyAtlas/Inference/PhysicalKnowledge.lean)
formalizes a different notion from Wolpert 2018. A certificate chooses a setup
block for each realized target value, answers that value's probe correctly on
the whole block, and requires nonempty true/false intersections with a context
`W`. The quantifiers do not reduce to `Knowable`'s one uniform decoder, and the
library proves neither direction between the notions.

The downstream
[`Epistemic`](../../AISafetyAtlas/Inference/PhysicalKnowledge/Epistemic.lean)
module shows the useful distinction: known premises may force a consequence to
be true without making it physically known. Corollaries 20–24 and an executable
distribution counterexample are mechanized. The
[`Event`](../../AISafetyAtlas/Inference/PhysicalKnowledge/Event.lean) module
also exposes a source boundary rather than smoothing it over: Corollary 25's
positive-introspection construction can produce an inadmissibly constant event,
and its natural singleton-image extension has a machine-checked countermodel.
The itemized source map is
[`wolpert-2018-knowledge.md`](../provenance/wolpert-2018-knowledge.md).

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

- **No dynamics in the self-measurement layer.** No transition relation anywhere
  in `Knowledge` or its specializations. Nothing there says *why* a collision
  arises or how a target moves between observations. A causal-innovation
  condition — the target changed since the last evidence-generating event — is
  what would have to *imply* these collisions, and it is not stateable in this
  kernel. `Compositional.Networks` does have a transition relation and does
  reach this kernel, which is why the exclusion is scoped rather than flat: what
  it projects in is a *contemporaneous* question — what a node's depth-`n` view
  settles about its state after `n` rounds — and not a claim about how a target
  moves while an observer watches it.
- **No achievability for the self-measurement results in Lean.** The constructive
  side of *those* is `LAND-CL-001`, reproduced in Isabelle, with no Lean surface.
  It is a `BOUNDARY_PARTNER`, not a formal dual: the two do not share a model.
  See [relations](../status/relations.md). This is not the claim that the kernel
  proves nothing positive — `Knowledge.Devices`, `Knowledge.Check`,
  `Oversight.JointObservation` and `Compositional.Networks` all conclude
  `Knowable`. It is the narrower claim that no Lean declaration here exhibits an
  observer achieving what the self-measurement impossibilities rule out.
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

Four domains project into this kernel. The table says what each one takes as the
unknown, as the observation, and as the target, because those three choices are
the whole content of an instance — the kernel supplies only the factorization
law, and picking the wrong observation is how a knowability statement ends up
being about nothing.

| Domain | Unknown | Observation | Target | Direction |
|---|---|---|---|---|
| `Oversight.JointObservation` | the world state | the coalition's joint evidence `q.observe` | the question `h` | both — `Covers` is definitionally `Knowable`, and coverage can hold or fail |
| `Wireheading.ObservationLimits` | the environment | the observed history a fixed policy receives | the true finite-horizon return | refutes |
| `Preference.Knowability` | the planner/reward pair | the evaluated policy `op3` | the reward `Prod.snd` | refutes |
| `Compositional.Networks` | the node | its view to depth `n` | its state after `n` rounds | establishes |

The kernel supports both directions and both are used.
`knowable_iff_no_collision` is an equivalence; `Knowledge.Devices` and
`Knowledge.Check` each conclude `Knowable`, and in `Oversight.JointObservation`
so do `covers_of_refines`, which transports a coverage hypothesis to a finer
observation, and `decideCoverage_covered_iff`, which reports coverage from a
checker over a finite enumeration.

`Compositional.Networks.knowable_runFor` derives knowability from a theorem its
own domain already proved, and carries no hypotheses, because the Angluin lemma
holds for every network, algorithm, configuration and round count without
qualification. No uniqueness follows from that and none is claimed.

### One proposition, four names

`Knowable`, `Determines`, `Covers` and `Refines` all unfold to
`∃ f, ∀ x, B x = f (A x)`. They are definitionally equal at full universe
generality, not merely analogous:

| Written | Unfolds to |
|---|---|
| `Knowable observation property` | `∃ decoder, ∀ ω, property ω = decoder (observation ω)` |
| `Determines finer coarser` | `∃ k, ∀ ω, coarser ω = k (finer ω)` |
| `Covers q h` | `∃ dh, ∀ σ, h σ = dh (q.observe σ)` |
| `Refines q' q` | `∃ f, ∀ σ, q.observe σ = f (q'.observe σ)` |

`Covers q h ↔ Knowable q.observe h` holds by `Iff.rfl`, and `Knowable.mono`
writes two of the names in one statement: its first hypothesis is a `Determines`
and its second a `Knowable`, and after unfolding both are the same proposition —
which makes that theorem the transitivity of one relation stated as the
monotonicity of another. `Determines.trans` is the same theorem again, at the
same universes; each proves the other by direct term application, with no
tactic.

The four names are worth keeping, because they say what a factorization is
*for*, and a reader of `Oversight` should not have to translate. But the
collapse belongs here rather than in each reader's rediscovery of it: what a
name adds is intent, not content.

The two refutations share a law rather than an argument.
`not_knowable_of_invariant_transform` is the shape both instantiate — an
observation-preserving map that moves the target — with the environment
complement in one case and the source's anti-rational negation `op4` in the
other. `Oversight.JointObservation` reaches the kernel through `Knowable.mono`,
`not_knowable_comp` and `knowable_iff_ambiguity_le_one` instead; its questions
are about refinement and residual ambiguity rather than about a single collision.

`python3 scripts/report_consumers.py --hub` prints the mechanical half of this
table: every one of the kernel's public declarations, and which module outside
the kernel names it. It enumerates the elaborated declaration index, so a
projection added or removed shows up without anyone remembering to edit here.

It read the *ledger* until 2026-09-07, which is not the same thing and was a
defect: `lean_artifact.declarations` is a curated subset, so
`Oversight.JointObservation.Residual`'s use of
`knowable_iff_worstAmbiguity_le_one` was invisible, and 73 of the kernel's 128
public declarations could not be reached at all. Two limits remain and the
report states them itself. It matches by source text, so it counts a mention
rather than an elaborated reference; and where a leaf name is shared by two
declarations — `IndistinguishabilityWitness.sameObservation` and
`CollisionWitness.sameObservation` are the live pair — a bare mention is
evidence for both and therefore for neither, so those declarations are counted
only on a qualified mention. The run prints how many needed that.

What each instance takes as observation and as target is a semantic fact and is
not generated.

Row-by-row structure, including which results are characterizations rather than
point impossibilities, is generated in [relations](../status/relations.md).
