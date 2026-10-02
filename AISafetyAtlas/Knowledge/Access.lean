module

public import AISafetyAtlas.Knowledge

/-!
# Forms of model access: the continuum, and what sits at each point on it

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four
layers: *(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Knowledge`, which is about
observation maps and decoders and names no model, no weights and no API. What is
added here is the arrow to an access question, stated over a model of a deployed
system.

`AISafetyAtlas.Knowledge.Audit` is the same kernel on the *when* axis — what a
measurement taken at one time settles about another. This is the *how much*
axis.

## The question

Reuel, Bucknall et al., *Open Problems in Technical AI Governance*, TMLR
04/2025:

> **Open Problem 37.** *"What research and auditing methodologies are possible
> given a range of forms of access on the continuum between black- and white-box
> access?"*

The operative phrase is **a continuum between black- and white-box access**, and
what varies along it is what an investigator can establish.

## The answer this module states

`Determines` is already a preorder on observation maps, so the continuum has a
home. What this module supplies is the thing the kernel cannot: **three named
points on it**, over a modelled artifact.

`AccessSetting` is a set of weights, an input type, and two things that can be
read off a run — the output, and a richer per-input score. Three access levels
are then three observations of the *same* weights:

* `whiteBox` — the artifact itself.
* `scoreAccess` — the full score function, one score per input.
* `blackBox` — the input-output behaviour, one output per input.

`whiteBox_determines_scoreAccess` and `scoreAccess_determines_blackBox` place
them in the order, and `whiteBox_determines_blackBox` composes them. That is the
continuum, *inside this model*, and `Knowable.mono` then says what R#37 asks:
anything establishable from a weaker access level is establishable from a
stronger one. `whiteBox_knowable` is the top — full access to the artifact
settles every property of the artifact, with no hypothesis at all.

The other direction is the part worth having. `no_blackBox_methodology` says
that if a property does not follow from behaviour, **no methodology over
behaviour recovers it** — not a cleverer probe, not more queries, not any
analysis of the transcript, because the analysis is a function of evidence that
was already insufficient. That is a statement about the access level and not
about anyone's ingenuity, and it is the sense in which R#37's question has a
sharp answer rather than a survey.

`exists_indistinguishable_behaviour` turns a negative answer into something an
auditor can act on: the two artifacts the access level cannot tell apart.

## What this module does not claim

**No real access level is placed in the order.** `whiteBox`, `scoreAccess` and
`blackBox` are three projections of *this* structure. Whether a particular
deployment's API is `behaviour`, whether returned logprobs are `scores`, and
where fine-tuning access or activation reads would sit, are layer-4 assignments
and none is made here. The order is proved between the projections, not between
the products.

`readOut_scores` is the one modelling commitment: the output is recoverable from
the score, which is deterministic decoding. Under sampling the output-level
observation is a distribution rather than a value; the chain has the same shape
there and is not stated.

`Knowable` is **exact** recovery. Real auditing is statistical and approximate,
and nothing here covers it.

`Knowable` is also the **existence of a decoder, not its computability**, and
`whiteBox_knowable` must not be read as "verification is possible with full
access". A property can be knowable from the artifact in this sense and have no
algorithm deciding it: `AISafetyAtlas.Computability.rice_code_iff` says that for
an extensional property of a program, a decision procedure over the code exists
only in the two trivial cases -- and the code is full access. What the order
here measures is what the evidence *contains*, which is prior to, and does not
imply, what can be computed from it.

Reuel et al.'s R#38 and R#39 — how forms of access affect misuse risk, and the
risk of model theft — are **not** addressed. Those are about what an adversary
can *do* with access, which is a capability and not a decoder-existence
question. The arrow is to R#37 alone.
-/

namespace AISafetyAtlas.Knowledge.Access

universe u v w y

/--
**A modelled system under audit**, carrying the distinction access levels are
about: an artifact, and two different things a run of it exposes.

`readOut_scores` is the modelling commitment that makes the order a chain — the
output is a function of the score. It is deterministic decoding, and it is the
only hypothesis in the structure.
-/
public structure AccessSetting (Weights : Type u) (Input : Type v)
    (Output : Type w) (Score : Type y) where
  /-- The input-output behaviour of an artifact. -/
  behaviour : Weights → Input → Output
  /-- The per-input score an artifact produces. -/
  scores : Weights → Input → Score
  /-- How an output is read off a score. -/
  readOut : Score → Output
  /-- The output is recoverable from the score: deterministic decoding. -/
  readOut_scores : ∀ ω i, readOut (scores ω i) = behaviour ω i

variable {Weights : Type u} {Input : Type v} {Output : Type w} {Score : Type y}
variable (M : AccessSetting Weights Input Output Score)

/-- **White-box access**: the artifact itself is the observation.

The setting is an explicit argument it does not use, so that the three access
levels read as three projections of one system. Reading the artifact is the
identity; that is the content. -/
@[expose] public def whiteBox (_M : AccessSetting Weights Input Output Score) :
    Weights → Weights := id

/-- **Score access**: the whole score function, one score per input. -/
@[expose] public def scoreAccess : Weights → (Input → Score) := M.scores

/-- **Black-box access**: the input-output behaviour and nothing else. -/
@[expose] public def blackBox : Weights → (Input → Output) := M.behaviour

/-! ## The continuum -/

/--
**White-box is at least as informative as score access.** Trivially: the scores
are computed from the artifact.
-/
public theorem whiteBox_determines_scoreAccess :
    Determines (whiteBox M) (scoreAccess M) :=
  ⟨M.scores, fun _ => rfl⟩

/--
**Score access is at least as informative as black-box.** This is the step that
uses `readOut_scores`, and it is the only place the modelling commitment is
spent: the behaviour is read off the scores pointwise.
-/
public theorem scoreAccess_determines_blackBox :
    Determines (scoreAccess M) (blackBox M) :=
  ⟨fun s i => M.readOut (s i), fun ω => funext fun i => (M.readOut_scores ω i).symm⟩

/--
**The two steps compose**, by `Determines.trans`. Nothing new is proved; the
point is that the three levels form a chain rather than two unrelated
comparisons.
-/
public theorem whiteBox_determines_blackBox :
    Determines (whiteBox M) (blackBox M) :=
  Determines.trans (whiteBox_determines_scoreAccess M) (scoreAccess_determines_blackBox M)

/-! ## What more access buys -/

/--
**Everything establishable from behaviour is establishable from scores.**
`Knowable.mono` at the lower step: this is R#37's monotonicity, and it is what
makes "more access" a meaningful phrase at all.
-/
public theorem scoreAccess_knowable_of_blackBox {Y : Sort*}
    {property : Weights → Y} (h : Knowable (blackBox M) property) :
    Knowable (scoreAccess M) property :=
  Knowable.mono (scoreAccess_determines_blackBox M) h

/-- The same at the upper step. -/
public theorem whiteBox_knowable_of_scoreAccess {Y : Sort*}
    {property : Weights → Y} (h : Knowable (scoreAccess M) property) :
    Knowable (whiteBox M) property :=
  Knowable.mono (whiteBox_determines_scoreAccess M) h

/--
**The top of the order.** Full access to the artifact settles every property of
the artifact — the decoder is the property itself. No hypothesis, and no
appeal to `knowable_id_iff_injective`, whose `Nonempty` side condition is not
needed here.

Read this as an *informational* statement and nothing more: the decoder is
asserted to exist, not to be computable. Full access leaves nothing about the
artifact undetermined; it does not follow that anything can be decided from it,
and for extensional properties of a program it provably cannot be.

This is the only unconditional positive statement in the module, and it is
unconditional precisely because `whiteBox` is the identity.
-/
public theorem whiteBox_knowable {Y : Sort*} (property : Weights → Y) :
    Knowable (whiteBox M) property :=
  ⟨property, fun _ => rfl⟩

/-! ## What more access does not buy, and what no methodology repairs -/

/--
**Two artifacts with the same behaviour refute black-box knowability.**

The certificate form: an auditor holding such a pair has a proof that the
property is outside black-box reach, with no hypothesis about the property.
-/
public theorem not_blackBox_knowable_of_behaviour_collision {Y : Sort*}
    {property : Weights → Y} {ω τ : Weights}
    (hbehaviour : ∀ i, M.behaviour ω i = M.behaviour τ i)
    (hproperty : property ω ≠ property τ) :
    ¬ Knowable (blackBox M) property :=
  not_knowable_of_collision (funext hbehaviour) hproperty

/-- The same one level up: artifacts scoring identically on every input. -/
public theorem not_scoreAccess_knowable_of_score_collision {Y : Sort*}
    {property : Weights → Y} {ω τ : Weights}
    (hscores : ∀ i, M.scores ω i = M.scores τ i)
    (hproperty : property ω ≠ property τ) :
    ¬ Knowable (scoreAccess M) property :=
  not_knowable_of_collision (funext hscores) hproperty

/--
**Open Problem 37's sharp half.** If a property does not follow from behaviour,
then *no* methodology over behaviour establishes it.

`analysis` is an arbitrary function of the entire input-output behaviour. It may
probe adaptively, aggregate across unboundedly many queries, or run any
statistic — it is still a function of evidence that was already insufficient, so
its output cannot separate what the evidence does not. R#37 asks which
methodologies a form of access permits; this says the answer is a property of
the access level, not of the method.

The contrapositive of `Knowable.mono`, by `not_knowable_comp`.
-/
public theorem no_blackBox_methodology {K : Sort*} {Y : Sort*}
    (analysis : (Input → Output) → K)
    {property : Weights → Y}
    (h : ¬ Knowable (blackBox M) property) :
    ¬ Knowable (fun ω => analysis (blackBox M ω)) property :=
  not_knowable_comp analysis h

/-- The same for any methodology over scores. -/
public theorem no_scoreAccess_methodology {K : Sort*} {Y : Sort*}
    (analysis : (Input → Score) → K)
    {property : Weights → Y}
    (h : ¬ Knowable (scoreAccess M) property) :
    ¬ Knowable (fun ω => analysis (scoreAccess M ω)) property :=
  not_knowable_comp analysis h

/-! ## Strictness, and what a negative answer hands the auditor -/

/--
**Score access is strictly below white-box** as soon as two distinct artifacts
score alike everywhere.

Stated order-theoretically rather than through a named property: what fails is
`Determines`, so the gap is between the access levels and not an artefact of
which question was asked. The proof is the collision lemma at `property := id`,
which is available because `Determines finer coarser` *is*
`Knowable finer coarser`.
-/
public theorem not_scoreAccess_determines_whiteBox {ω τ : Weights}
    (hscores : ∀ i, M.scores ω i = M.scores τ i) (hdistinct : ω ≠ τ) :
    ¬ Determines (scoreAccess M) (whiteBox M) :=
  not_knowable_of_collision (property := whiteBox M) (funext hscores) hdistinct

/-- **Black-box is strictly below score access** as soon as two artifacts agree
on every output while differing on some score. -/
public theorem not_blackBox_determines_scoreAccess {ω τ : Weights}
    (hbehaviour : ∀ i, M.behaviour ω i = M.behaviour τ i)
    (hscores : M.scores ω ≠ M.scores τ) :
    ¬ Determines (blackBox M) (scoreAccess M) :=
  not_knowable_of_collision (property := scoreAccess M) (funext hbehaviour) hscores

/--
**A negative answer is actionable.** An auditor who cannot settle a question
from black-box access can be handed the two artifacts that access cannot tell
apart — which is what makes the obstruction inspectable rather than a bare
failure.

Classical, via `exists_witness_of_not_knowable`.
-/
public theorem exists_indistinguishable_behaviour {Y : Type*} [Nonempty Y]
    {property : Weights → Y} (h : ¬ Knowable (blackBox M) property) :
    ∃ ω τ : Weights,
      (∀ i, M.behaviour ω i = M.behaviour τ i) ∧ property ω ≠ property τ := by
  obtain ⟨w⟩ := exists_witness_of_not_knowable h
  exact ⟨w.left, w.right, fun i => congrFun w.sameObservation i, w.propertyDiffers⟩

end AISafetyAtlas.Knowledge.Access
