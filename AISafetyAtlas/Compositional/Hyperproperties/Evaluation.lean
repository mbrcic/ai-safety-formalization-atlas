module

public import AISafetyAtlas.Compositional.Hyperproperties
public import AISafetyAtlas.Knowledge

/-!
# What an evaluation that scores runs one at a time can and cannot see

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../../docs/agent/policy/ledger-coverage.md)'s four
layers: *(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Compositional.Hyperproperties`,
which is about trace systems and sets of them and names no evaluation. What is
added here is the arrow to two governance questions, stated over a model of an
evaluation.

## The questions

Reuel, Bucknall et al., *Open Problems in Technical AI Governance*, TMLR
04/2025:

> **Open Problem 18.** *"How can the thoroughness of evaluations be measured?"*
>
> **Open Problem 19.** *"How can potential blind spots of evaluations be
> identified?"*

## The answer this module states

Model an evaluation as a **per-run score**: it executes runs, records something
about each one, and its whole evidence about the system is the set of scores it
saw. That is what a benchmark is.

`traceProperty_knowable_of_score_decides` is the positive half. Any requirement
of the form *"every run is acceptable"* — a **trace property** — is settled
exactly by such an evaluation, provided the score carries acceptability. Most of
what is written into evaluation suites has this shape, and for it thoroughness
really is a coverage question.

`not_knowable_of_score_collision` and `sampling_misses_subsingleton` are the
negative half, and they are the answer to Open Problem 19. A **hyperproperty** is
a property of the *set* of runs, not of each run. The moment the score maps two
different runs to the same value — which is what recording a score rather than
the whole run means — there is a hyperproperty the evaluation cannot see, and
**no number of additional runs helps**, because the two systems it confuses
produce identical evidence however often they are sampled.

So the blind spot is **structural, not a sampling budget**: measuring
thoroughness as coverage answers Open Problem 18 for trace properties and is the
wrong instrument for anything else.

## What this does not claim

That a given benchmark is per-run scoring is a claim about that benchmark, and
is layer 4. Nothing here says any particular evaluation suite has this shape, and
an evaluation that compares runs to each other — that records pairs, or the whole
batch — is simply not modelled by `score`. The theorem names what makes a blind
spot unavoidable; it does not survey which tools have one.

`Set.Subsingleton` is used as the witness hyperproperty because it is the
smallest one that is not a trace property. Reading it as a specific safety
requirement is not intended.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties.Evaluation

open AISafetyAtlas.Knowledge

universe u v

variable {Trace : Type u} {Score : Type v}

/--
The evidence a **per-run evaluation** gathers about a system: the set of scores
its runs produced.

Two systems are indistinguishable to such an evaluation exactly when they realize
the same scores, and nothing about how many times each was seen enters — which is
why running the benchmark for longer cannot separate them.
-/
@[expose] public def scoreSet (score : Trace → Score)
    (system : TraceSystem Trace) : Set Score :=
  score '' system

/--
**A requirement on every run is settled by scoring runs.**

`fun system ↦ ∀ t ∈ system, t ∈ acceptable` is the trace property *"every run is
acceptable"*. If the score is enough to decide acceptability of a single run,
then the set of scores is enough to decide the requirement of the whole system.

This is the half that makes evaluation suites work, and it is stated first so
that the obstruction below is not read as a claim that evaluations are useless.
-/
public theorem traceProperty_knowable_of_score_decides
    (score : Trace → Score) (acceptable : Set Trace) (decide : Score → Prop)
    (hsound : ∀ t : Trace, t ∈ acceptable ↔ decide (score t)) :
    Knowable (scoreSet score)
      (fun system : TraceSystem Trace ↦ ∀ t ∈ system, t ∈ acceptable) := by
  refine ⟨fun observed ↦ ∀ s ∈ observed, decide s, fun system ↦ ?_⟩
  apply propext
  constructor
  · rintro hall _ ⟨t, ht, rfl⟩
    exact (hsound t).mp (hall t ht)
  · intro hall t ht
    exact (hsound t).mpr (hall (score t) ⟨t, ht, rfl⟩)

/--
**Two systems the scores cannot separate refute knowability outright.**

The certificate form: a consumer holding such a pair has a proof that its
evaluation is blind to the property, with no hypothesis about the property at
all.
-/
public theorem not_knowable_of_score_collision
    {score : Trace → Score} {H : TraceSystem Trace → Prop}
    {system₁ system₂ : TraceSystem Trace}
    (hobs : scoreSet score system₁ = scoreSet score system₂)
    (hH : H system₁ ≠ H system₂) :
    ¬ Knowable (scoreSet score) H :=
  not_knowable_of_collision hobs hH

/--
**As soon as the score confuses two runs, a hyperproperty escapes the
evaluation.**

The hypothesis is exactly what it means to record a *score* rather than the run
itself: two distinct runs receive the same value. The conclusion names a property
of the run set — here *"the system has at most one behaviour"* — that no decoder
on the evaluation's evidence reproduces.

The two systems that collide are `{a}` and `{a, b}`. They produce the same
scores, so **every** sampling schedule, of any length and any repetition, sees
the same evidence from both. That is why this is a blind spot rather than a
budget: the missing information was never in the evidence to begin with.
-/
public theorem sampling_misses_subsingleton
    (score : Trace → Score) {a b : Trace}
    (hdistinct : a ≠ b) (hconfused : score a = score b) :
    ¬ Knowable (scoreSet score)
      (fun system : TraceSystem Trace ↦ system.Subsingleton) := by
  refine not_knowable_of_score_collision
    (system₁ := ({a} : Set Trace)) (system₂ := ({a, b} : Set Trace)) ?_ ?_
  · ext s
    simp only [scoreSet, Set.mem_image, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨t, rfl, rfl⟩
      exact ⟨t, Or.inl rfl, rfl⟩
    · rintro ⟨t, (rfl | rfl), rfl⟩
      · exact ⟨t, rfl, rfl⟩
      · exact ⟨a, rfl, hconfused⟩
  · have hone : ({a} : Set Trace).Subsingleton := Set.subsingleton_singleton
    have htwo : ¬ ({a, b} : Set Trace).Subsingleton := by
      intro h
      exact hdistinct (h (Set.mem_insert a _) (Set.mem_insert_of_mem a rfl))
    simp only [ne_eq, eq_iff_iff]
    exact fun h ↦ htwo (h.mp hone)

end AISafetyAtlas.Compositional.Hyperproperties.Evaluation
