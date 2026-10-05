# Bridge review — `Compositional.Hyperproperties.Evaluation.traceProperty_knowable_of_score_decides`

**Row `LAND-EVAL-BLINDSPOT-001` · module `AISafetyAtlas/Compositional/Hyperproperties/Evaluation.lean` · `HUMAN_REVIEW`**

Sibling: [`sampling_misses_subsingleton`](review-sampling-misses-subsingleton.md).
Arrow to Reuel, Bucknall et al., TMLR 04/2025, **Open Problems 18 and 19**.

**The positive half, and the larger class.**

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 on the allowed claim as sharpened. |

## The statement

```lean
public theorem traceProperty_knowable_of_score_decides
    (score : Trace → Score) (acceptable : Set Trace) (decide : Score → Prop)
    (hsound : ∀ t : Trace, t ∈ acceptable ↔ decide (score t)) :
    Knowable (scoreSet score)
      (fun system : TraceSystem Trace ↦ ∀ t ∈ system, t ∈ acceptable)
```

An evaluation is modelled as a **per-run score**: it executes runs, records
something about each, and its whole evidence is the set of scores.

## What to check

1. **`hsound` is a real hypothesis**: the score must be *enough to decide*
   acceptability of a single run. An evaluation whose score throws away what the
   requirement needs does not satisfy it.
2. **The decoder is constructed, not asserted** — `∀ s ∈ observed, decide s`.
   Constructive and inspectable.
3. **It is stated first in the module on purpose**, so the obstruction below is
   not read as a claim that evaluations are useless. For requirements of the
   *"every run is acceptable"* shape, thoroughness is a coverage question — which
   is R#18's answer for that class. How much of real evaluation has that shape is
   not claimed.
4. **The evidence is the score of every run the system can produce.** A real
   evaluation samples runs; a finite sample cannot establish *"every run is
   acceptable"*, and that gap is outside this statement.

## Allowed claim

> An evaluation whose evidence is the score of every run the system can produce
> settles every requirement of the form *"every run is acceptable"*, provided the
> score decides acceptability of a run.

## Forbidden

- **Not** a claim that any particular benchmark satisfies `hsound`.
- **Not** a statement about statistical confidence, sample size or measurement
  error. `Knowable` is exact.
- **Not** a claim that trace properties are the requirements that matter.
- **Not** about sampled evaluations. The statement needs every possible run
  scored; a finite sample settles no *"every run"* requirement.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Benchmarks provably work." | conditional on the score deciding acceptability, which is an assumption about the harness, and on every run being scored |
| "So per-run scoring is sufficient." | sufficient for trace properties when every run is scored; the sibling is the other half |
| "This validates our eval suite." | no real suite is modelled |

## Witness

`AISafetyAtlas/Examples/Compositional/Hyperproperties/Evaluation.lean`.
