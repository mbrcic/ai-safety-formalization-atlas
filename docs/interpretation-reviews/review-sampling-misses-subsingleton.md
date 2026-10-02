# Bridge review — `Compositional.Hyperproperties.Evaluation.sampling_misses_subsingleton`

**Row `LAND-EVAL-BLINDSPOT-001` · module `AISafetyAtlas/Compositional/Hyperproperties/Evaluation.lean` · `HUMAN_REVIEW`**

Sibling: [`traceProperty_knowable_of_score_decides`](review-traceproperty-knowable-of-score-decides.md).
Arrow to **Open Problem 19**.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem sampling_misses_subsingleton
    (score : Trace → Score) {a b : Trace}
    (hdistinct : a ≠ b) (hconfused : score a = score b) :
    ¬ Knowable (scoreSet score)
      (fun system : TraceSystem Trace ↦ system.Subsingleton)
```

## What to check

1. **The hypothesis is exactly what "recording a score" means**: two distinct
   runs receive the same value. The moment the score is not the run itself, it
   holds.
2. **"No number of additional runs helps" is the sentence that will be quoted.**
   The colliding systems are `{a}` and `{a, b}`; they produce the same scores, so
   every sampling schedule of any length sees identical evidence from both. That
   is why the blind spot is structural and not a budget. **Confirm this against
   the Lean** — it is the load-bearing claim.
3. **`Set.Subsingleton` is the smallest non-trace property**, used as a witness.
   **Reading it as a specific safety requirement is not intended** and the module
   says so.

## Allowed claim

> As soon as an evaluation's score maps two distinct runs to the same value,
> there is a property of the *set* of runs it cannot settle, and no sampling
> schedule changes that, because the two systems it confuses produce identical
> evidence however often they are sampled.

## Forbidden

- **Not** "benchmarks are structurally blind." Conditional on the score confusing
  two runs, and the positive half is the larger class.
- **Not** a claim about any particular evaluation suite. That a given benchmark
  is per-run scoring is layer 4.
- **Not** a claim about consistency, sandbagging, scheming or any named
  hyperproperty. `Subsingleton` is a minimal witness, nothing more.
- **Not** applicable to a harness that compares runs to each other, records
  pairs, or keeps the whole batch — that is not modelled by `score`.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Evals cannot detect scheming." | needs the target requirement shown to be a hyperproperty *and* the harness shown to be per-run scoring |
| "So run more samples." | the collision is invariant under sampling — the module's central point |
| "Recording full transcripts has the same problem." | the hypothesis is that the score confuses two runs; a harness recording the run does not satisfy it |

## Witness

`AISafetyAtlas/Examples/Compositional/Hyperproperties/Evaluation.lean`, with the
confusing score and the two systems it cannot separate.
