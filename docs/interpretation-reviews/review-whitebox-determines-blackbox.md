# Bridge review — `Knowledge.Access.whiteBox_determines_blackBox`

**Row `LAND-ACCESS-ORDER-001` · module `AISafetyAtlas/Knowledge/Access.lean` · `HUMAN_REVIEW`**

Siblings: [`no_blackBox_methodology`](review-no-blackbox-methodology.md),
[`exists_indistinguishable_behaviour`](review-exists-indistinguishable-behaviour.md).
Arrow to **Open Problem 37**.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem whiteBox_determines_blackBox :
    Determines (whiteBox M) (blackBox M) :=
  Determines.trans (whiteBox_determines_scoreAccess M) (scoreAccess_determines_blackBox M)
```

`AccessSetting` is a set of weights, an input type, and two things readable off a
run. The three levels are three observations of the **same** weights: `whiteBox`
(the artifact), `scoreAccess` (one score per input), `blackBox` (one output per
input).

## What to check

1. **Nothing real is placed on the order.** Whether a deployment's API is
   `behaviour`, whether logprobs are `scores`, and where fine-tuning access or
   activation reads sit are layer-4 assignments and **none is made**. The order
   is proved between the projections, not between the products. That is the
   honest limit of the claim, and it is also why the bridge grade is arguable.
2. **`readOut_scores` is the one modelling commitment** — the output is
   recoverable from the score, i.e. deterministic decoding. Under sampling the
   output-level observation is a distribution and the chain is not stated.
3. **`Determines` is the same proposition as `Knowable`**, under a name chosen
   for a different use. So this composes two steps and proves no new law; the
   content is that the three levels form a **chain** rather than two unrelated
   comparisons.

## Allowed claim

> Forms of model access sit in an informativeness order, and what an
> investigation can establish is monotone along it: anything establishable from a
> weaker access level is establishable from a stronger one. Inside this model the
> artifact determines the per-input scores, which determine the input-output
> behaviour.

## Forbidden

- **Not** a placement of any real API, tooling tier or access regime on the
  order.
- **Not** "full access settles everything in practice." `Knowable` is the
  existence of a decoder, **not its computability** — `whiteBox_knowable` must not
  be read as "verification is possible with full access". `rice_code_iff` is the
  counterweight and the module cites it.
- **Not** about sampling-based deployments.
- **Not** a cost, risk or policy statement about granting access.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Weight access dominates API access, so mandate it." | the order is informational; nothing about cost, misuse risk or necessity follows |
| "Full access means we can verify the model." | decoder existence ≠ computability; see the Rice pointer in the module |
| "Logprobs are the middle tier." | that assignment is layer 4 and is not made |

## Witness

`AISafetyAtlas/Examples/Knowledge/Access.lean`.
