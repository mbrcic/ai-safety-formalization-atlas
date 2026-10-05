# Bridge review — `Sovereignty.CapabilityAssessment.protocols_are_incomparable`

**Row `LAND-SOV-ASSESSMENT-001` · module `AISafetyAtlas/Sovereignty/CapabilityAssessment.lean` · `HUMAN_REVIEW`**

Siblings: [`no_procedure_on_output_recovers_fallback`](review-no-procedure-on-output-recovers-fallback.md),
[`withdrawal_settles_and_no_output_procedure_does`](review-withdrawal-settles-and-no-output-procedure-does.md).

**The sharp form of the module.**

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 on the allowed claim as qualified: one assisted result, borrowed part unconstrained; richer experimental designs are outside the model. |

## The statement

```lean
public theorem protocols_are_incomparable {R : Type u} [Ring R]
    {x y : R} (hxy : x ≠ y) :
    ¬ Determines (outputProtocol R) (withdrawalProtocol R) ∧
      ¬ Determines (withdrawalProtocol R) (outputProtocol R)
```

## What to check

1. **Both directions.** Withdrawal testing is not "more of" output observation,
   so observed work does not determine it — **and** it is not strictly
   better, since unaided capability says nothing about assisted performance. They
   answer different questions.
2. **The consequence is the reviewable one**: a measurement programme collecting
   only assisted work has **no exact decoder** for the question withdrawal
   testing answers from one assisted result. It does not make withdrawal testing
   the only option: designs over many tasks, varied assistance or many people
   are not modelled and might replace it.
3. **`hxy : x ≠ y` is the whole non-degeneracy condition.** A ring where the two
   coincide has nothing to separate.

## Allowed claim

> In a model where one assisted result is fallback capability plus a borrowed
> part free to take any value, neither a single assisted result nor a withdrawal
> test determines the other exactly, so within the model withdrawal testing is
> not redundant with observing one assisted result. Richer designs — many tasks,
> varied assistance, many people, a bounded or measured borrowed part — are not
> modelled and may recover partial or statistical information about either.

## Forbidden

- **Not** a claim that unaided capability cannot be estimated from assisted work
  in general. The model sees one assisted result with nothing known about the
  borrowed part; designs that vary tasks, assistance levels or people, or that
  bound or measure the borrowed part, are outside it and may well estimate
  unaided capability or its ratio to assisted performance.
- **Not** a recommendation that withdrawal testing be performed, at any
  frequency, on anyone. No cost, no ethics, no consent and no schedule is
  modelled.
- **Not** a claim that assisted output is uninformative. It determines assisted
  performance, which is a different and often the operative question.
- **Not** a claim about any measurement programme that exists.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "So mandate periodic unassisted testing." | the module says what answers the question; it recommends nothing and prices nothing |
| "Observed work is worthless as evidence." | it does not *determine* the answer to this question; the second conjunct says withdrawal testing likewise does not determine assisted performance |
| "More observation will eventually suffice." | not refused: the model has one observation with the borrowed part unconstrained; more observations, especially with varied or bounded assistance, are not modelled and may suffice |

## Witness

`AISafetyAtlas/Examples/Sovereignty/CapabilityAssessment.lean`.
