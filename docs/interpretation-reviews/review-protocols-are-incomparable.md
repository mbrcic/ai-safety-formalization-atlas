# Bridge review — `Sovereignty.CapabilityAssessment.protocols_are_incomparable`

**Row `LAND-SOV-ASSESSMENT-001` · module `AISafetyAtlas/Sovereignty/CapabilityAssessment.lean` · `HUMAN_REVIEW`**

Siblings: [`no_procedure_on_output_recovers_fallback`](review-no-procedure-on-output-recovers-fallback.md),
[`withdrawal_settles_and_no_output_procedure_does`](review-withdrawal-settles-and-no-output-procedure-does.md).

**The sharp form of the module.**

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem protocols_are_incomparable {R : Type u} [Ring R]
    {x y : R} (hxy : x ≠ y) :
    ¬ Determines (outputProtocol R) (withdrawalProtocol R) ∧
      ¬ Determines (withdrawalProtocol R) (outputProtocol R)
```

## What to check

1. **Both directions.** Withdrawal testing is not "more of" output observation,
   so no quantity of observed work approaches it — **and** it is not strictly
   better, since unaided capability says nothing about assisted performance. They
   answer different questions.
2. **The consequence is the reviewable one**: a measurement programme collecting
   only assisted work earns **no partial credit** toward the question withdrawal
   testing answers. That is what makes withdrawal testing *forced* rather than an
   expensive option a cheaper design could replace.
3. **`hxy : x ≠ y` is the whole non-degeneracy condition.** A ring where the two
   coincide has nothing to separate.

## Allowed claim

> The two protocols are incomparable in the informativeness order: neither
> determines the other. So the expense of withdrawal testing is not redundancy,
> and observing assisted work accrues nothing toward it.

## Forbidden

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
| "Observed work is worthless as evidence." | worthless *for this question*; the second conjunct says withdrawal testing is equally blind to assisted performance |
| "More observation will eventually suffice." | the first conjunct is the refusal of that, at any quantity |

## Witness

`AISafetyAtlas/Examples/Sovereignty/CapabilityAssessment.lean`.
