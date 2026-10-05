# Bridge review — `Sovereignty.CapabilityAssessment.withdrawal_settles_and_no_output_procedure_does`

**Row `LAND-SOV-ASSESSMENT-001` · module `AISafetyAtlas/Sovereignty/CapabilityAssessment.lean` · `HUMAN_REVIEW`**

Siblings: [`no_procedure_on_output_recovers_fallback`](review-no-procedure-on-output-recovers-fallback.md),
[`protocols_are_incomparable`](review-protocols-are-incomparable.md).

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 on the allowed claim as qualified: one assisted result, borrowed part unconstrained; richer experimental designs are outside the model. |

## The statement

```lean
public theorem withdrawal_settles_and_no_output_procedure_does {R : Type u} [Ring R]
    {K : Sort*} {x y : R} (hxy : x ≠ y) (report : R → K) :
    Knowable (withdrawalProtocol R) (fallbackCapability (R := R)) ∧
      ¬ Knowable (fun state : R × R => report (outputProtocol R state))
        (fallbackCapability (R := R))
```

## What to check

1. **The positive half is immediate and that is the point.** Withdrawal testing
   settles the question because it *observes the quantity*. It is not a clever
   method; it is the definition of measuring the thing.
2. **The conjunction is what a consumer cites.** "Evidence beyond assisted
   output is forced, and withdrawal testing supplies it" is the sentence; the
   declaration does not show withdrawal is the only such protocol. Decide whether the conjunction earns its own grade or whether the two
   halves suffice.
3. **So the 6% study is not an instance of the obstruction — it is the expensive
   way around it.** Check you are content with that framing; it is the module's
   reading of a cited empirical result and it is the most interpretive sentence
   in the file.

## Allowed claim

> In the same model — one assisted result, the sum of unaided capability and a
> borrowed part that can take any value — testing with the assistance removed
> recovers unaided capability by definition, and no function of that single
> assisted result does. So within the model some evidence beyond the one
> assisted result is needed. Withdrawal testing is one such; designs that vary
> tasks, assistance or people are others the model does not cover.

## Forbidden

- **Not** a claim that unaided capability cannot be estimated from assisted work
  in general. The model sees one assisted result with nothing known about the
  borrowed part; designs that vary tasks, assistance levels or people, or that
  bound or measure the borrowed part, are outside it and may well estimate
  unaided capability or its ratio to assisted performance.
- **Not** that withdrawal testing is practical, ethical, or advisable in any
  setting. Feasibility, consent and cost are unmodelled.
- **Not** evidence of any decline anywhere. See the sibling's forbidden list and
  the report's own caveat.
- **Not** a claim that the 6% study was well designed, or that its finding
  replicates.
- **Not** a claim about self-report.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "The atlas proves the 6% finding." | nothing here predicts, explains or corroborates it; the module states this explicitly |
| "So organisations must run withdrawal tests." | the theorem says what answers the question, not what anyone should do |
| "Assisted-work review can be dropped." | it answers a different question, which the sibling makes precise |

## Witness

`AISafetyAtlas/Examples/Sovereignty/CapabilityAssessment.lean`.
