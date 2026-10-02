# Bridge review — `Sovereignty.CapabilityAssessment.withdrawal_settles_and_no_output_procedure_does`

**Row `LAND-SOV-ASSESSMENT-001` · module `AISafetyAtlas/Sovereignty/CapabilityAssessment.lean` · `HUMAN_REVIEW`**

Siblings: [`no_procedure_on_output_recovers_fallback`](review-no-procedure-on-output-recovers-fallback.md),
[`protocols_are_incomparable`](review-protocols-are-incomparable.md).

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

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
2. **The conjunction is what a consumer cites.** "Withdrawal testing is forced
   rather than chosen" is the sentence, and it is this declaration that carries
   it. Decide whether the conjunction earns its own grade or whether the two
   halves suffice.
3. **So the 6% study is not an instance of the obstruction — it is the expensive
   way around it.** Check you are content with that framing; it is the module's
   reading of a cited empirical result and it is the most interpretive sentence
   in the file.

## Allowed claim

> Testing with the assistance removed recovers unaided capability; nothing
> computed from ordinary observed work does, at any level of sophistication. A
> consumer holding this pair has the argument that withdrawal testing is forced
> rather than chosen.

## Forbidden

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
