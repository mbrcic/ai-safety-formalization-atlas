# Bridge review — `Sovereignty.Attestation.properties_are_independent`

**Row `LAND-SOV-AUTH-001` · module `AISafetyAtlas/Sovereignty/Attestation.lean` · `HUMAN_REVIEW`**

Siblings: [`obedience_does_not_give_authority`](review-obedience-does-not-give-authority.md),
[`attestation_is_not_the_claim`](review-attestation-is-not-the-claim.md),
[`power_over_a_matter_does_not_compose`](review-power-over-a-matter-does-not-compose.md).

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem properties_are_independent :
    ∃ (Sys : Type) (p q : Sys → Prop) (neither onlyQ onlyP both : Sys),
      (¬ p neither ∧ ¬ q neither) ∧ (¬ p onlyQ ∧ q onlyQ) ∧
        (p onlyP ∧ ¬ q onlyP) ∧ (p both ∧ q both)
```

`B8` from `Sovereignty.Authority`.

## What to check

1. **All four quadrants are named separately**, not "the implication fails
   somewhere". The useful reading is that **each** combination occurs. Confirm the
   witnesses really are four distinct inhabitants and not three plus a
   simplification.
2. **It says the relation is not carried by the record**, not that the properties
   are unrelated in any real system. An argument moving from one to the other
   must name the mechanism — that is the whole content.
3. Same question as its sibling: a bare existential over abstract types. Decide
   whether the `BRIDGE` grade belongs on it or whether the AI reading is
   docstring-only.

## Allowed claim

> Two attested properties of the same system — accuracy and authorization,
> privacy and benefit, provenance and safety — admit every pairing. Neither the
> presence nor the absence of one constrains the other, so linking any two of
> them takes an assumption about the system and never a relabelling of the
> record.

## Forbidden

- **Not** that accuracy and privacy (or any named pair) are unrelated in
  practice. The claim is that the relation is not carried by both being recorded.
- **Not** a claim about any real pair of properties; the labels in the docstring
  are illustrative and the theorem quantifies over abstract predicates.
- **Not** a statement about trade-offs. Nothing here says the properties conflict
  — the point is that all four quadrants, including "both", are occupied.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Privacy and accuracy are provably independent." | the theorem is about labels on an abstract system, not about those properties |
| "So compliance records are meaningless." | it says one inference is unavailable, not that records carry nothing |
| "This shows a privacy-accuracy trade-off." | the opposite: the `both` quadrant is inhabited |

## Witness

`AISafetyAtlas/Examples/Sovereignty/Governance.lean`.
