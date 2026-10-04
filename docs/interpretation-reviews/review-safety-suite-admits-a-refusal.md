# Bridge review — `Sovereignty.Refusal.safety_suite_admits_a_refusal`

**Row `LAND-SOV-SERVICE-001` · module `AISafetyAtlas/Sovereignty/Refusal.lean` · `HUMAN_REVIEW`**

Only bridge on this row. Base: `Sovereignty.Service`. Executable side:
`atlas-check`'s `refusal` kind.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 on the allowed claim as sharpened. |

## The statement

```lean
public theorem safety_suite_admits_a_refusal {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {refusal : X} (hinert : Inert G₁ refusal)
    (hsafe : ∀ P ∈ A.mustHold, refusal ∈ P)
    {R : Set X} (hR : R ∈ A.mustServe) (hmiss : refusal ∉ R) (C₀ C₁ : Set N) :
    RetainsFamily G₀ G₁ C₀ C₁ A.mustHold ∧ ¬ Demandwise G₁ C₁ A.mustServe
```

`Audit` bundles `mustHold` (the safety suite) and `mustServe` (the requests).
Nothing relates them, which is the point.

## What to check

1. **`refusal_passes_safety` needs only inertness and that the refusal satisfies each property (`hsafe`).** A system that
   always returns the same outcome retains **every** safety property that outcome
   satisfies — not most, all, at every coalition. That strength is what makes the
   result about the suite rather than about a loophole.
2. **It is conditional on a request the refusal misses.** A refusal outcome is
   not bad. A deployment with no requests is not covered, correctly, because
   there refusing is the right behaviour.
3. **The check is decidable from the two lists alone and needs no system.** Both
   verdict branches carry agreement theorems —
   `exists_refusal_hole_of_admitsRefusal` and
   `not_exists_refusal_hole_of_admitsRefusal_eq_false`. **This is the only kind in
   the family exact in both directions**; the others are one-sided because their
   negative answer quantifies over systems or response functions.

## Allowed claim

> A safety suite consisting only of prohibitions is passed by a system that
> always returns one outcome, provided that outcome satisfies each prohibition,
> and that system fails the request catalogue whenever the outcome misses a request in it. Where such an outcome
> exists the suite admits a do-nothing pass, and the fact is about the **audit**
> rather than about any deployment.

## Forbidden

- **Not** "safety evaluations reward refusal." The atlas has no evaluation suite,
  no refusal and no request, and nothing says any real suite has this hole.
- **Not** that refusing is bad behaviour.
- **Not** that a suite passing this check is good. It excludes one specific
  vacuity and nothing else.
- **Not** a claim about over-refusal rates or any measured model behaviour.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Safety training makes models useless — here is the proof." | the only system is a hypothetical inert `G₁`; the statement is about a suite |
| "Our suite passed, so it is sound." | one vacuity excluded, nothing more |
| "So drop the prohibitions." | the conclusion is that a suite needs a service side |

## Witness

`AISafetyAtlas/Examples/Practitioner.lean` runs both verdict branches.
