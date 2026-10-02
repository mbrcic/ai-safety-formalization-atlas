# Bridge review — `Sovereignty.Conformity.passes_every_check_and_not_operable`

**Row `LAND-SOV-CATALOGUE-001` · module `AISafetyAtlas/Sovereignty/Conformity.lean` · `HUMAN_REVIEW`**

Only bridge on this row. Base: `Sovereignty.Catalogue`. Executable side:
`atlas-check`'s `conformity` kind via `Sovereignty.ConformityCheck`.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem passes_every_check_and_not_operable
    [∀ i, Nonempty (A.system.strategy i)] {Φ Ψ : Set X}
    (hpass : PassesEach A)
    (hΦ : Φ ∈ A.requirements) (hΨ : Ψ ∈ A.requirements) (hd : Disjoint Φ Ψ) :
    PassesEach A ∧ ¬ Operable A
```

`PassesEach` is `Demandwise` — one commitment **per requirement**, chosen knowing
which it must serve. `Operable` is `DemandwiseUniform` — a **single** commitment
whose outcomes lie inside every requirement.

## What to check

1. **The whole result is a quantifier swap**: `∀ req, ∃ commitment` against
   `∃ commitment, ∀ req`. **If `Sovereignty.Catalogue`'s two definitions do not
   differ this way, the module says nothing.** Check `Demandwise` against
   `DemandwiseUniform` directly — this is the one thing worth opening the base
   module for.
2. **`passesEach_of_operable` is stated** (not graded): operability implies
   passing, so the checklist is not measuring the wrong thing, it is measuring a
   strictly **weaker** thing. Signing the negative half alone invites "conformity
   assessment is broken", which is not the claim.
3. **The obstruction is visible in the requirements alone** — a disjoint pair is
   enough, no system need be examined. That is what makes the checker cheap and
   the finding actionable: the output names which pair is disjoint.

## Allowed claim

> A conformity assessment that asks, for each requirement separately, whether
> some way of operating the system meets it, certifies a strictly weaker property
> than a deployment needs. Where two requirements are disjoint, a system can pass
> every item and have no way of being run, and the certificate is then evidence
> about the assessment procedure rather than about the deployment.

## Forbidden

- **Not** "conformity assessment is broken." A scheme demanding a single
  documented operating policy tested against the whole catalogue is **not** an
  instance of `PassesEach`.
- **Not** a claim that any real standard contains a disjoint pair.
- **Not** a criticism of the assessor: conflicting requirements need allocation,
  time-indexing or arbitration, and the obstruction is in the requirement set.
- **Not** about partial compliance, materiality or risk tiering.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "[Named standard] certifies unrunnable systems." | needs a disjoint pair exhibited in that standard |
| "So certification is meaningless." | `passesEach_of_operable`: weaker, not wrong |
| "Any two requirements will conflict." | disjointness is strong and is exhibited, not assumed |

## Witness

`AISafetyAtlas/Examples/Sovereignty/Governance.lean`, with an inhabited disjoint
pair.
