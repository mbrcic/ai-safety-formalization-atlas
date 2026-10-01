# Bridge review — `Oversight.JointObservation.consortium_covers_of_registry_covers`

**Row `LAND-AUDIT-REGISTRY-001` · module `AISafetyAtlas/Oversight/JointObservation/Registry.lean` · `HUMAN_REVIEW`**

Sibling: [`not_registry_covers_of_emit_collision`](review-not-registry-covers-of-emit-collision.md).
Arrow to Reuel, Bucknall et al., TMLR 04/2025, **Open Problem 60**.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem consortium_covers_of_registry_covers
    {C : Finset A.Principal} {h : Hazard A}
    (hreg : Covers (registryCandidate A C) h) :
    Covers (consortiumCandidate A C) h
```

Compose the registry's decision rule with `emit`. **No hypothesis** — at every
coalition and every hazard.

## What to check

1. **The layer-2 facade explicitly disclaims being a bridge.**
   `Oversight.JointObservation`'s docstring says *"Not an AI-system bridge. No
   `ai_interpretation_status` graduation from this facade."* The bridge is
   `Registry.lean` only. Confirm the separation is real: the facade supplies
   coverage over an evidence architecture; this module adds the reading as a
   value-chain disclosure regime.
2. **`emit` is a function of private evidence.** No fabrication, no strategy, no
   deception. A party that files falsely is not modelled at all.
3. **This is why filing is worth requiring**, and it is the direction most likely
   to be skipped when the module is cited for its obstruction.

## Allowed claim

> A disclosure registry is never more informative than the private evidence the
> filings were computed from: whatever a set of filings settles, that evidence
> settles too.

## Forbidden

- **Not** a claim that raw evidence *should* be disclosed. `Covers` is
  informational; whether such a coalition should be formed, and whether
  disclosure is permissible, is a governance question this does not touch.
- **Not** a strategic result. The mechanism is fixed and truthful; incentive
  compatibility and robustness to deception are out of scope, and
  `observe_truthful` marks that boundary at the point of use.
- **Not** a design-space result. Nothing generates or optimises disclosure
  interfaces.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "So regulators should demand raw evidence." | the theorem compares informativeness, not permissibility or cost |
| "This covers parties lying on their filings." | `emit` is a function of private evidence; deception is outside the model |
| "Registries are redundant." | the opposite: it is the statement that makes filing worth requiring |

## Witness

`AISafetyAtlas/Examples/Oversight/JointObservationRegistry.lean`.
