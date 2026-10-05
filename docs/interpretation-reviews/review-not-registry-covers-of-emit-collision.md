# Bridge review — `Oversight.JointObservation.not_registry_covers_of_emit_collision`

**Row `LAND-AUDIT-REGISTRY-001` · module `AISafetyAtlas/Oversight/JointObservation/Registry.lean` · `HUMAN_REVIEW`**

Sibling: [`consortium_covers_of_registry_covers`](review-consortium-covers-of-registry-covers.md).
Arrow to **Open Problem 60**.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-03 |
| Note | Accepted on the allowed claim as sharpened 2026-10-03 after external review (PR #72). |

## The statement

```lean
public theorem not_registry_covers_of_emit_collision
    {C : Finset A.Principal} {h : Hazard A} {σ τ : A.Execution}
    (hfile : ∀ i : {p // p ∈ C},
      A.emit i.1 (A.privateState i.1 σ) = A.emit i.1 (A.privateState i.1 τ))
    (hhazard : h σ ≠ h τ) :
    ¬ Covers (registryCandidate A C) h
```

## What to check

1. **The coalition `C` is arbitrary, which is stronger than it looks.**
   Enlarging the chain repairs it only through a member whose filing separates
   the two executions: a new member whose filing also agrees across them leaves
   the enlarged registry still unable to separate them. **The obstruction lives in what a filing
   discards, not in how many filings were gathered** — so the repair is a richer
   declared interface and not a longer value chain. That is the reviewable
   sentence.
2. **`hfile` is quantified over members of `C` only.** A non-member holding
   separating evidence is not consulted, correctly — the theorem is about what
   that coalition's filings settle.
3. It is `Knowledge.not_knowable_of_collision` applied. No new mathematics; the
   content is the reading.

## Allowed claim

> Where two executions produce identical filings from every member of a
> disclosure coalition and differ on the hazard, no rule over the registry
> detects it. Adding members repairs it only if some new member's filing
> differs between the two executions; members whose filings also agree leave it
> unrepaired, however many are added.

## Forbidden

- **Not** "disclosure registries cannot detect hazards." Conditional on an
  exhibited collision, and the sibling is why registries are worth having.
- **Not** a claim that any real reporting schema collides.
- **Not** a strategic or incentive result; truthful filing is assumed.
- **Not** a claim that joint observation is safe, legal or desirable.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Transparency reporting is provably inadequate." | needs a collision in the real schema |
| "Expand the consortium to fix the gap." | holds only if a new member's filing separates the two executions; adding members whose filings also agree changes nothing — the size of the coalition is not the variable |
| "So value-chain accountability fails." | the repair the module names is a richer interface, and it says so |

## Witness

`AISafetyAtlas/Examples/Oversight/JointObservationRegistry.lean`, with the emit
collision exhibited.
