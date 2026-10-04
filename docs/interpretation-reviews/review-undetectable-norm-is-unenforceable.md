# Bridge review — `Sovereignty.Enforcement.undetectable_norm_is_unenforceable`

**Row `LAND-SOV-DEONTIC-001` · module `AISafetyAtlas/Sovereignty/Enforcement.lean` · `HUMAN_REVIEW`**

Only bridge on this row. Executable side: `atlas-check`'s `enforcement` kind via
`Sovereignty.EnforcementCheck`, which is **constructive** — a clean search hands
back the monitoring rule.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-03 |
| Note | Accepted on the allowed claim as sharpened 2026-10-03. |

## The statement

```lean
public theorem undetectable_norm_is_unenforceable {e e' : E}
    (hsame : R.observe e = R.observe e')
    (hbad : R.norms.forbidden e) (hgood : R.norms.permitted e')
    (hconsistent : R.norms.Consistent) :
    ¬ Detectable R ∧
      ∀ (S : Type w) (respond : O → S) (benign : S), ¬ Enforces R respond benign
```

## What to check

1. **The module is the edge between `Sovereignty.Deontic` and
   `Sovereignty.Auditability`, and neither imports the other.** Confirm the
   import graph — if one already reached the other, this is a restatement rather
   than a new edge, and the bridge grade weakens.
2. **The quantifier in the governance half is over every response function and
   every response type.** Not "no enforcement we have thought of". This is the
   sentence that makes it structural.
3. **`detectable_of_enforcement` proves the converse** (not graded): under a
   `Complete` norm system, an enforcement that works *is* a detector, recovered
   from it. So, for complete norms, an undetectable prohibition cannot be
   enforced, and a proposal conceding undetectability while asserting
   enforceability is incoherent rather than optimistic.
4. **`hconsistent` is needed** to rule out an act both forbidden and permitted.

## Allowed claim

> For a consistent norm system, where the monitoring channel maps a forbidden
> act and a permitted act to the same observation, no response computed from the
> observation sanctions every forbidden act while sparing every permitted one,
> and no detector for the prohibition exists either: one fact about the
> observation channel, reported in the two vocabularies the halves of a
> governance argument are usually written in.

## Forbidden

- **Not** "AI norms cannot be enforced." Conditional on an indistinguishable
  pair, which is a property of a monitoring design and is asserted of none.
- **Not** a claim about cost. The atlas has no monitoring apparatus, no logging
  schema and no notion of cost; nothing says a richer channel is unavailable.
- **Not** "an unenforceable norm is worthless." A norm that is not enforceable
  may still coordinate, and that is outside this model.
- **Not** a claim that any norm *ought* to be enforced.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Regulating AI systems is technically impossible." | needs the indistinguishable pair exhibited for a real channel |
| "So drop the rule." | the result argues for a channel that separates the acts |
| "We have detection but lack enforcement powers." | not what is refuted: only enforcement ⇒ detection is proved (under `Complete`), and `Enforces` is the existence of a response function, not authority to apply it |
| "More logging cannot fix it." | it may — `atlas-check`'s `enforcement` kind is how you check a specific channel, and returns the monitor when clean |

## Witness

`AISafetyAtlas/Examples/Sovereignty/Governance.lean`;
`Examples/Sovereignty/Checkers.lean` runs both branches of the constructive
checker.
