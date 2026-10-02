# Bridge review — `Knowledge.Audit.later_audit_does_not_close_the_gap`

**Row `LAND-AUDIT-LAG-001` · module `AISafetyAtlas/Knowledge/Audit.lean` · `HUMAN_REVIEW`**

Sibling: [`audit_certifies_audited_not_deployed`](review-audit-certifies-audited-not-deployed.md).

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem later_audit_does_not_close_the_gap [Preorder T]
    (A : AuditSetup Ω T I V) {tAudit tLater tDeploy : T}
    (hmono : Temporal.EvidenceMonotone A.report)
    (hle : tAudit ≤ tLater)
    (haudited : Temporal.KnowableFrom A.report A.version tAudit tAudit)
    (hcollide : Temporal.CollisionAt A.report A.version tDeploy) :
    Temporal.KnowableFrom A.report A.version tLater tAudit ∧
      ¬ Temporal.KnowableAt A.report A.version tDeploy
```

## What to check

1. **It is genuinely two-sided.** Under `EvidenceMonotone`, a later audit
   determines everything an earlier one did — that is why re-auditing is not
   pointless. The negative half is that a collision **at** the deployment time
   concerns the evidence available at that time, and evidence gathered elsewhere
   does not touch it.
2. **`EvidenceMonotone` is a real hypothesis**: evidence accumulates and is never
   lost. A regime that discards logs is not an instance.
3. **This is the repair-refutation**, so it will be read as "auditing more often
   is useless". It says something narrower: more auditing buys knowledge of the
   past and not contemporaneous knowledge.

## Allowed claim

> Auditing again later, with cumulative evidence, recovers more about the past;
> it does not make the contemporaneous question answerable, because a collision at
> the deployment time is a statement about that time alone. So the repair belongs
> in the evidence rather than in the schedule.

## Forbidden

- **Not** "re-auditing is pointless." The first conjunct says the opposite.
- **Not** "continuous monitoring cannot work." A monitor that reads evidence *at*
  the deployment time is not the object here; the theorem is about evidence from
  other times.
- **Not** a claim that any real regime has the collision.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Audit frequency does not matter." | frequency buys the past, which the first conjunct affirms |
| "So do not bother re-auditing." | `knowableFrom_mono` is stated precisely to block this |
| "Real-time monitoring is also defeated." | a collision *at* `tDeploy` is the hypothesis, not a conclusion about evidence taken at `tDeploy` |

## Witness

`AISafetyAtlas/Examples/Knowledge/Audit.lean`.
