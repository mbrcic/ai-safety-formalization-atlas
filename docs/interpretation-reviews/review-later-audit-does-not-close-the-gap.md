# Bridge review — `Knowledge.Audit.later_audit_does_not_close_the_gap`

**Row `LAND-AUDIT-LAG-001` · module `AISafetyAtlas/Knowledge/Audit.lean` · `HUMAN_REVIEW`**

Sibling: [`audit_certifies_audited_not_deployed`](review-audit-certifies-audited-not-deployed.md).

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☑ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Statement accepted 2026-10-04. AI reading withheld: both halves are close to definitional, and the name overstates them; a later audit about the moment in question is outside the statement. |

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

## The model, in plain terms

- A timeline of moments. `version t` is the model version actually running at
  moment `t`.
- `report t` is the record an audit performed at moment `t` can read.
  `EvidenceMonotone` says records accumulate and are never lost: a later record
  contains everything an earlier one did — a historical log.
- The moments named `tAudit` and `tDeploy` are not special. `tDeploy` is any
  moment in question — a release, the moment harm occurred, anything — and
  `tAudit` is the moment an audit looked at.
- A *collision* at a moment is two possible worlds whose records at that moment
  are identical while the version running then differs.

## What to check

1. **The first half needs `hmono`.** With a log that keeps history, an audit at a
   later moment knows at least what the audit at `tAudit` knew about the version
   at `tAudit`. A regime that discards records is not an instance.
2. **The second half is about one moment only.** If the records at the moment in
   question collide, an audit performed **at that moment** cannot tell which
   version was running. That is `not_knowableAt_of_collisionAt`, and it is close
   to the definition: the records do not contain the answer.
3. **Neither half concerns a later audit asking about the moment in question.**
   A later audit reads the records of that moment **and everything recorded
   since** — later logs, outputs, incident reports, forensics — and may well
   determine which version was running. The declaration's name, *later audit does
   not close the gap*, suggests otherwise; that reading is not supported. Only
   the narrow version follows: a later audit holding *only* the records of the
   moment in question gains nothing by re-reading them.

## Allowed claim

> Fix a moment in question. If the records existing at that moment cannot tell
> two different model versions apart, an audit performed at that moment cannot
> determine which version was running. With records that accumulate, a later
> audit knows at least what an earlier audit knew about the moment it examined.
> Nothing here concerns a later audit about the moment in question: records
> added since may well reveal which version was running.

## Forbidden

- **Not** "a later audit cannot find out what was running." Records added after
  the moment in question are outside the statement.
- **Not** "re-auditing is pointless." The first half says a later audit keeps
  what an earlier one knew.
- **Not** "continuous monitoring cannot work." A monitor whose records separate
  the versions has no collision and is not an instance.
- **Not** a claim that any real regime has such a collision.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Audit frequency does not matter." | no schedules are compared; the statement only says a later audit keeps what an earlier one knew |
| "After an incident, we can never establish which model was running." | the statement concerns records at the moment itself; later records are not covered and may settle it |
| "Real-time monitoring is also defeated." | only where the collision holds, which is assumed; records that separate the versions remove it |

## Witness

`AISafetyAtlas/Examples/Knowledge/Audit.lean`.
