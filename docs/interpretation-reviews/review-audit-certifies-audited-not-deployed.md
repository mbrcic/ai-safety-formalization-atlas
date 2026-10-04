# Bridge review — `Knowledge.Audit.audit_certifies_audited_not_deployed`

**Row `LAND-AUDIT-LAG-001` · module `AISafetyAtlas/Knowledge/Audit.lean` · `HUMAN_REVIEW`**

Sibling: [`later_audit_does_not_close_the_gap`](review-later-audit-does-not-close-the-gap.md).
Arrow to Reuel, Bucknall et al., TMLR 04/2025, **Open Problem 63**.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 on the rewritten claim: an audit certifies a running system only through records that bind the audited artifact to it. |

## The statement

```lean
public theorem audit_certifies_audited_not_deployed
    (A : AuditSetup Ω T I V) {tAudit tDeploy : T}
    (haudited : Temporal.KnowableFrom A.report A.version tAudit tAudit)
    (hcollide : ∃ ω ω' : Ω, A.report tAudit ω = A.report tAudit ω' ∧
      A.version tDeploy ω ≠ A.version tDeploy ω') :
    Temporal.KnowableFrom A.report A.version tAudit tAudit ∧
      ¬ Temporal.KnowableFrom A.report A.version tAudit tDeploy
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

1. **The first half is the hypothesis `haudited` repeated, not a result.** Where
   it holds, the records at `tAudit` determine the version that was audited.
2. **The second hypothesis is the content.** Two worlds whose records at
   `tAudit` are identical while the version running at the moment in question
   differs. Given that, the audit's records cannot determine which version ran
   then — whatever is computed from them. This is Open Problem 63: what was
   audited and what was run need not be the same thing.
3. **Nothing says any real audit has such a pair.** Records that bind the audited
   artifact to the running one — a signed hash of the weights, an attestation
   from the deployment — are evidence this model does not carry, and with them
   the collision may not exist. Read the statement as naming what an audit
   scheme must rule out.
4. **Only the audit's own records are considered.** Records from other moments
   or other sources are not in the statement.

## Allowed claim

> An audit's records determine what it looked at. If those same records are
> consistent with two different versions running at the moment in question, they
> do not determine which one ran then; nothing computed from them does. An audit
> certifies a running system only through records that tie the audited artifact
> to it.

## Forbidden

- **Not** "audits do not certify deployed systems." Only where the records admit
  such a pair.
- **Not** "version verification is impossible." Binding records — hashes,
  attestations — are outside the model and are what remove the collision.
- **Not** a claim about later or additional evidence, which is not considered.
- **Not** about audit quality, sampling or auditor independence.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Third-party audits cannot bind deployment; drop the requirement." | the negative half needs the collision, which binding records remove; the argument is for binding records, not against audits |
| "Signed model hashes are also defeated." | a hash is evidence the model does not carry, and it is what removes the collision |

## Witness

`AISafetyAtlas/Examples/Knowledge/Audit.lean` exhibits the colliding pair.
