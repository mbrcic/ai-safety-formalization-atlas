# Bridge review — `Knowledge.Audit.audit_certifies_audited_not_deployed`

**Row `LAND-AUDIT-LAG-001` · module `AISafetyAtlas/Knowledge/Audit.lean` · `HUMAN_REVIEW`**

Sibling: [`later_audit_does_not_close_the_gap`](review-later-audit-does-not-close-the-gap.md).
Arrow to Reuel, Bucknall et al., TMLR 04/2025, **Open Problem 63**.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

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

## What to check

1. **Both halves are asserted together and neither alone is honest.** The first
   conjunct — the audit determines the version it audited — is what makes an
   audit worth performing. The second is Open Problem 63.
2. **The second hypothesis is the entire content and it is explicit.** Two worlds
   the audit's own evidence cannot separate, differing in what was deployed.
   Given one, no decoder returns the deployed version, whatever it computes.
3. **Nothing says any real audit has such a pair.** A deployment publishing a
   signed hash of its weights has evidence this model does not carry, and under
   that evidence the collision may simply not exist. Read it as naming what a
   scheme must rule out.

## Allowed claim

> An audit is evidence gathered at one time about a target at one time, and those
> need not be the same time. Where the audit's evidence does not separate two
> worlds that differ in what was later deployed, nothing computed from that
> evidence recovers the deployed version.

## Forbidden

- **Not** "audits do not certify deployed systems." Conditional on the collision.
- **Not** "version verification is impossible." The atlas has no model registry,
  no version identity and no attestation; a cryptographically bound scheme is not
  refuted here.
- **Not** about audit quality, sampling or auditor independence.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Third-party audits cannot bind deployment; drop the requirement." | the first conjunct is why audits are worth doing; the argument is for binding evidence |
| "Signed model hashes are also defeated." | a hash is evidence this model does not carry, and the module names it as what may defeat the collision |

## Witness

`AISafetyAtlas/Examples/Knowledge/Audit.lean` exhibits the colliding pair.
