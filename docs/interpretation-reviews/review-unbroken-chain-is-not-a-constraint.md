# Bridge review — `Sovereignty.AmendmentLog.unbroken_chain_is_not_a_constraint`

**Row `LAND-SOV-CONST-001` · module `AISafetyAtlas/Sovereignty/AmendmentLog.lean` · `HUMAN_REVIEW`**

Only bridge on this row. Base: `Sovereignty.Constitution`.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-03 |
| Note | Accepted on the allowed claim as sharpened 2026-10-03. |

## The statement

```lean
public theorem unbroken_chain_is_not_a_constraint (origin : K) :
    ¬ ∃ κ : K, ¬ AuthorizedFrom (fun _ _ => True) origin κ
```

## What to check

1. **The graded declaration is at the *permissive* rule** `fun _ _ => True`, a
   limiting case. It is not a claim about any real rule, and the module says so.
   **A reviewer may reasonably think the limiting case is too weak to earn a
   bridge grade** — that is a fair verdict, and the declarations stay correct.
2. **The content lives in `the_rule_carries_the_assurance`** (not graded):
   authorisation is monotone, so a chain under a stricter rule is a chain under
   every weaker one; **the reverse is not proved**. That asymmetry is the reviewable
   claim. If you want the grade moved there, say so and I re-grade.
3. **This is not an argument against keeping logs.** `AuthorizedFrom` cannot even
   be evaluated without one.

## Allowed claim

> Under a rule that permits everything, an unbroken chain of authorised changes
> from the origin excludes no state at all, so that the chain is unbroken does
> not by itself establish that the record excludes anything; that depends on the
> rule. A review that confirms the record is complete without examining the rule
> has not shown that the record excludes any state.

## Forbidden

- **Not** "change logs are worthless."
- **Not** that any real change-control rule is permissive. The atlas has no model
  version, no approval workflow and no deployment.
- **Not** about tamper-evidence or log integrity. The log is assumed honest.
- **Not** about self-modifying agents specifically; they are one instance of the
  shape, not the subject.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Model change logs prove nothing." | conditional on a permissive rule, asserted of none |
| "So do not require change logs." | the log is the precondition for checking anything |
| "The chain is unbroken, so the system is where we approved it." | the inference this refuses at the limiting case |

## Witness

`AISafetyAtlas/Examples/Practitioner.lean`.
