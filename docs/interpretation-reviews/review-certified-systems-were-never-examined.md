# Bridge review — `Goodhart.RegulatoryTarget.certified_systems_were_never_examined`

**Row `LAND-GOODHART-REGTARGET-001` · module `AISafetyAtlas/Goodhart/RegulatoryTarget.lean` · `HUMAN_REVIEW`**

Siblings: [`risk_unconstrained_on_certified`](review-risk-unconstrained-on-certified.md),
[`raising_the_bar_does_not_help`](review-raising-the-bar-does-not-help.md).
Arrow to Reuel, Bucknall et al., TMLR 04/2025, **Open Problem 92**.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☑ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Statement accepted 2026-10-04. AI reading withheld: immediate from the extremal hypothesis, with a fixed evidence base. |

## The statement

```lean
public theorem certified_systems_were_never_examined {s : System}
    (hs : s ∈ certified P) : s ∉ P.evidenceBase
```

`RegulatoryScheme` is a bright-line rule: an indicator, a threshold, and the
**evidence base** — the systems on which the indicator's link to risk was
established. The one structural hypothesis is `observedCeiling_lt_threshold`: the
bar sits strictly above everything the evidence exhibits.

## What to check

1. **The extremal hypothesis is the whole modelling commitment and it is a
   choice.** A threshold set *inside* the range the evidence displays certifies
   systems that were studied, and this simply does not apply. Decide whether "a
   bar set to bind on systems more capable than anyone has examined" is a fair
   reading of that hypothesis — everything else is mechanical once it holds.
2. **The mathematics is atlas-original.** Manheim and Garrabrant number no
   theorem, so this rests on this repository's sharpening of prose, not on a
   published result's authority.
3. The proof is `Set.disjoint_left` on `certified_disjoint_evidenceBase`. One
   line, read one system at a time — which is the sentence R#92's second half
   turns on.

## Allowed claim

> Where a bright-line rule's threshold sits above everything its own evidence
> base exhibits, every system the rule certifies is one that evidence never
> covered. "Compliant" and "in the evidence base" cannot both hold.

## Forbidden

- **Not** about an evidence base that grows. The evidence base is fixed in the
  model; testing or monitoring systems above the bar enlarges it and changes the
  regime, and that is not modelled — it is the repair the module names.
- **Not** "bright-line thresholds do not work." Confined to the extremal regime.
- **Not** an evaluation of any proposed target. Which property indicates risk —
  R#92's first half — is empirical and untouched.
- **Not** a claim about how firms respond. No optimizer, no deadline, no
  enforcement; `selectedAt` is a set of systems clearing a number.
- **Not** a claim that inside-the-evidence rules are sound either.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Compute thresholds are proven ineffective." | needs the extremal hypothesis *and* a layer-4 assignment of `indicator`; neither is made |
| "So certification is meaningless." | `risk_bounded_on_evidence_base` says that, given a fit of the link (`hfit`), the indicator predicts risk inside the evidence base |
| "This is a published theorem." | atlas-original |

## Witness

`AISafetyAtlas/Examples/Goodhart/RegulatoryTarget.lean`: link fitted exactly on
systems scoring ≤ 1, bar at 2, system 3 certified and never examined.
