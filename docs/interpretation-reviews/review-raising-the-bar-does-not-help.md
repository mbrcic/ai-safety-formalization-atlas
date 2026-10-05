# Bridge review — `Goodhart.RegulatoryTarget.raising_the_bar_does_not_help`

**Row `LAND-GOODHART-REGTARGET-001` · module `AISafetyAtlas/Goodhart/RegulatoryTarget.lean` · `HUMAN_REVIEW`**

Siblings: [`certified_systems_were_never_examined`](review-certified-systems-were-never-examined.md),
[`risk_unconstrained_on_certified`](review-risk-unconstrained-on-certified.md).

**The policy-legible one, and therefore the one most likely to be quoted.**

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☑ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Statement accepted 2026-10-04. AI reading withheld: the name overstates a bookkeeping corollary; it concerns only the evidential gap. |

## The statement

```lean
public theorem raising_the_bar_does_not_help {c : ℝ} (hc : P.threshold ≤ c) :
    Disjoint (selectedAt P.indicator c) P.evidenceBase
```

## What to check

1. **"Does not help" means one specific thing**: every threshold at or above the
   rule's own selects only systems outside the evidence base, so the certified
   set stays disjoint from the evidence and never moves closer. (That the
   underdetermination holds at every higher threshold too is the sibling
   `risk_unconstrained_at_every_higher_bar`, not this theorem.)
2. **It does not say tightening is harmful in any other sense.** Nothing about
   compliance cost, deterrence, coverage of dangerous systems, or whether a
   higher bar catches more of them. The name is stronger than the theorem —
   **that is the thing to decide on.**
3. It is monotone bookkeeping over `selected_disjoint_observed`, inheriting the
   extremal hypothesis.

## Allowed claim

> Raising an extremal bar does not bring the certified set closer to the evidence
> that justified the indicator; every higher threshold selects only systems the
> evidence never covered, so the instrument that looks like a remedy is the same
> instrument.

## Forbidden

- **Not** about an evidence base that grows. The evidence base is fixed in the
  model; testing or monitoring systems above the bar enlarges it and changes the
  regime, and that is not modelled — it is the repair the module names.
- **Not** "stricter regulation is counterproductive." Nothing about deterrence,
  behaviour, cost or safety outcomes is modelled.
- **Not** an argument for a lower bar. Lowering it below the evidence ceiling
  exits the extremal regime, and the module says nothing about whether that rule
  is sound.
- **Not** a claim about any real threshold.
- **Not** quantified: no rate at which the gap grows.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Proof that raising the compute threshold makes things worse." | nothing is shown worse; every higher bar only stays disjoint from the evidence base |
| "So thresholds should be lowered." | that leaves the regime the module is about; no claim is made there |
| "Tightening the rule is futile." | futile for closing the evidential gap; the theorem is silent on every other purpose |

## Witness

`AISafetyAtlas/Examples/Goodhart/RegulatoryTarget.lean`.
