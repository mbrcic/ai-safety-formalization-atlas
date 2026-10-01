# Bridge review — `Goodhart.RegulatoryTarget.risk_unconstrained_on_certified`

**Row `LAND-GOODHART-REGTARGET-001` · module `AISafetyAtlas/Goodhart/RegulatoryTarget.lean` · `HUMAN_REVIEW`**

Siblings: [`certified_systems_were_never_examined`](review-certified-systems-were-never-examined.md),
[`raising_the_bar_does_not_help`](review-raising-the-bar-does-not-help.md).

**The strongest of the three.**

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem risk_unconstrained_on_certified
    (link : ℝ → ℝ) (ε : ℝ) (risk : System → ℝ)
    (hfit : FitsOn P.evidenceBase P.indicator risk link ε) (d : ℝ) :
    ∃ risk', FitsOn P.evidenceBase P.indicator risk' link ε ∧
      EqOn risk risk' P.evidenceBase ∧
      ∀ s ∈ certified P, risk s - risk' s = d
```

## What to check

1. **The quantifier is the content.** This is *not* "two risk models disagree
   somewhere", which any two functions satisfy. For **any** fitting risk function
   and **any** displacement `d`, a second fits equally well, agrees on the whole
   evidence base, and is off by exactly `d` at **every** certified system.
2. **Nothing is quantified about likelihood.** The displacement is arbitrary,
   which makes the underdetermination total rather than measured. No rate, no
   speed, no ranking of proxies follows.
3. **It inherits the extremal hypothesis** through
   `certified_disjoint_evidenceBase`. Where the bar sits inside the evidence, it
   does not apply.
4. **The positive half is `risk_bounded_on_evidence_base`** and is not graded
   `BRIDGE`. Signing this without reading it signs half a module.

## Allowed claim

> Where the bar is extremal, the fitted indicator-risk relationship leaves the
> true risk at certified systems unconstrained: whatever the truth is, the
> evidence permits it to be off by any amount you name, uniformly across
> everything the rule certifies.

## Forbidden

- **Not** a claim that the risk *is* different there. It is a statement about
  what the evidence constrains, not about what is true.
- **Not** a claim about any real regulatory scheme's evidence base.
- **Not** an argument to ignore the rule, or to ignore the indicator. Inside the
  evidence base the indicator predicts risk to the tolerance it was fitted at.
- **Not** quantified, ranked or probabilistic.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "The risk could be anything, so the threshold is worthless." | about evidential underdetermination, not about the risk |
| "Any two risk models disagree; this is trivial." | the quantifier is over *every* fitting model with a *prescribed* displacement at *every* certified system |
| "So we cannot regulate frontier systems." | the repair the module names is a wider evidence base, and it says so |

## Witness

`AISafetyAtlas/Examples/Goodhart/RegulatoryTarget.lean` — the displacement is
arbitrary at a bar of 100 as much as at 2.
