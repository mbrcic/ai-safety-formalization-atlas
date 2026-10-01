module

public import AISafetyAtlas.Goodhart.Extremal

/-!
# Choosing a regulatory target: what the evidence for the bar stops covering

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four
layers: *(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Goodhart.Extremal`, which is about
a proxy, a threshold and a fitted relationship, and names no regulator and no
rule. What is added here is the arrow to a governance question, stated over a
model of a bright-line rule.

## The question

Reuel, Bucknall et al., *Open Problems in Technical AI Governance*, TMLR
04/2025:

> **Open Problem 92.** *"What system properties (if any) are the most reliable
> indicators of risk, and thus candidates for serving as regulatory targets?"*

R#92 has two halves. **Which** property indicates risk is empirical and is not
addressed here. What happens to a property **once it is made a target** is the
half this module states, and the phrase *"and thus candidates for serving as
regulatory targets"* is exactly the step it is about.

## The answer this module states

`RegulatoryScheme` is a bright-line rule: an indicator measured on systems, a
threshold a system must clear, and the **evidence base** — the systems on which
the indicator's link to risk was actually established. The one structural
hypothesis is that the threshold sits above everything the evidence base
exhibits. That is the **extremal regime**, and it is a modelling choice: the
rule demands more than any studied system displayed. It is the regime
`AISafetyAtlas.Goodhart.Extremal` is about, and the regime a rule is in when it
is set to bind on systems more capable than those anyone has examined.

`certified_systems_were_never_examined` is then immediate and is the whole
point: **every system the rule certifies is a system the rule's evidence never
covered.** The two sets are disjoint, so "compliant" and "in the evidence base"
cannot both hold.

`risk_unconstrained_on_certified` says what that costs. Take any risk function
fitting the established link on the evidence base, and any displacement `d`.
There is a second risk function fitting that link equally well, agreeing with
the first everywhere in the evidence base — so nothing observed there tells them
apart — and differing from it by exactly `d` at every certified system. Not
"some models disagree", which any two functions satisfy, but: whatever the truth
is, the evidence permits it to be off by any amount you name, everywhere the
rule certifies.

`raising_the_bar_does_not_help` is the policy-legible corollary. Tightening the
threshold moves the certified set **further** from the evidence base, never
closer, and the underdetermination holds at every higher threshold too. The
instrument that looks like a remedy is the same instrument.

The positive half is `risk_bounded_on_evidence_base`, and it is stated first
among the consequences for a reason: **inside** the evidence base the indicator
does predict risk, to within the tolerance the fit was established at. That is
why measuring indicators is worth doing, and it is the thing the rest of the
module does not deny.

## What this module does not claim

**No proposed regulatory target is evaluated.** Whether a named property is or
is not a good indicator of risk — R#92's first half — is empirical, and nothing
here bears on it.

**The regulated party's behaviour is not modelled.** There is no optimizer, no
deadline and no enforcement; `selectedAt` is a set of systems that clear a
number, which is what a bright line selects and not how a firm responds to one.
A model of a party optimizing against the bar is a different and harder object
and is not this.

**Nothing is quantified.** The displacement `d` is arbitrary, which makes the
underdetermination total rather than measured; no rate, no speed and no ranking
of proxies follows.

**Only the extremal regime is modelled.** A threshold set *inside* the range the
evidence base displays -- at the median of studied systems, say -- certifies some
systems that were studied, and `certified_disjoint_evidenceBase` simply does not
apply to it. Nothing here says such a rule is sound either; it says only that
this module is about the other case.

The mathematics is atlas-original, routed as such: Manheim and Garrabrant,
*Categorizing Variants of Goodhart's Law*, arXiv:1803.04585v4, is cited by
`AISafetyAtlas.Goodhart.Extremal` for its **model**, and numbers no theorem. So
this bridge rests on this repository's sharpening of that prose and not on a
published theorem's authority.
-/

namespace AISafetyAtlas.Goodhart.RegulatoryTarget

open Set
open AISafetyAtlas.Goodhart.Extremal

universe u

variable {System : Type u}

/--
**A bright-line rule over a measured indicator.**

`evidenceBase` is the set of systems on which the indicator's relationship to
risk was actually established — the studied population, not the regulated one.

`observedCeiling_lt_threshold` puts the scheme in the **extremal regime**: the
bar sits above everything already examined. This is an assumption about the
rule, not a definition of one -- a threshold set inside the studied range is an
ordinary rule and is simply a different regime, not modelled here.
-/
public structure RegulatoryScheme (System : Type u) where
  /-- The regulatory target: the property actually measured on a system. -/
  indicator : System → ℝ
  /-- The systems on which the indicator's link to risk was established. -/
  evidenceBase : Set System
  /-- An upper bound on the indicator across the evidence base. -/
  observedCeiling : ℝ
  /-- The bright line a system must clear to be certified. -/
  threshold : ℝ
  /-- The indicator is bounded by the ceiling on the evidence base. -/
  indicator_le_observedCeiling : ∀ s ∈ evidenceBase, indicator s ≤ observedCeiling
  /-- The bar sits above everything already examined. -/
  observedCeiling_lt_threshold : observedCeiling < threshold

variable (P : RegulatoryScheme System)

/-- **The certified systems**: those whose indicator clears the bar. -/
@[expose] public def certified : Set System :=
  selectedAt P.indicator P.threshold

/-- Membership, unfolded. -/
@[simp] public theorem mem_certified {s : System} :
    s ∈ certified P ↔ P.threshold ≤ P.indicator s := Iff.rfl

/-! ## What the indicator does establish -/

/--
**Inside the evidence base, the indicator predicts risk.** To within the
tolerance the link was fitted at, which is the whole reason to measure an
indicator.

This is the half the rest of the module does not deny, and it is stated first so
that nothing below reads as a claim that indicators are useless.
-/
public theorem risk_bounded_on_evidence_base {link : ℝ → ℝ} {ε : ℝ}
    {risk : System → ℝ} (hfit : FitsOn P.evidenceBase P.indicator risk link ε)
    {s : System} (hs : s ∈ P.evidenceBase) :
    |risk s - link (P.indicator s)| ≤ ε :=
  hfit s hs

/-! ## Where it stops establishing it -/

/--
**Every certified system is one the evidence never covered.**

Immediate from the structural hypothesis, by `selected_disjoint_observed`. The
disjointness is the sharp form: a system cannot be both certified and in the
population the certification's link was established on.
-/
public theorem certified_disjoint_evidenceBase :
    Disjoint (certified P) P.evidenceBase :=
  selected_disjoint_observed P.indicator P.evidenceBase
    P.indicator_le_observedCeiling P.observedCeiling_lt_threshold

/-- The same read one system at a time, which is the sentence R#92's second half
turns on. -/
public theorem certified_systems_were_never_examined {s : System}
    (hs : s ∈ certified P) : s ∉ P.evidenceBase :=
  Set.disjoint_left.mp (certified_disjoint_evidenceBase P) hs

/--
**And so the evidence does not constrain risk there.**

For any risk function fitting the established link on the evidence base, and any
displacement `d`, there is a second risk function that fits that link equally
well, agrees with the first on the whole evidence base, and differs from it by
exactly `d` at every certified system.

The quantifier is the content. This is not "two models disagree somewhere",
which any two functions satisfy; it is that whatever the true risk is, nothing
in the evidence rules out its being off by any amount you name, uniformly across
everything the rule certifies.
-/
public theorem risk_unconstrained_on_certified
    (link : ℝ → ℝ) (ε : ℝ) (risk : System → ℝ)
    (hfit : FitsOn P.evidenceBase P.indicator risk link ε) (d : ℝ) :
    ∃ risk', FitsOn P.evidenceBase P.indicator risk' link ε ∧
      EqOn risk risk' P.evidenceBase ∧
      ∀ s ∈ certified P, risk s - risk' s = d :=
  fits_underdetermined_off_observed P.indicator link ε
    (certified_disjoint_evidenceBase P) risk hfit d

/-! ## Tightening the rule -/

/--
**Raising the bar does not repair it.** Every threshold at or above the rule's
own selects only systems outside the evidence base, so the certified set moves
further from the evidence rather than closer.
-/
public theorem raising_the_bar_does_not_help {c : ℝ} (hc : P.threshold ≤ c) :
    Disjoint (selectedAt P.indicator c) P.evidenceBase :=
  selected_disjoint_observed P.indicator P.evidenceBase
    P.indicator_le_observedCeiling
    (lt_of_lt_of_le P.observedCeiling_lt_threshold hc)

/--
**And the underdetermination survives the tightening**, with the same arbitrary
displacement. So the natural response to a rule that is not binding enough —
demand a higher score — leaves the epistemic situation exactly where it was.
-/
public theorem risk_unconstrained_at_every_higher_bar {c : ℝ} (hc : P.threshold ≤ c)
    (link : ℝ → ℝ) (ε : ℝ) (risk : System → ℝ)
    (hfit : FitsOn P.evidenceBase P.indicator risk link ε) (d : ℝ) :
    ∃ risk', FitsOn P.evidenceBase P.indicator risk' link ε ∧
      EqOn risk risk' P.evidenceBase ∧
      ∀ s ∈ selectedAt P.indicator c, risk s - risk' s = d :=
  fits_underdetermined_off_observed P.indicator link ε
    (raising_the_bar_does_not_help P hc) risk hfit d

/--
**Open Problem 92's second half, both sides together.** Inside the evidence base
the indicator predicts risk to within the fitted tolerance; at every certified
system the evidence permits the risk to be off by any amount named. A consumer
holding this pair has the precise statement of what choosing an indicator as a
target does: it does not make the indicator a worse measurement, it moves the
population it certifies outside the one it was measured on.
-/
public theorem indicator_informative_and_certification_unconstrained
    (link : ℝ → ℝ) (ε : ℝ) (risk : System → ℝ)
    (hfit : FitsOn P.evidenceBase P.indicator risk link ε) (d : ℝ) :
    (∀ s ∈ P.evidenceBase, |risk s - link (P.indicator s)| ≤ ε) ∧
      ∃ risk', FitsOn P.evidenceBase P.indicator risk' link ε ∧
        EqOn risk risk' P.evidenceBase ∧
        ∀ s ∈ certified P, risk s - risk' s = d :=
  ⟨fun _ hs => risk_bounded_on_evidence_base P hfit hs,
    risk_unconstrained_on_certified P link ε risk hfit d⟩

end AISafetyAtlas.Goodhart.RegulatoryTarget
