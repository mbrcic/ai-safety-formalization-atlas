module

public import AISafetyAtlas.Control.InformationLimits

/-!
# You cannot oversee better than you observe, and here is by how much

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Control.InformationLimits`, which
carries Touchette and Lloyd's theorems about a controller, an actuation channel
and noise, and names no AI system. What is added here is the reading as an
**oversight regime**, and the fact that the bound it inherits is a *number*.

## Why this one is different

Every other bridge in this repository answers a yes/no question: is the property
knowable, is the rule enforceable, does the checklist certify operation. Those
are the right shape for an obstruction and the wrong shape for a budget.

The argument this module bounds is *"add more monitoring"*. Answering it needs a
quantity, because the reply is not that monitoring never helps — it plainly does
— but that it helps **by at most the information the channel actually carries
about the hazard**. That is `oversight_reduction_le_budget`, and the right-hand
side has two terms the practitioner can separate: what a blind regime would
achieve anyway, and the mutual information of the monitoring channel.

## What is stated

`Oversight` bundles a hazard, what the overseer reads, and the outcome.

* `oversight_reduction_le_budget` — the reduction in uncertainty about the
  outcome is at most `Δblind + I[hazard : reading]`.
* `blind_channel_buys_nothing` — a monitoring channel independent of the hazard
  contributes zero, so the regime does no better than acting blind. Not "little
  better": the bound collapses to the blind term exactly.
* `budget_is_the_channel_not_the_volume` — the bound depends on the channel's
  mutual information and on nothing else about it, so duplicating a reading, or
  sampling it more often, moves the bound only insofar as it moves that quantity.

## What this does not claim

The atlas has **no monitoring stack, no telemetry and no incident**. Nothing here
says what `I[hazard : reading]` is for any real system, and measuring it is an
empirical question this repository does not touch.

The bound is an upper bound on what oversight can achieve, not a lower bound: a
regime with a rich channel may still achieve nothing, because the bound says only
that it cannot achieve more. Reading it as a guarantee is the error it is easiest
to make.

`Δblind` is a parameter and its value is part of the model. A regime that is
already effective blind has a large one, and the theorem then says little —
correctly, because in that regime monitoring was never the load-bearing part.

Identifying `reading` with any real monitoring channel is layer 4 and is not done
here.

## The witness that was owed, and what it had to clear

This section read *"a witness is owed"* until 2026-09-21. The debt was named
rather than hidden: `blind_channel_buys_nothing` and
`budget_is_the_channel_not_the_volume` had no `Examples/` instance, and
`scripts/agent_gate.sh` carried a ceiling raised by two. The reason was never
that the statements are doubtful — they are two lines from the bound above — but
that inhabiting their hypotheses needs a probability space with `IsPlant` and
`OpenLoopBound` discharged, and every *cheap* model of those makes every entropy
zero. A witness where the bound reads `0 ≤ 0 + 0` would satisfy the checker and
establish nothing, which is exactly the failure the witness discipline exists to
catch.

`AISafetyAtlas.Examples.Control.OversightBudget` is that witness, built to that
standard. Both regimes run on fair coins, so every entropy in sight is positive.
`blindRegime` has a hazard carrying `log 4` and a channel that is a genuine coin
independent of it: `blindRegime_entropyReduction_eq` shows the regime still
reduces uncertainty by `log 2`, the blind term **exactly**, so the bound is
attained — monitoring bought nothing while the regime achieved something, which
is the distinction this module exists to draw. `oneReadingRegime` and
`twoReadingsRegime` differ in volume and in nothing else, one recording the same
coin twice, and `duplication_mutualInfo_eq` puts both channels at `log 2` rather
than at zero. That second bound is **not** attained and
`oneReading_entropyReduction_eq` says by how much: the plant discards the
reading, so the channel's half of the budget is never spent, which is this
module's own caveat that the bound is a ceiling and not a guarantee.
-/

namespace AISafetyAtlas.Control.OversightBudget

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory
open AISafetyAtlas.Control

universe uΩ uS uK uN uT

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K]
variable [MeasurableSpace N] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K]
variable [MeasurableSingletonClass N] [MeasurableSingletonClass T]
variable [Countable S] [Countable K] [Countable N] [Countable T]
variable {μ : Measure Ω}

/--
**An oversight regime**: what could go wrong, what the overseer sees, and what
happens.

* `hazard ω` is the state the regime exists to constrain.
* `reading ω` is everything the monitoring channel delivers.
* `outcome ω` is the state after the regime has acted.

Nothing constrains `reading` to be informative, honest or complete. The theorems
take whatever relationship they need as a hypothesis, and the whole content is
that one of those hypotheses is a *number*.
-/
public structure Oversight (Ω : Type uΩ) (S : Type uS) (K : Type uK) (T : Type uT) where
  /-- What the regime exists to constrain. -/
  hazard : Ω → S
  /-- Everything the monitoring channel delivers. -/
  reading : Ω → K
  /-- The state after the regime has acted. -/
  outcome : Ω → T

variable (O : Oversight Ω S K T)

omit [MeasurableSpace N] [MeasurableSingletonClass N] [Countable N] in
/--
**The budget.** An oversight regime reduces uncertainty about the outcome by at
most what it would achieve blind, plus the information its channel carries about
the hazard.

This is Touchette and Lloyd's bound read as governance. The two terms are
separable and that is the practical content: the second is the only one
monitoring moves, and it is bounded by a property of the channel rather than by
effort, budget or attention.
-/
public theorem oversight_reduction_le_budget [IsProbabilityMeasure μ]
    {F : S → K → N → T} {Z : Ω → N}
    (hhaz : Measurable O.hazard) (hread : Measurable O.reading)
    (hout : Measurable O.outcome)
    [FiniteRange O.hazard] [FiniteRange O.reading] [FiniteRange O.outcome]
    (hplant : IsPlant F O.hazard O.reading Z O.outcome)
    {Δblind : ℝ} (hblind : OpenLoopBound μ F O.hazard Z Δblind) :
    entropyReduction μ O.hazard O.outcome ≤ Δblind + I[O.hazard : O.reading ; μ] :=
  entropyReduction_le_of_openLoopBound μ hhaz hread hout hplant hblind

omit [MeasurableSpace N] [MeasurableSingletonClass N] [Countable N] in
/--
**A channel that says nothing about the hazard buys nothing.**

When the reading is informationally independent of the hazard, the budget
collapses to the blind term exactly. Not "the gain is small" — the bound is the
same bound the regime had before the channel existed, so every argument for the
monitoring rests on the mutual information being positive, which is a measurable
claim about the channel and not a matter of design intent.
-/
public theorem blind_channel_buys_nothing [IsProbabilityMeasure μ]
    {F : S → K → N → T} {Z : Ω → N}
    (hhaz : Measurable O.hazard) (hread : Measurable O.reading)
    (hout : Measurable O.outcome)
    [FiniteRange O.hazard] [FiniteRange O.reading] [FiniteRange O.outcome]
    (hplant : IsPlant F O.hazard O.reading Z O.outcome)
    {Δblind : ℝ} (hblind : OpenLoopBound μ F O.hazard Z Δblind)
    (hindep : I[O.hazard : O.reading ; μ] = 0) :
    entropyReduction μ O.hazard O.outcome ≤ Δblind := by
  have h := oversight_reduction_le_budget O hhaz hread hout hplant hblind
  rw [hindep, add_zero] at h
  exact h

omit [MeasurableSpace N] [MeasurableSingletonClass N] [Countable N] in
/--
**The budget is the channel, not the volume.**

Two regimes whose channels carry the same information about the hazard inherit
the same bound, whatever else differs between them. So a proposal that adds
readings, retains them longer, or samples them more often improves this bound
only through the quantity named, and an argument that does not mention that
quantity is not an argument about this bound at all.
-/
public theorem budget_is_the_channel_not_the_volume [IsProbabilityMeasure μ]
    {F : S → K → N → T} {Z : Ω → N} (O' : Oversight Ω S K T)
    (hhaz : Measurable O.hazard) (hread : Measurable O.reading)
    (hout : Measurable O.outcome)
    [FiniteRange O.hazard] [FiniteRange O.reading] [FiniteRange O.outcome]
    (hplant : IsPlant F O.hazard O.reading Z O.outcome)
    {Δblind : ℝ} (hblind : OpenLoopBound μ F O.hazard Z Δblind)
    (hsame : I[O'.hazard : O'.reading ; μ] = I[O.hazard : O.reading ; μ]) :
    entropyReduction μ O.hazard O.outcome ≤ Δblind + I[O'.hazard : O'.reading ; μ] := by
  rw [hsame]
  exact oversight_reduction_le_budget O hhaz hread hout hplant hblind

end AISafetyAtlas.Control.OversightBudget
