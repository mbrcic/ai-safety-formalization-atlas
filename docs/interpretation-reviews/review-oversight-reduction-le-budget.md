# Bridge review — `Control.OversightBudget.oversight_reduction_le_budget`

**Row `BY-005` · module `AISafetyAtlas/Control/OversightBudget.lean` · `HUMAN_REVIEW`**

Only bridge on this row. **The only quantitative bridge in the repository**, and
it carries a named witness debt.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 as an upper bound on entropy reduction, one step, plant fixed. |

## The statement

```lean
public theorem oversight_reduction_le_budget [IsProbabilityMeasure μ]
    {F : S → K → N → T} {Z : Ω → N}
    (hhaz : Measurable O.hazard) (hread : Measurable O.reading)
    (hout : Measurable O.outcome)
    [FiniteRange O.hazard] [FiniteRange O.reading] [FiniteRange O.outcome]
    (hplant : IsPlant F O.hazard O.reading Z O.outcome)
    {Δblind : ℝ} (hblind : OpenLoopBound μ F O.hazard Z Δblind) :
    entropyReduction μ O.hazard O.outcome ≤ Δblind + I[O.hazard : O.reading ; μ]
```

Touchette–Lloyd's bound read as governance. Base:
`Control.InformationLimits.entropyReduction_le_of_openLoopBound`.

## What to check

1. **It is an upper bound, never a lower one.** A regime with a rich channel may
   achieve nothing; the bound says only that it cannot achieve more. Reading it
   as a guarantee is the error a quantitative statement invites.
2. **`Δblind` is a parameter, and its value is part of the model.** A regime
   already effective blind has a large one and the theorem then says little —
   correctly, because monitoring was never load-bearing there.
3. **The two terms are separable, which is the practical content.** Mutual
   information is the only term monitoring moves, and it is a property of the
   channel rather than of effort, budget or attention.
4. **The witness debt, paid 2026-09-21.** This item read: the module's two
   corollaries — `blind_channel_buys_nothing` and
   `budget_is_the_channel_not_the_volume` — have no `Examples/` instance, the
   gate carries a raised pin (`--max-ungrounded 11 --max-unapplied 317`, was
   8/314), and *"declining to sign until a model with a real channel exists is a
   reasonable verdict"*. That model exists.
   `AISafetyAtlas.Examples.Control.OversightBudget` witnesses both at fair coins,
   where the hazard carries `log 4` and the outcome `log 2` — so the
   `0 ≤ 0 + 0` failure the item was guarding against is excluded by construction
   rather than by assertion. For the blind channel the bound is **attained**
   (`blindRegime_entropyReduction_eq`). For the duplication pair it is not, and
   `oneReading_entropyReduction_eq` names the slack rather than leaving it
   unsaid: the plant discards the reading, so the channel's `log 2` is budget
   never spent. Both channels carry `log 2` of mutual information rather than
   zero. The pin is lowered to `--max-ungrounded 3 --max-unapplied 299`, and
   the three that remain are the provably vacuous `Causal.O24Solution` pair and
   one theorem downstream of it. **The condition this item set for signing is
   met**; the verdict itself is still the reviewer's.

## Allowed claim

> Where the outcome is a fixed function of the hazard, the reading and noise
> alone, an oversight regime reduces entropy from hazard to outcome by at most
> `Δblind` (any bound on what a fixed action, chosen without the reading,
> achieves on every conditional ensemble) plus the mutual information its
> monitoring channel carries about the hazard. With the plant fixed, the second
> term is the only one monitoring moves, and it is a property of the channel
> rather than of effort or volume.

## Forbidden

- **Not** a guarantee. Upper bound only.
- **Not** about harm or risk. The quantity is entropy — uncertainty about the
  outcome relative to the hazard — not expected loss.
- **Not** about repeated or adaptive oversight. One step, with the plant fixed.
- **Not** a number for any real system. Nothing says what `I[hazard : reading]`
  is anywhere; the atlas has no monitoring stack, no telemetry and no incident.
- **Not** "monitoring does not help." It plainly does; this bounds by how much.
- **Not** a budgeting instrument. No cost and no exchange rate is modelled.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Our monitoring gives X bits, so we are Y% safer." | upper bound, and nothing is measured |
| "A second log stream doubles oversight." | the bound moves only with mutual information |
| "Oversight is information-limited in practice." | requires measuring a real channel against a real hazard |

## Witness

**None hand-written.** `oversight_reduction_le_budget` is grounded only through
the generated `Examples/Registry.lean`. See point 4.
