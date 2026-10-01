# Bridge review — `Oversight.forces_of_constant_effect_of_not_knowable`

**Row `LAND-OVERSIGHT-VARIETY-001` · module `AISafetyAtlas/Oversight/VarietyBound.lean` · `HUMAN_REVIEW`**

Sibling bridge: [`forces_of_constant_effect`](review-forces-of-constant-effect.md).
Context: the [`BY-004` package](review-oversight-varietybound.md), signed
2026-08-17.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem forces_of_constant_effect_of_not_knowable {effect : Sit → Act → Out}
    {observe : Sit → Obs} {hazard : Sit → Bool} {a : Act} {target : Out}
    (_hunknown : ¬ AISafetyAtlas.Knowledge.Knowable observe hazard)
    (hconst : ∀ σ, effect σ a = target) :
    Forces effect observe (fun _ => a) target :=
  forces_of_constant_effect hconst
```

## What to check

1. **`_hunknown` is unused, and the underscore says so.** This is
   `forces_of_constant_effect` restated with an explicit unknowability
   hypothesis, so that the independence is visible in a single statement rather
   than inferred from two. **Decide whether a deliberately-unused hypothesis
   earns a `BRIDGE` grade** — the argument for it is that the statement is the
   claim (*control survives total unknowability*) and a reader cannot see that in
   the shorter theorem; the argument against is that it proves nothing new.
2. **The unknowability is total, not partial.** `¬ Knowable observe hazard` means
   no decoder at all recovers the hazard from what the overseer reads. The
   theorem holds at that extreme, which is what makes it a boundary rather than a
   trade-off.
3. It is the exact counterpart of `not_forces_of_card_lt`, which holds at
   **perfect** observation. The pair is the claim; each half alone is misleading.

## Allowed claim

> An overseer can hold the outcome to a target even when its observations
> determine nothing whatever about the hazard, provided some available
> intervention produces that outcome in every situation. Together with the
> counting bound — which bites at perfect observation — this makes coverage and
> control independent capacities in both directions: neither substitutes for the
> other.

## Forbidden

- **Not** "observation is worthless." The atlas bounds decoder error rates
  through `Knowledge.Entropy` when observation *is* the binding constraint.
- **Not** a claim that the flattening intervention exists anywhere.
- **Not** a probabilistic or partial statement. `Forces` is certainty in every
  situation.
- **Not** an argument about deception or capability; `effect` is a fixed table
  and a system that changes it is outside the model.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Blind oversight works." | conditional on `hconst`, which is the whole strength and is assumed |
| "So interpretability is unnecessary." | the hypothesis supplies by fiat the control that interpretability is usually sought in order to obtain |
| "The unused hypothesis means the theorem is vacuous." | it is not vacuous — it is the shorter theorem restated at an extreme, and the witness exhibits the extreme |

## Witness

`AISafetyAtlas/Examples/Oversight/VarietyBound.lean` via
`coverage_and_control_are_independent`; grounded through
`Examples/Registry.lean` as well.
