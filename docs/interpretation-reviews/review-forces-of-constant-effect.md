# Bridge review — `Oversight.forces_of_constant_effect`

**Row `LAND-OVERSIGHT-VARIETY-001` · module `AISafetyAtlas/Oversight/VarietyBound.lean` · `HUMAN_REVIEW`**

Sibling bridge on this row:
[`forces_of_constant_effect_of_not_knowable`](review-forces-of-constant-effect-of-not-knowable.md),
signed separately. The row's third relative, `BY-004`'s
`not_forces_of_card_lt`, was accepted at `REVIEWED` on 2026-08-17 —
[package](review-oversight-varietybound.md), which argues the pair and is the
context for this one.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 as the control-without-coverage corner paired with BY-004's not_forces_of_card_lt. |

## The statement

```lean
public theorem forces_of_constant_effect {effect : Sit → Act → Out} {observe : Sit → Obs}
    {a : Act} {target : Out} (hconst : ∀ σ, effect σ a = target) :
    Forces effect observe (fun _ => a) target :=
  fun σ => hconst σ
```

One intervention that flattens every situation onto the target forces the
outcome, whatever the overseer observes — the constant policy ignores `observe`.

## What to check

1. **The proof is one line and that is the point.** This is the *second corner*:
   control with no observation. It exists to bound
   `not_forces_of_card_lt` from the other side, and a reader who sees only the
   counting bound will read the cluster as "oversight needs more interventions",
   which is not what it says.
2. **`hconst` is a hypothesis about the world, not a policy recommendation.** A
   table where one intervention flattens every situation is a strong and unusual
   property. The theorem does not say such an intervention exists anywhere.
3. **`observe` is quantified but unused.** Confirm that is deliberate — it is the
   content: forcing *by a constant policy* is a property of the effect table
   alone, and `Knowable` is a property of the observation; the Examples'
   `coverage_and_control_are_independent` shows neither implies the other.

## Allowed claim

> An overseer can hold the outcome to a target while distinguishing nothing about
> the situation, provided some available intervention produces that outcome in
> every situation. Coverage of the situation space is not a prerequisite for
> control of the outcome.

## Forbidden

- **Not** "monitoring is unnecessary." Conditional on a flattening intervention
  existing, which is an empirical claim about the effect table and is not made.
- **Not** a recommendation to build such an intervention. No cost, no side
  effect and no feasibility is modelled.
- **Not** a claim about any real oversight arrangement.
- **Not** about a system that changes its own effect table. `effect` is fixed;
  adaptation, deception or drift are outside the model.
- **Not** a statement about partial control. `Forces` is a single target in every
  situation, with certainty.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Oversight can skip observation." | requires a flattening intervention; the theorem assumes one rather than supplying one |
| "So a kill switch replaces monitoring." | a kill switch that flattens every situation onto a safe outcome is exactly `hconst`, and whether any real one does is layer 4 |
| "Coverage results already cover this." | those are about deciding a hazard; this is about forcing an outcome, and the two are independent |

## Witness

`AISafetyAtlas/Examples/Oversight/VarietyBound.lean` exhibits the corner at three
situations, and `coverage_and_control_are_independent` states both corners as one
conjunction so the independence is a checked object rather than prose.
