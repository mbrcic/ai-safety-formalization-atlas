# Bridge review package — `Oversight.VarietyBound`

**Status: `REVIEWED`, 2026-08-17.** Recorded on `BY-004`; see *Registry
recording*.

## Maintainer decision

**Accepted at `REVIEWED` by Mario Brcic (mbrcic), 2026-08-17**, on this document
unchanged: both reviews below, the *Allowed claim* and the independence of
coverage and control, all **as conditionals**. None of the *Forbidden claims* is
licensed — in particular nothing is asserted about any deployed system.

The rename question was decided for the pair: `not_forces_of_card_lt` alone would
be a relabelling, but that the obstruction survives *perfect* observation is a
claim relating two capacities the oversight and control clusters formalize
separately, and `coverage_and_control_are_independent` makes it a checked object
in both directions.

## What was reviewed

| | |
|---|---|
| Module | `AISafetyAtlas/Oversight/VarietyBound.lean` |
| Worked model | `AISafetyAtlas/Examples/Oversight/VarietyBound.lean` |
| Declarations | `Forces`, `not_forces_of_card_lt`, `forces_of_constant_effect`, `forces_of_constant_effect_of_not_knowable` |
| Mathematical base | `Control.two_le_card_admittedOutcomes` (Ashby ch. 11, `BY-004`), `Knowledge.Knowable` |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |

## Statement review (accepted)

**The model.** `Sit` is the set of situations the overseer is answerable for,
`Obs` what it observes, `Act` its interventions, `Out` the outcomes. An overseer
is a map `Obs → Act`. `Forces effect observe act target` says the composed policy
pins the outcome at `target` in every situation.

**Three things worth checking, checked.**

1. *The policy is observation-mediated, not omniscient.* `act` has domain `Obs`,
   and the realized intervention is `act (observe σ)`. An overseer that could
   read `σ` directly would be a different, stronger object; the theorem is stated
   against the weaker one, which is the conservative direction.

2. *The quantifier on `Forces` is over all situations.* This is the strongest
   reading of "oversight works" and therefore the one whose *necessary*
   conditions are weakest. A necessary condition for forcing every situation is
   not a necessary condition for reducing harm on average, and the module says
   so.

3. *`hcol` is a hypothesis on the effect table, not a modelling convenience.* It
   says a fixed intervention still distinguishes situations. Where it fails the
   theorem does not apply, and `forces_of_constant_effect` is precisely the case
   where it fails. That is why the two theorems sit in one module: the second is
   the boundary of the first, not a separate remark.

**The proof.** `not_forces_of_card_lt` instantiates Ashby's counting bound at
`ρ := act ∘ observe`, then observes that `Forces` would collapse
`admittedOutcomes` to `{target}`, contradicting `2 ≤ card`. No new mathematics;
the content is the model and the composition.

**Is this a rename?** `docs/guide/methodology.md` is explicit that renaming a
classical object as an agent does not earn a bridge grade. Taken alone,
`not_forces_of_card_lt` would be close to that line: relabel Ashby's regulator
"overseer" and the theorem follows. What is offered as more than a rename is the
**pair**, which is a statement about the relation between two capacities the
oversight cluster and the control cluster respectively formalize, and which
neither states alone. A reviewer who rejects that reading should reject the
bridge grade and keep the module as mathematics; the declarations remain correct
either way.

## Interpretation review (accepted 2026-08-17)

### Intended systems (mapping)

| Model object | Intended reading | What has to be true for the reading to hold |
|---|---|---|
| `Sit` | the situations an oversight regime is accountable for | the set is fixed in advance and finite |
| `observe` | everything the overseer gets, from every channel | genuinely everything; a channel omitted makes the model optimistic |
| `Act` | the distinct interventions available | *distinct in effect*, not distinct in name. Two buttons with the same consequence are one intervention |
| `effect` | what actually happens | assumes the intervention's consequence is a function of situation and intervention alone |
| `Forces` | "oversight holds the outcome to the target" | the target is a single outcome, in every situation, with certainty |

### Allowed claim (accepted)

> In a setting where the situations are fixed and finite, where each available
> intervention still leaves different situations leading to different outcomes,
> and where the number of interventions distinct in effect is smaller than the
> number of situations, no oversight policy — however good its observations —
> holds the outcome to a single target in every situation.

And, separately:

> Coverage and control are independent. An overseer may distinguish every
> situation and still not force the outcome; it may distinguish nothing and force
> it. Neither capacity substitutes for the other.

### Forbidden claims (not licensed even if this is accepted)

- **Not** "oversight does not work". The theorem is about forcing a single
  outcome with certainty in every situation. Partial mitigation, detection,
  delay, and reduction of expected harm are all untouched.
- **Not** "monitoring is useless". `forces_of_constant_effect_of_not_knowable`
  shows control without observation; it does not show observation is worthless,
  and `Knowledge.Entropy` gives a floor on error rates when observation *is* the
  binding constraint.
- **Not** a claim about any deployed system. Nobody has established that a real
  overseer's interventions are fewer than its situations. Until someone does, the
  bound is a conditional with an unverified antecedent.
- **Not** "more interventions make oversight work". `not_forces_of_card_lt` is
  necessary, not sufficient, and its converse is false.
- **Not** a probabilistic statement. There is no measure in this module.
- **Not** an argument about capability, deception, or alignment. `effect` is a
  fixed table; a system that changes the table is outside the model.

### Misuse tests (must be blocked)

| Attempted use | Blocked because |
|---|---|
| "This proves human oversight of AI is impossible." | `Sit`, `Act` and `effect` are arbitrary; nothing instantiates them at a real deployment, and `Forces` is certainty in every situation |
| "Adding interventions until `card Act ≥ card Sit` makes oversight sound." | necessary condition only; the converse is not proved and is false |
| "The overseer sees everything, so the bound does not apply." | the bound's hypotheses contain nothing about `observe`; that is the theorem |
| "Coverage results in `JointObservation` already cover this." | they are about deciding a hazard, not about forcing an outcome; `not_forces_revealing` holds at perfect observation |
| "It shows monitoring can be dropped." | the second corner is a model where one intervention flattens every situation; that is a hypothesis about the world, not a policy recommendation |

## Worked model

`Examples.Oversight.VarietyBound` exhibits both corners at three situations each,
and `coverage_and_control_are_independent` states them as one conjunction so the
independence is a checked object rather than a claim in prose.

## Registry recording

`LAND-OVERSIGHT-VARIETY-001`, related to `BY-004` (the mathematical base) and
`LAND-JOINTOBS-001` (the coverage side). The four declarations are recorded as
`BRIDGE` in `lean_artifact`.

**The signature sits on `BY-004`, not here.** `ai_bridge_status` and
`bridge_review` are rejected on rows without an `informal_claim`, and every
`LAND-` row is of that kind — a reviewed bridge is an accepted claim about the
world, so the field belongs where a claim lives. `BY-004` (Ashby's law) is that
claim row and already owns `Oversight.not_forces_of_card_lt` as a `BRIDGE`
declaration, so it carries the review, scoped in its notes to that bridge and
explicitly not to Ashby's law in general. This is the `BY-012` pattern.

Reviewed-bridge count: 3.
