# Bridge review — `Knowledge.IncidentCount.count_is_not_a_measurement`

**Row `LAND-INCIDENT-COUNT-001` · module `AISafetyAtlas/Knowledge/IncidentCount.lean` · `HUMAN_REVIEW`**

Only bridge on this row. **The row was written on 2026-09-16**: the module had
declared bridge-hood in its docstring since it was added and carried no ledger
entry at all, so it was invisible to the bridge count and had no label.

Arrow to Sidhu, Scholefield, Annan, Hernandez, Nieh Hou, Alshaikhi, Chin,
Gipiškis, *Open Problems in AI Incident Governance*, arXiv:2607.05163v1, 6 July
2026 — a **directory**, so nothing is graded against it.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-03 |
| Note | Accepted on the allowed claim as sharpened 2026-10-03 after external review (PR #72); no claim that any real form repairs a collision. |

## The statement

```lean
public theorem count_is_not_a_measurement {ω ω' : Ω}
    (hsame : G.report ω = G.report ω') (hdiff : G.count ω ≠ G.count ω') :
    ∀ rule : R → Nat, rule (G.report ω) = rule (G.report ω') ∧ G.count ω ≠ G.count ω' :=
  fun rule => ⟨congrArg rule hsame, hdiff⟩
```

`Reporting` is a regime: `report`, everything it records about a deployment, and
`count`, how many incidents actually occurred. Nothing constrains `report` to be
honest or complete, and nothing relates it to `count`.

## What to check

1. **The quantifier over rules is the content.** Given a filing collision, *every*
   counting rule scores the two deployments identically while their true counts
   differ. So no methodology is the repair. That points at what is recorded
   rather than at anyone's counting practice; it does not show that any record
   suffices.
2. **The proof is `congrArg`.** That is honest and it is thin: the mathematical
   work is in `count_not_determined_of_collision` (graded `WRAPPER`, since it is
   `not_knowable_of_collision` applied), and what this declaration adds is the
   *form* — a statement about published numbers rather than about decoders.
   **Decide whether that reframing earns the grade.**
3. **The positive half is not graded, deliberately.** `schema_fixes_the_count` is
   literally `:= h` — `Knowable` unfolded — so it proves nothing beyond the
   definition, and `knowable_of_report_carries_count` keeps it from being a
   hypothesis nothing satisfies. Both are recorded on the row as `WRAPPER`.
4. The question is **individuation** — not what happened, but how many things
   happened. It looks like a definitional problem to be settled by agreeing a
   taxonomy; the claim is about what such an agreement has to achieve.

## Allowed claim

> Where two deployments file identically and differ in how many incidents
> actually occurred, every counting rule gives them the same published number,
> so that number does not determine how many incidents occurred. Comparing
> published numbers with each other or with a target is always possible; what
> such a comparison does not show is a fact about incidents. A published count
> that meets a target expressed in incidents does not show that the incidents
> meet it, and a difference between counts across regimes, or across a schema
> change, may reflect the schemas rather than the incidents. No change of
> counting rule removes such a collision. Only a form that records more could,
> and only if what it records determines the true count — which presupposes an
> answer to what counts as one incident, and that filings are complete and
> honest. Neither is modelled here, and nothing here says such a form exists for
> any real regime.

## Forbidden

- **Not** a claim that any real incident regime collides. The atlas has **no
  incident, no taxonomy and no reporting standard**, and exhibiting the two
  deployments is an empirical claim about a schema that is not made here.
- **Not** an argument against counting incidents. A count inherits the resolution
  of the schema it is computed from — a reason to specify the schema first, not a
  reason to stop counting.
- **Not** a claim about under-reporting, incentives or honesty. Nothing
  constrains `report` to be honest, and nothing here is about a party that
  misfiles.
- **Not** a taxonomy, and not a recommendation for one.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Published AI incident counts are meaningless." | conditional on a collision in that schema, which is not established for any regime |
| "So harmonise the counting methodology across jurisdictions." | the quantifier is over every rule — under a collision, harmonising the rule changes nothing; harmonising what is recorded is the only candidate, and nothing here shows it succeeds |
| "This shows incidents are under-counted." | direction-free: the collision says the count is undetermined, not that it is low |
| "Firms will game the count." | no incentives, no strategy and no filer behaviour are modelled |

## Witness

`AISafetyAtlas/Examples/Practitioner.lean` applies the bridge.
