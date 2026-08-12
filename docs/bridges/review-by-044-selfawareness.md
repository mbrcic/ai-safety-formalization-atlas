# Bridge review — BY-044 SelfAwareness / limited self-awareness

**Registry status:** `STATEMENT_REVIEWED` (2026-08-12).
**Statement:** accepted. **Interpretation:** not reviewed — deliberately withheld.
**Scope of row status:** `STATEMENT_REVIEWED` documents that the Lean statement
is a faithful reading of Brcic and Yampolskiy §4.3. It licenses **no** claim
about any AI system, deployed or hypothetical.

## Reviewer

- **Name:** Mario Brcic (mbrcic)
- **Date:** 2026-08-12
- **Scope:** `AISafetyAtlas.SelfAwareness` — the `Model` structure, `AgentAware`,
  `PerfectlySelfAware`, and the four theorems; the witnesses in
  `AISafetyAtlas.Examples.SelfAwareness`; the source map in
  [`../provenance/limited-self-awareness.md`](../provenance/limited-self-awareness.md).
- **Standing:** first author of the source paper. Recorded because the
  provenance note relies on that authority for one step — that `awareness_cost`
  is intended semantic content of Definition 4.6 together with assumptions 2–5.

## Statement review (accepted)

| Item | Location | Outcome |
|---|---|---|
| Process carrier | `Process` with `SemilatticeSup`; order is constituent containment, `⊔` is joint composite | Accepted |
| Horizon | `Model.available`, finite and nonempty; instances relevant to one bounded awareness horizon | Accepted |
| Awareness edge | `Model.aware` — active observation and predictive modelling within the horizon | Accepted |
| Non-collapse law | `awareness_cost` : `cost target + minAwarenessCost ≤ cost (target ⊔ observer)` | Accepted |
| Positive increment | `minAwarenessCost_pos` | Accepted |
| Composite closure | `awareness_closed` — a witnessed edge makes the joint composite available | Accepted |
| Agent-level awareness | `AgentAware`, `PerfectlySelfAware` | Accepted |
| Boundary | `Model.not_aware_of_le` — no constituent completely models its container | Accepted |
| Proposition 4.7 | `Model.process_not_self_aware` | Accepted |
| Theorem 4.8, maximal form | `Model.not_agentAware_of_maximal` | Accepted |
| Theorem 4.8, source form | `Model.limited_self_awareness` | Accepted |
| Corollary | `Model.not_perfectlySelfAware` | Accepted |
| Non-vacuity | `Examples.SelfAwareness.cyclicModel` inhabits every field, with a live two-process cycle | Accepted |
| Sharpness | `flatTwoCycle` — irreflexivity alone does not give Theorem 4.8 without composite closure | Accepted |
| Axiom profile | within `{propext, Classical.choice, Quot.sound}` | Accepted |

### Source-fidelity items reviewed

| Source item | Treatment | Outcome |
|---|---|---|
| Definition 4.6, richer ontology | semantic, carried by `aware` | Accepted |
| Definition 4.6, model simpler than the process | **not formalized**; recorded in the provenance note | Accepted as a stated residual |
| Assumptions 1–3 (budget, costliness, lower bound) | absorbed into `available_finite` and `minAwarenessCost_pos` rather than derived from a scalar budget | Accepted |
| Assumptions 4–5 (propagation, bounded lag) | semantic in the horizon-relative `aware`; no clock type | Accepted |
| Assumption 6 (awareness graph) | the `aware` relation itself; no acyclicity anywhere | Accepted |
| Weakly connected component / supernode step | replaced by semilattice composition plus closure under a witnessed edge | Accepted |
| Grade | `EQUIVALENT`, not `EXACT`, recording those representational changes | Accepted |

### Exclusions at the statement layer

Not claimed by the Lean statement, and not reviewed here: the paper's
consciousness hypothesis; the open question about cycles; any Lawvere,
Brandenburger–Keisler, Breuer, or Wolpert connection; approximate, cached,
delayed, or selected-property self-models; thermodynamic or Landauer bounds; any
derivation of the horizon's finiteness from a physical resource budget.

## Interpretation review (withheld)

| Field | Value |
|---|---|
| Decision | `NOT REVIEWED` |
| Reason | No AI-system model has been proposed, so there is nothing to accept or reject |

The row's three `application` lines are discovery prose describing what the
theorems say in process vocabulary. They are not an AI-system reading and are
not evidence of one. Graduating to `REVIEWED` would require naming an in-scope
modelling class — what a `Process` is in a real system, what makes a composite
*available*, and what makes an awareness edge hold — and none of that exists yet.

## Allowed claim (accepted)

> In any model where internal processes form a semilattice of composites, only
> finitely many are available within one bounded awareness horizon, and an
> awareness activity added to its target raises the joint composite's cost by at
> least a fixed positive amount, some available process or composite has no
> available internal observer that completely observes and predictively models
> it. Perfect self-awareness, meaning complete coverage of every available
> atomic and composite internal process, is therefore unattainable in such a
> model. Ordinary awareness cycles are consistent with these hypotheses and are
> exhibited. This is the process-compositional core of Brcic and Yampolskiy
> (2023), §4.3, Proposition 4.7 and Theorem 4.8.

## Forbidden claims (not licensed by `STATEMENT_REVIEWED`)

1. That any AI system, architecture, or deployed model cannot monitor itself.
   No system is modelled, and `STATEMENT_REVIEWED` explicitly withholds the
   interpretation layer.
2. That the result says anything about consciousness, phenomenal experience, or
   introspection as a mental faculty. The paper's own consciousness hypothesis
   is outside both proofs.
3. That partial, approximate, or selected-property self-monitoring is impossible.
   The theorem denies *complete* awareness of every available composite.
4. That a system cannot know its own global state. Distributed snapshots
   (`LAND-CL-001`) determine consistent global states while computation
   continues; the obstruction here is horizon-relative and contemporaneous.
5. That awareness cycles or recurrent architectures are paradoxical. Cycles are
   permitted, inhabited, and witnessed.
6. That the result follows from Gödel, Rice, Lawvere, or any diagonal argument.
   The mechanism is cost non-collapse plus finiteness.
7. That an awareness edge may be read as a lossless or exhaustive model of its
   target. Definition 4.6 requires the model be *simpler* than the process.

## Misuse tests (blocked)

| Misread | Why blocked |
|---|---|
| "LLMs provably cannot be interpretable." | No encoding of any system into `Process` / `aware` is assumed or proved; interpretability is not complete process awareness. |
| "Self-monitoring is futile." | Only recursively complete coverage is denied; partial monitors are untouched. |
| "This proves machines cannot be conscious." | Consciousness appears in the paper as a hypothesis, in neither proof, and in no Lean declaration. |
| "Recurrent or self-referential architectures are inconsistent." | The witnessed model contains a two-process awareness cycle and satisfies every hypothesis. |
| "The agent has a permanently hidden process." | The statement is horizon-relative; which composite is unobserved may differ across horizons. |

## Survey row

- BY-044's informal claim is unchanged: an agent cannot be perfectly self-aware
  across the survey's operational boundaries.
- The formalization grade (`EQUIVALENT`) is independent of this bridge status and
  is not affected by graduating or withholding it.
- BY-042 and BY-043, the survey's other two author-original results, remain
  unformalized and unreviewed.

## Registry recording

```json
"ai_bridge_status": "STATEMENT_REVIEWED",
"bridge_review": {
  "reviewer": "Mario Brcic (mbrcic)",
  "date": "2026-08-12",
  "statement_reviewed": true,
  "interpretation_reviewed": false,
  "evidence": "docs/bridges/review-by-044-selfawareness.md"
}
```

The validator enforces the pairing: `STATEMENT_REVIEWED` requires
`statement_reviewed: true` and rejects `interpretation_reviewed: true` — that
combination is what `REVIEWED` means, and it is not what this review found.
