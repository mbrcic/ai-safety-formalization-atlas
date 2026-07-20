# A3 — BY-001 Unobservability: AFP candidate triage

CT-2-style statement triage of structured `candidate_formalizations` that
pointed generically at AFP “observability” theories.

## Survey claim (BY-001)

| Field | Value |
|---|---|
| Name | Unobservability |
| Informal claim | A system's internal state cannot in general be reconstructed from its observable outputs. |
| Cited source | J. Klamka, “Uncontrollability and unobservability of multivariable systems,” *IEEE Trans. Autom. Control*, 17(5):725–726, 1972 (`survey-ref-021`) |
| Domain | Classical **control theory** (linear/multivariable systems) |

## Candidates inspected

Structured candidate (pre-triage):

- Framework: Isabelle/HOL (AFP release 2026-02-06)
- Declaration: “(AFP observability / control candidates; declaration pending)”
- States: `inspection_state: UNVERIFIED`, `relationship_review: PENDING`

Keyword paths from `docs/provenance/formalization-search.json` (query
`observability` / `observable output`):

| AFP path | Actual topic |
|---|---|
| `FSM_Tests/Observability.thy` | Making **finite-state machines** language-equivalent **observable** (determinization-style), for FSM testing |
| `FSM_Tests/FSM.thy`, minimisation, prime transformation | FSM testing library |
| `Adaptive_State_Counting/FSM/…` | Adaptive state counting / FSM |
| `CommCSL`, `Consensus_Refined`, `Key_Agreement_*`, `Security_Protocol_Refinement` | Protocol / refinement “observable” wording — not Klamka observability |

No path is a formalization of Klamka’s multivariable **control-theoretic**
unobservability (state reconstruction from outputs for dynamical systems).

## Statement match

| | Survey BY-001 | AFP hits |
|---|---|---|
| Object | Continuous / multivariable **control systems** | Discrete **FSMs**, protocols |
| Claim shape | Internal state not reconstructible from outputs (control theory) | Construct observable FSM equivalent / testing |
| Shared word | “observability” | “observability” |

**Verdict: DISTINCT — not coverage.** Keyword false friends (same word, different
mathematics), analogous to AFP `No_Free_Lunch_ML` vs Wolpert BY-020/021.

## Registry action

- Remove the pending `candidate_formalizations` entry for BY-001.
- Record triage conclusion in BY-001 `notes` with link to this file.
- No landscape formalization row (nothing to reproduce as BY-001 evidence).
- No Isabelle harness session for BY-001 (no matching session retained).

## Reproduction

Not applicable — no session accepted as a match. If a future control-theory AFP
entry appears, re-open with a new pin and statement map.

## Date

2026-07-19
