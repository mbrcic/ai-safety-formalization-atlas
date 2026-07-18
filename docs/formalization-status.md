# Formalization Status

The machine-readable source of truth is [`registry.yaml`](../registry.yaml).
This page is generated manually from verified registry records during v0.1
development and must not claim completeness beyond the survey inventory.

| Metric | Current |
|---|---:|
| Survey results inventoried | 44 / 44 |
| Survey results with verified formalizations | 3 |
| Verified formalization records | 9 |
| Atlas Lean theorem declarations | 7 across 3 survey results |
| Reproduced external coverage records | 3 across 2 survey results / 2 sessions |
| Additional reproduced external variants | 2 (`Rice_1`, `Rice_3`) |
| New Lean proofs | 1 representation bridge |
| Reviewed AI-system bridge theorems | 0 |
| Survey rows with six-corpus discovery evidence | 44 / 44 |

## Verified Lean coverage

| Survey result | Mathlib module | Maintained declarations | Atlas interface | Relationship |
|---|---|---|---|---|
| Rice's theorem | `Mathlib.Computability.Halting` | `ComputablePred.rice`, `ComputablePred.rice₂` | `rice`, `rice_code_iff` | Equivalent / exact |
| Undecidability (halting instance) | `Mathlib.Computability.Halting` | `halting_problem_re`, `halting_problem`, `halting_problem_not_re` | `halting_re`, `halting_problem`, `nonhalting_not_re` | Related / exact / related |
| Arrow's impossibility theorem | CC Liang `arrow` | `Impossibility` | `SocialChoice.arrow`, `SocialChoice.Utility.arrow` | Equivalent / bridge |

The five computability declarations were compiled from Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997` through the atlas facade. The
canonical Arrow proof is pinned to commit
`758398779decc66d2830a70b02597b0f22030181`; its atlas utility theorem is a new
finite-representation bridge rather than an independent proof of Arrow's core.
The halting module remains the v0.1 worked example.

## Verified external coverage

| Survey result | Framework/session | Declarations | Relationship | Reproduced |
|---|---|---|---|---|
| Rice's theorem | Isabelle/HOL `Recursion-Theory-I` | `Rice_1`, `Rice_2`, `Rice_3` | Equivalent | Yes |
| Arrow's impossibility theorem | Isabelle/HOL `ArrowImpossibilityGS` | `Arrow`, `dictator` | Equivalent | Yes |

The two Isabelle Arrow declarations are representation variants of one survey
result, not two coverage results. They remain provenance and specification
sources; neither proof was ported.

## Discovery coverage

All 44 rows were searched across pinned Mathlib, Isabelle AFP, Rocq
Undecidability, HOL4, HOL Light, and Agda standard-library snapshots. Eleven rows
produced raw candidate-file hits. These candidates remain distinct from the nine
statement-level formalization records above; see
[`formalization-search.md`](formalization-search.md).

Relationship labels are `EXACT`, `EQUIVALENT`, `RELATED`, `DEPENDENCY_ONLY`,
and `UNCLEAR`. An AI-safety interpretation remains `HUMAN_REVIEW` unless it has
been separately defined and reviewed.
