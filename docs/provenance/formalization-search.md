# Formal-Library Search Evidence

Search date: 2026-07-18

This is a version-pinned, scoped discovery pass across maintained corpora.
A candidate hit is not a verified formalization, and zero keyword hits do
not prove nonexistence. Counts are unions of files matching at least one
query; query-level counts and up to 12 representative paths per corpus are
recorded in `formalization-search.json`. High raw counts usually indicate
broad query noise rather than coverage. Only statement-level checked matches
belong in `registry.yaml` under `formalizations`.

## Corpora

| ID | Framework | Version | Scope |
|---|---|---|---|
| mathlib | Lean | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` | Mathlib source tree |
| isabelle-afp | Isabelle/HOL | `AFP release 2026-02-06` | All AFP entry source files |
| rocq-undecidability | Rocq/Coq | `c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c` | Default-branch source snapshot |
| hol4 | HOL4 | `3e2cd21c3c465ecd77540b1eb1146b4916158cdf` | Default-branch source snapshot |
| hol-light | HOL Light | `b4caefbb21638893e0d74085b1209bff7b03bb3d` | Default-branch source snapshot |
| agda-stdlib | Agda | `5abbf1dc9423377df4db7a10f869665e53c4f13c` | Default-branch source snapshot |

## Per-result discovery

| ID | Result | Query terms | Candidate corpora | Raw candidate files |
|---|---|---|---|---:|
| BY-001 | Unobservability | `observability`, `unobservable state`, `state reconstruction`, `observable output` | isabelle-afp | 10 |
| BY-002 | Uncontrollability of dynamical systems | `uncontrollability`, `not controllable`, `controllability` | none | 0 |
| BY-003 | Good Regulator Theorem | `good regulator theorem`, `good regulator` | none | 0 |
| BY-004 | Law of Requisite Variety | `requisite variety`, `law of requisite variety` | none | 0 |
| BY-005 | Information-theoretical control limits | `information-theoretic control`, `information theoretic control` | none | 0 |
| BY-006 | (Anti)codifiability thesis | `codifiability`, `moral particularism`, `virtue codification` | none | 0 |
| BY-007 | Arrow's impossibility theorem | `arrow impossibility`, `arrow's theorem`, `arrow theorem` | mathlib, isabelle-afp | 15 |
| BY-008 | Impossibility theorems in population ethics | `population ethics`, `population axiology` | isabelle-afp | 1 |
| BY-009 | Impossibility theorems in AI alignment | `value alignment`, `ai alignment`, `utility alignment` | none | 0 |
| BY-010 | Fairness impossibility theorem | `fairness impossibility`, `calibration fairness`, `equalized odds` | none | 0 |
| BY-011 | Limits on preference deduction | `preference deduction`, `preference inference`, `inverse reinforcement` | none | 0 |
| BY-012 | Rice's theorem | `rice theorem`, `rice's theorem`, `rice_` | mathlib, isabelle-afp, rocq-undecidability, hol4, agda-stdlib | 12 |
| BY-013 | Unprovability | `gödel incompleteness`, `goedel incompleteness`, `unprovability` | mathlib, isabelle-afp, hol-light | 29 |
| BY-014 | Undecidability | `halting problem`, `undecidability`, `undecidable` | mathlib, isabelle-afp, rocq-undecidability, hol4, hol-light | 705 |
| BY-015 | Chaitin incompleteness | `chaitin incompleteness`, `kolmogorov complexity incompleteness` | none | 0 |
| BY-016 | Undefinability | `tarski undefinability`, `undefinability of truth`, `undefinability` | hol-light | 1 |
| BY-017 | Unsurveyability | `unsurveyability`, `surveyability of proof` | none | 0 |
| BY-018 | Unlearnability | `unlearnability`, `learnability undecidable`, `pac learnability` | none | 0 |
| BY-019 | Unpredictability of rational agents | `predicting rational agents`, `rational agent unpredictability` | none | 0 |
| BY-020 | No Free Lunch — supervised learning | `no free lunch`, `supervised learning` | isabelle-afp | 2 |
| BY-021 | No Free Lunch — optimization | `no free lunch`, `black box optimization`, `wolpert`, `macready` | isabelle-afp | 2 |
| BY-022 | Free lunches in continuous spaces and coevolution | `continuous free lunch`, `coevolutionary free lunch` | none | 0 |
| BY-023 | Unidentifiability | `unidentifiability`, `nonidentifiability`, `disentanglement impossibility` | none | 0 |
| BY-024 | Physical limits on inference | `physical limits of inference`, `inference device` | none | 0 |
| BY-025 | Uncontainability | `uncontainability`, `superintelligence cannot be contained`, `containment problem` | none | 0 |
| BY-026 | Uninterruptibility | `safe interruptibility`, `uninterruptibility`, `off-switch` | none | 0 |
| BY-027 | Löb's theorem (unverifiability) | `loebs theorem`, `loeb theorem`, `loeb formula`, `provability logic` | isabelle-afp, hol-light | 9 |
| BY-028 | Unpredictability of superhuman AI | `superhuman unpredictability`, `unpredictability of ai` | none | 0 |
| BY-029 | Unexplainability | `unexplainability`, `explanation impossibility` | none | 0 |
| BY-030 | Incomprehensibility | `incomprehensibility`, `software comprehension` | none | 0 |
| BY-031 | k-incomprehensibility | `k-incomprehensibility`, `kolmogorov intelligence` | none | 0 |
| BY-032 | Unverifiability | `unverifiability`, `verifier theory` | isabelle-afp | 3 |
| BY-033 | Unverifiability of robot ethics | `robot ethics verification`, `ethical robot` | none | 0 |
| BY-034 | Intractability of bottom-up ethics | `bottom-up ethics`, `machine ethics complexity` | none | 0 |
| BY-035 | No-flattening theorems for deep learning | `no-flattening`, `deep shallow network` | none | 0 |
| BY-036 | Efficiency of computing Boolean functions for multilayered perceptrons | `multilayer perceptron`, `boolean functions neural` | none | 0 |
| BY-037 | Goodhart's law (Strathern) | `goodhart`, `measure becomes a target` | none | 0 |
| BY-038 | Campbell's law | `campbell's law`, `campbell law` | none | 0 |
| BY-039 | Reward corruption unsolvability | `reward corruption`, `corrupted reward channel`, `reward tampering` | none | 0 |
| BY-040 | Uncontrollability of AI | `uncontrollability of ai`, `ai control` | none | 0 |
| BY-041 | Impossibility of unambiguous communication | `unambiguous communication`, `ambiguity communication` | none | 0 |
| BY-042 | Unfairness of explainability | `unfairness of explainability`, `strategic inequality` | none | 0 |
| BY-043 | Misaligned embodiment | `misaligned embodiment`, `operationally cloned`, `clone misalignment` | none | 0 |
| BY-044 | Limited self-awareness | `limited self-awareness`, `locus of self`, `self-awareness limit` | none | 0 |

Full candidate paths and per-query counts are in [`formalization-search.json`](formalization-search.json). Review candidates against source statements before changing a registry relationship or status.
