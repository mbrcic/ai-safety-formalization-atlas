# Open Work

The v0.1 candidate intentionally exposes uncertainty instead of presenting the
inventory as complete formal coverage.

The contributor-facing priorities and selection principles are summarized in
[`ROADMAP.md`](../ROADMAP.md). This file retains the detailed review queue,
research leads, and integration decisions behind that strategy.

## Human review

- Approve the public framing and mandatory scope disclaimer.
- Review the `EXACT`/`EQUIVALENT` classifications for Rice, halting, and Arrow.
- Review source-level statements for the three survey-introduced proof sketches:
  unfairness of explainability, misaligned embodiment, and limited self-awareness.
- Decide whether and how any classical result should be connected to an explicit
  AI-system model. Every such bridge remains `HUMAN_REVIEW`.
- Approve the v0.1 candidate before the repository becomes public.

## Formalization search

- Forty-two survey rows still lack a maintained Lean declaration in the registry.
- Search Isabelle/HOL, Rocq, HOL4, HOL Light, and Agda for exact declarations,
  licenses, and immutable versions before proposing new proofs.
- Reproduce additional external developments only when they are credible exact or
  equivalent matches; do not count a paper or repository link as verification.

## Lean integration decisions

1. Arrow's impossibility theorem uses CC Liang's Apache-2.0 Lean 4 development
   at pinned commit `758398779decc66d2830a70b02597b0f22030181` as its canonical
   source. A namespaced snapshot is vendored because the upstream legacy module
   cannot cross Lean 4.32's public-module boundary directly.
2. The utility-facing Arrow theorem is a bridge over that canonical proof. It
   represents finite total preorders by lower-contour cardinalities; neither
   independent Isabelle proof was ported.
3. Do not port Isabelle `Rice_2`. Defer `Rice_1` until explicit reductions are
   needed and `Rice_3` until a semantic c.e.-set interface is needed.
4. Rank later candidates by reusable structure and AI-safety bridge value, not
   by the number of upstream proofs or declarations.

## Leads added from the parent research reports

The two research reports in the parent directory are discovery inputs, not
committed project sources. They added the following actionable leads that were
not represented in the original plan:

- Prefer AI-specific bridge theorems over new proofs of already-formalized
  classical results. Candidate bridges include containment and verification
  limits derived from Rice or the halting problem.
- Investigate the Lean 4 vNM expected-utility work described in arXiv:2506.07066
  before designing the atlas utility vocabulary. The paper is verified to
  exist, but the reported public code repository was unavailable on 2026-07-18,
  so it is not yet a dependency or registry formalization.
- Treat No Free Lunch as a high-novelty candidate after a fresh primary-source
  and formal-library search. The reports' claim that no formalization exists is
  useful search direction, not verified negative evidence.
- Track AI-safety-native Lean developments outside the 44-row survey as a
  separate landscape, not as survey coverage. Verified repository leads include
  Google DeepMind's archived doubly-efficient debate development and the recent
  attribution-impossibility development; both need statement-level and build
  review before registry inclusion.
- Defer FairBot, PrudentBot, bounded-Löb cooperation, and a constraint-based
  design-space solver until the relevant modal or utility foundations are stable
  and they unblock a precise intended theorem.

## Deferred expansion

Causality, multi-agent systems, corrigibility, reward tampering, and FDT remain
deferred until they create reusable value or unblock a precise mapped result.
Decision theory, verification, reflection, and containment may advance earlier
when implemented as small bridges over stable foundations.
