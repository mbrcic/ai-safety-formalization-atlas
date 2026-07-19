# Contributor Tasks

Bounded, ready-to-take units of work derived from [`open-work.md`](open-work.md)
and the round-5 review. Each task states its goal, acceptance evidence, and what
it explicitly does **not** change so a new contributor can pick one up without
prior context. This file is the source for the public issue queue; open one
GitHub issue per task when the queue is created.

Difficulty: **S** self-contained verification, **M** new Lean/schema work,
**L** larger design or external-toolchain work.

## CT-1 — Reproduce the Chaitin BY-015 candidate (M) — **done**

- **Goal:** reproduce `AlexeyMilovanov/kolmogorov-complexity-lean` at revision
  `005ac4c81eefe09642ef561057199d489cd79485`, compare
  `FormalSystem.chaitinIncompleteness` against survey source `survey-ref-039`,
  and classify the relationship.
- **Done (2026-07-19):** clean build at the pinned revision; trust scan clean;
  Lean/Mathlib 4.31 compatible; statement comparison in
  [`external-formalizations.md`](../provenance/external-formalizations.md); relationship
  **`EQUIVALENT`**; `formalizations` record + `scripts/reproduce_chaitin.sh`;
  thin aliases `AISafetyAtlas.Logic.chaitin_incompleteness` /
  `chaitin_bound` (vendored import closure for the Lean module boundary).
  Follow-on (done): BY-013 Unprovability now covered by classical Gödel first
  incompleteness from `FormalizedFormalLogic/Foundation` (Lake dependency,
  `EQUIVALENT`, `godel_first_incompleteness`), with Gödel second incompleteness
  (`godel_second_incompleteness`) as a `RELATED` companion on the same row. The
  earlier Kritchman–Raz skeleton is retired.

## CT-2 — Triage AFP `No_Free_Lunch_ML` for BY-020 / BY-021 (L)

- **Goal:** inspect the AFP `No_Free_Lunch_ML` declarations and hypotheses,
  reproduce a pinned AFP artifact, and classify each of BY-020 and BY-021 as
  same theorem, partial overlap, or distinct.
- **Acceptance evidence:** a pinned AFP revision and Isabelle version; a
  reproduction log; a per-row relationship classification with reasoning.
- **Does not change:** coverage until each row is reproduced and classified;
  a repository link alone is candidate evidence, not coverage.

## CT-3 — Domain and statement review of the robot bridge (M) — **done (reviewed)**

- **Goal:** review `AISafetyAtlas.Verification.Robot.action_safety_unverifiable`
  against van Leeuwen & Wiedermann Theorem 1: the modeled total-trace system,
  the explicit switching-construction certificate, and the `RELATED`
  classification.
- **Review package:** [`ct3-robot-review-package.md`](../bridges/ct3-robot-review-package.md).
- **Done (2026-07-19):** maintainer **reviewed** statement and scoped
  interpretation; accepts transparent **`RELATED`** packaging (Lean assumes
  `SwitchingConstruction`; not paper EXACT). Registry: formalization
  **`RELATED`**, bridge **`REVIEWED`**.
- **Does not change:** machine-checked statement; headline coverage still
  excludes BY-033 as RELATED-only.

## CT-4 — Give `Verification.rice` a downstream consumer or retire it (M) — **done**

- **Goal:** decide whether the `AISafetyAtlas.Verification.rice` interface earns
  its public slot.
- **Done (2026-07-19):** `AISafetyAtlas.Verification.AgentBehavior` models
  encoded agents (Mathlib codes), `SafetySpec` / `BehavioralSafetyVerifier`, and
  proves `no_behavioral_safety_verifier` by reducing through `Verification.rice`.
  Root import, PublicAPI smoke example, and BY-012 registry declaration updated.
- **Bridge review (2026-07-19):** maintainer accepted statement and scoped
  interpretation; BY-012 is `REVIEWED`
  ([`review-by-012-agentbehavior.md`](../bridges/review-by-012-agentbehavior.md)).

## CT-5 — Surface the generated atlas index in project navigation (S) — **done**

- **Goal:** link [`atlas-index.md`](../status/atlas-index.md) from README/docs entry points.
- **Done:** README repository-contents list links the atlas index; landscape
  index is linked alongside it.

## Maintainer-only: public issue queue (R6-11)

Do **not** open GitHub issues without maintainer authorization. When authorized,
open issues for remaining outward work (e.g. CT-2) using the acceptance
evidence above as the issue body. Suggested title:

1. `CT-2: Triage AFP No_Free_Lunch_ML for BY-020 / BY-021`

## Completed since round 5–7

- Bridge-status lifecycle vocabulary (`HUMAN_REVIEW` / `STATEMENT_REVIEWED` /
  `REVIEWED`) with `bridge_review` evidence, enforced by
  `scripts/validate_registry.py`; the v0.1 all-`HUMAN_REVIEW` snapshot now lives
  only in the release audit.
- Structured `candidate_formalizations` schema; BY-015 Chaitin promoted to
  coverage; BY-001 / BY-020 / BY-021 candidates populated (R6-4).
- Generated full-registry human view at [`atlas-index.md`](../status/atlas-index.md).
- `landscape.yaml` + generated landscape index for non–Table-1 formalizations
  (R6-3).
- Status breakdown of WRAPPER vs BRIDGE (R6-2); STATE generated snapshot (R7-1).
- Kernel `#print axioms` CI check (R7-2); Upstream LICENSE copies (R7-3).
- Validator perimeter documented in methodology (R7-2).
- CT-4 AgentBehavior consumer; CT-3 review package (no fake graduation).
