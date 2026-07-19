# Open Work

The v0.1 baseline intentionally exposes uncertainty instead of presenting the
inventory as complete formal coverage.

The contributor-facing priorities and selection principles are summarized in
[`ROADMAP.md`](../../ROADMAP.md). This file retains the detailed review queue,
research leads, and integration decisions behind that strategy.

## Human review

- Revisit the public framing and scope disclaimer when coverage claims change
  (see [`../releases/v0.2.md`](../releases/v0.2.md) for the current release
  non-claims).
- Optional: external domain review of bridge packages beyond maintainer review.
- Review source-level statements for the three survey-introduced proof sketches:
  unfairness of explainability, misaligned embodiment, and limited self-awareness.
- Other classical wrappers / Utility Arrow remain without AI-bridge graduation;
  only BY-012 and BY-033 currently carry `REVIEWED` AI-facing bridge status.
- **Done (v0.2):** `Verification.rice` + `AgentBehavior` (BY-012) and robot
  `action_safety_unverifiable` (BY-033, formalization `RELATED`) are maintainer
  `REVIEWED` with evidence under `docs/bridges/`.

## Formalization search

- Forty survey rows still lack an atlas Lean declaration in the registry.
- Search Isabelle/HOL, Rocq, HOL4, HOL Light, and Agda for exact declarations,
  licenses, and immutable versions before proposing new proofs.
- Reproduce additional external developments only when they are credible exact or
  equivalent matches; do not count a paper or repository link as verification.
- BY-015 Chaitin incompleteness is covered by a reproduced external Lean
  formalization (`FormalSystem.chaitinIncompleteness` @
  `005ac4c81eefe09642ef561057199d489cd79485`, relationship `EQUIVALENT`) and
  thin atlas wrappers `AISafetyAtlas.Logic.chaitin_incompleteness` /
  `chaitin_bound`. The import closure is vendored under
  `AISafetyAtlas/Upstream/KolmogorovMathlib` (Lean module boundary; not a
  Lake dependency). Reproduction of the upstream pin:
  `scripts/reproduce_chaitin.sh`.
- BY-013 Unprovability is covered by classical Gödel first incompleteness
  (`LO.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence`,
  relationship `EQUIVALENT`) from `FormalizedFormalLogic/Foundation` @
  `b47cf447255addf88a5d72781d0d29641948eb6e`, exposed as
  `AISafetyAtlas.Logic.godel_first_incompleteness`. Gödel second incompleteness
  (`consistent_unprovable`, `AISafetyAtlas.Logic.godel_second_incompleteness`)
  is recorded on the same row as a `RELATED` companion. Foundation is a Lake
  dependency (no vendoring). The earlier Kritchman–Raz skeleton is retired.
- Retain Thierry Coquand's
  [`agda-godel-tree`](https://github.com/coquand/agda-godel-tree/tree/5475628ea4b648f956dce4baee7d0273ba257730)
  as secondary Chaitin/Gödel provenance only. No license was identified and it
  does not provide a directly reusable Lean algorithmic-information library. Do
  not vendor or count it without resolving those issues and reproducing the
  relevant Agda modules.

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
5. KolmogorovMathlib is vendored only for the incompleteness import closure
   needed by `AISafetyAtlas.Logic`. Do not expand the vendored tree (prefix
   complexity, algorithmic probability/statistics) unless a named theorem needs
   it; prefer thin wrappers and keep the external pin as provenance.
6. Retain TCSLib's Fourier-analytic Arrow theorem as deferred provenance. Its
   Boolean-analysis infrastructure is a meaningful distinct capability, but a
   second Arrow proof alone does not justify the Lean 4.25/PFR dependency stack.
   Reassess only for a concrete theorem that needs Fourier weights, correlation,
   or influence.

## Leads from parent research reports and the initial plan

The files in the parent directory (`../`) are **discovery inputs**, not committed
project sources:

- `AI_Safety_Formalization_Atlas_Initial_Plan.md` / `.docx` — execution plan
- `formalization_registry_chatgpt.md` — early survey-vs-ITP coverage sketch
- `registry_of_formalizations_ai_safety.md` — broader landscape and staging advice
- `AI Safety Formalization Atlas-simple.docx` — short framing note

They remain intentionally outside git. Leads below are re-checked against the
current registry and public API so assimilation does not re-open completed work.

### Already assimilated (do not re-do)

| Lead | Status in this repo |
|---|---|
| Survey map 44/44 + six-corpus search | Done |
| Arrow / Rice / halting Lean wrappers | Done (BY-007, BY-012, BY-014) |
| Utility Arrow bridge | Done (partial ROADMAP checkpoint) |
| Robot ethics bridge from halting | Done as `RELATED` (BY-033); bridge `REVIEWED` (CT-3) |
| Chaitin incompleteness | Done BY-015 `EQUIVALENT` + Logic aliases |
| Gödel I / II | Done via Foundation: BY-013 I `EQUIVALENT`, II `RELATED` |
| Tarski undefinability | Done BY-016 `EQUIVALENT` + `Logic.tarski_undefinability` |
| Löb’s theorem | Done BY-027 `EQUIVALENT` + `Logic.loeb` |
| vNM expected utility | Reproduced provenance (not a dependency) |
| AFP Arrow / Rice external reproduction | Done |
| Prefer AI bridges over re-proving classics | Policy in ROADMAP / this file |

### Highest-value remaining assimilation (ranked)

1. **NFL triage (CT-2 / BY-020–021)** — structured
   `candidate_formalizations` point at AFP `No_Free_Lunch_ML`. Statement-level
   triage still required before coverage claims.
2. **BY-025 Uncontainability** — survey row still `MAPPED`; Alfonseca pattern is
   only *indirectly* related to AgentBehavior packaging (see literature map).
   Optional: dedicated statement map or bridge if a named containment API is
   needed; do not claim BY-025 is formalized.
3. **AI-native landscape (not survey coverage):** DeepMind doubly-efficient
   debate still needs pin/build/license review. **Attribution impossibility** is
   **in-atlas** as `AISafetyAtlas.Explainability.attribution_impossibility`
   and listed in [`landscape.yaml`](../../landscape.yaml) (`LAND-ATTR-001`; not
   BY-042/BY-029 coverage).
4. **Survey-original / pen-and-paper AI claims** (unfairness of explainability,
   misaligned embodiment, limited self-awareness; uncontainability;
   Yampolskiy unverifiability/uncontrollability) — no ITP proofs in parent
   reports; only useful as **new bridges** over Rice/halting/Löb with explicit
   models, not as “missing classical theorems.”
5. **Defer:** FairBot / PrudentBot / bounded-Löb cooperation; constraint-based
   design-space solver; population-ethics Isabelle partials; AFP
   `Deep_Learning` / no-flattening (BY-035-ish) until a named consumer needs
   them; TCSLib Fourier Arrow (already deferred above).

**Done this cycle (do not re-open as “pending review”):** CT-3 robot (RELATED +
`REVIEWED` bridge); CT-4 AgentBehavior (BY-012 `REVIEWED`); Tarski/Löb/Gödel;
GS landscape Isabelle + Lean facade (LAND-GS-001/002); literature map + packaging vocabulary.

**Assimilated from Foundation (2026-07-19):** Tarski (BY-016) and Löb (BY-027)
as `EQUIVALENT` Logic wrappers alongside Gödel I/II — see
[`logic-incompleteness.md`](logic-incompleteness.md).

### Plan-phase check (`Initial_Plan`)

Phases 1–4 of the initial plan are effectively complete. Phase 5–6 remaining is
selective: NFL triage, optional BY-025 packaging clarity, AI-native landscape
leads — not another full survey remap or re-review of closed CT-3/CT-4.

Policy from the plan still binding: reuse before reprove; separate theorem /
bridge / system claim; stop rules; no unreviewed AI-safety implications.

## Deferred expansion

Causality, multi-agent systems, corrigibility, reward tampering, and formal
decision theories remain deferred until they create reusable value or unblock a
precise mapped result.
Decision theory, verification, reflection, and containment may advance earlier
when implemented as small bridges over stable foundations.
