# Contributor Tasks

Bounded, ready-to-take units of work derived from [`open-work.md`](open-work.md)
and the round-5 review. Each task states its goal, acceptance evidence, and what
it explicitly does **not** change so a new contributor can pick one up without
prior context. This file is the source for the public issue queue; open one
GitHub issue per task when the queue is created.

Difficulty: **S** self-contained verification, **M** new Lean/schema work,
**L** larger design or external-toolchain work.

## Open now

Live units across the contribution rungs. Take one, open the matching proposal
issue, or ask in a draft PR. CT-1…CT-5 below are completed history, kept for
provenance.

**New here? Start with an S.** CT-11…CT-14 are first tasks — one sitting, no
prior context, a single deterministic done-check. Take one, then climb.

### CT-11 — Add a candidate lead to an uncovered row (S) — **Pointer rung**

- **Goal:** pick one `MAPPED`-only survey row in [`registry.yaml`](../../registry.yaml)
  whose `candidate_formalizations` is `[]`, and add **one** lead — a repository
  or paper URL that plausibly formalizes or proves it. No Lean, no proof, no
  coverage claim.
- **Acceptance:** a schema-valid `candidate_formalizations` entry;
  `scripts/setup.sh --pointer` (i.e. `scripts/agent_gate.sh`) green. A lead is
  candidate evidence, not coverage.
- **Does not change:** the row's `status` or any coverage count — a candidate is
  not a formalization until reproduced and classified.

### CT-12 — Verify one citation against its source (S) — **Verification rung**

- **Goal:** take one `original_source_refs` entry in
  [`registry.yaml`](../../registry.yaml) — e.g. `survey-ref-018` (doi
  `10.1162/neco.1996.8.7.1391`) — confirm the DOI/arXiv id resolves to the cited
  paper and that the transcribed title, authors, and pages match. Correct the
  entry if anything is off.
- **Acceptance:** either "verified, no change" recorded in the PR description
  with the resolved link, or a precise transcription fix; `scripts/agent_gate.sh`
  green. Source verification is a first-class contribution.
- **Does not change:** any Lean, any relationship classification.

### CT-13 — Add one Lean use-site over a shipped theorem (S) — **New-proof rung, scoped**

- **Goal:** copy [`AISafetyAtlas/Examples/FirstContribution.lean`](../../AISafetyAtlas/Examples/FirstContribution.lean)
  as your model and add one new `example` that exercises an existing shipped
  theorem (e.g. `no_free_lunch_supervised`, or anything on the README "Lean API"
  list over `import AISafetyAtlas`). No new math — a use-site, not a reproof.
- **Acceptance:** `lake build AISafetyAtlas.Examples.FirstContribution` (or
  `.PublicAPI`) green; `python3 scripts/check_print_axioms.py` clean. Runs under
  the fast `scripts/setup.sh --quick` path if you stay on the learning layer.
- **Does not change:** any theorem statement or the public facade.

### CT-14 — Report a proof we don't have (S) — **Pointer rung**

- **Goal:** you know a result — or a proof of one — not in the catalogue. Report
  where it lives, via the [Known formalization issue form](https://github.com/mbrcic/ai-safety-formalization-atlas/issues/new?template=known-formalization.yml).
  Value grades by readiness: **pen and paper** (a formalization target) →
  **another prover** (an Isabelle/Coq/HOL reproduction candidate) → **already in
  Lean** (a possible thin vendor/alias). This is the reuse thesis as a rung:
  point us at a building block instead of reinventing it.
- **Acceptance:** a filled discovery issue, or a schema-valid
  `candidate_formalizations` entry with source coordinates and license;
  `scripts/agent_gate.sh` green if you touch the registry. No coverage claimed
  until reproduced and classified.
- **Does not change:** any coverage count — a lead is candidate evidence only.

### CT-15 — Formalize the survey's own three theorems (BY-042 / BY-043 / BY-044) (L) — **New proof rung**

The three results the survey [*Impossibility Results in AI: A Survey*](https://doi.org/10.1145/3603371)
introduces **itself** — presented with proof sketches in a dedicated section,
distinct from the Table-1 catalogue of others' results. Each is `PROOF_SKETCH`,
`MAPPED`, and unformalized. This is the highest-legitimacy native target in the
ledger: the authors' own sketched theorem turned into a machine-checked one,
dual to CT-6 but in-house. A sketch is a scaffold, not a full proof —
mechanizing it audits the sketch.

- **Targets (pick one):**
  - **BY-044 — Limited self-awareness:** an agent cannot be perfectly
    self-aware across the survey's operational boundaries. Sketch likely rests on
    self-reference / a fixed-point argument — check reuse of the atlas's Gödel,
    Rice, and halting layers before building primitives.
  - **BY-043 — Misaligned embodiment:** mistakenly cloned self-interested agents
    cannot perfectly control one another. Likely an uncontrollability /
    self-reference argument — same reuse check.
  - **BY-042 — Unfairness of explainability:** a verifier and a decision-maker
    hold structurally unequal strategic positions when explanations omit the full
    execution trace. Likely game-theoretic / information-asymmetry — expect new
    machinery; scope the hardest, take last.
- **Step 0 (do first, low effort):** in [`registry.yaml`](../../registry.yaml)
  set the chosen row's `original_source_refs` to the survey itself
  (`10.1145/3603371`) — these are survey-original results and the field is
  currently empty — and write a provenance note under
  [`../provenance/`](../provenance/) that pins the **exact** paper statement,
  section/theorem number, the sketch, and every definition it assumes
  (e.g. what "perfectly self-aware" or "operational boundaries" mean formally).
  Pin the model before writing Lean.
- **Acceptance:** a kernel-checked Lean theorem under the facade (new namespace as
  needed — `AISafetyAtlas.SelfAwareness`, `.Embodiment`; `.Explainability`
  already exists) with an honest `EXACT`/`EQUIVALENT`/`RELATED` classification
  against the paper statement; the provenance note stating exactly which
  assumptions are and are not mechanized and **any gap the sketch leaves**;
  `agent_gate.sh` + `lake build` green; kernel axioms clean.
- **Does not change:** the other two rows until each lands; no retro-claim of
  coverage in README/registry until a proof (not a statement) is in.

### CT-6 — First possibility proof: continuous free lunches (BY-022) (L) — **New proof rung**

- **Goal:** give BY-022 (*Free lunches in continuous spaces and coevolution*,
  Auger–Teytaud 2010 / Wolpert–Macready coevolutionary) its first Lean
  statement — a setting where the finite NFL symmetry provably fails, dual to
  `AISafetyAtlas.Learning.no_free_lunch`.
- **Acceptance:** a kernel-checked Lean theorem under the facade (or a landscape
  entry if the natural home is adjacent), a `formalizations`/landscape record
  with honest `EXACT`/`EQUIVALENT`/`RELATED` classification against
  `survey-ref-047`/`survey-ref-048`, provenance note, `agent_gate.sh` +
  `lake build` green, kernel axioms clean.
- **Does not change:** the impossibility rows; do not retro-claim BY-022 as
  formalized in README/registry until this lands.

### CT-7 — Reproduce DeepMind doubly-efficient debate into the landscape (M) — **done (reproduced 2026-07-20)**

The formalization exists and is Lean 4: `google-deepmind/debate`
(Apache-2.0), a machine-checked correctness proof of the stochastic oracle
protocol from Brown-Cohen–Irving–Piliouras 2023 (*Scalable AI Safety via
Doubly-Efficient Debate*, arXiv 2311.14125). This is a **possibility /
scalable-oversight guarantee**, not an impossibility — a live landscape anchor
dual to the impossibility rows.

- **Coordinates:** repo `github.com/google-deepmind/debate`, revision
  `de3a6e500ae1a65dfeea2f91ef519ebad9704be0` (single `main`, no release tag,
  last commit 2024-10-08). Main theorems in `Debate/Correct.lean`:
  `completeness`, `soundness`, `correctness` (paper Theorem 6.2). License
  Apache-2.0.
- **Version gap:** upstream pins `leanprover/lean4:v4.8.0` and Mathlib
  `v4.8.0`; the atlas is on `v4.31.0`. Do **not** vendor into the 4.31 tree.
  Reproduce like Chaitin/Isabelle — build at the upstream toolchain from a
  separate checkout via a new `scripts/reproduce_debate.sh`.
- **Acceptance:** clean build at the pinned revision under its own toolchain;
  strict-trust scan of the reproduced tree; a `landscape.yaml` record
  (`LAND-DEBATE-001` — revision, `Debate/Correct.lean`, the three theorem
  names, Apache-2.0, relationship `RELATED`, reproduction status,
  `survey_coverage: null`); `scripts/reproduce_debate.sh`; regenerated views;
  provenance note. Never a headline coverage count.
- **Honest scope:** carry upstream's own caveats — correctness only; space
  complexity not formalized; time counts oracle queries only; Lipschitz oracle
  machine defined slightly differently (a stronger variant). No AI-system
  reading without a separate reviewed bridge.
- **Does not change:** survey `registry.yaml` coverage; the 4.31 build closure.
- **Done (2026-07-20):** clean build at the pinned revision under upstream
  `leanprover/lean4:v4.8.0` (`Debate.Correct`, 1721/1721 targets); strict-trust
  scan clean across 19 upstream Lean sources; `completeness`/`soundness`/
  `correctness` present in `Debate/Correct.lean`. Landscape record
  `LAND-DEBATE-001` (`survey_coverage: null`, no atlas import surface);
  `scripts/reproduce_debate.sh`; evidence
  [`debate-reproduction.md`](../provenance/debate-reproduction.md). First
  reproduced possibility / scalable-oversight anchor. Never headline coverage.

### CT-8 — BY-025 Uncontainability: bridge or documented no-map (M) — **Bridge rung**

- **Goal:** decide whether BY-025 (still `MAPPED`) earns a dedicated bridge over
  Rice/halting with an explicit containment model, or stays mapped-only.
- **Acceptance:** either a bridge declaration with stated modeled system,
  assumptions, quantifier order, conclusion, and the practical claim it does
  **not** establish (`ai_bridge_status: HUMAN_REVIEW`), or a provenance note
  recording why no clean statement map exists. Do not claim BY-025 is
  formalized.
- **Does not change:** the Alfonseca/AgentBehavior packaging; no fake bridge
  graduation.

### CT-9 — Formalize a debate follow-up with no existing proof (L) — **New proof rung**

Greenfield: these debate refinements are **pen-and-paper only** — no ITP
formalization exists (checked 2026-07-20). Formalizing one is original work,
dual to CT-7's *reproduction* of the already-formalized doubly-efficient debate.

Each target has a complete pen-and-paper proof; the task is to mechanize it.
Pointer to the informal proof is given per target.

- **Targets (pick one):**
  - *Avoiding Obfuscation with Prover-Estimator Debate* (arXiv 2506.13609) —
    relaxes the equal-compute-provers assumption of doubly-efficient debate.
    **Pen-and-paper proof:** the paper has exactly three theorems — **6.1**
    (completeness: honest debater wins under (ε,ρ)-stability) and **6.2**
    (soundness: honest output is truth in every Stackelberg equilibrium), the
    two "main theorems" in Section 6; and **8.3** (Section 8), the
    training-convergence companion (debaters reach Stackelberg equilibria via
    standard gradient methods). Supporting proofs in Appendices A–D. Formalize
    any one; smallest scoped core is Theorem 6.1 completeness alone.
  - *How to Avoid Debate: Scalable AI Safety via Doubly-Efficient Interactive
    Proofs* (arXiv 2607.03561) — doubly-efficient **single-prover** interactive
    proofs/arguments for oracle-aided (relativizing) computation.
    **Pen-and-paper proof:** two main-results settings — (1) robust computation
    (output stable if a small fraction of oracle answers are wrong) and
    (2) low-degree-polynomial oracle; pick one setting's protocol + soundness
    proof. (Paper is days old as of 2026-07-20; take exact theorem numbers from
    the arXiv PDF, HTML not yet rendered.)
- **Acceptance:** a kernel-checked Lean statement + proof of the paper's central
  guarantee (or an explicitly scoped core of it) under the facade or landscape;
  honest relationship classification against the paper theorem; provenance note
  stating exactly which theorem and which assumptions are and are not
  mechanized; `agent_gate.sh` + `lake build` green; kernel axioms clean.
- **Reuse first:** the `google-deepmind/debate` Lean development (CT-7) is the
  natural scaffold — check whether its `Prob`/`Comp` monads and protocol
  definitions carry over before rebuilding primitives.
- **Honest scope:** a possibility/oversight guarantee, `RELATED` at most; no
  AI-system reading without a separate reviewed bridge. Do not claim the paper
  is "formalized" until a proof (not a statement) lands.
- **Does not change:** survey `registry.yaml` coverage.

### CT-10 — Reproduce the closed-under-permutation NFL iff (BY-020, optional) (L) — **New reproduction rung**

- **Goal:** reproduce the sharp *both-directions* NFL characterization on the
  **prior axis**: over a distribution `P` on target functions `X → Y`, expected
  performance is algorithm-independent **iff** `P` is closed under permutation of
  the domain. This is the general boundary that subsumes every uniform-prior core
  already in `AISafetyAtlas.Learning` (`no_free_lunch`, `no_free_lunch_supervised`,
  `no_free_lunch_adaptive`) — those are the trivially-c.u.p. special case.
- **Source (in the literature — citable proof to diff against):** Schumacher,
  Vose, Whitley, *The No Free Lunch and Problem Description Length* (GECCO 2001,
  first c.u.p. iff); Igel & Toussaint, *A No-Free-Lunch Theorem for Non-Uniform
  Distributions of Target Functions* (J. Math. Modelling & Algorithms 2004,
  doi `10.1023/B:JMMA.0000049381.24625.f7`, both directions). Because it is a
  published result, this graduates to **`EXACT`/`EQUIVALENT`** — not the folklore
  `NEW_PROOF` status of the loss-axis iff `homogeneous_iff_learner_indep`.
- **Acceptance:** kernel-checked Lean theorem under the facade; finite weighted
  sums over `Fintype` suffice (no Mathlib probability needed); honest
  `EXACT`/`EQUIVALENT`/`RELATED` classification against `survey-ref-018`;
  provenance note in [`../provenance/lean-wolpert-nfl.md`](../provenance/lean-wolpert-nfl.md)
  recording which paper and which assumptions; `agent_gate.sh` + `lake build`
  green; kernel axioms clean.
- **Why it may wait (read before taking):** no current downstream consumer needs
  it — the uniform cores already carry the headline. Its distinctive value is
  bridge-readiness: c.u.p. is the exact condition under which NFL is *vacuous*
  (real learning priors are structured, not permutation-symmetric), so it is the
  one NFL variant with a plausible AI-safety bridge story. Pull it only if a
  bridge needs "which priors kill learning"; otherwise it is completeness polish.
- **Does not change:** the existing `NEW_PROOF` loss-axis iff stays as-is; no
  retro-claim of c.u.p. coverage in README/registry until a proof lands. See
  reference note `nfl-cup-iff-lineage` and [`ct2-nfl-triage.md`](../provenance/ct2-nfl-triage.md).

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

## CT-2 — Triage AFP `No_Free_Lunch_ML` for BY-020 / BY-021 (L) — **done (reproduced)**

- **Goal:** inspect the AFP `No_Free_Lunch_ML` declarations and hypotheses,
  reproduce a pinned AFP artifact, and classify each of BY-020 and BY-021 as
  same theorem, partial overlap, or distinct.
- **Acceptance evidence:** a pinned AFP revision and Isabelle version; a
  reproduction log; a per-row relationship classification with reasoning.
- **Does not change:** coverage until each row is reproduced and classified;
  a repository link alone is candidate evidence, not coverage.
- **Done (2026-07-19):** AFP `No_Free_Lunch_ML` reproduced (pinned `2026-02-06`,
  SHA-256 `93ce8953…173588`, `isabelle build` exit 0 via
  `scripts/reproduce_isabelle.sh nfl`) and triaged as the Shalev-Shwartz–Ben-David
  PAC no-free-lunch (Understanding ML §5.1) — **DISTINCT** from BY-020 (Wolpert
  supervised NFL) and BY-021 (Wolpert–Macready optimization NFL). Candidate tags
  removed from both rows; reproduced SSBD entry recorded as landscape row
  `LAND-NFL-001`. Evidence:
  [`ct2-nfl-triage.md`](../provenance/ct2-nfl-triage.md).

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
