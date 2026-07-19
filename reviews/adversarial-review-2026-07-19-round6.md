# Adversarial Review — Round 6 (post–Logic cluster)

Date: 2026-07-19  
Scope: local `agent-work` tree at `77a6cec` (29 commits ahead of published
`main`). Untracked editor scaffolding (`**/CLAUDE.md`, `.claude/`, etc.) is
not treated as deliverable.  
Method: claim-vs-artifact checks against `README.md`, `STATE.md`, `ROADMAP.md`,
`registry.yaml`, Lean public API, validators, reproduction docs, and prior
reviews (rounds 1–5). Every finding below is backed by a concrete path or
count; rhetorical complaints without evidence are excluded.  
Primary question: after the post-v0.1 Logic incompleteness work, attribution
facade, and Gibbard–Satterthwaite integration decision, does the repository
still advance its stated purpose—or has it optimized for coverage count and
facade breadth while the decisive research layer stays empty?

This review **complements** rounds 4–5. Round 5’s structural defects were
largely fixed; this round asks whether the **current** branch is honest,
usable, and strategically sound.

## Verdict

The repository remains an unusually disciplined **formalization inventory and
Lean facade**, with real post-v0.1 gains: headline coverage moved from **3 → 7**
survey results (`EXACT`/`EQUIVALENT`), Logic aliases for Gödel I/II, Tarski,
Löb, and Chaitin compile from attributed sources, and GS was closed with a
documented Isabelle operational path rather than a greenwashed Lean port.

It is **still not** the research object the roadmap describes as valuable:

| Claimed layer | Honest status at `77a6cec` |
|---|---|
| Survey map + discovery | Strong (44/44 inventoried; six-corpus evidence) |
| Parsimonious Lean API | Strong for classical wrappers; **mixed** for landscape theorems |
| Reviewed AI-system bridge | **0 / 44** (`HUMAN_REVIEW` on every row) |
| Downstream consumer of atlas theorems | Essentially **examples only** |
| Public collaboration queue | **Zero open GitHub issues** |

**Recommendation:** do **not** raise the coverage numerator further until one
bridge graduates through real review (CT-3) and either `Verification.rice` earns
a consumer or is retired (CT-4). Further thin wrappers over Foundation or
Mathlib improve the facade without improving the project’s load-bearing claim.

## Verification performed

| Check | Result |
|---|---|
| `python3 scripts/validate_registry.py` | Pass (44 results, 15 formalizations, 15 Lean artifacts) |
| `python3 scripts/generate_registry_views.py --check` | Pass |
| `python3 scripts/validate_current_state.py` | Pass |
| `lake build` (Logic / package, warm cache) | Pass (Foundation warnings present; see R6-6) |
| Headline counts vs registry | Consistent: **7** EXACT/EQUIVALENT rows; **1** RELATED-only (BY-033); **0** reviewed bridges |
| `candidate_formalizations` population | **0** leads on any row |
| Open GitHub issues | **None** |
| Prior R5 structural gates | Lifecycle vocabulary present; forced all-`HUMAN_REVIEW` current-state gate **gone** |

Published `main` still reports **3 of 44** coverage and a thinner status page.
Everything below concerns the **unpublished** `agent-work` delta unless noted.

## Disposition of round-5 findings

| ID | Round-5 finding | Status now |
|---|---|---|
| R5-1 | Validator froze bridges at `HUMAN_REVIEW` | **Fixed.** Vocabulary `HUMAN_REVIEW` / `STATEMENT_REVIEWED` / `REVIEWED` + `bridge_review` evidence; v0.1 snapshot only in release audit |
| R5-2 | Utility checkpoint overstated “downstream” | **Fixed.** ROADMAP admits partial implementation and open success criterion |
| R5-3 | Best leads trapped in prose | **Schema fixed, content empty.** `candidate_formalizations` exists and is validated; **no row uses it** (Chaitin was promoted to coverage; NFL/AFP still prose-only) |
| R5-4 | No browsable 44-row atlas | **Fixed.** `docs/status/atlas-index.md` generated |
| R5-5 | No operational contributor queue | **Partial.** `docs/guide/contributor-tasks.md` exists; GitHub issue list still empty |

Round 5’s infrastructure thesis largely holds. The remaining problems are
**strategic and semantic**, not missing validators.

## What holds up under adversarial inspection

1. **Epistemic constitution is real, not marketing.** README, methodology, and
   robot module docs separate mathematical statement from AI-system claim.
   BY-033 stays `RELATED` and outside headline coverage. Strict-trust scanning
   rejects `sorry` / `sorryAx` / `native_decide` / `@[implemented_by]` in atlas
   sources. `IN_TREE` provenance avoids self-referential commit hashes.

2. **Coverage counting is not inflated by RELATED or landscape work.**
   Attribution and Gibbard–Satterthwaite are documented as non–Table-1 coverage.
   Gödel II is a `RELATED` companion on BY-013, not a second headline row.
   Headline formula requires reproduced `EXACT`/`EQUIVALENT` — verified in
   `generate_registry_views.py`.

3. **GS decision is honest.** Lean SocialChoiceLean was tried on 4.31, failed
   to green Main, and was **closed** rather than vendored half-broken or dual-
   toolchained. Isabelle `Gibbard_Satterthwaite` via
   `scripts/reproduce_isabelle.sh arrow` is the operational formalization, with
   re-run green 2026-07-19 recorded in `docs/provenance/external-formalizations.md`.

4. **Logic layer is attributed and non-skeletal.** Foundation @
   `b47cf447…` supplies concrete arithmetic theorems; KolmogorovMathlib pin is
   vendored for the module boundary with a clean-room reproduce script. ASCII
   `loeb` vs upstream `löb_theorem` is documented. `docs/guide/logic-incompleteness.md`
   correctly warns against Chaitin/Gödel/Löb conflation.

5. **Parsimony mostly holds for survey cores.** One canonical Arrow (CC Liang +
   utility bridge), Mathlib Rice/halting, no Isabelle→Lean Rice port, no second
   Fourier Arrow dependency.

These are non-trivial. The findings below attack the gap between that foundation
and a credible **AI-safety formalization research** artifact.

---

## Findings

### R6-1 — Critical: zero reviewed bridges after all post-v0.1 work

**Evidence.** `ai_bridge_status` is `HUMAN_REVIEW` on **all 44** rows.
`docs/status/formalization-status.md` reports “Survey results with reviewed AI-system
bridges | 0”. ROADMAP still identifies layer 3 (bridge theorems with reviewed
interpretation) as “where much of the prospective AI-safety research value
lies.” CT-3 remains the top open task; the lifecycle from R5-1 was built and
**never exercised**.

**Why adversarial.** Raising coverage 3→7 and adding Logic/attribution APIs
looks like progress in git history and README metrics. Under the project’s own
value function, the decisive metric is unchanged since v0.1. The repository can
truthfully claim better classical math packaging; it cannot truthfully claim
closer AI-safety formalization research value.

**Required correction.** Run CT-3 with a named human reviewer (maintainer or
domain expert). Produce a written statement/paper-model review and either:

- record `STATEMENT_REVIEWED` or `REVIEWED` with a real `bridge_review` record, or
- document why the robot theorem stays `HUMAN_REVIEW` / should be demoted in
  prominence.

Do not open new classical wrappers until this exists once.

---

### R6-2 — Major: coverage growth is mostly alias density, not research density

**Evidence.** Of the **7** headline rows:

| ID | Nature of atlas work |
|---|---|
| BY-007 | Vendored Arrow + utility representation bridge (v0.1 era) |
| BY-012 | Mathlib wrappers + `Verification.rice` bridge |
| BY-014 | Mathlib wrappers |
| BY-013, BY-016, BY-027 | Thin `Logic.*` wrappers over **one** Foundation pin |
| BY-015 | Thin wrappers over vendored KolmogorovMathlib |

Non-upstream atlas Lean is ~**1.0k LOC**; Upstream vendored trees ~**2.4k LOC**.
Public root import lists many entry points; nearly all Logic entries are
`public theorem … := upstream…`.

**Why adversarial.** Reuse-before-reproving is correct policy. Calling the
result “7 of 44 formalization coverage” is accurate as a **map** metric and
misleading as a **research output** metric. Four of seven rows ride a single
external incompleteness package. A hostile reader will say: *the atlas is a
namespace over Mathlib + Foundation with two small bridges.*

**Required correction.**

- In status docs, report **separately**: (a) survey rows with reproduced
  EXACT/EQUIVALENT evidence; (b) rows whose atlas contribution is only a
  WRAPPER; (c) rows with NEW_PROOF/BRIDGE content. The data already exist in
  `lean_artifact.declarations[].type`.
- Prefer CT-2/3/4 over another Foundation or Mathlib alias.

---

### R6-3 — Major: dual ledger — public Lean API vs machine-readable map

**Evidence.**

- `AISafetyAtlas.Explainability.attribution_impossibility` is on the **root
  import**, listed in README’s “stable entry points,” and smoke-tested in
  `Examples.PublicAPI`.
- It does **not** appear in `registry.yaml` (no attribution/Rashomon/DASH
  strings). Methodology §“Parsimony and source roles” says adjacent landscape
  formalizations “do not enter `registry.yaml`.”
- Gibbard–Satterthwaite is “atlas-canonical” in external docs but also outside
  the registry and outside the Lean API.
- Generated `docs/status/atlas-index.md` and formalization-status tables therefore
  **omit** first-class public Lean theorems.

**Why adversarial.** The project’s brand is a *map*. A researcher who trusts the
registry or atlas index will miss theorems the README presents as stable API.
Conversely, a researcher who trusts the Lean root import will assume survey
backing that does not exist for attribution. Two truth sources with incomplete
overlap is an atlas failure mode even when each half is carefully worded.

**Required correction.** Choose one:

1. **Landscape registry** (preferred): a machine-readable `landscape.yaml` (or
   registry section) for non–Table-1 formalizations with relationship
   `LANDSCAPE` / `ADJACENT`, never counted in the 7/44 numerator; generate a
   landscape index; or
2. **API discipline:** keep landscape theorems out of the root import and README
   “stable entry points” until they are either survey-mapped or in (1).

Do not leave “canonical in prose, invisible to generators.”

---

### R6-4 — Moderate: `candidate_formalizations` is dead schema

**Evidence.** Schema and validators exist (`validate_registry.py`, methodology).
Count of results with nonempty `candidate_formalizations`: **0**. Meanwhile free-
text `notes` still mention concrete leads, e.g.:

- BY-020 / BY-021: AFP `No_Free_Lunch_ML` “candidate… require statement-level
  verification”
- BY-001: AFP observability candidates

Round 5 claimed the Chaitin lead was recorded structurally; that lead was
promoted to coverage (good) and **no subsequent lead was migrated** into the
schema CT-2 is supposed to use.

**Why adversarial.** A schema that is never populated is documentation theater.
Discovery work keeps living in notes that generators report as “Candidate leads:
—” for every row of the atlas index.

**Required correction.** For every note that names a specific repository /
AFP entry / declaration as a candidate, add a `candidate_formalizations` object
**or** delete the promissory note language. Start with BY-020/BY-021 and any
remaining AFP control-theory pointers.

---

### R6-5 — Moderate: BY-027 `EQUIVALENT` is the softest headline classification

**Evidence.**

- Survey informal claim (registry): *“A sufficiently strong formal system cannot
  generally prove its own soundness; the precise modal reading follows Löb’s
  hypotheses.”*
- Encoded theorem (`Logic.loeb`): Löb’s schema
  \(T \vdash \mathrm{Prov}_T(\sigma)\to\sigma \implies T \vdash \sigma\).
- Module doc and registry notes both state that the survey’s “cannot prove its
  own soundness” reading is a **standard consequence** under hypotheses, “not a
  weaker separate claim” / “not a separate theorem.”

**Why adversarial.** Methodology’s `EQUIVALENT` is for equivalent mathematical
content, not “implies the informal slogan.” The notes are careful; the
**relationship label** that feeds the 7/44 count is not. A stricter atlas would
mark Löb `RELATED` (or `EQUIVALENT` only to a survey statement that *is* Löb)
and keep “own soundness” as interpretation.

Compare: Gödel II is correctly `RELATED` on BY-013 rather than a second
headline. BY-027 did not get the same conservatism.

**Required correction.** Re-triage BY-027:

- if the survey table entry is truly “Löb’s theorem,” keep `EQUIVALENT` and
  tighten the informal_claim to the modal schema; or
- if the survey entry is “unverifiability / cannot prove own soundness,” set
  relationship to `RELATED` and drop BY-027 from the headline 7 until a bridge
  or exact match exists.

Either choice is defensible; the current pair (slogan claim + schema theorem +
`EQUIVALENT`) is the weakest link in the coverage chain.

---

### R6-6 — Moderate: Foundation couples four coverage rows to one heavy pin

**Evidence.** `lakefile.toml` requires Foundation @ `b47cf447…`. BY-013, BY-016,
and BY-027 (and Gödel II companion) all depend on that pin. Warm `lake build`
replays **1000+** Foundation jobs. Foundation sources emit `warningAsError`-
relevant warnings (unused simp args, class reducibility); they do not fail the
atlas package today but enlarge the trusted/build surface. Strict-trust scans
**atlas** trees only—not Foundation.

**Why adversarial.** One upstream regression, license/policy change, or Lean
bump can desynchronize three headline rows at once. Vendoring Kolmogorov while
depending on Foundation is a coherent trade-off, but correlated coverage risk is
undocumented as risk.

**Required correction.** Document correlated-failure risk in
`docs/guide/logic-incompleteness.md` or external formalizations. Prefer a single
`scripts/reproduce_foundation.sh` (or package target list) that pins the exact
modules used. Do not add more Foundation-only survey rows without a consumer.

---

### R6-7 — Moderate: six-corpus search cannot see the formalizations that matter

**Evidence.** Pinned corpora: Mathlib, AFP, Rocq Undecidability, HOL4, HOL
Light, Agda stdlib. Post-v0.1 wins came from:

- FormalizedFormalLogic/Foundation (not in corpora)
- AlexeyMilovanov/kolmogorov-complexity-lean (not in corpora)
- DrakeCaraker/dash-impossibility-lean (not in corpora)
- DominikPeters/SocialChoiceLean (not in corpora)

Discovery correctly labels zero hits as **scoped** negative evidence. The
atlas-index and search docs still present six-corpus completeness as a major
accomplishment. Adversarially: the search layer is excellent for classical
libraries and **blind by design** to the Lean ecosystem packages where AI-
safety-native and modern incompleteness work actually lives.

**Required correction.** Either:

- extend discovery with an explicit “extra Lean package watchlist” (revision-
  pinned path search), results stored as candidates; or
- demote six-corpus language from “complete discovery” to “baseline classical
  corpus pass,” which it already is methodologically but not always rhetorically.

---

### R6-8 — Moderate: `Verification.rice` remains an unearned public slot

**Evidence.** ROADMAP and CT-4 state the theorem has a root-import contract but
**no substantive domain-specific downstream theorem**. Robot deliberately does
**not** route through it. The only consumers are declaration checks and
examples. The name lives under `Verification`, which suggests AI-safety content
beyond a semantic-to-code restatement of Mathlib Rice.

**Why adversarial.** Public API surface has a maintenance and interpretation
cost. Keeping an unused “verification” bridge invites over-reading (already
flagged `HUMAN_REVIEW`) without paying the research cost of a real model.

**Required correction.** Execute CT-4: one real consumer theorem **or** remove
from public facade (keep Mathlib wrappers under `Computability` only).

---

### R6-9 — Moderate: “operational” Isabelle GS ≠ integrated research interface

**Evidence.** Docs call Isabelle `Gibbard_Satterthwaite` the
**“atlas-canonical machine-checked GS”** and “operational.” What exists:

- pinned AFP archive + Docker reproduce script (green 2026-07-19);
- prose decision not to Lean-port or facade.

What does **not** exist:

- registry/landscape machine record (R6-3);
- Lean declaration a downstream proof can import;
- CI job that runs Isabelle (CI is Lean + Python validators only).

**Why adversarial.** For a Lean-centered atlas, “operational” usually implies
“usable in the project’s primary toolchain.” Here it means “we can rebuild the
AFP session.” That is valuable provenance—not an integrated result. The wording
is one notch stronger than the engineering reality.

**Required correction.** Prefer “reproduced landscape formalization (Isabelle
only; no Lean interface)” in STATE/README. Reserve “operational integration”
for results that either enter CI or a stable multi-prover interface contract.

---

### R6-10 — Minor: structural debris and doc micro-drift

**Evidence.**

- Empty directories `AISafetyAtlas/Limits/`, nearly empty
  `AISafetyAtlas/Foundations/` (only untracked `CLAUDE.md`).
- `docs/guide/contributor-tasks.md` “Completed since round 5” still narrates Chaitin
  as a structural **candidate** lead; the row is now coverage.
- Attribution software license rests on upstream `CITATION.cff` without a root
  `LICENSE` file (documented residual risk—acceptable if explicit, easy to
  forget later).
- Package version remains `0.1.0` while branch is explicitly post-v0.1.

**Why adversarial.** Low severity each; together they signal agent churn without
cleanup discipline.

**Required correction.** Remove empty dirs or place a one-line README of intent;
refresh CT-1 completion notes; decide whether post-v0.1 bumps `version` only at
publish time (document that rule).

---

### R6-11 — Minor: public collaboration still not operational

**Evidence.** Round 5 required a small GitHub issue queue. `docs/guide/contributor-tasks.md`
is good local scaffolding (CT-2–CT-5). `gh issue list --state open` returns
empty. README still invites contributions via issue forms.

**Why adversarial.** “Contributors welcome” without takeable public tasks is
performative. This is a **maintainer** action (and push policy forbids agents
from opening issues without authorization)—flagged, not an agent defect.

**Required correction.** When the maintainer authorizes outward work, open 4–6
issues from CT-2–CT-5 with acceptance evidence copied from
`contributor-tasks.md`.

---

## Strategic scorecard (plan / roadmap outcomes)

| Outcome | Status at round 6 |
|---|---|
| Reliable formalization map | **Strong** inventory; **weaker** dual-ledger for landscape Lean (R6-3); empty candidates (R6-4) |
| Coherent Lean interface | **Good** classical names; **attribution** on root import without map; **rice** unearned |
| Foundations for future theorems | **Not demonstrated**—no reviewed downstream AI-safety theorem |
| Survey-first v0.1 | **Done** (on `main`) |
| Reuse before proving | **Done** consistently; GS Lean refusal is evidence |
| Explicit theorem / bridge / system layers | **Designed**; bridge graduation **unexercised** (R6-1) |
| Utility / value-alignment foundation | **Partial** (utility Arrow only); ROADMAP honest after R5-2 |
| Precise verification limit | **Machine core yes**; semantic review **no** |
| Coverage growth 3→7 | **True** as map metric; **mostly wrappers** (R6-2) |
| Public collaboration | **Prepared**, not operational (R6-11) |

## Highest-leverage next sequence

1. **CT-3** — real human review of the robot bridge; first nonzero
   `bridge_review` record (fixes R6-1).
2. **CT-4** — consumer or retire `Verification.rice` (fixes R6-8).
3. **Landscape ledger** — machine-readable non-survey formalizations so
   attribution/GS/vNM/TCSLib are not prose-only (fixes R6-3, softens R6-9).
4. **Populate candidates** for NFL and other note-only leads (fixes R6-4);
   then **CT-2** triage.
5. **Re-triage BY-027** relationship vs informal claim (fixes R6-5).
6. **Stop** adding Foundation/Mathlib aliases for coverage optics.
7. Maintainer-only: issue queue + authorize publish delta when ready.

## Bottom line

There is still no reason to reverse the project’s epistemic standards—they are
its main asset. Round 6’s charge is different: **post-v0.1 work improved the
classical facade and closed a difficult GS decision honestly, but did not move
the metric the roadmap treats as decisive.**

The truthful summary for a skeptical peer:

> This is a carefully maintained map of 44 surveyed impossibility results with
> reproduced formalization evidence for seven of them (mostly classical
> computability and incompleteness), thin Lean aliases, two small bridges still
> under human review, zero reviewed AI-system interpretations, and an adjacent
> landscape documented in prose more than in data.

That is a **strong v0.1+ foundation**. It is not yet a research institution for
machine-checked AI-safety limits. The next honest increment is one reviewed
bridge and a single ledger for everything the public API claims—not an eighth
wrapper.

## Appendix A — Current counts (agent-work @ `77a6cec`)

| Metric | Value |
|---|---:|
| Survey rows | 44 |
| `LEAN_AVAILABLE` | 8 |
| `MAPPED` only | 36 |
| Headline EXACT/EQUIVALENT coverage | 7 |
| RELATED-only (headline-excluded) | 1 (BY-033) |
| Formalization records | 15 |
| Reviewed AI bridges | 0 |
| `candidate_formalizations` entries | 0 |
| Commits ahead of `main` | 29 |
| Open GitHub issues | 0 |

## Appendix B — Prior review chain

| Round | File | Focus |
|---|---|---|
| 1–2 | `adversarial-review-2026-07-18*.md` | Early integrity |
| 3 | `…-round3.md` | Mechanical defect classes |
| 4 | `…-round4.md` | Injection tests of R3 fixes |
| 5 | `…-round5-purpose-plan.md` | Purpose vs plan; lifecycle; candidates; atlas view |
| 6 | this file | Post–Logic/attribution/GS honesty and strategy |

## Resolution (implemented 2026-07-19, R6+R7 remediation)

| ID | Disposition |
|---|---|
| R6-1 | **Blocked honestly.** `docs/bridges/ct3-robot-review-package.md` + STATE blocked entry; no fake `bridge_review` |
| R6-2 | **Fixed.** Status table breaks out WRAPPER/BRIDGE/NEW_PROOF/REFERENCE and wrapper-only rows |
| R6-3 | **Fixed.** `landscape.yaml` + `docs/status/landscape-index.md` + validator; attribution dual-listed |
| R6-4 | **Fixed.** Candidates on BY-001, BY-020, BY-021 |
| R6-5 | **Fixed.** BY-027 informal claim tightened to Löb schema; `EQUIVALENT` retained |
| R6-6 | **Fixed.** Foundation risk + `scripts/reproduce_foundation.sh` in logic-incompleteness |
| R6-7 | **Fixed.** Six-corpus demoted to baseline classical pass in methodology/status |
| R6-8 | **Fixed.** `Verification.AgentBehavior.no_behavioral_safety_verifier` consumer |
| R6-9 | **Fixed.** GS wording → reproduced landscape (Isabelle only; no Lean interface) |
| R6-10 | **Fixed.** Empty dirs removed; LICENSE/NOTICE; CT notes; version rule in STATE |
| R6-11 | **Maintainer-only.** Issue drafts in contributor-tasks; not opened without auth |

