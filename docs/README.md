# Documentation map

Docs are split by **role** so explainers, provenance, generated status, bridge
reviews, and release evidence are not mixed in one flat directory.

| Directory | Role | Edit by hand? |
|---|---|---|
| [`agent/`](agent/) | Agent navigation + compact `by-id.json` lookup | INDEX yes; `by-id.json` **No** — regenerate |
| [`guide/`](guide/) | Human-facing explainers: methodology, open work, model notes, tasks | Yes |
| [`provenance/`](provenance/) | Discovery evidence and external reproduction narrative | Search JSON is generated; narrative yes |
| [`status/`](status/) | Generated coverage tables and indexes | **No** — regenerate |
| [`interpretation-reviews/`](interpretation-reviews/) | Human sign-off on a claim row's AI reading (`ai_interpretation_status`). Not Lean; see `type: BRIDGE` for bridges. | Yes |
| [`releases/`](releases/) | Immutable release evidence notes | Freeze after release |

Root project files still used for navigation: [`README.md`](../README.md),
[`STATE.md`](../STATE.md), [`ROADMAP.md`](../ROADMAP.md),
[`CONTRIBUTING.md`](../CONTRIBUTING.md), [`registry.yaml`](../registry.yaml),
and [`conjectures.yaml`](../conjectures.yaml).

## Agent (token-cheap navigation)

- [Agent index](agent/INDEX.md) — small start set and targeted lookup recipes
- [by-id.json](agent/by-id.json) — generated compact `BY-###` / `CLM-*` / `LAND-*` map
- [search-summary.json](agent/search-summary.json) — generated compact discovery hits

## Guide (explain / process)

- [Methodology](guide/methodology.md) — evidence rules, bridge lifecycle, trust
- [Open work](guide/open-work.md) — research queue and strategy notes
- [Contributor tasks](guide/contributor-tasks.md) — bounded CT units
- [Logic incompleteness](guide/logic-incompleteness.md) — Chaitin vs Gödel aliases
- [Robot verification model](guide/robot-verification-model.md) — paper vs Lean model
- [Knowability model](guide/knowledge-model.md) — what a system can learn about
  itself: the observation-factorization kernel and the five things "a system
  cannot know itself" conflates
- [Joint observation model](guide/joint-observation-model.md) — what a coalition's evidence can decide
- [AI safety literature map](guide/related-literature.md) — papers first: how the atlas addresses them
- [Agent-instruction design](guide/agent-instruction-design.md) — dated evidence
  and recommendations for maintainers; not default agent context

## Public project page

[`site/`](../site/) holds the public landing page — what the workbench is, why it
exists, and what each result is good for. It is one static HTML file, deployed to
GitHub Pages by [`.github/workflows/pages.yml`](../.github/workflows/pages.yml).
No build step: the workflow checks out, uploads the directory, and deploys.

There is **no generated per-declaration API site**. A `doc-gen4` pipeline was
built and removed: it renders the full import closure, which produced 372 MB of
HTML for 2.5 MB of this project's own pages, and it has no way to link out to
Mathlib's published docs instead of rebuilding them. Declaration-level reference
lives in the module docstrings and the generated status tables below. The
decision and what would reverse it are recorded in
[open work](guide/open-work.md).

Deploying needs Pages configured with **Source: GitHub Actions** (Settings →
Pages → Build and deployment); the workflow header says so too, because nothing
in the repository can detect it.

## Provenance (evidence)

- [Formalization search summary](provenance/formalization-search.md)
- [Formalization search JSON](provenance/formalization-search.json) (machine-readable)
- [External formalizations](provenance/external-formalizations.md) — Isabelle etc.
- [A1–A3/B1–B3/B7 statement maps](provenance/a1-a3-b1-b3-b7-statement-maps.md)
- [A1–A3/B1–B3/B7 re-verification](provenance/a1-a3-b1-b3-b7-reverification.md)
- [Self-measurement kernel](provenance/self-measurement-kernel.md) — Breuer source
  map, transcribed propositions, omissions, non-vacuity, stop rules
- [Embedded self-knowledge landscape](provenance/embedded-self-knowledge-landscape.md) —
  what already exists around knowability; negative searches and the Lawvere correction
- [Limited self-awareness](provenance/limited-self-awareness.md) — BY-044 source map,
  strict-extension interpretation, proof split, and fidelity residual
- [Debate reproduction](provenance/debate-reproduction.md) — Path-A external build
- [Source coverage audit](provenance/source-coverage-audit.md) — the statement-by-statement
  grading of every printed source the atlas transcribes: coverage, scope, and the
  readings that are choices rather than transcriptions
- [Toolchain v4.33.0 migration](provenance/toolchain-v4330-migration.md) — what
  moved, what broke, and which build records were deliberately not rewritten
- [Verification scheduling](provenance/verification-scheduling.md) — what CI runs
  on which trigger and why: the cost ladder, the two gated checks, and the window
  each gating leaves open
- [MAIS source pin](provenance/mais-source-pin.md) — the commit and per-file SHA-256
  the MAIS-A2 grading is anchored to
- [MAIS-O70 conditional verification](provenance/mais-o70-conditional-verification.md) —
  release claim, unconditional fragment, three assumed frontiers, and validation order
- [MAIS-O70 frontier manifest](provenance/frontier-manifest.md) — exact assumed
  propositions, consumers, source comparison, stress evidence, and debt
- [MAIS-O70 fidelity adjudications](provenance/mais-o70-fidelity-adjudications.md) —
  the two source readings that remain drafts until a human countersigns them
- [MAIS-O7/O77 verification](provenance/mais-o7-o77-verification.md) — source
  receipts, volume-order fidelity, the O7 and O77(b) proofs, and the O77(a) frontier

This section is a **map, not an inventory**: `provenance/` holds triage notes,
per-source clash logs and dated audits that a reader does not need in order to
check the work. The two entries above are here because everything else in the
grading chain refers back to them.

## Status (generated)

Regenerate with `python3 scripts/generate_registry_views.py` (also refreshes
`docs/agent/by-id.json`).

- [By mathematical area](status/by-area.md) — **start here** if you know an area
  and want to see what is shipped and what is thin
- [Contributor tasks](guide/contributor-tasks.md) — generated from `tasks.yaml`
- [Conjectures](guide/conjectures.md) — open questions with compiling statements
  and no proof; how to propose one
- [Formalization status](status/formalization-status.md)
- [Landscape index](status/landscape-index.md) — atlas formalizations and public
  Lean surface
- [Relations and shapes](status/relations.md) — the ledger as a graph: how two
  results stand to each other, and which are characterizations rather than point
  impossibilities
- [Blueprint](status/blueprint.md) — claims and what realizes them, both directions;
  machine-readable as [blueprint.json](agent/blueprint.json)
- [Uncovered rows](status/uncovered-rows.md) — every row with no atlas Lean and the
  reason: reproduced elsewhere, triaged distinct, a lead to read, or nobody has looked
- [Escape routes](status/escape-routes.md) — what you weaken to get out from under
  each obstruction, and how much of that weakening the atlas actually proves
- [Source reports](status/sources/) — per catalogued source: papers, formalizations,
  atlas declarations, bridge state
- [MAIS submitted solutions](status/mais-solutions.md) — solutions other people
  filed against the MAIS open-problems agenda, with what checking each one found,
  kept apart from which artifact the ledger grades it against

## Interpretation reviews (human semantic review)

**Start at the [bridge register](interpretation-reviews/README.md)** — one review
file per bridge declaration, with what a signature means and where it is
recorded. **37 bridges, 3 signed, 34 open.** The label lives on the declaration,
not the row.

Signed:

- [CT-3 robot review package](interpretation-reviews/ct3-robot-review-package.md) — `BY-033`
- [BY-012 AgentBehavior review](interpretation-reviews/review-by-012-agentbehavior.md)
- [Oversight VarietyBound package](interpretation-reviews/review-oversight-varietybound.md) —
  `BY-004`, accepted at `REVIEWED` 2026-08-17; also covers
  `LAND-OVERSIGHT-VARIETY-001`, which cannot carry a signature of its own

Reviewed but deliberately not graduated:

- [BY-044 SelfAwareness review](interpretation-reviews/review-by-044-selfawareness.md) — statement
  reviewed; the AI-system interpretation is withheld

## Releases

- [v0.7 release](releases/v0.7.md) — current published release (`0.7.0`, tagged)
- [v0.6 release](releases/v0.6.md) — historical (`0.6.0`, tagged)
- [v0.5.1 release](releases/v0.5.1.md) — historical (`0.5.1`, tagged)
- [v0.5 release](releases/v0.5.md) — historical (`0.5.0`, tagged)
- [v0.4 release](releases/v0.4.md) — historical (`0.4.0`, tagged)
- [v0.3 release](releases/v0.3.md) — historical (`0.3.x`)
- [v0.2 release](releases/v0.2.md) — historical
- [v0.1 release](releases/v0.1.md) — historical

## Path policy

- Registry `formal_library_search.evidence_file` points at
  `docs/provenance/formalization-search.json`.
- Bridge `interpretation_review.evidence` points at a file under `docs/interpretation-reviews/`.
- Prefer links through this map or the root README rather than deep-coupling
  scripts to ad-hoc paths.
