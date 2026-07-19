# Documentation map

Docs are split by **role** so explainers, provenance, generated status, bridge
reviews, and release evidence are not mixed in one flat directory.

| Directory | Role | Edit by hand? |
|---|---|---|
| [`agent/`](agent/) | Agent navigation + compact `by-id.json` lookup | INDEX yes; `by-id.json` **No** — regenerate |
| [`guide/`](guide/) | Human-facing explainers: methodology, open work, model notes, tasks | Yes |
| [`provenance/`](provenance/) | Discovery evidence and external reproduction narrative | Search JSON is generated; narrative yes |
| [`status/`](status/) | Generated coverage tables and indexes | **No** — regenerate |
| [`bridges/`](bridges/) | Bridge review packages and human review evidence | Yes |
| [`releases/`](releases/) | Immutable release evidence notes | Freeze after release |

Root project files still used for navigation: [`README.md`](../README.md),
[`STATE.md`](../STATE.md), [`ROADMAP.md`](../ROADMAP.md),
[`CONTRIBUTING.md`](../CONTRIBUTING.md), [`registry.yaml`](../registry.yaml),
[`landscape.yaml`](../landscape.yaml). Adversarial project reviews live in
[`reviews/`](../reviews/) (historical; not default agent context — see
[`reviews/README.md`](../reviews/README.md)).

## Agent (token-cheap navigation)

- [Agent index](agent/INDEX.md) — default open set and lookup recipes
- [by-id.json](agent/by-id.json) — generated compact `BY-###` / `LAND-###` map

## Guide (explain / process)

- [Methodology](guide/methodology.md) — evidence rules, bridge lifecycle, trust
- [Open work](guide/open-work.md) — research queue and strategy notes
- [Contributor tasks](guide/contributor-tasks.md) — bounded CT units
- [Logic incompleteness](guide/logic-incompleteness.md) — Chaitin vs Gödel aliases
- [Robot verification model](guide/robot-verification-model.md) — paper vs Lean model
- [AI safety literature map](guide/related-literature.md) — papers first: how the atlas addresses them

## Provenance (evidence)

- [Formalization search summary](provenance/formalization-search.md)
- [Formalization search JSON](provenance/formalization-search.json) (machine-readable)
- [External formalizations](provenance/external-formalizations.md) — Isabelle etc.

## Status (generated)

Regenerate with `python3 scripts/generate_registry_views.py` (also refreshes
`docs/agent/by-id.json`).

- [Formalization status](status/formalization-status.md)
- [Atlas index](status/atlas-index.md) (44 survey rows)
- [Landscape index](status/landscape-index.md) (non–Table-1)
- [Paper coverage](status/paper-coverage.md) — source papers ↔ formalizations ↔ atlas

## Bridges (human semantic review)

- [CT-3 robot review package](bridges/ct3-robot-review-package.md)
- [BY-012 AgentBehavior review](bridges/review-by-012-agentbehavior.md)

## Releases

- [v0.2 release scope](releases/v0.2.md) (current package version on branch)
- [v0.1 release evidence](releases/v0.1.md)

## Path policy

- Registry `formal_library_search.evidence_file` points at
  `docs/provenance/formalization-search.json`.
- Bridge `bridge_review.evidence` points at a file under `docs/bridges/`.
- Prefer links through this map or the root README rather than deep-coupling
  scripts to ad-hoc paths.
