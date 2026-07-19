# Contributor and Agent Guidance

Read this file before autonomous work. Live phase status is in [`STATE.md`](STATE.md);
survey inventory is [`registry.yaml`](registry.yaml); human doc map is
[`docs/README.md`](docs/README.md). Agent navigation: [`docs/agent/INDEX.md`](docs/agent/INDEX.md).

## Context budget (agents)

Token cost is dominated by large inventory dumps. Prefer small generated indexes.

### Default open set

1. This file (policy)
2. [`STATE.md`](STATE.md)
3. [`docs/agent/INDEX.md`](docs/agent/INDEX.md) and [`docs/agent/by-id.json`](docs/agent/by-id.json)
4. [`docs/status/atlas-index.md`](docs/status/atlas-index.md) / [`landscape-index.md`](docs/status/landscape-index.md) as needed
5. The single facade module under `AISafetyAtlas/` for the task domain
6. [`docs/guide/open-work.md`](docs/guide/open-work.md) or [`contributor-tasks.md`](docs/guide/contributor-tasks.md) when picking work

### Do not read by default

| Path | Why | When to open |
|---|---|---|
| Full [`registry.yaml`](registry.yaml) (~100KB+) | Redundant with `by-id.json` | One `BY-###` via `rg` for notes / candidates / bridge_review |
| Full [`landscape.yaml`](landscape.yaml) | Redundant with `by-id.json` + landscape-index | One `LAND-###` detail |
| [`docs/provenance/formalization-search.json`](docs/provenance/formalization-search.json) | Large discovery dump | Updating search evidence or auditing a candidate |
| [`reviews/**`](reviews/) | Historical adversarial rounds | Maintainer names a specific round finding |
| `vendor/**` | Upstream vendor trees | Editing that vendored package only |
| `.lake/**`, `**/CLAUDE.md`, `ai_context.txt` | Build cache / tool dumps | Never as task context |
| Accidental `https:/`, `http:/` trees | wget path debris (gitignored) | Delete if recreated; do not index |

### Cheap vs full validation

```console
./scripts/agent_gate.sh   # cheap: registry, landscape, views --check, current-state, docs paths
```

Full green (Lean + axioms) is listed under **Validation before claiming green** below.
Do not run `lake build` on every tiny docs-only edit unless the task touches Lean.

## Public Lean API

Treat `AISafetyAtlas` as a small, stable facade over proofs that may live in
Mathlib, this repository, or another maintained Lean package. Downstream users
and agents should not need to know the location of an upstream declaration.

- Expose one canonical public declaration for each mathematical result.
- Preserve the theorem's conventional, recognizable name whenever one exists.
- Use the form `AISafetyAtlas.<Domain>.<OptionalRepresentation>.<Theorem>`.
- Use `UpperCamelCase` for namespaces and Lean's `snake_case` for declarations.
- Introduce a representation namespace only when it supplies a meaningfully
  different interface needed by downstream proofs.
- Add a suffix such as `_iff`, `_reduction`, or `_undecidable` only when it
  identifies a genuinely useful distinction.
- Do not turn theorem names into namespaces merely to group variants.
- Do not mirror all upstream declarations. Add only the stable aliases that
  make the atlas easier to use.

Preferred examples include:

```lean
AISafetyAtlas.Computability.rice
AISafetyAtlas.Verification.rice
AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier
AISafetyAtlas.Verification.Robot.action_safety_unverifiable
AISafetyAtlas.SocialChoice.arrow
AISafetyAtlas.SocialChoice.Utility.arrow
AISafetyAtlas.SocialChoice.gibbard_satterthwaite
AISafetyAtlas.Logic.godel_first_incompleteness
AISafetyAtlas.Logic.godel_second_incompleteness
AISafetyAtlas.Logic.tarski_undefinability
AISafetyAtlas.Logic.loeb
AISafetyAtlas.Explainability.attribution_impossibility
AISafetyAtlas.Learning.no_free_lunch
```

## Parsimony and Multiple Formalizations

Minimize semantic and API redundancy. Reuse a maintained Lean result and place
a stable atlas alias or a thin interface bridge over it before porting another
proof of the same theorem.

Keep an additional formalization only when it provides a documented,
substantial gain, such as:

- a stronger theorem needed by intended proofs;
- a materially different representation, such as a utility-facing interface;
- an explicit reduction certificate needed for compositional arguments;
- constructive or computational content that the canonical result lacks; or
- necessary independence from an unsuitable upstream dependency.

Alternative Coq, Rocq, Isabelle, or other proofs may be recorded as provenance
without becoming duplicate public Lean declarations or separate coverage
claims. Explain the unique value before adding a second public formalization.

For Arrow's theorem, prefer one canonical Lean proof and derive a utility-facing
bridge from it when possible. For Rice's theorem, do not duplicate the ordinary
undecidability result; add an explicit one-reduction or a c.e.-set interface only
when downstream work actually requires that extra structure. Prefer packaging
Rice for AI safety as `Verification.rice` /
`Verification.AgentBehavior.no_behavioral_safety_verifier` rather than a second
undecidability proof.

These rules are defaults. Override them only when the significant gain is
recorded in the relevant source, registry entry, or design documentation.

## Coverage, landscape, and bridges

- **Headline coverage** counts only reproduced registry formalizations with
  relationship `EXACT` or `EQUIVALENT`. `RELATED` (e.g. robot BY-033) does
  **not** increase that count.
- **`landscape.yaml`** holds non–Table-1 formalizations (attribution, GS,
  vNM, …). Landscape entries never increase survey headline coverage.
- **Theorem layers:** (1) math theorem, (2) atlas interface, (3) AI-safety
  bridge statement, (4) claim about a real AI system. Layers 3–4 need human
  semantic review; a Lean proof at layer 1–2 does not inherit an AI reading.
- **`ai_bridge_status`:** `HUMAN_REVIEW` → `STATEMENT_REVIEWED` → `REVIEWED`.
  Any status other than `HUMAN_REVIEW` requires a real `bridge_review` record
  (`reviewer`, `date`, `statement_reviewed`, `interpretation_reviewed`,
  `evidence` under `docs/bridges/`). **Never invent** a human review or
  graduate a bridge without maintainer/domain authorization.
- **Statement vs interpretation:** statement review accepts the encoded model
  and conclusion; interpretation review accepts a bounded, misuse-resistant
  AI-safety reading. Prefer staying at `STATEMENT_REVIEWED` over overclaiming
  real systems.
- Robot (`action_safety_unverifiable`) formalizes the **conditional reduction
  core** of van Leeuwen & Wiedermann Thm 1 / Cor 1 under an assumed
  `SwitchingConstruction`; relationship is `RELATED`. Do not lengthen the
  proof for paper show-off; full SPA/Def. 3 fidelity is optional future work.
- Gibbard–Satterthwaite: Isabelle landscape `LAND-GS-001` remains the AFP
  reproduce path; Lean interface is vendored SocialChoiceLean GS closure →
  `AISafetyAtlas.SocialChoice.gibbard_satterthwaite` (`LAND-GS-002`). Do not
  vendor the rest of SocialChoiceLean without a documented consumer need.

Policy detail: [`docs/guide/methodology.md`](docs/guide/methodology.md).

## Documentation layout

Do not dump new narrative into a flat `docs/` root. Use the role split in
[`docs/README.md`](docs/README.md):

| Path | Role |
|---|---|
| `docs/agent/` | Agent navigation + generated compact `by-id.json` |
| `docs/guide/` | Human explainers: methodology, open work, tasks, model notes, related-literature map |
| `docs/status/` | **Generated** coverage tables — regenerate, do not hand-edit |
| `docs/provenance/` | Discovery search evidence + external reproduction narrative |
| `docs/bridges/` | Bridge review packages and human review evidence |
| `docs/releases/` | Release evidence notes |
| `reviews/` (repo root) | **Historical** adversarial reviews — not default agent context |

Registry search evidence path:
`docs/provenance/formalization-search.json`. After registry edits run
`python3 scripts/generate_registry_views.py` (updates `docs/status/*`,
`docs/agent/by-id.json`, README scope snippet, STATE snapshot, Lean registry
checks). Use `docs/status/paper-coverage.md` for the **theorem / survey** paper ↔
formalization map. Use `docs/guide/related-literature.md` for **AI safety
literature first** (how each paper is addressed: packaging, related-formal,
none)—including papers that also have a BY row (e.g. robot ethics).
**Packaging** means classical math under AI-safety vocabulary matching a paper’s
pattern, not EXACT paper fidelity—defined in that guide. Dedicated per-article
guides only for large fidelity gaps—not for every paper.

## Branch, version, and publication discipline

Treat `main` as the protected, published baseline. Do not commit or push agent
work directly to it.

- Start development branches from the current `main` tree so later pull requests
  contain only the intended delta.
- Use the local `agent-work` branch for autonomous batches unless the maintainer
  names another branch.
- Commit coherent, verified increments locally, but do not push `agent-work` or
  open a pull request without explicit maintainer authorization.
- Do **not** open public GitHub issues without maintainer authorization; drafts
  live in `docs/guide/contributor-tasks.md`.
- Package version (`lakefile.toml`, `CITATION.cff`) stays at the last published
  baseline until the maintainer authorizes a bump and release note (e.g. v0.1.0
  until an explicit 0.2 publication). Branch names and `STATE.md` may describe
  post-release work without implying a released version.
- Publish through a reviewed pull request and squash merge so `main` retains a
  small, linear release history.
- Preserve pre-squash development history under a local archive branch when it
  remains useful; do not mix that history into new public deltas.

## Validation before claiming green

Cheap preflight (schema + generated views, no Lean):

```console
./scripts/agent_gate.sh
```

Full local gate before claiming green (adjust if the maintainer names a subset):

```console
./scripts/agent_gate.sh
python3 scripts/check_print_axioms.py
lake build
xargs lake build < scripts/lean_build_targets.txt
```

Historical v0.1 evidence only: `python3 scripts/audit_release_v0_1.py` (must not
block genuine post-v0.1 bridge graduation).

## Audience and wording

Primary readers are **AI safety researchers**. Prefer clear models, explicit
exclusions, and honest `RELATED` / `HUMAN_REVIEW` labels over maximum
paper-syntax fidelity.

**Tracked prose is strategic.** Do not put conversational shorthand or
imprecise slogans into registry notes, Lean docs, README, or other committed
files. Cite papers with the claim they actually state (model, property,
quantifiers). Reserve informal chat phrasing for private discussion only.
