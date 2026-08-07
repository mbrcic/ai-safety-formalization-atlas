# Contributor and Agent Guidance

Read this file before autonomous work. Live phase: [`STATE.md`](STATE.md).
Agent map: [`docs/agent/INDEX.md`](docs/agent/INDEX.md). Human doc map:
[`docs/README.md`](docs/README.md). Policy detail:
[`docs/guide/methodology.md`](docs/guide/methodology.md).

## Context budget (agents)

### Default open set

1. This file (short policy)
2. [`STATE.md`](STATE.md)
3. [`docs/agent/INDEX.md`](docs/agent/INDEX.md), [`by-id.json`](docs/agent/by-id.json),
   and [`search-summary.json`](docs/agent/search-summary.json) as needed
4. [`docs/status/landscape-index.md`](docs/status/landscape-index.md) /
   [`docs/status/sources/`](docs/status/sources/) if browsing coverage
5. **One facade module** under `AISafetyAtlas/*.lean` (or a small nested facade
   such as `Verification/Robot.lean`) for the task domain — not `Upstream/`
6. [`docs/guide/open-work.md`](docs/guide/open-work.md) or
   [`contributor-tasks.md`](docs/guide/contributor-tasks.md) when picking work

### Do not read by default

| Path | Why | When to open |
|---|---|---|
| Full [`registry.yaml`](registry.yaml) | Redundant with `by-id.json` | One `BY-###` or `LAND-###` via `rg` for notes / candidates / bridge_review |
| [`docs/provenance/formalization-search.json`](docs/provenance/formalization-search.json) | Large discovery dump | Regenerating evidence or deep candidate audit |
| [`ROADMAP.md`](ROADMAP.md) | Human strategy, not live tasking | Maintainer names roadmap work |
| `AISafetyAtlas/Upstream/**` | Large vendored/collapsed proofs | Editing that formalization only |
| `vendor/**` | Upstream vendor trees | Editing that vendored package only |
| `.lake/**`, `**/CLAUDE.md`, `ai_context.txt` | Build cache / tool dumps | Never as task context |
| Accidental `https:/`, `http:/` trees | wget path debris (gitignored) | Delete if recreated |

### Lean surface rule

Prefer **facade** modules (`AISafetyAtlas/Learning.lean`, `SocialChoice.lean`,
`Logic.lean`, `Verification.lean`, … and small nested facades). Do not open
`Upstream/` or `vendor/` unless the task is to change that proof tree.

### Cheap vs full validation

```console
./scripts/agent_gate.sh   # schema + generated views + path checks (no lake)
```

Full Lean gate is under **Validation** below. Skip `lake build` for pure docs
or agent-index edits.

## Public Lean API

`AISafetyAtlas` is a small stable facade. One canonical public declaration per
result; keep conventional theorem names; namespace form
`AISafetyAtlas.<Domain>.<OptionalRepresentation>.<Theorem>` (`UpperCamelCase`
namespaces, `snake_case` declarations). Add representation namespaces or
suffixes (`_iff`, `_reduction`, …) only for genuine interface distinctions.
Do not mirror entire upstream libraries.

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

## Parsimony (formalizations)

Reuse a maintained Lean result + thin atlas alias before porting another proof.
Keep a second formalization only for a documented substantial gain (stronger
theorem, different representation, reduction certificate, constructive content,
or necessary independence). Non-Lean proofs may be provenance without duplicate
public Lean declarations. Prefer packaging Rice as `Verification.rice` /
`AgentBehavior.no_behavioral_safety_verifier` rather than a second undecidability
proof. Detail: [`docs/guide/methodology.md`](docs/guide/methodology.md).

## Coverage, landscape, and bridges

- **Headline coverage:** reproduced registry formalizations with `EXACT` or
  `EQUIVALENT` only. `RELATED` does not increase the count.
- **Which record takes your edit:**
  | Where | Holds | Note |
  |---|---|---|
  | `registry.yaml` survey claim rows | what the Brčić–Yampolskiy survey asserted | `BY-001`…`BY-044` is **closed**; never add `BY-045` |
  | `registry.yaml` other claim rows | what any other source asserted | `CLM-` prefix; no survey-only fields (`paper_reference`, `survey_proof_assessment`, `formal_library_search`) |
  | `registry.yaml` artifact rows | formalizations standing on their own | `LAND-` prefix, no `informal_claim`, never headline coverage |
  | `conjectures.yaml` | open questions, compiling statement, no proof | never a theorem, never counted as one |
  | `tasks.yaml` | the task board | `docs/guide/contributor-tasks.md` is **generated** — never edit the Markdown |
- **Sources are `directory` or `work`.** A directory is a curated map (the survey
  itself, `mathforaisafety.org`, AISI, MAIS): never graded against, entry count
  never a metric. A `work` is statement-bearing and is the only thing a
  statement-match grade may cite.
- **Claiming something does not exist?** That needs a `novelty_checks` record in
  `docs/provenance/formalization-search.json` — corpus, revision, date, and what
  the search did not cover. The six-corpus sweep is the `baseline-catalogue`
  profile for one source and is **not** inherited by new work.
- **Layers:** (1) math theorem → (2) atlas interface → (3) AI-safety bridge →
  (4) real-system claim. Layers 3–4 need human review; Lean at 1–2 does not
  inherit an AI reading.
- **`ai_bridge_status`:** `HUMAN_REVIEW` → `STATEMENT_REVIEWED` → `REVIEWED`.
  Non-`HUMAN_REVIEW` needs a real `bridge_review` record under `docs/bridges/`.
  **Never invent** human review or graduate a bridge without authorization.
- Prefer `STATEMENT_REVIEWED` over overclaiming real systems.
- Robot (`action_safety_unverifiable`): **conditional reduction core**,
  relationship `RELATED`. Do not lengthen for paper show-off.
- GS: Isabelle `LAND-GS-001`; Lean facade `gibbard_satterthwaite` (`LAND-GS-002`).
  Do not vendor the rest of SocialChoiceLean without a consumer need.

## Documentation layout

| Path | Role |
|---|---|
| `docs/agent/` | Agent navigation + generated compact indexes |
| `docs/guide/` | Human explainers (methodology, open work, tasks, …) |
| `docs/status/` | **Generated** coverage tables — do not hand-edit |
| `docs/provenance/` | Discovery evidence + external reproduction narrative |
| `docs/bridges/` | Bridge review packages |
| `docs/releases/` | Release evidence notes |

After editing **any** ledger — `registry.yaml`,
`conjectures.yaml`, `tasks.yaml`, or `docs/provenance/formalization-search.json` —
run `python3 scripts/generate_registry_views.py` (updates `docs/status/*`,
`docs/guide/contributor-tasks.md`, `docs/agent/by-id.json`,
`docs/agent/search-summary.json`, README/STATE snippets, and the Lean registry and
conjecture checks), then `./scripts/agent_gate.sh`. Paper ↔ formalization map:
`docs/status/sources/`. AI-safety literature map:
`docs/guide/related-literature.md`.

## Branch, version, and publication

- `main` is protected; do not commit or push agent work to it.
- Use local `agent-work` unless the maintainer names another branch.
- Commit coherent verified increments locally; **do not push** or open PRs/issues
  without explicit maintainer authorization (draft tasks in `tasks.yaml` or the
  issue tracker; `docs/guide/contributor-tasks.md` is generated).
- Package version stays at the last published baseline until authorized.
- Publish via reviewed PR + squash merge; keep pre-squash history on a local
  archive branch when useful.

## Validation

Cheap preflight:

```console
./scripts/agent_gate.sh
```

The gate ends with `pytest tests/` (malformed-shape regressions) and
`ty check scripts/ tests/`. Both are skipped with a notice when the tool is not
installed, so the gate still runs without them; CI installs both, so neither is
optional on a pull request. Install with `python3 -m pip install pytest ty`.

Full green (Lean + axioms):

```console
./scripts/agent_gate.sh
python3 scripts/check_print_axioms.py
lake build
xargs lake build < scripts/lean_build_targets.txt
```

Historical v0.1 only: `python3 scripts/audit_release_v0_1.py` (must not block
genuine post-v0.1 bridge graduation).

## Audience and wording

Primary readers are **AI safety researchers**. Prefer clear models, explicit
exclusions, and honest `RELATED` / `HUMAN_REVIEW` labels. Tracked prose is
strategic: no conversational shorthand in registry notes, Lean docs, or README.
Cite papers with the claim they actually state.
