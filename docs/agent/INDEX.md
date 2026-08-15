# Agent index

Read [`AGENTS.md`](../../AGENTS.md) first (context budget at the top), then this
file. Prefer the small paths below over loading full inventory dumps.

## Start here (small by design)

Open these three files first. They are the only default context needed to route
an ordinary contribution. Everything below is conditional: open it only when
the task requires that particular inventory, domain, or evidence.

| Path | Why |
|---|---|
| [`AGENTS.md`](../../AGENTS.md) | Short policy, public API, do-not-read list |
| [`STATE.md`](../../STATE.md) | Live phase + generated coverage snapshot |
| [`docs/agent/INDEX.md`](INDEX.md) | This routing map and targeted lookup recipes |

## Open only when needed

| Path | Open it when… |
|---|---|
| [`docs/agent/by-id.json`](by-id.json) | looking up one `BY-*`, `CLM-*`, or `LAND-*` row; prefer the recipe below over loading it wholesale |
| [`docs/agent/search-summary.json`](search-summary.json) | checking discovery hits for one result; do not load the full search evidence |
| [`docs/status/applications.md`](../status/applications.md) | working on an AI-system model reading or bridge |
| [`docs/status/by-area.md`](../status/by-area.md) | browsing the catalogue by mathematical area |
| [`docs/guide/conjectures.md`](../guide/conjectures.md) | proposing or reviewing a conjecture |
| [`docs/status/landscape-index.md`](../status/landscape-index.md) | auditing the atlas Lean surface or artifact rows |
| [`docs/status/relations.md`](../status/relations.md) | asking how two results stand to each other, or which are characterizations rather than point impossibilities |
| [`docs/status/sources/brcic-yampolskiy-2023.md`](../status/sources/brcic-yampolskiy-2023.md) | auditing the survey source specifically |
| [`docs/guide/open-work.md`](../guide/open-work.md) | choosing research work rather than a bounded task |
| [`docs/guide/contributor-tasks.md`](../guide/contributor-tasks.md) | choosing or implementing a CT unit |
| [`docs/provenance/a1-a3-b1-b3-b7-reverification.md`](../provenance/a1-a3-b1-b3-b7-reverification.md) | working on those domain residuals |
| [`docs/guide/atlas-check.md`](../guide/atlas-check.md) | answering a question about one finite model — `lake exe atlas-check` decides it and names the theorem, no Lean to write |
| Facade modules under `AISafetyAtlas/*.lean` | writing Lean for the relevant domain |

## Lookup recipe

```console
# One survey row (no full registry load in the agent context):
python3 -c "import json; d=json.load(open('docs/agent/by-id.json')); print(json.dumps(d['results_by_id']['BY-020'], indent=2))"

# One landscape entry:
python3 -c "import json; d=json.load(open('docs/agent/by-id.json')); print(json.dumps(d['results_by_id']['LAND-NFL-001'], indent=2))"

# Discovery hits for one id (prefer over formalization-search.json):
python3 -c "import json; d=json.load(open('docs/agent/search-summary.json')); print(json.dumps(d['results']['BY-001'], indent=2))"

# Where a row's declarations are defined — file and line, so no search is needed:
python3 -c "import json; d=json.load(open('docs/agent/by-id.json')); print('\n'.join(f\"{x['file']}:{x['line']}  {x['atlas_declaration']}\" for x in d['results_by_id']['LAND-KNOW-DEVICE-001']['lean_artifact']['declarations']))"
```

Every declaration in `lean_artifact` carries `file` and `line`, so reading one is
a single `Read` at an offset rather than a repository-wide grep. Vendored and
external declarations have no in-tree definition site and omit both fields
rather than carrying empty ones.

Open [`registry.yaml`](../../registry.yaml) only when you need full notes,
`candidate_formalizations`, or `bridge_review` detail for **one** id (prefer
`rg -n '"id": "BY-0xx"' -A 80 registry.yaml` over reading the whole file).

## Lean surface

Open **facade** modules only (`AISafetyAtlas/Learning.lean`,
`SocialChoice.lean`, `Logic.lean`, `Verification.lean`, nested facades such as
`Verification/Robot.lean`). Do **not** open `AISafetyAtlas/Upstream/**` or
`vendor/**` unless the task is to edit that formalization.

## Regenerated artifacts

After editing a maintained ledger — `registry.yaml`, `conjectures.yaml`, or
`tasks.yaml`:

```console
python3 scripts/generate_registry_views.py
```

Updates `docs/status/*`, the generated contributor-task board and conjecture
checks, `docs/agent/by-id.json`, `docs/agent/search-summary.json`, README/STATE
snippets, and `AISafetyAtlas/Examples/Registry.lean`. Do not hand-edit generated
files. Do not hand-edit `docs/provenance/formalization-search.json`. When
search terms, corpora, or pins change, first rebuild that evidence with
`scripts/update_formalization_search.py` using its pinned corpus arguments, then
run the generator above and the gate.

## Cheap validation gate

```console
./scripts/agent_gate.sh
```

Schema/views/path checks only — no `lake build`. CI runs this on every PR;
Lean build runs only when Lean-related paths change (always on `main` push).

## Full gate (before claiming green)

See `AGENTS.md` § Validation. Includes Lean builds and axiom checks.

## Do not load by default

See the context-budget section at the top of [`AGENTS.md`](../../AGENTS.md).
In short: full `registry.yaml`, full `formalization-search.json`, `ROADMAP.md`,
`AISafetyAtlas/Upstream/**`, `vendor/**`, `.lake/**`, and
accidental download debris.

## Routing: which file takes your edit

Generated Markdown is never the answer. Edit the ledger, regenerate, gate.
This table is the same one the README shows, rendered from one source.

<!-- BEGIN GENERATED ROUTING -->
<!-- Generated by scripts/generate_registry_views.py; do not edit by hand. -->

| I have… | It goes in | Then |
|---|---|---|
| a pointer to a result, or a proof, that is not recorded here | the [discovery issue form](https://github.com/mbrcic/ai-safety-formalization-atlas/issues/new?template=known-formalization.yml) — we classify it and place it | nothing to install |
| a correction to a record you have already found | the ledger file that holds it | `scripts/setup.sh --pointer` |
| an open question and no proof | the [conjecture issue form](https://github.com/mbrcic/ai-safety-formalization-atlas/issues/new?template=conjecture.yml) | no Lean needed; the statement enters the ledger after it compiles |
| a proof to write, or any Lean change | the facade for your area (see Domain imports); for new coverage, dependencies, or public API, start with the [formalization proposal](https://github.com/mbrcic/ai-safety-formalization-atlas/issues/new?template=formalization-proposal.yml) | `scripts/setup.sh`, then build + gate + `check_print_axioms.py` |
| a change to a contributor task | `tasks.yaml` — never the generated Markdown | regenerate + gate |
| evidence that something does not exist | `novelty_checks` in `docs/provenance/formalization-search.json` | update search evidence, then regenerate + gate |
| a new source to catalogue | `source_catalog` in `registry.yaml`, with its `role`; add a `CLM-*` row with `original_source_refs` if it states a result | regenerate + gate |

**regenerate** `python3 scripts/generate_registry_views.py` · **gate** `./scripts/agent_gate.sh` · **build** `lake build`

Nothing here needs the whole picture: take the row that matches what you
have and ignore the rest.
<!-- END GENERATED ROUTING -->

**Five rules worth knowing before you edit anything:**

1. A **conjecture is not a theorem.** It ships as a `Prop`-valued definition that
   asserts nothing, lives off the root import, and is counted on its own line.
   `sorry` stays banned.
2. A **claim of absence needs recorded evidence** — corpus, revision, date, and
   what the search missed. It is the one claim a reader cannot check.
3. A **source is a `directory` or a `work`.** Directories hand you pointers and
   are never graded against; only a statement-bearing work can carry a grade.
4. A **public `RELATED` record carries its `scope_delta`** — what it does not
   cover, and where that is documented.
5. An **id prefix says what a row is**, not where it came from. `BY-###` is the
   closed survey block, `CLM-*` is a claim from any other source and must name
   that provenance in `original_source_refs`, `LAND-*` is a formalization
   standing on its own account. Only `BY-` rows carry
   `paper_reference`, `survey_proof_assessment`, and `formal_library_search`;
   another source's claim cannot answer them.

One declaration has one owning row. Two rows naming the same
`atlas_declaration` is rejected: every consumer that maps a declaration back to
a result would otherwise answer by iteration order.
