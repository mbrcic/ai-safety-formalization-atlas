# Agent index

Read [`AGENTS.md`](../../AGENTS.md) first (context budget at the top), then this
file. Prefer the small paths below over loading full inventory dumps.

## Default open set

| Path | Why |
|---|---|
| [`AGENTS.md`](../../AGENTS.md) | Short policy, public API, do-not-read list |
| [`STATE.md`](../../STATE.md) | Live phase + generated coverage snapshot |
| [`docs/agent/by-id.json`](by-id.json) | Compact `BY-###` / `LAND-###` lookup |
| [`docs/agent/search-summary.json`](search-summary.json) | Compact discovery hits (not full search dump) |
| [`docs/status/atlas-index.md`](../status/atlas-index.md) | 44-row survey table |
| [`docs/status/landscape-index.md`](../status/landscape-index.md) | Non–Table-1 landscape |
| [`docs/guide/open-work.md`](../guide/open-work.md) | Research queue |
| [`docs/guide/contributor-tasks.md`](../guide/contributor-tasks.md) | Bounded CT units |
| Facade modules under `AISafetyAtlas/*.lean` | Public Lean surface for the task domain |

## Lookup recipe

```console
# One survey row (no full registry load in the agent context):
python3 -c "import json; d=json.load(open('docs/agent/by-id.json')); print(json.dumps(d['results_by_id']['BY-020'], indent=2))"

# One landscape entry:
python3 -c "import json; d=json.load(open('docs/agent/by-id.json')); print(json.dumps(d['landscape_by_id']['LAND-NFL-001'], indent=2))"

# Discovery hits for one id (prefer over formalization-search.json):
python3 -c "import json; d=json.load(open('docs/agent/search-summary.json')); print(json.dumps(d['results']['BY-001'], indent=2))"
```

Open [`registry.yaml`](../../registry.yaml) only when you need full notes,
`candidate_formalizations`, or `bridge_review` detail for **one** id (prefer
`rg -n '"id": "BY-0xx"' -A 80 registry.yaml` over reading the whole file).

## Lean surface

Open **facade** modules only (`AISafetyAtlas/Learning.lean`,
`SocialChoice.lean`, `Logic.lean`, `Verification.lean`, nested facades such as
`Verification/Robot.lean`). Do **not** open `AISafetyAtlas/Upstream/**` or
`vendor/**` unless the task is to edit that formalization.

## Regenerated artifacts

After registry, landscape, or search-evidence edits:

```console
python3 scripts/generate_registry_views.py
```

Updates `docs/status/*`, `docs/agent/by-id.json`, `docs/agent/search-summary.json`,
README/STATE snippets, and `AISafetyAtlas/Examples/Registry.lean`. Do not
hand-edit generated files.

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
`reviews/**`, `AISafetyAtlas/Upstream/**`, `vendor/**`, `.lake/**`, and
accidental download debris.
