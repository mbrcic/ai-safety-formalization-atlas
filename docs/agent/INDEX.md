# Agent index

Read [`AGENTS.md`](../../AGENTS.md) first (context budget at the top), then this
file. Prefer the small paths below over loading the full registry or provenance
dumps.

## Default open set

| Path | Why |
|---|---|
| [`AGENTS.md`](../../AGENTS.md) | Policy, public API, do-not-read list |
| [`STATE.md`](../../STATE.md) | Live phase + generated coverage snapshot |
| [`docs/agent/by-id.json`](by-id.json) | Compact `BY-###` / `LAND-###` lookup |
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
```

Open [`registry.yaml`](../../registry.yaml) only when you need full notes,
`candidate_formalizations`, or `bridge_review` detail for **one** id (prefer
`rg -n '"id": "BY-0xx"' -A 80 registry.yaml` over reading the whole file).

## Regenerated artifacts

After registry or landscape edits:

```console
python3 scripts/generate_registry_views.py
```

Updates `docs/status/*`, `docs/agent/by-id.json`, README/STATE snippets, and
`AISafetyAtlas/Examples/Registry.lean`. Do not hand-edit generated files.

## Cheap validation gate

```console
./scripts/agent_gate.sh
```

Runs registry/landscape validators, generated-view check, current-state check,
and docs path check. Does **not** run `lake build` or axiom scans.

## Full gate (before claiming green)

See `AGENTS.md` § Validation. Includes Lean builds and axiom checks.

## Do not load by default

See the context-budget section at the top of [`AGENTS.md`](../../AGENTS.md).
In short: full `registry.yaml`, `docs/provenance/formalization-search.json`,
`reviews/**`, `vendor/**`, `.lake/**`, and accidental download debris.
