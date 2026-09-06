## Documentation layout

| Path | Role |
|---|---|
| `docs/agent/` | Agent navigation + generated compact indexes |
| `docs/guide/` | Human explainers (methodology, open work, tasks, …) |
| `docs/status/` | **Generated** coverage tables — do not hand-edit |
| `docs/provenance/` | Discovery evidence + external reproduction narrative |
| `docs/bridges/` | Bridge review packages |
| `docs/releases/` | Release evidence notes |

After editing a maintained ledger — `registry.yaml`, `conjectures.yaml`, or
`tasks.yaml` — run `python3 scripts/generate_registry_views.py` (updates
`docs/status/*`, `docs/guide/contributor-tasks.md`, `docs/agent/by-id.json`,
`docs/agent/search-summary.json`, README/STATE snippets, and the Lean registry
and conjecture checks), then `./scripts/agent_gate.sh`. Do **not** hand-edit
`docs/provenance/formalization-search.json`: when search terms, corpora, or pins
change, rebuild that generated evidence with
`scripts/update_formalization_search.py` using its pinned corpus arguments,
then regenerate the views and run the gate. Paper ↔ formalization map:
`docs/status/sources/`. AI-safety literature map:
`docs/guide/related-literature.md`.
