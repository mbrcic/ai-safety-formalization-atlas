#!/usr/bin/env bash
# Cheap agent validation gate: schema + generated views + path checks.
# Does not run lake build or axiom scans (use full AGENTS.md gate for that).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "==> validate_registry"
python3 scripts/validate_registry.py

echo "==> validate_conjectures"
python3 scripts/validate_conjectures.py

echo "==> validate_tasks"
python3 scripts/validate_tasks.py

echo "==> test_validators"
python3 scripts/test_validators.py

echo "==> generate_registry_views --check"
python3 scripts/generate_registry_views.py --check

echo "==> validate_current_state"
python3 scripts/validate_current_state.py

echo "==> check_docs_paths"
python3 scripts/check_docs_paths.py

echo "agent_gate: ok (cheap validators only; lake build not run)"
