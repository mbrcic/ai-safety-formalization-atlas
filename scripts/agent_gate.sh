#!/usr/bin/env bash
# Cheap agent validation gate: schema + generated views + path checks.
# Does not run lake build or axiom scans (use full AGENTS.md gate for that).
set -euo pipefail

# Agents often run the cheap gate repeatedly while iterating.  Preserve the
# full diagnostic stream on failure, but make successful probes cheap in the
# context window when explicitly requested.
if [ "${1:-}" = "--quiet" ]; then
  if [ "$#" -ne 1 ]; then
    echo "usage: $0 [--quiet]" >&2
    exit 2
  fi
  gate_log="$(mktemp)"
  trap 'rm -f "$gate_log"' EXIT
  if "$0" >"$gate_log" 2>&1; then
    echo "agent_gate: ok (quiet; full checks passed)"
    exit 0
  fi
  cat "$gate_log"
  exit 1
fi

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

echo "==> test_source_neutral_views"
python3 scripts/test_source_neutral_views.py

echo "==> test_a1_a3_pattern_a_harness"
python3 scripts/test_a1_a3_pattern_a_harness.py

echo "==> generate_registry_views --check"
python3 scripts/generate_registry_views.py --check

echo "==> validate_current_state"
python3 scripts/validate_current_state.py

echo "==> check_docs_paths"
python3 scripts/check_docs_paths.py

# Shape-level regressions (malformed containers, wrong metadata types). Kept in
# pytest because they are parameterised and pytest is not a dependency of the
# repository — a contributor without it still gets every check above, and CI
# installs it so the suite is not optional there.
echo "==> pytest tests/"
if python3 -c "import pytest" >/dev/null 2>&1; then
  python3 -m pytest tests/ -q --no-header -p no:cacheprovider
else
  echo "pytest not installed; skipping tests/ (CI runs it)"
fi

# Type checking is not decoration here: it found a `match.lastindex >= 3`
# comparison against a value the standard library types as `int | None`, and two
# `.group()` calls guarded by a helper that narrows nothing.
echo "==> ty check"
if command -v ty >/dev/null 2>&1; then
  ty check scripts/ tests/
else
  echo "ty not installed; skipping type check (CI runs it)"
fi

echo "agent_gate: ok (cheap validators only; lake build not run)"
