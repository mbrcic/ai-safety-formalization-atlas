#!/usr/bin/env bash
# Cheap agent validation gate: schema + generated views + path checks.
# Does not run lake build or axiom scans (use full AGENTS.md gate for that).
set -euo pipefail

quiet=0
lean_only=0
for arg in "$@"; do
  case "$arg" in
    --quiet) quiet=1 ;;
    --fast|--lean) lean_only=1 ;;
    *) echo "usage: $0 [--quiet] [--fast]   (--lean: old name for --fast)" >&2; exit 2 ;;
  esac
done

# Agents often run the cheap gate repeatedly while iterating.  Preserve the
# full diagnostic stream on failure, but make successful probes cheap in the
# context window when explicitly requested.
if [ "$quiet" = 1 ]; then
  gate_log="$(mktemp)"
  trap 'rm -f "$gate_log"' EXIT
  inner=()
  [ "$lean_only" = 1 ] && inner=(--fast)
  if "$0" "${inner[@]}" >"$gate_log" 2>&1; then
    if [ "$lean_only" = 1 ]; then
      echo "agent_gate: ok (quiet, --fast; Python self-tests NOT run)"
    else
      echo "agent_gate: ok (quiet; full checks passed)"
    fi
    exit 0
  fi
  cat "$gate_log"
  exit 1
fi

# --fast (--lean is the old name, still accepted) skips the five steps that
# exercise the validator scripts themselves.
#
# CORRECTION, 2026-08-29.  This comment used to claim those five "take no input
# from AISafetyAtlas/ or docs/", so "a Lean edit cannot change their verdict".
# That is false and was the stated reason the lane is safe.  test_validators
# copies registry.yaml, conjectures.yaml, tasks.yaml, formalization-search.json,
# AISafetyAtlas.lean, the whole AISafetyAtlas/ tree and several docs/ trees into
# a temporary tree and runs the validators against them; test_source_neutral_views
# reads the live registry; the a1-a3 harness reads a reproduction script and
# provenance documents; and tests/ reaches declaration locations and repository
# Markdown.  Repository content is an input to all of them.
#
# So the lane is justified by *when* it is used, not by independence: it is the
# retry after a failure inside one edit cycle, and the full gate is owed before
# the commit regardless -- non-negotiable if scripts/, tests/ or a ledger schema
# was touched.  A green --fast is not a green change.
#
# Cost, measured 2026-08-29: test_validators is ~12 s, down from ~53 s.  Two
# implementation fixes, no check removed: the Lean masker stopped scanning a
# character at a time, and the import-line regex stopped running under re.M
# where its leading \s* consumed newlines.  Whole-gate numbers on this machine
# vary by roughly threefold run to run, so they are not quoted here: measure,
# do not inherit a number.
# Everything that reads the tree, the ledgers, or the generated views still
# runs.  See AGENTS.md "Validation" for when the full gate is mandatory.
skip_self_tests() { [ "$lean_only" = 1 ]; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "==> validate_registry"
python3 scripts/validate_registry.py

echo "==> validate_conjectures"
python3 scripts/validate_conjectures.py

echo "==> validate_tasks"
python3 scripts/validate_tasks.py

if skip_self_tests; then
  echo "==> test_validators, test_source_neutral_views, test_a1_a3_pattern_a_harness (skipped: --fast)"
else
  echo "==> test_validators"
  python3 scripts/test_validators.py

  echo "==> test_source_neutral_views"
  python3 scripts/test_source_neutral_views.py

  echo "==> test_a1_a3_pattern_a_harness"
  python3 scripts/test_a1_a3_pattern_a_harness.py
fi

echo "==> generate_registry_views --check"
python3 scripts/generate_registry_views.py --check

echo "==> validate_current_state"
python3 scripts/validate_current_state.py

echo "==> check_wolpert_status_table"
python3 scripts/check_wolpert_status_table.py

echo "==> check_wolpert_2018_status_table"
python3 scripts/check_wolpert_2018_status_table.py

echo "==> generate_dependency_graph --check"
python3 scripts/generate_dependency_graph.py --check

echo "==> check_public_api"
python3 scripts/check_public_api.py

echo "==> check_examples_layout"
python3 scripts/check_examples_layout.py

echo "==> check_example_coverage"
python3 scripts/check_example_coverage.py

echo "==> check_coverage_audit"
python3 scripts/check_coverage_audit.py

# Advisory: reports Wider/Beyond rows with no worked witness. Never blocks —
# it produces a worklist, and most unwitnessed rows are fine.
echo "==> check_statement_freeze (advisory)"
python3 scripts/check_statement_freeze.py | head -20

echo "==> check_scope_witnesses (advisory)"
python3 scripts/check_scope_witnesses.py | head -1

echo "==> generate_non_claims --check"
python3 scripts/generate_non_claims.py --check

echo "==> check_docstring_identifiers"
python3 scripts/check_docstring_identifiers.py

echo "==> check_conjecture_grade_prose"
python3 scripts/check_conjecture_grade_prose.py

echo "==> check_cited_declarations"
python3 scripts/check_cited_declarations.py

echo "==> check_docs_paths"
python3 scripts/check_docs_paths.py

# Shape-level regressions (malformed containers, wrong metadata types). Kept in
# pytest because they are parameterised and pytest is not a dependency of the
# repository — a contributor without it still gets every check above, and CI
# installs it so the suite is not optional there.
if skip_self_tests; then
  echo "==> pytest tests/ (skipped: --fast)"
elif python3 -c "import pytest" >/dev/null 2>&1; then
  echo "==> pytest tests/"
  python3 -m pytest tests/ -q --no-header -p no:cacheprovider
else
  echo "==> pytest tests/"
  echo "pytest not installed; skipping tests/ (CI runs it)"
fi

# Type checking is not decoration here: it found a `match.lastindex >= 3`
# comparison against a value the standard library types as `int | None`, and two
# `.group()` calls guarded by a helper that narrows nothing.
if skip_self_tests; then
  echo "==> ty check (skipped: --fast)"
elif command -v ty >/dev/null 2>&1; then
  echo "==> ty check"
  ty check scripts/ tests/
else
  echo "==> ty check"
  echo "ty not installed; skipping type check (CI runs it)"
fi

if skip_self_tests; then
  echo "agent_gate: ok (--lean; Python self-tests NOT run, lake build not run)"
  echo "  Run without --lean before committing: the skipped steps are the only"
  echo "  checks on the validator scripts themselves, and CI runs them."
else
  echo "agent_gate: ok (cheap validators only; lake build not run)"
fi
