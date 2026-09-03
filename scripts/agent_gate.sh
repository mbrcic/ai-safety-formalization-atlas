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
  # Under Bash 3.2 with `set -u`, expanding an empty array is an
  # unbound-variable error. Keep the recursive command nonempty instead.
  if [ "$lean_only" = 1 ]; then
    quiet_command=("$0" --fast)
  else
    quiet_command=("$0")
  fi
  if "${quiet_command[@]}" >"$gate_log" 2>&1; then
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
# Those five are NOT independent of repository content, and the lane must not be
# justified that way.  test_validators copies registry.yaml, conjectures.yaml,
# tasks.yaml, formalization-search.json, AISafetyAtlas.lean, the whole
# AISafetyAtlas/ tree and several docs/ trees into a temporary tree and runs the
# validators against them; test_source_neutral_views reads the live registry;
# the a1-a3 harness reads a reproduction script and provenance documents; and
# tests/ reaches declaration locations and repository Markdown.
#
# The lane is justified by *when* it is used: it is the retry after a failure
# inside one edit cycle, and the full gate is owed before the commit regardless
# -- non-negotiable if scripts/, tests/ or a ledger schema was touched.  A green
# --fast is not a green change.
#
# Run times vary by roughly threefold between runs, so no figure is quoted here:
# measure, do not inherit a number.
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
#
# Truncated with `awk`, never `head`. This script runs under `pipefail`, and
# `head` closes the pipe as soon as it has its lines: the writer then takes
# SIGPIPE, Python turns that into a BrokenPipeError, and an *advisory* check
# fails the whole gate for having had too much to say. `awk` reads its input to
# the end, so the truncation stays a display choice. `check_scope_witnesses`
# already prints 44 lines and grows with the registry, so this is the live case.
echo "==> check_statement_freeze (advisory)"
python3 scripts/check_statement_freeze.py | awk 'NR <= 20'

echo "==> check_scope_witnesses (advisory)"
python3 scripts/check_scope_witnesses.py | awk 'NR <= 1'

# Advisory: says what a branch did to statements as opposed to proofs. On a
# feature branch new theorems are the point, so this never blocks; run it with
# --fail-on-drift for a toolchain migration, where the answer should be none.
# Skipped when origin/main is not fetched, as in a shallow CI checkout.
echo "==> check_statement_drift (advisory)"
if git rev-parse --verify --quiet origin/main >/dev/null; then
  # Both summary lines matter: an adjudication is a declaration the tool cannot
  # classify, and printing only the first line would hide whichever came second.
  python3 scripts/check_statement_drift.py --ref origin/main \
    | grep -E "^(adjudicate|statement drift)" || true
else
  echo "check_statement_drift skipped: origin/main is not available in this checkout"
fi

# Blocking, and the only check here that is. The advisory above never blocks
# because a feature branch is supposed to add statements; a toolchain bump is
# not, and the flag written for that case was never wired to anything. This
# decides which situation it is from lean-toolchain rather than from intent, and
# passes untouched on an ordinary branch.
echo "==> check_migration_adjudicated"
python3 scripts/check_migration_adjudicated.py

# The silent elaboration changes a migration records rest on substitution-class
# verdicts, and a verdict is only worth what still holds it up: a class widened,
# a dump edited, or a regression in the classifier would leave the recorded
# "every silent change is accounted for" true of nothing. Reading the committed
# dumps needs no toolchain and takes a second, so the accounting is checked here
# and not only in CI. The awk filter reads its input to the end -- `head` would
# SIGPIPE the writer and, under pipefail, fail the gate for succeeding too
# loudly -- and pipefail keeps the checker's own exit status.
echo "==> check_elaboration_drift --classify"
python3 scripts/check_elaboration_drift.py --classify \
  docs/status/elab-baseline-v4310.json docs/status/elab-baseline-v4330.json \
  | awk '/^elaboration classes:/ || /silent change\(s\)/ || /^check_elaboration_drift:/'

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
