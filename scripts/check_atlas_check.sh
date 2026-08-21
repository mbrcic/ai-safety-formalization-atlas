#!/usr/bin/env bash
# Assert that `atlas-check` returns what the Lean proofs already say.
#
# The models under docs/examples/atlas-check/ mirror architectures the tree
# already proves things about — Examples.Oversight.Overseer for the devices, and
# Examples.Oversight.JointObservation.Procurement for the coalitions — so this
# compares a running program against kernel-checked theorems rather than against
# a recorded transcript. If the two ever disagree,
# one of them is wrong and the disagreement is the finding.
#
# Not in agent_gate.sh: that gate is explicitly the cheap validators and does not
# run `lake build`. This belongs beside the Lean compile step.
set -euo pipefail

readonly ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly MODELS="$ROOT/docs/examples/atlas-check"
readonly BINARY="$ROOT/.lake/build/bin/atlas-check"

cd "$ROOT"
lake build atlas-check

if [[ ! -x "$BINARY" ]]; then
  echo "atlas-check did not produce $BINARY" >&2
  exit 1
fi

failures=0
checks=0

expect() {
  local model="$1"
  local pattern="$2"
  local output
  if ! output=$("$BINARY" "$MODELS/$model" 2>&1); then
    echo "FAIL $model: exited non-zero" >&2
    echo "$output" >&2
    failures=$((failures + 1))
    return
  fi
  if ! grep -qF -- "$pattern" <<<"$output"; then
    echo "FAIL $model: expected to find '$pattern'" >&2
    echo "$output" >&2
    failures=$((failures + 1))
    return
  fi
  checks=$((checks + 1))
  echo "ok   $model: $pattern"
}

# Overseer A answers every probe, and no blockwise collision is present.
# Lean: Examples.Oversight.Overseer.overseerA_weaklyInfers.
expect overseer-reads-the-world.json "weak inference (Definition 3): HOLDS"
expect overseer-reads-the-world.json "blockwise collision at value 1: ABSENT"

# Overseer B is refuted at every configuration and every context.
# Lean: overseerB_not_weaklyInfers, overseerB_not_physicallyKnows.
expect overseer-reports-its-setting.json "weak inference (Definition 3): FAILS"
expect overseer-reports-its-setting.json "blockwise collision at value 1: PRESENT"

# A's report stream does not determine the hazard.
# Lean: overseerA_report_not_knowable.
expect report-stream-is-blind.json "verdict: NOT KNOWABLE"

# An injective observation does.
expect full-state-is-readable.json "verdict: KNOWABLE"

# The procurement architecture, against the theorems that already decide it.
# Lean: Examples.Oversight.JointObservation.Procurement.not_covers_qEmitted,
# whose documented witness is (sigma10, sigma11) — states 1 and 3 here.
expect procurement-emitted-interface.json "verdict: NOT KNOWABLE"
expect procurement-emitted-interface.json "states 1 and 3 share an observation"

# Lean: Procurement.covers_qCD — the permitted joint predicate over private evidence.
expect procurement-private-joint.json "verdict: KNOWABLE"

# Lean: Procurement.not_covers_qC — one principal's full private evidence is still
# not enough, because the hazard is relational.
expect procurement-private-data-owner.json "verdict: NOT KNOWABLE"

# The variety bound, both branches. Three situations and two interventions, with
# every intervention still separating them: no overseer forces the outcome, and
# the agreement theorem quantifies over every observation, so the verdict is
# about all policies rather than one.
# Lean: Examples.Oversight.VarietyBound.not_forces_revealing.
expect oversight-repertoire-too-small.json "verdict: NO OVERSEER CAN FORCE THE OUTCOME"

# The same shape with one intervention that flattens every situation to a single
# outcome. The counting hypothesis fails, so the bound is silent — and the
# checker must say that it is silent rather than report success.
# Lean: Examples.Oversight.VarietyBound.forces_flattening.
expect oversight-has-a-flattening-lever.json "verdict: THE COUNTING BOUND DOES NOT APPLY"
expect oversight-has-a-flattening-lever.json "this is NOT a finding that oversight succeeds"

# A model the reader must refuse rather than silently decide.
# The X's must end the template: BSD `mktemp` substitutes them only there, so an
# `.json` suffix made both calls resolve to the same name and the second failed.
malformed="$(mktemp "${TMPDIR:-/tmp}/atlas-check-XXXXXX")"
trap 'rm -f -- "$malformed"' EXIT
cat >"$malformed" <<'JSON'
{ "schema": "atlas-check/1", "kind": "knowability",
  "states": 4, "observation": [0, 1], "property": [0, 1, 0, 1] }
JSON
if "$BINARY" "$malformed" >/dev/null 2>&1; then
  echo "FAIL malformed model: a short array was accepted" >&2
  failures=$((failures + 1))
else
  checks=$((checks + 1))
  echo "ok   malformed model: rejected rather than decided"
fi

# The device check is exponential in the number of distinct target values and
# must not be exponential in the state count. An earlier version relabelled the
# target into the state count and took 11s at 22 states; this model has 120
# states and two target values, and finishes in well under a second. A timeout
# here means the exponent moved back onto the wrong quantity.
wide="$(mktemp "${TMPDIR:-/tmp}/atlas-check-XXXXXX")"
python3 - "$wide" <<'PY'
import json, sys
n = 120
json.dump({"schema": "atlas-check/1", "kind": "device", "states": n,
           "setup": [i // 2 for i in range(n)],
           "conclusion": [i % 2 == 0 for i in range(n)],
           "target": [i % 2 for i in range(n)], "value": 1},
          open(sys.argv[1], "w"))
PY
# `timeout` is GNU coreutils, absent on a stock macOS. Skipping with a notice is
# the trade `agent_gate.sh` already makes for pytest and ty; CI runs on Linux, so
# the guard still holds on a pull request.
timeout_command=""
for candidate in timeout gtimeout; do
  if command -v "$candidate" >/dev/null 2>&1; then
    timeout_command="$candidate"
    break
  fi
done
if [[ -z "$timeout_command" ]]; then
  echo "skip 120 states with two target values: no timeout(1) available (CI runs it)"
elif "$timeout_command" 30 "$BINARY" "$wide" >/dev/null 2>&1; then
  checks=$((checks + 1))
  echo "ok   120 states with two target values: decided within the timeout"
else
  echo "FAIL 120 states with two target values: timed out or errored" >&2
  echo "     the device check is exponential in distinct target values and must" >&2
  echo "     not be exponential in the state count; see docs/guide/atlas-check.md" >&2
  failures=$((failures + 1))
fi
rm -f -- "$wide"

# The step no theorem covers: reading the file. The proofs in Knowledge/Check.lean
# say the *normalization* is harmless; nothing says the parse built the model the
# author wrote. That is tested rather than proved, and it is where the clamp in
# runVariety was found.
if ! python3 "$ROOT/scripts/check_atlas_check_parse.py"; then
  echo "FAIL parse battery: see scripts/check_atlas_check_parse.py" >&2
  failures=$((failures + 1))
else
  checks=$((checks + 1))
fi

if (( failures > 0 )); then
  echo "atlas-check disagrees with the Lean proofs in $failures place(s)" >&2
  exit 1
fi

if [[ -n "$timeout_command" ]]; then
  echo "atlas-check ok: $checks checks agree with the Lean proofs and the scaling guard holds"
else
  echo "atlas-check ok: $checks checks agree with the Lean proofs; scaling guard skipped (no timeout(1))"
fi
