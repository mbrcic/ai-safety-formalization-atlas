#!/usr/bin/env bash
# One-shot onboarding bootstrap for the AI Safety Formalization Atlas.
#
#   scripts/setup.sh            full proof setup: elan + prebuilt Mathlib + build + validators
#   scripts/setup.sh --pointer  docs/registry only: skip the Lean toolchain, run cheap validators
#
# Idempotent and safe to re-run. Installs elan only when `lake` is missing;
# the toolchain version is taken from `lean-toolchain`, dependencies from the
# committed `lake-manifest.json` (never `lake update`).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="full"
for arg in "$@"; do
  case "$arg" in
    --pointer|--no-lean) MODE="pointer" ;;
    -h|--help) awk 'NR>1 && /^#/{sub(/^# ?/,"");print;next} NR>1{exit}' "$0"; exit 0 ;;
    *) echo "unknown option: $arg (try --help)" >&2; exit 2 ;;
  esac
done

need() { command -v "$1" >/dev/null 2>&1; }

if ! need python3; then
  echo "error: python3 is required — the validators are pure-stdlib Python 3." >&2
  exit 1
fi

if [ "$MODE" = "pointer" ]; then
  echo "==> pointer mode: skipping the Lean toolchain"
  ./scripts/agent_gate.sh
  echo
  echo "setup: ok (pointer). Add a lead under a row's candidate_formalizations in"
  echo "registry.yaml, re-run scripts/agent_gate.sh, then open a PR."
  exit 0
fi

# --- Lean toolchain (elan) ---
if ! need lake; then
  echo "==> installing elan (Lean toolchain manager)"
  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi

# elan installs under ~/.elan; make it visible for the rest of this script.
if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1091
  . "$HOME/.elan/env"
fi

if ! need lake; then
  echo "error: 'lake' is still not on PATH after installing elan." >&2
  echo "Open a new shell (or run '. ~/.elan/env') and re-run scripts/setup.sh." >&2
  exit 1
fi

echo "==> fetching prebuilt Mathlib (lake exe cache get)"
lake exe cache get

echo "==> lake build"
lake build

echo "==> building explicit targets (scripts/lean_build_targets.txt)"
xargs lake build < scripts/lean_build_targets.txt

echo "==> cheap validators (scripts/agent_gate.sh)"
./scripts/agent_gate.sh

echo
echo "setup: ok (full). Public API is on 'import AISafetyAtlas'."
echo "Pick a bounded unit: docs/guide/contributor-tasks.md#open-now"
