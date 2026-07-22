#!/usr/bin/env bash
# One-shot onboarding bootstrap for the AI Safety Formalization Atlas.
#
#   scripts/setup.sh            full proof setup: elan + prebuilt Mathlib + build + validators
#   scripts/setup.sh --quick    fast first compile: elan + Mathlib cache + one small example
#   scripts/setup.sh --pointer  docs/registry only: skip the Lean toolchain, run cheap validators
#
# Idempotent and safe to re-run. Installs elan only when neither `elan` nor
# `lake` is present; the toolchain version is taken from `lean-toolchain`,
# dependencies from the committed `lake-manifest.json` (never `lake update`).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="full"
for arg in "$@"; do
  case "$arg" in
    --quick) MODE="quick" ;;
    --pointer|--no-lean) MODE="pointer" ;;
    -h|--help) awk 'NR>1 && /^#/{sub(/^# ?/,"");print;next} NR>1{exit}' "$0"; exit 0 ;;
    *) echo "unknown option: $arg (try --help)" >&2; exit 2 ;;
  esac
done

need() { command -v "$1" >/dev/null 2>&1; }

require() {  # require <cmd> <why>
  if ! need "$1"; then
    echo "error: '$1' is required — $2" >&2
    exit 1
  fi
}

require python3 "the validators are pure-stdlib Python 3."

if [ "$MODE" = "pointer" ]; then
  echo "==> pointer mode: skipping the Lean toolchain"
  ./scripts/agent_gate.sh
  echo
  echo "setup: ok (pointer). Add a lead under a row's candidate_formalizations in"
  echo "registry.yaml, re-run scripts/agent_gate.sh, then open a PR."
  exit 0
fi

# --- Lean toolchain (elan) ---
# Gate on elan, not just lake: elan is what honors `lean-toolchain`. A stray
# non-elan `lake` on PATH would pin a different toolchain, so only skip the
# install when elan (or a lake) is already present.
if ! need elan && ! need lake; then
  require curl "needed to download the elan installer."
  echo "==> installing elan (Lean toolchain manager)"
  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi

# elan installs under ~/.elan; make it visible for the rest of this script.
if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1091
  . "$HOME/.elan/env"
fi

require lake "'lake' is not on PATH after installing elan — open a new shell (or run '. ~/.elan/env') and re-run scripts/setup.sh."

echo "==> selected Lean toolchain: $(cat lean-toolchain)"
lake --version

echo "==> fetching prebuilt Mathlib (lake exe cache get)"
lake exe cache get

if [ "$MODE" = "quick" ]; then
  echo "==> quick build: one small Foundation-free example (AISafetyAtlas.Examples.NFLConcrete)"
  lake build AISafetyAtlas.Examples.NFLConcrete
  echo
  echo "setup: ok (quick). One example compiles — the toolchain works."
  echo "Before opening a PR that touches Lean, run the full setup: scripts/setup.sh"
  echo "Pick a bounded unit: docs/guide/contributor-tasks.md#open-now"
  exit 0
fi

echo "==> lake build"
lake build

echo "==> building explicit targets (scripts/lean_build_targets.txt)"
require xargs "needed to build the explicit non-root targets."
xargs lake build < scripts/lean_build_targets.txt

echo "==> cheap validators (scripts/agent_gate.sh)"
./scripts/agent_gate.sh

echo
echo "setup: ok (full). Public API is on 'import AISafetyAtlas'."
echo "Pick a bounded unit: docs/guide/contributor-tasks.md#open-now"
