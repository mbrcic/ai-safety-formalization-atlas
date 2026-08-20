#!/usr/bin/env bash
# Reproduce the pinned google-deepmind/debate Lean development recorded as
# landscape evidence LAND-DEBATE-001 (doubly-efficient debate correctness,
# Brown-Cohen–Irving–Piliouras 2023, arXiv 2311.14125, paper Theorem 6.2).
#
# Two lanes, deliberately both kept:
#
#   (no argument)  Path A — build UPSTREAM at its own toolchain (Lean/Mathlib
#                  v4.8.0) from a separate checkout. Independent of anything the
#                  atlas vendors, so it stays a check on the upstream artifact
#                  itself rather than on the atlas's copy of it.
#
#   --in-tree      Path B — check the vendored port that now lives inside the
#                  atlas 4.31 build closure: strict-trust scan, build, and a
#                  kernel `#print axioms` on the facade declarations. The gate
#                  covers the same declarations via OFF_ROOT_FACADES in
#                  scripts/check_print_axioms.py; this driver is the standalone,
#                  citable form of that evidence, and adds the trust scan.
#
# Path A reproduces; Path B is what makes the result usable from Lean. Neither
# is headline coverage, and neither supports an AI-system reading on its own.
set -euo pipefail

readonly DEBATE_REPOSITORY="https://github.com/google-deepmind/debate.git"
readonly DEBATE_COMMIT="de3a6e500ae1a65dfeea2f91ef519ebad9704be0"
# Correctness theorems (paper Theorem 6.2) live in Debate/Correct.lean.
readonly TARGETS=(
  "Debate.Correct"
)
readonly EXPECTED_THEOREMS=(
  "completeness"
  "soundness"
  "correctness"
)

# --- Path B: the vendored port inside the atlas tree ------------------------

readonly ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly VENDORED_DIRECTORY="AISafetyAtlas/Upstream/Debate"
readonly IN_TREE_TARGETS=(
  "AISafetyAtlas.Upstream.Debate"
  "AISafetyAtlas.Oversight.Debate"
  "AISafetyAtlas.Examples.Oversight.Debate"
)
# The facade surface. Correctness *and* the query-complexity half: a debate
# protocol that were only correct would not be the result the paper states.
readonly FACADE_DECLARATIONS=(
  "AISafetyAtlas.Oversight.Debate.completeness"
  "AISafetyAtlas.Oversight.Debate.soundness"
  "AISafetyAtlas.Oversight.Debate.correctness"
  "AISafetyAtlas.Oversight.Debate.alice_fast"
  "AISafetyAtlas.Oversight.Debate.bob_fast"
  "AISafetyAtlas.Oversight.Debate.vera_fast"
)
readonly ALLOWED_AXIOMS="propext, Classical.choice, Quot.sound"

run_in_tree() {
  cd "$ROOT"

  if [[ ! -d "$VENDORED_DIRECTORY" ]]; then
    echo "vendored tree missing: $VENDORED_DIRECTORY" >&2
    exit 1
  fi

  # Same strict-trust gate as Path A. `axiom` is matched in declaration position
  # only, so prose in a module docstring cannot trip it — and cannot hide a real
  # `axiom` command either, since those start a line.
  local scan_paths=(
    "$VENDORED_DIRECTORY"
    "AISafetyAtlas/Upstream/Debate.lean"
    "AISafetyAtlas/Oversight/Debate.lean"
    "AISafetyAtlas/Examples/Oversight/Debate.lean"
  )
  local forbidden
  forbidden=$(
    rg -n --glob '*.lean' \
      -e '\bsorry\b' \
      -e '\badmit\b' \
      -e '^\s*axiom\b' \
      -e 'sorryAx' \
      -e 'native_decide' \
      -e 'implemented_by' \
      -e '@\[extern' \
      "${scan_paths[@]}" || true
  )
  if [[ -n "$forbidden" ]]; then
    echo "forbidden trusted-base or incomplete-proof tokens found:" >&2
    echo "$forbidden" >&2
    exit 1
  fi
  echo "trust scan: no forbidden tokens in $(find "${scan_paths[@]}" -name '*.lean' | wc -l | tr -d ' ') vendored Lean sources"

  lake build "${IN_TREE_TARGETS[@]}"

  # Kernel-level axiom check. The textual scan above cannot see through an
  # imported dependency; `#print axioms` can, and it is the whole point of
  # having the development inside the build closure rather than beside it.
  local harness
  harness=$(mktemp "${TMPDIR:-/tmp}/atlas-debate-axioms-XXXXXX.lean")
  # EXIT rather than RETURN: under `set -e` a failed build leaves the function
  # without returning, and the harness would survive in the temp directory.
  trap 'rm -f -- "$harness"' EXIT
  {
    echo "import AISafetyAtlas.Oversight.Debate"
    for declaration in "${FACADE_DECLARATIONS[@]}"; do
      echo "#print axioms $declaration"
    done
  } >"$harness"

  local report
  report=$(lake env lean "$harness")
  echo "$report"

  local failures=0
  for declaration in "${FACADE_DECLARATIONS[@]}"; do
    local line
    line=$(printf '%s\n' "$report" | rg -F "'$declaration' depends on axioms:" || true)
    if [[ -z "$line" ]]; then
      echo "no axiom report for $declaration" >&2
      failures=1
    elif [[ "$line" != *"[$ALLOWED_AXIOMS]"* ]]; then
      echo "unexpected axioms for $declaration: $line" >&2
      failures=1
    fi
  done
  if (( failures )); then
    exit 1
  fi

  echo "debate in-tree check ok: ${#FACADE_DECLARATIONS[@]} facade declarations depend only on [$ALLOWED_AXIOMS]"
}

case "${1:-}" in
  --in-tree)
    if [[ "$#" -ne 1 ]]; then
      echo "usage: $0 [--in-tree]" >&2
      exit 2
    fi
    for command_name in lake rg; do
      if ! command -v "$command_name" >/dev/null 2>&1; then
        echo "required command not found: $command_name" >&2
        exit 127
      fi
    done
    run_in_tree
    exit 0
    ;;
  "") ;;
  *)
    echo "usage: $0 [--in-tree]" >&2
    exit 2
    ;;
esac

# --- Path A: upstream at its own toolchain ----------------------------------

for command_name in git lake rg; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "required command not found: $command_name" >&2
    exit 127
  fi
done

work_directory=$(mktemp -d "${TMPDIR:-/tmp}/atlas-debate-XXXXXX")
trap 'rm -rf -- "$work_directory"' EXIT

upstream_directory="$work_directory/upstream"

git init --quiet "$upstream_directory"
git -C "$upstream_directory" remote add origin "$DEBATE_REPOSITORY"
git -C "$upstream_directory" fetch --quiet --depth 1 origin "$DEBATE_COMMIT"
git -C "$upstream_directory" checkout --quiet --detach FETCH_HEAD

actual_commit=$(git -C "$upstream_directory" rev-parse HEAD)
if [[ "$actual_commit" != "$DEBATE_COMMIT" ]]; then
  echo "unexpected debate revision: $actual_commit" >&2
  exit 1
fi

echo "reproducing $DEBATE_REPOSITORY @ $DEBATE_COMMIT"
echo "toolchain: $(cat "$upstream_directory/lean-toolchain")"

# The three headline theorems must be present in the correctness module.
correct_module="$upstream_directory/Debate/Correct.lean"
if [[ ! -f "$correct_module" ]]; then
  echo "expected correctness module missing: Debate/Correct.lean" >&2
  exit 1
fi
for theorem_name in "${EXPECTED_THEOREMS[@]}"; do
  if ! rg -n --glob '*.lean' -e "\\b(theorem|lemma)\\s+$theorem_name\\b" "$correct_module" >/dev/null; then
    echo "expected theorem not found in Debate/Correct.lean: $theorem_name" >&2
    exit 1
  fi
done
echo "theorem scan: ${EXPECTED_THEOREMS[*]} present in Debate/Correct.lean"

# Strict-trust gate: no incomplete proofs or trusted-base shortcuts in sources.
forbidden_matches=$(
  rg -n --glob '*.lean' \
    -e '\bsorry\b' \
    -e '\badmit\b' \
    -e '\baxiom\b' \
    -e 'sorryAx' \
    -e 'native_decide' \
    -e 'implemented_by' \
    -e '@\[extern' \
    "$upstream_directory" || true
)
if [[ -n "$forbidden_matches" ]]; then
  echo "forbidden trusted-base or incomplete-proof tokens found:" >&2
  echo "$forbidden_matches" >&2
  exit 1
fi
echo "trust scan: no forbidden tokens in $(find "$upstream_directory" -name '*.lean' | wc -l) Lean sources"

(
  cd "$upstream_directory"
  lake exe cache get || true
  lake build "${TARGETS[@]}"
)

echo "debate reproduction ok: ${TARGETS[*]}"
