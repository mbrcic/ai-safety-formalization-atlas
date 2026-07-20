#!/usr/bin/env bash
# Reproduce the pinned google-deepmind/debate Lean development used as external
# landscape evidence LAND-DEBATE-001 (doubly-efficient debate correctness,
# Brown-Cohen–Irving–Piliouras 2023, arXiv 2311.14125, paper Theorem 6.2).
#
# Path A: build at the UPSTREAM toolchain (Lean/Mathlib v4.8.0) from a separate
# checkout. Upstream is NOT vendored into the atlas 4.31 tree and carries no
# atlas Lean import surface — this is reproduction evidence, not coverage.
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
