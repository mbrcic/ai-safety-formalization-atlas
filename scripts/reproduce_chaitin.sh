#!/usr/bin/env bash
# Reproduce the pinned KolmogorovMathlib Chaitin incompleteness development
# used as external formalization evidence for survey row BY-015.
set -euo pipefail

readonly CHAITIN_REPOSITORY="https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean.git"
readonly CHAITIN_COMMIT="005ac4c81eefe09642ef561057199d489cd79485"
readonly TARGETS=(
  "KolmogorovMathlib.Complexity.Chaitin"
  "KolmogorovMathlib.Complexity.ChaitinCorollaries"
)

for command_name in git lake rg; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "required command not found: $command_name" >&2
    exit 127
  fi
done

work_directory=$(mktemp -d "${TMPDIR:-/tmp}/atlas-chaitin-XXXXXX")
trap 'rm -rf -- "$work_directory"' EXIT

upstream_directory="$work_directory/upstream"

git init --quiet "$upstream_directory"
git -C "$upstream_directory" remote add origin "$CHAITIN_REPOSITORY"
git -C "$upstream_directory" fetch --quiet --depth 1 origin "$CHAITIN_COMMIT"
git -C "$upstream_directory" checkout --quiet --detach FETCH_HEAD

actual_commit=$(git -C "$upstream_directory" rev-parse HEAD)
if [[ "$actual_commit" != "$CHAITIN_COMMIT" ]]; then
  echo "unexpected Chaitin revision: $actual_commit" >&2
  exit 1
fi

echo "reproducing $CHAITIN_REPOSITORY @ $CHAITIN_COMMIT"
echo "toolchain: $(cat "$upstream_directory/lean-toolchain")"

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
  lake update
  lake exe cache get || true
  lake build "${TARGETS[@]}"
)

echo "chaitin reproduction ok: ${TARGETS[*]}"
