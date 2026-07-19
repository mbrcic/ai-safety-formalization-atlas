#!/usr/bin/env bash
set -euo pipefail

readonly VNM_REPOSITORY="https://github.com/jingyuanli-hk/vNM-Theorem-pub.git"
readonly VNM_COMMIT="89ed1680170bcf947f77bd26cdf614c1ce02222c"
readonly MATHLIB_COMMIT="fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
readonly LEAN_TOOLCHAIN="leanprover/lean4:v4.31.0"

for command_name in git lake; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "required command not found: $command_name" >&2
    exit 127
  fi
done

work_directory=$(mktemp -d "${TMPDIR:-/tmp}/atlas-vnm-XXXXXX")
trap 'rm -rf -- "$work_directory"' EXIT

upstream_directory="$work_directory/upstream"
reproduction_directory="$work_directory/reproduction"

git init --quiet "$upstream_directory"
git -C "$upstream_directory" remote add origin "$VNM_REPOSITORY"
git -C "$upstream_directory" fetch --quiet --depth 1 origin "$VNM_COMMIT"
git -C "$upstream_directory" checkout --quiet --detach FETCH_HEAD

actual_commit=$(git -C "$upstream_directory" rev-parse HEAD)
if [[ "$actual_commit" != "$VNM_COMMIT" ]]; then
  echo "unexpected vNM revision: $actual_commit" >&2
  exit 1
fi

mkdir -p "$reproduction_directory/vNM01"
cp "$upstream_directory"/{Core,MixLemmas,Tactics,Claims,Theorem,Unique}.lean \
  "$reproduction_directory/vNM01/"

printf '%s\n' "$LEAN_TOOLCHAIN" > "$reproduction_directory/lean-toolchain"
printf '%s\n' \
  'name = "vnm-reproduction"' \
  'version = "0.0.0"' \
  'defaultTargets = ["vNM01.Unique"]' \
  '' \
  '[[require]]' \
  'name = "mathlib"' \
  "git = \"https://github.com/leanprover-community/mathlib4.git\"" \
  "rev = \"$MATHLIB_COMMIT\"" \
  '' \
  '[[lean_lib]]' \
  'name = "vNM01"' \
  > "$reproduction_directory/lakefile.toml"

(
  cd "$reproduction_directory"
  lake update
  lake exe cache get
)

(
  cd "$reproduction_directory"
  lake build vNM01.Unique
)
