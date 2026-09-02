#!/usr/bin/env bash
# Independent kernel re-verification of the atlas's own modules.
#
# `leanchecker` replays declarations through the kernel and asks whether they
# typecheck at all -- the failure mode `#print axioms` cannot see, because an
# environment built by metaprogramming reports whatever axioms it likes.
#
# One process per module. Cost tracks the module's *import closure*, not the
# module itself: the six-declaration facade `AISafetyAtlas.Oversight.Debate`
# costs 2.6 GB because it imports the vendored development, so batching modules
# pays the union of their closures. Passing all 255 in one process is
# OOM-killed, as is every 24-module chunk. The peak reached is printed when this
# script finishes; size the host from that number, not from this comment.
#
# Pure aggregators -- modules that declare nothing and only re-export -- are
# skipped. Their closures are the largest in the tree (the root imports 76
# modules and declares nothing) and they carry no declaration that the modules
# actually declaring it do not already cover.
#
# The aggregator set is recomputed on each run by querying the elaborated
# environment. Do not replace this with a scan of the sources for declaration
# keywords: macros such as `declare_aesop_rule_sets` emit declarations with no
# keyword to match, so a declaring module is silently dropped from the replay
# and loses its coverage, while keywords in comment prose cause aggregators to
# be replayed at their full closure cost. Stripping comments first fixes only
# the second and worsens the first.
set -euo pipefail
export LC_ALL=C

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# GNU time, not the bash `time` keyword: only the former reports peak RSS, which
# is the number this script exists to publish. It is not installed by default on
# every host -- a self-hosted runner is the likely one to be missing it -- so it
# is probed once here rather than discovered inside the loop. Without the probe a
# missing binary surfaces as `FAIL <first module> (exit 127)`, which reads as a
# broken proof and sends the reader to the wrong place entirely.
TIME_BIN="${ATLAS_TIME_BIN:-/usr/bin/time}"
if ! "$TIME_BIN" -f '%M %e' true >/dev/null 2>&1; then
  echo "GNU time not usable at '$TIME_BIN' (needs -f support)." >&2
  echo "Install it (Debian/Ubuntu: apt-get install time) or set ATLAS_TIME_BIN." >&2
  exit 1
fi

# A module is ours when it has both a compiled artifact and a source. Scoping to
# .lake/build/lib/lean/AISafetyAtlas is not enough on its own: lake does not
# prune build output for a source that no longer exists, so an orphan left by a
# rename survives *inside* that scope and fails to load with "incompatible
# header", which reads as a broken tree rather than as the stale artifact it is.
# A restored build cache is where these come from. Requiring the artifact keeps
# a .lean outside every target from becoming an import error; requiring the
# source drops the orphans.
mapfile -t modules < <(
  {
    [ -f .lake/build/lib/lean/AISafetyAtlas.olean ] && echo AISafetyAtlas.lean
    find .lake/build/lib/lean/AISafetyAtlas -name '*.olean' -printf 'AISafetyAtlas/%P\n' 2>/dev/null \
      | sed 's|\.olean$|.lean|'
  } | while read -r source; do
      [ -f "$source" ] && printf '%s\n' "${source%.lean}" | tr '/' '.'
    done | sort
)

# Modules that contribute no constant to the elaborated environment.
#
# Imports are the root plus scripts/lean_build_targets.txt: the atlas root does
# not transitively import the whole library, and that file is what reaches the
# off-root modules (`generate_declaration_index.py` builds its harness the same
# way). Every constant counts, including internal and auxiliary ones that the
# declaration index filters out -- the question is whether the module put
# anything in the environment, not whether it is public surface.
aggregator_query="$(mktemp -t atlas-aggregators-XXXXXX.lean)"
time_file="$(mktemp -t atlas-replay-time-XXXXXX)"
trap 'rm -f "$aggregator_query" "$time_file"' EXIT
{
  echo 'import AISafetyAtlas'
  awk 'NF && $1 !~ /^#/ { print "import " $1 }' scripts/lean_build_targets.txt
  echo 'import Lean'
  cat <<'LEANEOF'

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut declaring : NameSet := {}
  for (n, _) in env.constants.toList do
    match env.getModuleFor? n with
    | some m => declaring := declaring.insert m
    | none   => pure ()
  IO.println "ATLAS-AGG-BEGIN"
  for m in env.header.moduleNames do
    if (`AISafetyAtlas).isPrefixOf m && !(declaring.contains m) then
      IO.println m
  IO.println "ATLAS-AGG-END"
LEANEOF
} >"$aggregator_query"

# Fail closed. A query that errors, or that returns output without both markers,
# says nothing about which modules are safe to skip; guessing would leave a
# module unverified while this script reports success.
if ! aggregator_out="$(lake env lean "$aggregator_query" 2>&1)"; then
  echo "Aggregator query failed; refusing to guess which modules declare nothing." >&2
  printf '%s\n' "$aggregator_out" | awk 'NR <= 30' >&2
  exit 1
fi
case $aggregator_out in
  *ATLAS-AGG-BEGIN*ATLAS-AGG-END*) ;;
  *)
    echo "Aggregator query produced no marked output; refusing to skip anything." >&2
    printf '%s\n' "$aggregator_out" | awk 'NR <= 30' >&2
    exit 1
    ;;
esac
mapfile -t aggregators < <(
  printf '%s\n' "$aggregator_out" |
    awk '/^ATLAS-AGG-BEGIN$/ { on = 1; next } /^ATLAS-AGG-END$/ { on = 0 } on'
)
is_aggregator() {
  local candidate=$1 name
  for name in "${aggregators[@]}"; do
    [ "$name" = "$candidate" ] && return 0
  done
  return 1
}
if [ "${#modules[@]}" -eq 0 ]; then
  echo "No atlas oleans found — the build step did not produce them." >&2
  exit 1
fi

# Fixed up front so the progress denominator does not shrink as modules skip.
to_replay=0
for module in "${modules[@]}"; do
  is_aggregator "$module" || to_replay=$((to_replay + 1))
done

replayed=0
skipped=0
failed=0
peak_kb=0
started=$SECONDS

for module in "${modules[@]}"; do
  if is_aggregator "$module"; then
    skipped=$((skipped + 1))
    continue
  fi
  # `-o`: a module whose last write lacks a newline would otherwise have time's
  # line appended to it, and the peak would silently read 0. Non-zero exits
  # prepend a "Command exited..." note, hence the last line.
  measurement=$("$TIME_BIN" -f '%M %e' -o "$time_file" \
    lake env leanchecker "$module" 2>&1) && status=0 || status=$?
  stats=$(tail -1 "$time_file")
  module_kb=$(awk '{print $1+0}' <<<"$stats")
  if [ "$status" -ne 0 ]; then
    failed=$((failed + 1))
    echo "FAIL $module (exit $status)" >&2
    # `awk`, not `head`: under `pipefail` a `head` that closes the pipe early
    # SIGPIPEs the writer, replacing the failure report with a pipe error.
    printf '%s\n' "$measurement" | awk 'NR <= 30' >&2
    break
  fi
  [ "$module_kb" -gt "$peak_kb" ] && peak_kb=$module_kb
  replayed=$((replayed + 1))
  if [ $((replayed % 25)) -eq 0 ]; then
    echo "  ... $replayed/$to_replay replayed, peak so far $((peak_kb / 1024)) MB"
  fi
done

elapsed=$((SECONDS - started))
if [ "$failed" -ne 0 ]; then
  echo "kernel replay FAILED after $replayed module(s) in ${elapsed}s" >&2
  exit 1
fi
echo "kernel replay ok: $replayed modules re-verified through the kernel," \
     "$skipped pure aggregators skipped, peak $((peak_kb / 1024)) MB, ${elapsed}s"
