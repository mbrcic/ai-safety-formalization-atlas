#!/usr/bin/env bash
# Independent kernel re-verification of the atlas's own modules.
#
# Each module's declarations are replayed through the kernel against the
# environment its imports give, which asks whether they typecheck at all -- the
# failure mode `#print axioms` cannot see, because an environment built by
# metaprogramming reports whatever axioms it likes.
#
# The replay is scripts/kernel_replay.lean, not `leanchecker`, and the reason is
# cost. `leanchecker M` replays every module whose name starts with M, all in
# one process, so a per-module loop replayed each parent module's whole subtree
# again on the parent's turn: 918 module-replays for 612 modules, a peak near
# 18 GB from the parents with fifty-odd children, and a nightly run that
# outgrew its 75-minute budget (2026-10-07 to 2026-10-12). The Lean file runs
# the toolchain's own `replayFromImports` on exactly one module; this script
# checks that copy against the installed toolchain first and refuses to run if
# they differ.
#
# One process per module, run in parallel. Cost tracks the module's *import
# closure*, not the module itself, and closures differ per module, so modules
# cannot share one import. ATLAS_REPLAY_JOBS sets the parallelism; by default it
# is sized from the host's available memory at ATLAS_REPLAY_GB_PER_JOB each,
# capped at the core count. The peak per module is printed when this script
# finishes; size the budget from that number, not from this comment.
#
# Pure aggregators -- modules that declare nothing and only re-export -- are
# skipped. The Lean file reads the module's own constants from its olean before
# importing anything, so an aggregator costs a file read rather than its import
# closure (the root's is the largest in the tree). This is the same set the
# elaborated environment would give: a module is an aggregator exactly when no
# constant in it belongs to it.
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

# The replay must be the toolchain's. Fail closed when the copied function no
# longer matches the installed LeanChecker.lean, or when that file cannot be
# found: re-copy it from the toolchain, re-measure, and only then run again.
replay_lean=scripts/kernel_replay.lean
upstream="$(lake env lean --print-prefix)/src/lean/LeanChecker.lean"
if [ ! -f "$upstream" ]; then
  echo "Toolchain source $upstream not found; cannot confirm the replay is the toolchain's." >&2
  exit 1
fi
ours=$(awk '/^-- BEGIN verbatim replayFromImports$/ { on = 1; next }
            /^-- END verbatim replayFromImports$/ { on = 0 } on' "$replay_lean")
theirs=$(awk '/^unsafe def replayFromImports / { on = 1 }
              on && /^$/ { exit } on' "$upstream")
if [ -z "$ours" ] || [ "$ours" != "$theirs" ]; then
  echo "$replay_lean: replayFromImports differs from $upstream." >&2
  diff <(printf '%s\n' "$theirs") <(printf '%s\n' "$ours") | awk 'NR <= 40' >&2 || true
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
if [ "${#modules[@]}" -eq 0 ]; then
  echo "No atlas oleans found — the build step did not produce them." >&2
  exit 1
fi

cores=$(nproc)
if [ -n "${ATLAS_REPLAY_JOBS:-}" ]; then
  jobs=$ATLAS_REPLAY_JOBS
else
  avail_gb=$(awk '/^MemAvailable:/ { print int($2 / 1048576) }' /proc/meminfo)
  jobs=$(( avail_gb / ${ATLAS_REPLAY_GB_PER_JOB:-6} ))
  [ "$jobs" -gt "$cores" ] && jobs=$cores
  [ "$jobs" -lt 1 ] && jobs=1
fi

work="$(mktemp -d -t atlas-replay-XXXXXX)"
trap 'rm -rf "$work"' EXIT

# One line per module in $work/results: `<status> <module> <peak KB> <seconds>`.
# A failing module also leaves its output in $work/<module>.log. `-o` keeps
# time's line out of the module's own output; on a non-zero exit time prepends a
# "Command exited..." note, hence the last line.
replay_one() {
  local module=$1 status=0 out
  out=$("$TIME_BIN" -f '%M %e' -o "$work/$module.time" \
    lean --run "$replay_lean" "$module" 2>&1) || status=$?
  local stats
  stats=$(tail -1 "$work/$module.time")
  if [ "$status" -ne 0 ]; then
    printf '%s\n' "$out" >"$work/$module.log"
    echo "FAIL $module $stats exit=$status" >>"$work/results"
  elif [[ $out == "skip $module" ]]; then
    echo "SKIP $module $stats" >>"$work/results"
  elif [[ $out == "ok $module "* ]]; then
    echo "OK $module $stats" >>"$work/results"
  else
    printf '%s\n' "$out" >"$work/$module.log"
    echo "FAIL $module $stats unmarked-output" >>"$work/results"
  fi
}
export -f replay_one
export TIME_BIN work replay_lean

echo "kernel replay: ${#modules[@]} modules"
started=$SECONDS
# `lake env` once, around the whole pool, never per module: while anything
# reconfigures the package, every concurrent `lake env` exits 1 with "could not
# acquire an exclusive configuration lock". Observed once, 3 of 612 modules in
# the first parallel trial, when another lake touched the package mid-run; each
# would have read as a failed proof.
printf '%s\n' "${modules[@]}" |
  lake env xargs -r -P "$jobs" -I{} bash -c 'replay_one "$1"' _ {} || true
elapsed=$((SECONDS - started))

# Fail closed: every module must have exactly one OK or SKIP line. A worker
# killed before it wrote its line (the OOM killer takes the whole bash -c) is a
# missing line, and a missing line is a failure, not a pass.
touch "$work/results"
replayed=$(awk '$1 == "OK"' "$work/results" | wc -l)
skipped=$(awk '$1 == "SKIP"' "$work/results" | wc -l)
failed=$(awk '$1 == "FAIL"' "$work/results" | wc -l)
missing=$(( ${#modules[@]} - replayed - skipped - failed ))
read -r peak_kb peak_module < <(
  awk '$1 == "OK" && $3 + 0 > m { m = $3 + 0; w = $2 } END { print m + 0, w }' "$work/results"
)

if [ "$failed" -ne 0 ] || [ "$missing" -ne 0 ]; then
  awk '$1 == "FAIL"' "$work/results" >&2
  for log in "$work"/*.log; do
    [ -f "$log" ] || continue
    echo "--- ${log##*/}" >&2
    awk 'NR <= 30' "$log" >&2
  done
  echo "kernel replay FAILED: $failed failed, $missing produced no result," \
       "$replayed ok, in ${elapsed}s" >&2
  exit 1
fi
echo "kernel replay ok: $replayed modules re-verified through the kernel," \
     "$skipped pure aggregators skipped," \
     "peak $((peak_kb / 1024)) MB ($peak_module), ${elapsed}s"
