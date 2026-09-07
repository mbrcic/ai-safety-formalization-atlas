# What verification runs where, and why

**What this file is.** A record of how CI verification is scheduled, and of the
reasoning behind it. Every check here could in principle run on every pull
request. Some take seconds; two take between five minutes and half an hour, and
those two are gated. This file gives the trigger for each and the coverage each
gating forgoes, so that a deliberate budget can be told apart from an oversight
and so that revisiting one of these decisions means engaging with a stated
reason.

It is not an inventory of checks.
[`workflow-validation.md`](../agent/policy/workflow-validation.md) covers what to
run before a commit; this covers what CI runs, and when.

## The rule

**A check runs at the frequency of the cause it detects, not at the frequency of
the files it reads.**

A file-extension trigger is the natural first choice, and it misallocates cost.
A check wired to "any `.lean` file changed" runs most often on the pull requests
least able to trigger it, while the event that genuinely produces its failure —
a moved pin, a rebuilt dependency — gets no additional attention. Matching the
trigger to the cause corrects both halves at once.

Two properties follow.

**Throughput.** An ordinary pull request should complete in minutes. The
30-minute budget on the `lean` job is a ceiling rather than a target, and a
single 342-second step consumes a fifth of it.

**Contained risk, rather than no risk.** Gating a check does not prevent the
failure it looks for. What it does is bound the time such a failure can go
unnoticed, and each gating below states that bound explicitly. A gating with no
stated bound would amount to dropping the check, and neither of the two here
does that.

## The ladder

Measured figures, not estimates. Times vary by runner; the ratios do not.

| Check | Cost | Runs on | Cause it detects |
|---|---|---|---|
| `agent_gate.sh` (schema, views, paths, shape suite) | seconds | **everything**, unfiltered | a ledger, view or path that no longer matches the tree |
| `check_elaboration_drift.py --classify` (inside the cheap gate) | ~1 s, no toolchain | **everything** | a substitution class widened or a committed dump edited |
| no-op `lake build` | ~4 s | any Lean-touching change | a broken tree |
| `check_print_axioms.py`, `axiom-audit` | ~40 s | any Lean-touching change | a declaration that stopped being proved |
| elaboration adjudication anchors (`.lean`) | ~4 s | any Lean-touching change | a later toolchain breaking an equality a recorded verdict rests on |
| `report_consumers.py` | ~2 s | any Lean-touching change | a stale reuse report |
| **`check_elaboration_drift.py --dump` + `--compare --fatal silent`** | **342 s, 2.2 GB** | **migration, both schedules, release tags, manual** | a declaration whose printed type is unchanged and whose *elaborated* type moved |
| **`leanchecker` kernel replay** | **1961 s over 239 modules** | **nightly cron, release tags, manual** | an environment built by metaprogramming rather than by proving |

The two bold rows are the gated ones. Everything above them is cheap enough that
gating would cost more in reasoning than it saves in runtime.

Runner and budget follow the same split: workflow dispatch, release tags and the
nightly `15 3 * * *` cron get the self-hosted `leanchecker` runner and a
75-minute budget; everything else gets `ubuntu-latest` and 30 minutes. The
weekly `0 6 * * 1` cron is an ordinary hosted run.

## The decision this file was written for

### `check_elaboration_drift` — dump and compare

| | |
|---|---|
| **Initial** | `if: steps.filter.outputs.run_lean == 'true'` — every pull request that touched a `.lean` file, a `lakefile`, a manifest, or one of several scripts. |
| **Final** | Toolchain migrations, both schedules, release tags, and `workflow_dispatch`. Migration is decided from the diff: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, or a baseline dump moved. |
| **Reason** | The check was **built for a migration**. It exists because on a toolchain bump the dangerous change is the one where the source does not move — an upstream rename behind an alias, a different instance chosen, a definition made reducible — and every other check here reads source. Its cost matches that origin: it elaborates the whole environment, 342 s and 2.2 GB on an idle 12-core host against an already-built tree, slower on a two-core hosted runner. That made it the largest single step on an ordinary pull request, and it was triggered by a file extension rather than by the event it was built for. |
| **Check** | `python3 -c "import yaml; yaml.safe_load(open('.github/workflows/ci.yml'))"` parses; the step's `if:` names `run_migration`, `schedule`, `workflow_dispatch` and `refs/tags/v`. |

**Why `lakefile.toml` is in the migration pattern on its own account.** The
manifest records resolved revisions, so a `rev` change reaches it. `leanOptions`
— `autoImplicit`, `pp.*`, `maxHeartbeats` — do not: they change elaboration with
no manifest movement at all. A pattern that trusted the manifest alone would
gate out the one edit in that file most likely to move an elaborated type.

**What the change forgoes.** Silent drift arises predominantly from the
environment moving beneath unchanged source, and every cause of that kind
remains gated. An ordinary pull request can nonetheless produce it: adding a
typeclass instance alters resolution for declarations nobody edited, as can a
new attribute, a notation, or a change to a definition's implicit arguments. In
each case the printed type is unchanged while the elaborated type is not.

Those cases now surface on the nightly run rather than blocking the pull request
that introduced them, which puts **the detection window at one day**. No such
case has been observed here, and 342 s on every Lean-touching pull request is a
certain cost weighed against an uncertain one.

**What would overturn this.** If the nightly run begins reporting silent changes
traceable to a pull request, rather than to a toolchain or dependency movement,
the balance assumed here does not hold and the step should return to running on
every Lean pull request. That is the observation worth watching, and the one
that should settle the question.

### `leanchecker` — the same decision, taken earlier

Gated to the nightly cron, release tags and manual runs since before this file
existed, for the same reason and with the same shape of window. Its own comment
carries the argument that release tags alone would leave it effectively unrun,
which is why the nightly cron is what keeps it honest. The elaboration-drift
gating above deliberately mirrors it, with `run_migration` added because that is
the event the drift check answers to and the kernel replay does not.

## Applying this to a future check

Two gated checks, two stated windows, one rule.

**Adding an expensive check.** Identify the cause it detects and gate on that.
If no cause can be named more precisely than "the tree changed", the check is
either cheap enough for the standard gate or does not belong in CI at all.

**Removing a gating.** State which window closes as a result, and what the check
costs on every pull request. Both numbers belong in the change that makes it, so
that the next reader can weigh the same trade this file weighed.
