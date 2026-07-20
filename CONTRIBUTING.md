# Contributing

Welcome — and thank you. If you can state what "safe" should mean, there's a
place for you here. You don't need to be a Lean expert or a published
researcher; you need a question and a willingness to make it precise.

## Start here — pick your rung

Lowest step that fits. Every one moves the atlas forward:

1. **Pointer** — found a theorem that might match a survey row? Add a candidate
   lead in that row's `candidate_formalizations`. No Lean, no proof, no risk —
   just a source and a note.
2. **Reproduction** — you have a proof in another system (Isabelle, Coq, Agda)?
   Bring it into the landscape lane. Cross-system results are first-class here.
3. **Bridge** — say what a theorem does, and does not, establish about an AI
   system.
4. **New proof** — formalize a result in Lean against the stable facade.

Impossibility or possibility both belong: a bound, a guarantee, a tradeoff, or
a limit. The seed leans toward impossibility results, but the infrastructure
doesn't — continuous free lunches (BY-022) is a possibility row waiting to be
formalized.

Ready to start? [**Open now**](docs/guide/contributor-tasks.md#open-now) lists
live bounded units across the rungs — with goal, acceptance evidence, and scope.

## Where does it go?

- Reproduced **Table-1 survey** result, `EXACT`/`EQUIVALENT` → `registry.yaml`
  coverage (counts toward the headline).
- Reproduced result **adjacent** to the survey (any prover) → `landscape.yaml`
  (real and credited, never a headline count).
- **Found but not yet reproduced** → the row's `candidate_formalizations`
  (a lead, promoted once reproduced).
- A claim about an **AI system** → a bridge, kept separate from the math and
  marked for human review.

`RELATED` isn't a demotion — it's how we credit a partial or adjacent match
honestly, without overclaiming an exact fit.

## Before you open a pull request

For anything that changes formalization coverage, dependencies, or the public
Lean API, open a formalization proposal issue first — it saves you rework. Small
factual corrections and documentation fixes can go straight to a pull request.

A few things we keep, and why:

- reuse a maintained theorem before writing another proof — less to maintain,
  more to build on;
- one canonical atlas declaration per result — a stable name others can import;
- justify a second representation or proof by its unique downstream value;
- keep mathematical theorems separate from claims about AI systems; and
- treat search hits as leads, not verified formalizations.

The [roadmap](ROADMAP.md), [methodology](docs/guide/methodology.md), and
[public API and parsimony policy](AGENTS.md) have the full detail when you want
it.

## Development setup

Install Lean with [`elan`](https://lean-lang.org/install/manual/). The repository
pins its Lean toolchain, Mathlib revision, and all transitive dependencies in
[`lake-manifest.json`](lake-manifest.json). From the repository root, run:

```console
lake exe cache get   # fetch prebuilt Mathlib — skips an hours-long local compile
lake build
xargs lake build < scripts/lean_build_targets.txt
python3 scripts/validate_registry.py
python3 scripts/generate_registry_views.py --check
python3 scripts/validate_current_state.py
```

Build from the committed manifest; do not run `lake update` unless you are
deliberately bumping a dependency (it re-resolves floating revisions off the
pinned set and can break the Lean 4.31 build).

Every proof here checks all the way to the Lean kernel — that's what lets you
build on someone else's result without re-reading it. So Lean changes compile
under the strict-trust policy: no `sorry`, `admit`, new axioms, direct
`sorryAx`, `native_decide`, or `@[implemented_by]`. Every Lean module stays
reachable from the public root or listed in `scripts/lean_build_targets.txt`,
which CI consumes directly. If a change only affects documentation or registry
evidence, still run all three current-state Python checks. Run `scripts/generate_registry_views.py` without
`--check` after changing registry data. `scripts/audit_release_v0_1.py` is
historical and is not an ordinary development gate.

## Evidence and registry changes

A verified external formalization record needs an immutable version, exact
module or file, declaration name, relationship to the surveyed statement,
license, and reproduction status. Same-repository records use `IN_TREE`,
meaning the source in the same immutable checkout or release tag as the
registry. Prefer primary sources. Coverage comes from a reproduced proof, not a
paper title, repository description, or keyword match — only reproduced `EXACT`
and `EQUIVALENT` records increase the headline count.

A discovered-but-unaccepted formalization belongs in a result's
`candidate_formalizations` list, not in `formalizations`. A candidate lead
records repository, revision, framework, license, declaration,
`inspection_state`, `relationship_review`, and notes, and never changes headline
coverage. Promote it to a `formalizations` record only after reproduction and
statement-level classification.

Formalizations that are **not** Table-1 survey coverage (adjacent landscape)
belong in [`landscape.yaml`](landscape.yaml), not in `registry.yaml` coverage
counts. Public Lean landscape theorems on the root import must set
`root_import: true` and keep `survey_coverage: null`. Regenerate views with
`python3 scripts/generate_registry_views.py` (includes the landscape index and
the `STATE.md` registry snapshot).

`docs/provenance/formalization-search.json` is generated evidence. When search terms or
pinned corpora change, regenerate it with
`scripts/update_formalization_search.py`; do not hand-edit its results. Keep
`registry.yaml`, the generated evidence, and the status documentation
synchronized.

## Lean and public API changes

Use conventional theorem names and the namespace pattern documented in
[`AGENTS.md`](AGENTS.md). A pull request that changes the public facade should
show the intended downstream import and theorem use. Vendored or adapted source
must retain its license, immutable upstream revision, attribution, and a clear
list of atlas modifications.

For an AI-safety bridge, state the modeled system, assumptions, quantifier
order, mathematical conclusion, and the practical claim it does not establish.
Bridge interpretation remains subject to separate human review, tracked by the
`ai_bridge_status` lifecycle: `HUMAN_REVIEW` (default), `STATEMENT_REVIEWED`
(the encoded statement accepted, interpretation not), and `REVIEWED` (both
accepted). Graduating a bridge past `HUMAN_REVIEW` requires a `bridge_review`
record (reviewer, date, the two review flags, and an evidence pointer); ordinary
validation accepts a well-formed graduation, so recording a real review does not
require editing a validator.

## Pull requests

Create a focused branch and submit a pull request to `main`. Keep unrelated
changes out of the branch. The pull request should explain:

1. the exact gap addressed;
2. existing formalizations and dependencies checked;
3. the unique capability added;
4. public API and registry effects; and
5. any interpretation requiring domain review.

CI must pass before merge. Maintainers use squash merging so `main` retains one
coherent commit per accepted contribution. Force-pushes and direct changes to
`main` are not part of the normal contributor workflow.

By contributing, you agree that your contribution is licensed under the
repository's Apache-2.0 license.
