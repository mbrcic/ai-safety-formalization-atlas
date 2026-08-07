# Contributing

Welcome — and thank you. **There is always something useful to do.** You do not
need to be a Lean expert or a survey specialist. Docs, leads, examples, reviews,
and agent-assisted proofs all count.

**Coding agents are supported here.** Draft Lean against a facade, then run the
full Lean loop below. A red build is cheap feedback; a merged primitive is shared
capital. The survey’s 44 rows are a **seed map**, not the only menu — domain
work, landscape entries, and new questions all move the workbench forward.

## Start here — pick any track

### A. No Lean required (today)

| Track | What you do |
|---|---|
| **Lead** | Point at an existing formalization or a missing target (CT-11, CT-14) |
| **Source check** | Verify a citation / DOI against the paper (CT-12) |
| **Docs / UX** | Fix a docstring, primary-surface table, or example path |
| **Issue** | File a clear gap: missing consumer, unclear non-claim, broken link |

### B. Lean with an agent (recommended default)

| Track | What you do |
|---|---|
| **Toolchain** | One use-site in `FirstContribution.lean` (CT-13) — prove CI works |
| **Consumer** | Nontrivial facade use-site (see bar below; pattern: `WorkbenchConsumers.lean`) |
| **Core / RELATED** | Formalize a useful specialization or boundary; grade honestly |
| **New domain claim** | State a precise AI-safety (or computable governance/ethics) claim and prove it against existing primitives |

### C. Classical rungs (still valid)

1. **Pointer** → candidate lead  
2. **Reproduction** → landscape or registry after build  
3. **Bridge** → scoped AI interpretation (human review)  
4. **New proof** → Lean against a public facade  

Live bounded units: [**Open now**](docs/guide/contributor-tasks.md#open-now).

## Agent / Lean verification loop

For Lean changes (agent-drafted or hand-written):

```console
lake build
xargs lake build < scripts/lean_build_targets.txt   # every Lean PR
./scripts/agent_gate.sh
python3 scripts/check_print_axioms.py
```

`agent_gate.sh` is cheap only (schema, views, paths — no `lake build`). Always
pair it with a real build and the axiom check when theorems change.

**A green build establishes kernel validity** of the encoded statement under the
strict-trust policy. It does **not** establish source alignment, model adequacy,
non-vacuous assumptions, usefulness, or a valid AI-system interpretation — those
remain review questions (registry notes, bridge packages, human review).

**Nonvacuity is claim-relative.** A model presented as satisfiable or applicable
ships an inhabitant (e.g. `Examples/SixTargets.lean`); label the limitation if
the witness is degenerate, or record that satisfiability is unestablished. For a
negative theorem of the form `A → ¬ Nonempty T`, demonstrate that its assumptions
`A` and ambient setting are realizable or nontrivial—the forbidden target `T`
need not be inhabited. Pure parameter records used only under binders need no
instance until a positive applicability claim or named consumer requires one.

**Retained consumers** (not one-off CT-13) need at least one of: cross-surface
composition, meaningful instantiated model, use-site boundary, or downstream
theorem. `WorkbenchConsumers.lean` is the bar; trivial restatements stay out.

## Where does it go?

- **Survey Table-1**, statement matches the paper → `registry.yaml`
  (`EXACT` / `EQUIVALENT`)
- **Substantively related to a specific survey row**, but not full match →
  `registry.yaml` as `RELATED`, with a **written scope delta** (what matches,
  what does not). An entry without that delta is not mergeable.
- **Adjacent or independent formal capital** (no load-bearing survey attachment)
  → `registry.yaml`
- **Internal helper with a named in-tree consumer** → Lean only (no forced
  registry row)
- **Found but not reproduced** → `candidate_formalizations`
- **AI-system interpretation** → bridge package + `ai_bridge_status` (human review)

Do not attach arbitrary useful theorems to a survey row just to land somewhere.
Detail on grades: [methodology](docs/guide/methodology.md).

## Before you open a pull request

For anything that changes formalization coverage, dependencies, or the public
Lean API, open a formalization proposal issue first — it saves you rework. Small
factual corrections and documentation fixes can go straight to a pull request.

A few things we keep, and why:

- reuse a maintained theorem before writing another proof — less to maintain,
  more to build on;
- one canonical atlas declaration per result — a name others can import from a
  public facade;
- justify a second representation or proof by its unique downstream value;
- keep mathematical theorems separate from claims about AI systems; and
- treat search hits as leads, not verified formalizations.

The [roadmap](ROADMAP.md), [methodology](docs/guide/methodology.md), and
[public API and parsimony policy](AGENTS.md) have the full detail when you want
it.

## Development setup

One command provisions everything and is idempotent — from the repository root:

```console
scripts/setup.sh            # installs elan if missing, fetches Mathlib, builds, validates
scripts/setup.sh --pointer  # docs/registry-only work: skips the Lean toolchain
```

It installs Lean via [`elan`](https://lean-lang.org/install/manual/) when `lake`
is missing, pins its toolchain, Mathlib revision, and all transitive
dependencies from [`lake-manifest.json`](lake-manifest.json), then runs
`lake build`, the explicit `scripts/lean_build_targets.txt`, and the cheap
validators (`scripts/agent_gate.sh`). Zero local install: open the repo in
GitHub Codespaces or any [Dev Container](.devcontainer/devcontainer.json).

Build from the committed manifest; do not run `lake update` unless you are
deliberately bumping a dependency (it re-resolves floating revisions off the
pinned set and can break the Lean 4.31 build).

Every proof here checks all the way to the Lean kernel — that's what lets you
build on someone else's result without re-reading the proof text. Lean changes
compile under the strict-trust policy: no `sorry`, `admit`, new axioms, direct
`sorryAx`, `native_decide`, or `@[implemented_by]`. Public surface axioms are
audited with `python3 scripts/check_print_axioms.py`. Every Lean module stays
reachable from the public root or listed in `scripts/lean_build_targets.txt`,
which CI consumes directly. A documentation- or registry-only change still needs
the cheap validators green — `scripts/agent_gate.sh` runs them (schema, generated
views, path checks). Run `scripts/generate_registry_views.py` without `--check`
after changing registry data. `scripts/audit_release_v0_1.py` is historical and
is not an ordinary development gate.

## Evidence and registry changes

A verified external formalization record needs an immutable version, exact
module or file, declaration name, relationship to the surveyed statement,
license, and reproduction status. Same-repository records use `IN_TREE`,
meaning the source in the same immutable checkout or release tag as the
registry. Prefer primary sources. Statement-match coverage (`EXACT`/`EQUIVALENT`)
comes from a reproduced proof, not a paper title or keyword match. `RELATED`
requires a written scope delta against the named survey statement; landscape
capital is adjacent work without that attachment. Neither raises the
statement-match grade.

A discovered-but-unaccepted formalization belongs in a result's
`candidate_formalizations` list, not in `formalizations`. A candidate lead
records repository, revision, framework, license, declaration,
`inspection_state`, `relationship_review`, and notes, and never changes headline
coverage. Promote it to a `formalizations` record only after reproduction and
statement-level classification.

Formalizations that are **not** Table-1 survey coverage (adjacent landscape)
belong in `registry.yaml`, not in `registry.yaml` coverage
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
