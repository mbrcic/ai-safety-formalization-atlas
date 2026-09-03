## Context budget (agents)

### Start here (small by design)

**Fastest route, and it needs no agent in particular:** make your change, then
run `python3 scripts/preflight.py`. It reads the diff, works out which kinds of
contribution it contains, and prints only the obligations and commands that
apply, each naming the section here that governs it. It restates no rule and
decides nothing — the gate does that — but it removes the step where a
contributor reads a thousand lines of policy to find the twenty that bind them.

Agents that load project skills will find the same route as
[`.agents/skills/atlas-contribution/SKILL.md`](../../../.agents/skills/atlas-contribution/SKILL.md);
it holds the order to work in and no rules, which stay here.

Open this file, `STATE.md`, and `docs/agent/INDEX.md` first. The other paths
below are conditional and should be opened only when the task needs them.

1. This file (short policy)
2. [`STATE.md`](../../../STATE.md)
3. [`docs/agent/INDEX.md`](../INDEX.md), [`by-id.json`](../by-id.json),
   and [`search-summary.json`](../search-summary.json) as needed
4. [`docs/status/landscape-index.md`](../../status/landscape-index.md) /
   [`docs/status/sources/`](../../status/sources/) if browsing coverage
5. **One facade module** under `AISafetyAtlas/*.lean` (or a small nested facade
   such as `Verification/Robot.lean`) for the task domain — not `Upstream/`
6. [`docs/guide/open-work.md`](../../guide/open-work.md) or
   [`contributor-tasks.md`](../../guide/contributor-tasks.md) when picking work

### Do not read by default

| Path | Why | When to open |
|---|---|---|
| Full [`registry.yaml`](../../../registry.yaml) | Redundant with `by-id.json` | One `BY-###`, `CLM-*`, or `LAND-*` via `rg` for notes / candidates / bridge_review |
| [`docs/provenance/formalization-search.json`](../../provenance/formalization-search.json) | Large discovery dump | Regenerating evidence or deep candidate audit |
| [`ROADMAP.md`](../../../ROADMAP.md) | Human strategy, not live tasking | Maintainer names roadmap work |
| `AISafetyAtlas/Upstream/**` | Large vendored/collapsed proofs | Editing that formalization only |
| `vendor/**` | Upstream vendor trees | Editing that vendored package only |
| `.lake/**`, `**/CLAUDE.md`, `ai_context.txt` | Build cache / tool dumps | Never as task context |
| [`docs/status/declaration-index.json`](../../status/declaration-index.json) | ~214k tokens; it is a lookup table, never a read | Resolving one name — `rg '"AISafetyAtlas\.Foo\.bar"'`, or ask the Lean LSP |
| `docs/status/*-dependency-graph.json` | Machine view of one cluster; `inference` ~58k tokens, `causal` ~41k | A tool consumes it. To *read* a cluster, open the `.md` sibling |
| [`docs/provenance/source-coverage-audit.md`](../../provenance/source-coverage-audit.md) | ~47k tokens of statement-by-statement grading | One source's section (`rg -A40 '^## 6\.'`) or one row, never the file |
| [`docs/agent/by-id.json`](../by-id.json) | ~46k tokens | One `BY-###` via `rg`, as with `registry.yaml` |
| `docs/status/elab-baseline-*.json` | ~3M tokens each; a normal-form dump, unreadable by construction | Only `--compare` / `--classify`. Never open one |
| [`docs/status/public-api.txt`](../../status/public-api.txt) | ~31k tokens | One name via `rg`; the pin is the diff, not the read |
| Accidental `https:/`, `http:/` trees | wget path debris (gitignored) | Delete if recreated |

### Lean surface rule

Prefer **facade** modules (`AISafetyAtlas/Learning.lean`, `SocialChoice.lean`,
`Logic.lean`, `Verification.lean`, `Knowledge.lean`, and small nested facades
such as `Knowledge/Embedded.lean` and `Oversight/JointObservation.lean`). Do not
open `Upstream/` or `vendor/` unless the task is to change that proof tree.

**One facade is not always the whole domain.** Parents differ in what they
re-export, so check the pattern before concluding a result is missing:

| Pattern | One import supplies | Parents |
|---|---|---|
| Aggregating facade | the domain's whole public surface | `Compositional`, `Oversight.JointObservation`, `Wireheading` |
| Partial aggregate | the mathematical base only | `Verification` (re-exports `Computability`; **not** `AgentBehavior`, **not** `Robot`) |
| Kernel and specializations | a closed surface; specializations import separately | `Knowledge.*`, `Preference.*` |

The kernels withhold their specializations by design: `Knowledge` states what it
excludes, so importing it must not drag in the embedded, temporal, or
self-referential layers. Full table with one-line domains:
[`AISafetyAtlas.lean`](../../../AISafetyAtlas.lean).

Each facade's module docstring carries a **primary surface** table; read that
before the declarations. `AISafetyAtlas.Knowledge` is the generic
observation-factorization kernel that `Oversight.JointObservation` and
`Knowledge.Embedded` both build on — reach for it before restating a
fibre/collision argument.

### Examples layout rule

`AISafetyAtlas/Examples/` holds two kinds of file:

- **Mirror** — non-vacuity or a witness for one module. Its path and namespace
  repeat that module's: `Verification/Robot.lean` is witnessed by
  `Examples/Verification/Robot.lean` in `AISafetyAtlas.Examples.Verification.Robot`.
  A mirror directory may also hold extra scenario files with no module of their
  own (`Examples/Oversight/JointObservation/Procurement.lean`).
- **Harness** — serves no single module and stays flat in `Examples/`:
  `PublicAPI`, `Registry`, `NonVacuity`, `SixTargets`, `WorkbenchConsumers`,
  `FirstContribution`, `HaltingExample`, `NFLConcrete`.

**Two namespace spellings are legal**, and the tree uses both: the full path
(`AISafetyAtlas.Examples.Verification.Robot`, 47 files) or the directory holding
it (`AISafetyAtlas.Examples.Verification`, 21 files). Either is findable from the
module being witnessed, which is what the convention is for. A namespace
agreeing with neither is not legal, and `scripts/check_examples_layout.py`
decides all of this in the cheap gate — so this section is background, not
something to check by hand. Files a script generates are skipped: they declare
nothing.

A new example for one module takes the mirror path. Renaming an existing one
also touches `scripts/lean_build_targets.txt`,
`scripts/validate_current_state.py`, any `build_command` or `application` prose
in `registry.yaml`, and the generated views — regenerate rather than hand-edit
`docs/status/`.

### Tactics and search surface

| Capability | Where | How to use it |
|---|---|---|
| SMT-flavoured automation | `grind`, with `@[grind]` / `@[grind →]` on four Layer-0 facts | `grind` alone closes goals about `not_stronglyInfers_self`, `not_weaklyInfers_own_concl`, `weaklyInfers_of_stronglyInfers`, `infersDevice_of_stronglyInfers`. Demonstrated in `Explore.lean`; the two attribute forms are **not** interchangeable — the forward form is rejected on a hypothesis-free fact |
| Measurability | `fun_prop`, with `@[fun_prop]` on `measurable_setup` / `measurable_concl` | `by fun_prop` in place of `Measurable.of_discrete` in every discrete model |
| Goal-directed search | `aesop`, rule set `inference` | Registered rules are only those that demonstrably fire; see `Inference/Search/RuleSet.lean` |
| Exhaustion over devices | `FinDevice` + `decide` | Kernel-checked over **all** devices of a fixed shape, which is what an existential claim needs. `plausible` is measured but banned from commits: it closes an unrefuted goal with `sorry` |
| Hypothesis minimisation | `scripts/minimize_hypotheses.py` | Reverse proving. Frozen core (Device, Reality, SelfAware, PhysicalKnowledge): 157 candidates, **0 REMOVABLE**, 1 CALLSITE (`add_one_mod`'s `_hn`, unused inside its own proof but required by a caller). **Causal layer, first full run 2026-08-22**: all 12 `AISafetyAtlas/Causal/` modules plus all 12 `Examples/Causal/` modules, 196 candidates, **0 REMOVABLE, 0 CALLSITE**, every candidate `USED`; `--dead-haves-only` clean on all 24. **Read that for what it is.** The deletion test drops a binder and re-elaborates *without rewriting the proof body*, so `USED` means the proof **mentions** the hypothesis, not that the statement needs it — a proof that took a convenient route through a hypothesis the theorem is true without still reports `USED`. `--dead-haves-only` is the only part of the tool that reaches past that, and it covers just one shape (`have _x := …` whose result is discarded). So this run rules out stated-but-unmentioned hypotheses and dead `have`s in the causal layer; it does **not** establish that every hypothesis there is necessary. Closing that gap needs a proof-rewriting search the tool does not do |
| Declaration dependency view | `scripts/generate_dependency_graph.py --write`, checked with `--check` | `docs/status/<domain>-dependency-graph.{md,json}` — one view per top-level domain, all 13 from one Lean run. The domain list is derived from the tree, not hand-listed: a new domain gets a view by existing. **Edges are statement-level for theorems**: Lean's module system does not export proof terms, and `import all` does not change that — `ConstantInfo.value?` is `none` for every imported theorem, `some` for every definition. Read the JSON from a program; the Markdown is for people. `--check` is a **liveness** check only — it cannot see a view that is missing newly added declarations, which is how the inference view sat at 536 while the tree had 682, and how twelve domains had no view at all. CI regenerates after the Lean build and fails if the tree moves |
| Public-name pin | `scripts/check_public_api.py` | The etalon list. A rename must appear as a deleted line in `docs/status/public-api.txt`, regenerated with `--write`. **It pins names, not signatures**: on 2026-08-22 thirteen pinned theorems gained a hypothesis and the file came out byte-identical, so it is not a guard against a statement changing |
| Scope-axis surface of a row | `#check @<decl>` on every name in the audit row's atlas column | The only reliable way to list what a `Narrower`/`Mixed` row actually carries. Source greps and section-`variable` reading both get it wrong: `omit … in` binds one declaration, section instances are included only when used, and two structures in this tree share names (`SCM.jointProb` and `Model.jointProb`). Four separate mispricings came from enumerating axes off the printed object instead |

**Do not** add `lean-smt`, `Duper` or any external solver as a dependency. A
proof this tree publishes is a proof its own kernel checked; `native_decide` is
banned for the same reason.

### Every library module needs a worked model

`scripts/check_example_coverage.py` (part of the cheap gate) fails when a module
declaring public API is referenced by **no** file under `Examples/`.

The rule exists because the same defect shipped six times: `Prop6Law`, section
9's `Infallible`, the general section-8 measure layer, section 5's inference
complexity, Proposition 3(ii)'s mutual distinguishability, and the
general-measure section-5 layer were each a compiling, axiom-clean,
correctly-transcribed statement about nothing. Every other check passes on those
— a theorem no model satisfies is a valid proof, and a definition no model
evaluates is a valid definition. Generalising an existing layer is one way to
reintroduce it (two of the six), because the general statement gets no witness
even though the special case had one; the other four were simply never
witnessed at all.

One reference to one declaration clears a whole module; the check is weak on
purpose. Exempt a module only with a reason in the script's `EXEMPT` map, which
is re-checked — a module that gains coverage must lose its entry.

### Cheap vs full validation

```console
./scripts/agent_gate.sh          # schema + generated views + path checks (no lake)
./scripts/agent_gate.sh --fast   # same, minus the validator self-tests
```

Full Lean gate is under **Validation** below, together with what `--fast` drops
and when dropping it is not allowed. Skip `lake build` for pure docs or
agent-index edits.
