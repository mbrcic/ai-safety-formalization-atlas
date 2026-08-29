# Contributor and Agent Guidance

Read this file before autonomous work. Live phase: [`STATE.md`](STATE.md).
Agent map: [`docs/agent/INDEX.md`](docs/agent/INDEX.md). Human doc map:
[`docs/README.md`](docs/README.md). Policy detail:
[`docs/guide/methodology.md`](docs/guide/methodology.md).

## Context budget (agents)

### Start here (small by design)

**Fastest route, and it needs no agent in particular:** make your change, then
run `python3 scripts/preflight.py`. It reads the diff, works out which kinds of
contribution it contains, and prints only the obligations and commands that
apply, each naming the section here that governs it. It restates no rule and
decides nothing — the gate does that — but it removes the step where a
contributor reads a thousand lines of policy to find the twenty that bind them.

Agents that load project skills will find the same route as
[`.agents/skills/atlas-contribution/SKILL.md`](.agents/skills/atlas-contribution/SKILL.md);
it holds the order to work in and no rules, which stay here.

Open this file, `STATE.md`, and `docs/agent/INDEX.md` first. The other paths
below are conditional and should be opened only when the task needs them.

1. This file (short policy)
2. [`STATE.md`](STATE.md)
3. [`docs/agent/INDEX.md`](docs/agent/INDEX.md), [`by-id.json`](docs/agent/by-id.json),
   and [`search-summary.json`](docs/agent/search-summary.json) as needed
4. [`docs/status/landscape-index.md`](docs/status/landscape-index.md) /
   [`docs/status/sources/`](docs/status/sources/) if browsing coverage
5. **One facade module** under `AISafetyAtlas/*.lean` (or a small nested facade
   such as `Verification/Robot.lean`) for the task domain — not `Upstream/`
6. [`docs/guide/open-work.md`](docs/guide/open-work.md) or
   [`contributor-tasks.md`](docs/guide/contributor-tasks.md) when picking work

### Do not read by default

| Path | Why | When to open |
|---|---|---|
| Full [`registry.yaml`](registry.yaml) | Redundant with `by-id.json` | One `BY-###`, `CLM-*`, or `LAND-*` via `rg` for notes / candidates / bridge_review |
| [`docs/provenance/formalization-search.json`](docs/provenance/formalization-search.json) | Large discovery dump | Regenerating evidence or deep candidate audit |
| [`ROADMAP.md`](ROADMAP.md) | Human strategy, not live tasking | Maintainer names roadmap work |
| `AISafetyAtlas/Upstream/**` | Large vendored/collapsed proofs | Editing that formalization only |
| `vendor/**` | Upstream vendor trees | Editing that vendored package only |
| `.lake/**`, `**/CLAUDE.md`, `ai_context.txt` | Build cache / tool dumps | Never as task context |
| [`docs/status/declaration-index.json`](docs/status/declaration-index.json) | The largest file in the repository (~155k tokens); it is a lookup table, never a read | Resolving one name — `rg '"AISafetyAtlas\.Foo\.bar"'`, or ask the Lean LSP |
| `docs/status/*-dependency-graph.json` | Machine view of one cluster; `inference` alone is ~52k tokens | A tool consumes it. To *read* a cluster, open the `.md` sibling |
| [`docs/provenance/source-coverage-audit.md`](docs/provenance/source-coverage-audit.md) | ~42k tokens of statement-by-statement grading | One source's section (`rg -A40 '^## 6\.'`) or one row, never the file |
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
[`AISafetyAtlas.lean`](AISafetyAtlas.lean).

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

## Public Lean API

`AISafetyAtlas` is a small stable facade. One canonical public declaration per
result; keep conventional theorem names; namespace form
`AISafetyAtlas.<Domain>.<OptionalRepresentation>.<Theorem>` (`UpperCamelCase`
namespaces, `snake_case` declarations). Add representation namespaces or
suffixes (`_iff`, `_reduction`, …) only for genuine interface distinctions.
Do not mirror entire upstream libraries.

```lean
AISafetyAtlas.Computability.rice
AISafetyAtlas.Verification.rice
AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier
AISafetyAtlas.Verification.Robot.action_safety_unverifiable
AISafetyAtlas.SocialChoice.arrow
AISafetyAtlas.SocialChoice.Utility.arrow
AISafetyAtlas.SocialChoice.gibbard_satterthwaite
AISafetyAtlas.Logic.godel_first_incompleteness
AISafetyAtlas.Logic.godel_second_incompleteness
AISafetyAtlas.Logic.tarski_undefinability
AISafetyAtlas.Logic.loeb
AISafetyAtlas.Explainability.attribution_impossibility
AISafetyAtlas.Learning.no_free_lunch
AISafetyAtlas.SelfAwareness.Model.limited_self_awareness
```

## Parsimony (formalizations)

Reuse a maintained Lean result + thin atlas alias before porting another proof.
Keep a second formalization only for a documented substantial gain (stronger
theorem, different representation, reduction certificate, constructive content,
or necessary independence). Non-Lean proofs may be provenance without duplicate
public Lean declarations. Prefer packaging Rice as `Verification.rice` /
`AgentBehavior.no_behavioral_safety_verifier` rather than a second undecidability
proof. Detail: [`docs/guide/methodology.md`](docs/guide/methodology.md).

**Parsimony governs duplication, not foundations.** A second way to establish
something the tree can already state is duplication, and the rule above is
strict about it. A definitional layer that catalogued rows cannot be *stated*
without is a foundation, and asking it to show consumers first is a rule no
foundation can pass: the consumers are blocked on the thing being judged. A
foundation may land ahead of its consumers when all four hold:

1. **Two blocked rows, by id.** At least two existing `BY-`/`CLM-`/`LAND-` rows
   or `tasks.yaml` entries that cannot be stated without it — blocked, not
   merely inconvenienced.
2. **The gap is upstream and recorded.** A `novelty_checks` entry showing the
   pinned corpora lack it, so the blocker is availability rather than effort.
3. **Definitions may precede consumers; theorems may not.** The definitional
   layer may land with none. Theorems built on it need a consumer landing in the
   same change or the next.
4. **An expiry.** The row names a release by which a consumer must land, or the
   layer is deleted or demoted to provenance. Removal is an ordinary outcome —
   the `doc-gen4` pipeline was built and removed on cost grounds.

A foundation is a `LAND-` artifact row, never headline coverage, and carries no
statement-match grade against a source it does not state.

## Statement freeze

**A reviewed statement is frozen. Proofs are not.** A statement is reviewed
once it carries a fidelity grade in `registry.yaml` or `conjectures.yaml`, or a
pinned source in `docs/provenance/`.

| may change freely | frozen |
|---|---|
| proof bodies, `have`/`let` structure, tactic choice | the binders, hypotheses, quantifiers and conclusion of the declaration |
| new private helper lemmas | the axiom set — nothing may be added |
| docstring prose that does not restate the claim | the claim a docstring or grade asserts |

Weakening a hypothesis, narrowing a quantifier, adding a side condition, or
specializing the conclusion is **not** a proof step, even when it makes the
proof go through. It is a **schema event**: revise the statement in its own
change, say which direction fidelity moved, and re-grade the row. A grade
earned by the old statement does not transfer to the new one.

The reason is that the kernel cannot see this failure. Every fidelity defect
this repository has shipped and later fixed was in a definition or a statement,
and every one compiled. An agent that may edit statements can always close a
goal by editing the goal, and the build reports success either way.

If a statement looks wrong, say so and stop — a `sorry` with a note naming the
suspected defect is a better outcome than a proof of something else.

`scripts/check_statement_freeze.py` hashes the signature of every ledger-graded
declaration against `docs/status/statement-lock.json` and reports drift in the
cheap gate. It is advisory and compares source text, so reformatting reports a
change that is not one — the report is a question, never a verdict. Answer it,
re-grade the row if fidelity moved, then `--write` to record the new statement.

## Coverage, landscape, and bridges

- **Headline coverage:** reproduced registry formalizations with `EXACT` or
  `EQUIVALENT` only. `RELATED` does not increase the count.
- **Which record takes your edit:**
  | Where | Holds | Note |
  |---|---|---|
  | `registry.yaml` survey claim rows | what the Brcic–Yampolskiy survey asserted | `BY-001`…`BY-044` is **closed**; never add `BY-045` |
  | `registry.yaml` other claim rows | what any other source asserted | `CLM-` prefix; at least one `original_source_refs`; no survey-only fields (`paper_reference`, `survey_proof_assessment`, `formal_library_search`) |
  | `registry.yaml` artifact rows | formalizations standing on their own | `LAND-` prefix, no `informal_claim`, never headline coverage |
  | `conjectures.yaml` | open questions, compiling statement, no proof | never a theorem, never counted as one |
  | `tasks.yaml` | the task board | `docs/guide/contributor-tasks.md` is **generated** — never edit the Markdown |
- **Sources are `directory` or `work`.** A directory is a curated map (the survey
  itself, `mathforaisafety.org`, AISI, MAIS): never graded against, entry count
  never a metric. A `work` is statement-bearing and is the only thing a
  statement-match grade may cite.
- **Claiming something does not exist?** That needs a `novelty_checks` record in
  `docs/provenance/formalization-search.json` — corpus, revision, date, and what
  the search did not cover. The six-corpus sweep is the `baseline-catalogue`
  profile for one source and is **not** inherited by new work.
- **Applications:** a declaration stated over an AI-system model may record a
  proposed `application` line — what it claims, over which model, and where the
  statement comes from. It is discovery prose, not review evidence; only a
  `REVIEWED` bridge supports a reviewed AI-system interpretation. Required on
  every `BRIDGE`. Generated view:
  [`docs/status/applications.md`](docs/status/applications.md).
- **Layers:** (1) math theorem → (2) atlas interface → (3) AI-safety bridge →
  (4) real-system claim. Layers 3–4 need human review; Lean at 1–2 does not
  inherit an AI reading.
- **`ai_bridge_status`:** `HUMAN_REVIEW` → `STATEMENT_REVIEWED` → `REVIEWED`.
  Non-`HUMAN_REVIEW` needs a real `bridge_review` record under `docs/bridges/`.
  **Never invent** human review or graduate a bridge without authorization.
- Prefer `STATEMENT_REVIEWED` over overclaiming real systems.
- Robot (`action_safety_unverifiable`): **conditional reduction core**,
  relationship `RELATED`. Do not lengthen for paper show-off.
- GS: Isabelle `LAND-GS-001`; Lean facade `gibbard_satterthwaite` (`LAND-GS-002`).
  Do not vendor the rest of SocialChoiceLean without a consumer need.

## Documentation layout

| Path | Role |
|---|---|
| `docs/agent/` | Agent navigation + generated compact indexes |
| `docs/guide/` | Human explainers (methodology, open work, tasks, …) |
| `docs/status/` | **Generated** coverage tables — do not hand-edit |
| `docs/provenance/` | Discovery evidence + external reproduction narrative |
| `docs/bridges/` | Bridge review packages |
| `docs/releases/` | Release evidence notes |

After editing a maintained ledger — `registry.yaml`, `conjectures.yaml`, or
`tasks.yaml` — run `python3 scripts/generate_registry_views.py` (updates
`docs/status/*`, `docs/guide/contributor-tasks.md`, `docs/agent/by-id.json`,
`docs/agent/search-summary.json`, README/STATE snippets, and the Lean registry
and conjecture checks), then `./scripts/agent_gate.sh`. Do **not** hand-edit
`docs/provenance/formalization-search.json`: when search terms, corpora, or pins
change, rebuild that generated evidence with
`scripts/update_formalization_search.py` using its pinned corpus arguments,
then regenerate the views and run the gate. Paper ↔ formalization map:
`docs/status/sources/`. AI-safety literature map:
`docs/guide/related-literature.md`.

## Branch, version, and publication

- `main` is protected; do not commit or push agent work to it.
- Use local `agent-work` unless the maintainer names another branch.
- Commit coherent verified increments locally; **do not push** or open PRs/issues
  without explicit maintainer authorization (draft tasks in `tasks.yaml` or the
  issue tracker; `docs/guide/contributor-tasks.md` is generated).
- Package version stays at the last published baseline until authorized.
- Publish via reviewed PR + squash merge; keep pre-squash history on a local
  archive branch when useful.

## Proving: tactic order and the exploration target

Try automation before writing a proof by hand, in this order:

1. **`grind`** — Lean core, so it needs no import and is available even inside
   `Inference/Device.lean`'s two-module import surface. Measured, not assumed.
2. **`aesop (rule_sets := [inference])`** — for goals about devices, after
   `import AISafetyAtlas.Inference.Search`. That module is deliberately not on the
   public root import: the core's narrow imports are what keep it cheap to audit.
3. **`decide`** — on finite models. `native_decide` stays banned; the gate rejects it.

**Test a conjecture before proving it.** `AISafetyAtlas.Explore` imports the full
`Mathlib.Tactic` surface plus `Plausible` and is built by CI as an explicit target,
so the discovery tactics stay available without widening any shipped import graph.

**`plausible` may never appear in committed code.** On a goal it cannot refute it
reports *"Unable to find a counter-example"* and closes the goal with `sorry`. Use
it interactively; commit the counterexample it found as a real theorem, or the
proof it failed to refute.

**To search over devices, not just over values:** `InferenceDevice` carries its
setup type as a field, so a statement quantifying over devices ranges over a proper
class and nothing can enumerate it. `Examples.Inference.Enumerable.FinDevice` fixes both types
(`U = Fin m`, `Setup = Fin n`), is a `Fintype`, and carries a `Decidable` instance
for `WeaklyInfers`. `decide` then settles *"no device of this shape does X"* in the
kernel — exhaustive and trusted, where sampling would be neither. The instance has
to unfold `WeaklyInfers`, `Realized` and `IsProbe` by hand, because instance search
runs at reducible transparency and those are `def`s.

**Before adding a hypothesis, check the ones already there:**

```console
python3 scripts/minimize_hypotheses.py <module.lean> --decl <name>
python3 scripts/minimize_hypotheses.py <module.lean> --dead-haves-only
```

`REMOVABLE` means the statement is true without that hypothesis — drop it, or say
in the docstring why print fidelity keeps it. A hypothesis consumed only by a
`have _x` the proof then discards reports `USED` and is really removable, which is
what `--dead-haves-only` finds. This is an offline audit, not a gate: each
candidate costs a full elaboration.

## Validation

Cheap preflight:

```console
./scripts/agent_gate.sh
# repeated agent iterations: one-line success, full output on failure
./scripts/agent_gate.sh --quiet
```

The gate ends with `pytest tests/` (malformed-shape regressions) and
`ty check scripts/ tests/`. Both are skipped with a notice when the tool is not
installed, so the gate still runs without them; CI installs both, so neither is
optional on a pull request. Install with `python3 -m pip install pytest ty`.

### The `--fast` lane (`--lean` is the old name)

```console
./scripts/agent_gate.sh --fast          # skips the five self-test steps
./scripts/agent_gate.sh --fast --quiet  # both flags compose
```

`--fast` skips exactly five steps: `test_validators`, `test_source_neutral_views`,
`test_a1_a3_pattern_a_harness`, `pytest tests/`, and `ty check`. Those five
exercise the validator scripts themselves.

**Correction, 2026-08-29.** This section used to say those five *"take no input
from `AISafetyAtlas/`, `docs/`, or the ledgers"* and that *"editing Lean cannot
change their verdict."* Both are false, and they were the stated reason the lane
is safe. `test_validators` copies `registry.yaml`, `conjectures.yaml`,
`tasks.yaml`, `formalization-search.json`, `AISafetyAtlas.lean`, the whole
`AISafetyAtlas/` tree and several `docs/` trees into a temporary tree and runs
the validators against them; `test_source_neutral_views` reads the live
registry; the a1–a3 harness reads a reproduction script and provenance
documents; and `tests/` reaches declaration locations and repository Markdown.
Repository content is an input to all of them, so a `--fast` run can be green
over a change they would reject.

What justifies the lane is therefore **when** it is used, not independence — see
the retry-loop paragraph below — and the rule that the full gate is owed before
the commit stands unchanged.

Everything that reads the tree, the ledgers, or the generated views *directly*
still runs, so `--fast` still catches a rename that orphaned a docstring name, a
module missing from the root import, a stale dependency graph, a mislaid example
file, a changed graded statement, or a registry `line:` field that shifted.

**Numbers are measurements, not constants.** On 2026-08-29 `test_validators`
runs in ~12 s, down from ~53 s. Nothing was dropped to get there: the Lean
masker stopped scanning one character at a time, and the import-line regex
stopped running under `re.M`, where its leading `\s*` consumed newlines and made
the engine rescan blank runs from every position. Whole-gate timings on one
machine varied roughly threefold run to run, so no single figure for them is
quoted here. Measure; do not inherit a number from this file.

**This is a retry loop, not an iteration loop.** The gate belongs before a
commit, not between edits, so `--fast` earns nothing on the first run — you owe
the full gate anyway. Where it pays is the second run and after: the gate fails
on a Lean-facing check, you fix, and you want to know whether the fix took. That
retry is a fraction of the full gate, and the failures that put you in that loop are
exactly the ones `--fast` still watches — a shifted registry `line:` field, a
regenerated view that did not get regenerated, a docstring name orphaned by a
rename. Fix, `--fast`, fix, `--fast`, then the full gate once to commit.

**The full gate is mandatory before you commit**, and non-negotiable whenever
you touched anything under `scripts/`, `tests/`, or the ledger schemas — those
are precisely the inputs `--fast` stops watching, and its own last line says so.
A green `--fast` is never a green change. CI runs the full gate regardless, so
skipping it locally only moves the failure later.

If you are reaching for the gate to find out whether Lean is happy, that is the
wrong tool and the real cost. Ask the language server
(`lean_diagnostic_messages` and friends): it answers per-file in seconds what a
build reports minutes later, and unresolved names after a rename are exactly its
job. When you do build, build the cone you changed —
`lake build AISafetyAtlas.Causal.Query` — rather than bare `lake build`, which
elaborates the root's whole closure. A no-op full build is ~4 s, so once the
tree is warm the build is not what costs; the generators and the gate are, and
both are once-per-commit.

Full green (Lean + axioms):

```console
./scripts/agent_gate.sh
python3 scripts/check_print_axioms.py
lake build
xargs lake build < scripts/lean_build_targets.txt
python3 scripts/generate_declaration_index.py --write   # after adding or renaming
```

`generate_declaration_index.py` walks the **elaborated environment** and writes
`docs/status/declaration-index.json`, which is what lets
`check_docstring_identifiers.py` tell a real declaration from a name that merely
appears somewhere in the source. It costs a full elaboration, so it belongs
here rather than in the cheap gate; the cheap gate reads the committed file and
says nothing when it is absent.

Two worklists exist for the step *after* a gap closes. Neither can fail and
neither is in the gate, because both ask a question a regex cannot answer:

```console
python3 scripts/where_is_graded.py CONJ-002   # every line restating a grade
python3 scripts/list_absence_claims.py        # every "X is not here" sentence
```

Run them after landing anything that closes a gap. The recurring defect on this
repository is not a broken proof — it is a sentence that outlived the field or
the declaration it described, and these print the sentences to re-read.

Historical v0.1 only: `python3 scripts/audit_release_v0_1.py` (must not block
genuine post-v0.1 bridge graduation).

## Audience and wording

Primary readers are **AI safety researchers**. Prefer clear models, explicit
exclusions, and honest `RELATED` / `HUMAN_REVIEW` labels. Tracked prose is
strategic: no conversational shorthand in registry notes, Lean docs, or README.
Cite papers with the claim they actually state.
