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
| [`docs/status/declaration-index.json`](docs/status/declaration-index.json) | ~214k tokens; it is a lookup table, never a read | Resolving one name — `rg '"AISafetyAtlas\.Foo\.bar"'`, or ask the Lean LSP |
| `docs/status/*-dependency-graph.json` | Machine view of one cluster; `inference` ~58k tokens, `causal` ~41k | A tool consumes it. To *read* a cluster, open the `.md` sibling |
| [`docs/provenance/source-coverage-audit.md`](docs/provenance/source-coverage-audit.md) | ~47k tokens of statement-by-statement grading | One source's section (`rg -A40 '^## 6\.'`) or one row, never the file |
| [`docs/agent/by-id.json`](docs/agent/by-id.json) | ~46k tokens | One `BY-###` via `rg`, as with `registry.yaml` |
| `docs/status/elab-baseline-*.json` | ~3M tokens each; a normal-form dump, unreadable by construction | Only `--compare` / `--classify`. Never open one |
| [`docs/status/public-api.txt`](docs/status/public-api.txt) | ~31k tokens | One name via `rg`; the pin is the diff, not the read |
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

Read the relocated policy at
[`docs/agent/policy/public-lean-api.md`](docs/agent/policy/public-lean-api.md).

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

### Conditional results, and the debt they create

A result proved under a proposition the atlas does not prove is a **conditional
verification**, and the assumed proposition is a debt. `CONTRIBUTING.md` says how
to report the result; this says how the debt is tracked.

Every assumed proposition gets a row in the `FRONTIERS` registry at the top of
`scripts/check_frontier_evidence.py`, which the cheap gate runs. The row names the
frozen `..._iff` surface, the unconditional stress artifacts, and three fields no script
can check: `owed_to`, `decision`, `reason`. The gate prints all of it on every run,
which is the whole reason the registry is a literal in the checker rather than a
fourth ledger with a validator and a generated view — three rows do not earn that,
and the debt is more discoverable printed beside its own evidence than filed away.

`owed_to` must not be collapsed. `"candidate"` means a submitted solution cites the
proposition rather than deriving it, so assuming it leaves that derivation intact
and verifying the submission does not require paying the debt. `"source"` means the
printed problem statement asserts it. `"atlas"` means we chose a formulation the
source did not, and the gap is of our own making — the expensive kind. Never report
a total across the three.

`decision` is `hold` or `discharge`, and a hold is a decision rather than a
silence: the `reason` must say what discharging would cost and record that no
maintainer has ruled, if none has. An artifact counts only when it does not itself
assume the frontier — a theorem `frontier → X` reads exactly as strong whether the
frontier is true or false, and the check enforces that. Passing this check does not
show that the frontier is satisfiable: an artifact may only probe a formula, rule
out a cheap branch, or verify that the asserted setting has a required property.

### The layer a text diff cannot reach

Every check above reads source. On a toolchain bump the dangerous change is the
one where the source does not move: an upstream rename behind an alias, a
different instance chosen, a definition made reducible. The text is identical,
the build is green, `axiom-audit` still says proved — of something else.

`scripts/check_elaboration_drift.py` compares declarations by their **elaborated
type**. It emits a normal form from Lean and hashes it in Python, never in Lean,
because `String.hash` belongs to the toolchain under comparison and hashing there
would make every declaration look changed in exactly the situation the tool
exists for.

```bash
python3 scripts/check_elaboration_drift.py --self-test              # on either tree
python3 scripts/check_elaboration_drift.py --dump out.json --raw    # on each tree
python3 scripts/check_elaboration_drift.py --compare old.json new.json
python3 scripts/check_elaboration_drift.py --classify old.json new.json

# the standing check, and what CI runs on every branch that touches Lean
python3 scripts/check_elaboration_drift.py --dump out.json --raw
python3 scripts/check_elaboration_drift.py --compare \
  docs/status/elab-baseline-v4330.json out.json --fatal silent
```

Dump `--raw`, which keeps the normal form instead of a digest of it, and commit
that. A hashed dump halves to ~3 MB and loses the only thing `--classify` can
work from, so the recorded class breakdown stops being reproducible from this
repository.

Commit them as **plain text, never gzipped**. Git already zlib-compresses every
blob and deltas each dump against the one before it; a `.gz` defeats both, and
this pair measured 734,042 bytes packed gzipped against 391,190 bytes packed as
text. The 42,000-line diff that compression was meant to solve is handled by
`.gitattributes` instead: `-diff` renders a migration as one `Bin` line and
costs nothing. Nothing but `--compare` and `--classify` ever reads a dump.

Run `--self-test` first on any tree you dump: it decides four known-answer cases
against a real elaborator, and a fingerprint that never changes and one that
always changes are both useless. `--dump` needs everything built, including
`scripts/lean_build_targets.txt`, because module discovery is artifact-based — a
target you did not build is silently not compared.

A dump selects declarations **by the module they compiled into**, not by their
name, and records which it did under `selector`. Selecting on the `AISafetyAtlas`
name prefix misses everything our modules compile under someone else's namespace
— the vendored `Kolmogorov.*` and debate `Comp.*` layers, 636 declarations, 72 of
them on the public API pin, including the theorem
`AISafetyAtlas.Logic.chaitin_incompleteness` is assigned from. `--compare` warns
when the two dumps disagree on `selector`, because then the report counts the
difference between the selectors as well as the difference between the trees.

The bucket that matters is **silent**: printed type identical, elaborated type
not. A hashed dump can only say *that* something moved, which is why the
committed dumps are `--raw`.

That bucket is also the only one a branch can be **gated** on, which is what
`--fatal silent` selects. A plain `--compare` fails on any movement at all —
the right question for a migration, and red on every ordinary pull request,
since adding statements is what a branch is for. A declaration whose printed
type is unchanged cannot have changed meaning through an edit, so a silent
change is never work anyone asked for, and CI holds this tree to
`docs/status/elab-baseline-v4330.json` on that bucket alone. It catches what no
source-reading check can: a Mathlib rebuild against a moved artifact, an
upstream alias, a different instance chosen.

Expect it to go red on a toolchain bump. That is the tool working. Re-adjudicate
the silent set, re-dump both sides, record the classes — do not widen the flag.
`agent_gate.sh` separately runs `--classify` over the committed pair, which needs
no toolchain and holds the recorded accounting to the class registry, so a class
widened or a dump edited turns the cheap gate red without waiting for CI.

The silent count grows with the library — 131 at 5358 declarations, 171 at 5994
— because it counts declarations that happen to touch whatever upstream renamed.
The number of *reasons* does not: there were eleven, and they come from upstream's
churn. So a class is adjudicated once against an anchor that holds at both
toolchains, recorded in `docs/status/elaboration-classes.json`, and never
re-litigated; `--classify` matches a migration's silent set against the registry
and exits non-zero only on what is left over.

A class states its verdict as `removes` and `adds`, and both are enforced: a
declaration is classified only when the classes that fired account for every
constant that left *and* every constant that arrived. The `change` string is
prose for a reader and is checked by nothing. Matching on the departure alone is
unsound: `setOf` leaving would match the `setOf` class whatever replaced it, so
`setOf -> Evil` would certify clean and an unrelated substitution in the same
statement would be swallowed. A class excuses a
*replacement*; a check that never reads the replacement is not checking it. **Reading two new classes is work
that stays the same size as this library grows; reading 171 names is not.** A
silent change that kept every constant and rearranged them is reported apart and
can never be excused by a registry entry — that is a binder kind, an argument
order or a universe moving, and it needs its own verdict.

`docs/status/elab-baseline-v4310.json` and
`docs/status/elab-baseline-v4330.json` are the two sides of the last
migration, both module-selected and both kept because a dump cannot be
regenerated once its tree moves; compare the next toolchain against the v4.33.0
one. **Keep two.** When a bump lands, its two sides replace the previous pair;
Foundation moves monthly, and a dump per toolchain we ever pinned turns a fixed
cost into an accruing one. `tests/test_elaboration_drift.py` enforces the two.
`docs/provenance/elaboration-adjudication-v4310-v4330.lean` holds the anchors,
checkable at either toolchain, and `docs/status/migration-baseline.json` records
the per-class counts for the migration itself.

## Coverage, landscape, and bridges

Read the relocated policy at
[`docs/agent/policy/coverage-landscape-and-bridges.md`](docs/agent/policy/coverage-landscape-and-bridges.md).

## Documentation layout

Read the unchanged policy at
[`docs/agent/policy/documentation-layout.md`](docs/agent/policy/documentation-layout.md).

## Branch, version, and publication

Read the relocated policy at
[`docs/agent/policy/branch-version-and-publication.md`](docs/agent/policy/branch-version-and-publication.md).

## Proving: tactic order and the exploration target

Read the relocated policy at
[`docs/agent/policy/proving-tactic-order.md`](docs/agent/policy/proving-tactic-order.md).

Read the relocated policy at
[`docs/agent/policy/validation.md`](docs/agent/policy/validation.md).

## Audience and wording

Read the relocated policy at
[`docs/agent/policy/audience-and-wording.md`](docs/agent/policy/audience-and-wording.md).
