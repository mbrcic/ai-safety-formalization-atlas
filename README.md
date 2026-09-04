# AI Safety Formalization Atlas

[![CI](https://github.com/mbrcic/ai-safety-formalization-atlas/actions/workflows/ci.yml/badge.svg)](https://github.com/mbrcic/ai-safety-formalization-atlas/actions/workflows/ci.yml)
[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/mbrcic/ai-safety-formalization-atlas?quickstart=1)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21483033.svg)](https://doi.org/10.5281/zenodo.21483033)

> **Quickstart:** [Open in Codespaces](https://codespaces.new/mbrcic/ai-safety-formalization-atlas?quickstart=1) — the toolchain provisions itself and one example compiles in minutes — then pick a [first task](docs/guide/contributor-tasks.md#open-now). Prefer local? `scripts/setup.sh --pointer` (docs only, no Lean) or `scripts/setup.sh --quick` (one example). Full detail: [Get started](#get-started).

**The open Lean library for formal AI-safety results.**

The Atlas develops, reproduces, and audits machine-checked AI-safety mathematics:
shared definitions, theorems, counterexamples, and reviewed interpretation
bridges. Researchers use it to sharpen and discover claims; engineers may use
public facade cores as **reference specifications** inside larger assurance
arguments. Runtime systems and product stacks normally remain downstream.

Most of AI safety lives in prose and scattered proofs, so every citation
rebuilds the model from scratch and words it a little differently each time.
This repo is durable memory against that: **ingredients and primitives** on one
kernel-checked Lean surface, so impossibility, possibility, tradeoffs, and—when
computable—governance or ethics claims name their objects once and reuse them,
instead of every paper re-deriving its own. Humans and proof agents work here
together.

## Why this exists

**The situation.** AI systems are gaining capability faster than anyone is
gaining understanding of them, and they are being deployed on the near side of
that gap. Decisions about what is safe to build and release are being made now.

**Why mathematics.** Most of the evidence behind those decisions is empirical —
evaluations, red-teaming, incident review. That evidence is one-sided by
construction: testing can show that a system fails, never that it cannot. As
capability grows the space of behaviors grows with it, so the fraction any test
suite covers shrinks. A proof is the only form of evidence that speaks about
every case. Its assumptions can still stop matching the system, which is why
nothing here is read as a claim about a real system without a separate reviewed
step.

**Why now.** The same systems that make this urgent are what make it tractable.
Autoformalization has turned mechanization from a specialist craft into ordinary
work: models draft the Lean, and a kernel that does not care who wrote it decides
whether the proof holds. Trust never routes through the model. What this
accelerates is implementation, not discovery — stating the right property, and
reviewing whether it matches the system, still move at human speed. AI is the
subject, the instrument, and the deadline at once.

What the kernel settles is whether a proof is valid. Whether it is the right
statement stays a human question — and that is the bottleneck. Stating a safety
property exactly enough to be checkable is the hard part, and it does not require
knowing what a proof assistant is.

**Bring a question.** Alignment, control, oversight, interpretability,
robustness—if you can make a safety property precise, this is where you turn it
into something machine-checked. Impossibility and possibility both count (e.g.
DeepMind debate reproduced as
[`LAND-DEBATE-001`](docs/provenance/debate-reproduction.md); continuous free
lunches BY-022 [open](docs/guide/contributor-tasks.md#open-now)).

**If the question is causal identifiability**, the `AISafetyAtlas.Causal.*` modules carry
finite categorical Bayesian networks over an ordered field, interventions and
regret, Everitt's structural models and influence diagrams, and the objects the
MAIS-A2 agenda phrases its query problems over — a semialgebraic class, the
`K(G)` parameter chart, and a rational-weight query layer. Two behaviourally
identical models with different graphs are exhibited, not assumed.

**If you want an open question instead of a theorem**,
[`conjectures.yaml`](conjectures.yaml) tracks precise statements — mostly
causal-identifiability questions from
[MAIS](https://github.com/lionellevine/MAIS)'s open-problems agenda, plus one
from an information-theory survey. Every conjecture entry names a closed, compiling `Prop`, and the ledger also holds determine-problem specifications and printed problems with no Lean object at all;
defining one asserts nothing about its truth, and the four rows that are settled
say so and name the proof. Worked models establish that the hypotheses can be met
where a row says so, and the rows whose antecedents still have no witness
disclose it — the MAIS-O26 row needs a solution to MAIS-O24, and no such
solution is exhibited in this tree, so that statement may hold vacuously. See
[conjectures](docs/guide/conjectures.md).

**If the question is control**, `AISafetyAtlas.Control` carries Ashby's variety
bounds and Touchette–Lloyd's information limits at their printed quantifiers: a
regulator cannot hold an outcome steadier than its own repertoire allows, and
feedback improves on open loop by at most the information the sensor actually
supplied. **If it is the reach of a no-free-lunch argument**,
`AISafetyAtlas.Learning.Sharp` proves the characterization in both directions —
performance is algorithm-independent *exactly* on priors closed under relabelling
the search space — together with the count saying almost no prior is one. Several
of the survey's control rows are still empty; see
[open work](docs/guide/open-work.md). Reading these across domains:
[symmetry and impossibility](docs/guide/symmetry-and-impossibility.md).

## Who this is for

- **Lean formalizers and AI-safety theory researchers** (and proof agents)
  developing, reproducing, or auditing formal claims.
- **Formal-methods and safety engineers** using cores as reference
  specifications or to pressure-test assumptions in a larger assurance
  argument.
- **Contributors** willing to make a claim precise, including with help from
  formal-methods collaborators or agents.

A theorem is **not** a system safety case. Applying it to a real system needs a
scoped reviewed bridge where relevant, implementation evidence, and the rest of
the assurance argument. Bridge review validates a scoped interpretation; it does
not by itself prove operational safety.

## Library status

**Primary goal:** develop, reproduce, and machine-check formal AI-safety results
(including using shared foundations to discover new ones), for AI safety and
related computable governance/ethics. **Also:** keep cores usable as reference
specifications downstream. **Not a goal:** growing counts, or growing a product
monorepo in-tree. Reusable structure and honest grading over volume.

<!-- BEGIN GENERATED REGISTRY SCOPE -->
| Metric | Current |
|---|---:|
| Atlas Lean declarations | **253** |
| Results stating a source claim | **49** |
| Results recording a formalization only | **37** (28 on root import) |
| Reviewed AI-system bridges | **3** |
| Statement-reviewed bridges (interpretation withheld) | **1** |
| Open conjectures | **3** |
| Claim results with statement-match | **14** |
| Claim results with `RELATED`-only formalization | **8** |

`EXACT`/`EQUIVALENT` = conservative citation grade (completely
formalization-covered source statements). `RELATED` = value-based scoped
formalization, with documented deltas; it does **not by itself** mean
unfinished, but postponed until justified (paper residuals stay in
provenance). The two grade rows count **claim results**, not
formalization records: one result may carry several, and an artifact
row's own grade is never in these numbers. Detail:
[formalization status](docs/status/formalization-status.md);
[by mathematical area](docs/status/by-area.md);
per-source reports under [`docs/status/sources/`](docs/status/sources/).
<!-- END GENERATED REGISTRY SCOPE -->

Published units must rebuild under documented commands and the axiom policy
([Validation](#validation)).

## Depending on the Atlas from your own project

Add it to your `lakefile.toml`. There is no Reservoir entry, so require it by git:

```toml
[[require]]
name = "ai-safety-formalization-atlas"
git = "https://github.com/mbrcic/ai-safety-formalization-atlas.git"
rev = "v0.7.0"
```

`v0.7.0` is the published release and is what that stanza gets you. **The module
list below describes the working tree, which is ahead of it** — anything added
since the tag is not in `v0.7.0`, so check the tag's own module list before
depending on a name you read here.

Then `import AISafetyAtlas.Knowledge` (or whichever module below) and instantiate
the statements at your own types — they are unbundled maps, not an atlas-specific
agent structure, so your `State` does not have to be one of ours.

Three things worth knowing before you do:

- **Your toolchain has to match, exactly.** Lean `v4.33.0`, Mathlib at the
  `v4.33.0` tag, and Foundation and PFR pinned by commit — PFR is a research
  development whose API is not stable across revisions, which is why it is pinned
  that way. If your project already sits on a different Mathlib, this is not a
  drop-in.
- **You inherit every dependency**, Mathlib, Foundation and PFR, because Lake
  resolves requirements per package rather than per import. Splitting the counting
  half of Ashby's law out of the PFR-importing module (`Control.VarietyCounting`)
  means less has to be *elaborated*, not less fetched.
- **`warningAsError` is this package's option and does not reach yours** —
  verified, not assumed.

## Domain imports

Prefer a facade over the full root import when starting a proof. Some parents
re-export their domain (`Wireheading`, `Compositional`, `Control`,
`Oversight.JointObservation`); the kernels do not, so `Knowledge` and
`Preference` specializations are imported one by one, and `Verification`
supplies its mathematical base without the `AgentBehavior` and `Robot` bridges.
`Inference` re-exports its own subtree, so one import carries the whole Wolpert
development; `Knowledge.Devices` is the transport between the two and imports
both. `InformationTheory` deliberately has **no** parent — each module is one
result and none is built on the others, so there is no surface for a facade to
aggregate. **`Causal` has no parent either, for a stronger reason**: the domain
holds two different objects, and an aggregating import would force a consumer of
one to take the other. `Causal.Model` is a causal Bayesian network — a graph with
conditional probability tables. `Causal.StructuralModel` is Everitt's structural
causal model, influence diagram and SCIM, where the randomness sits in exogenous
variables and the endogenous variables are related deterministically. Neither is
a special case of the other as rendered here. Import contracts per module:
[`AISafetyAtlas.lean`](AISafetyAtlas.lean).

**Two senses of "control" live in this tree.** `Inference` has Wolpert's, which
is a device controlling another device; `Control` has Ashby's and
Touchette–Lloyd's, which is a regulator against a disturbance. No theorem
identifies them.

```lean
import AISafetyAtlas.Control       -- Ashby variety bounds + Touchette–Lloyd limits (facade)
import AISafetyAtlas.Control.RequisiteVariety -- or one module at a time
import AISafetyAtlas.InformationTheory.Fano   -- peers, no facade: import the one needed
import AISafetyAtlas.InformationTheory.DataProcessing
import AISafetyAtlas.InformationTheory.ChannelCapacity
import AISafetyAtlas.Combinatorics.PermInvariance -- relabelling-invariance machinery
import AISafetyAtlas.Learning      -- finite NFL cores
import AISafetyAtlas.Learning.Sharp -- the permutation-closed characterization, both directions
import AISafetyAtlas.Preference    -- planner/reward unidentifiability (kernel)
import AISafetyAtlas.Preference.Override -- overriding human reward functions
import AISafetyAtlas.Preference.Regret   -- half-maximal regret not ruled out
import AISafetyAtlas.Wireheading   -- reward channels, self-modification
import AISafetyAtlas.Compositional -- rectangles, hyperproperties, networks
import AISafetyAtlas.Oversight.JointObservation -- coalition evidence, coverage, collision
import AISafetyAtlas.Knowledge     -- exact knowability, decoders, indistinguishability (kernel)
import AISafetyAtlas.Knowledge.Embedded -- restriction, meshing, self-measurement limits
import AISafetyAtlas.Knowledge.Embedded.Composition -- complement ⇒ proper inclusion; positive boundary
import AISafetyAtlas.Knowledge.Embedded.Finite -- finite cardinality gap ⇒ proper inclusion
import AISafetyAtlas.Knowledge.Temporal -- time-indexed knowability, collisions, delay
import AISafetyAtlas.Knowledge.Ambiguity -- finite fibre ambiguity, counting obstruction
import AISafetyAtlas.Knowledge.SelfReference -- model as part of the state it models
import AISafetyAtlas.Knowledge.Accumulation -- window ambiguity bounds over time
import AISafetyAtlas.Knowledge.Devices -- transports between the kernel and inference devices
import AISafetyAtlas.Knowledge.Check -- executable checkers, each with an agreement theorem
import AISafetyAtlas.Inference     -- Wolpert devices: weak/strong inference, control, physical knowledge
import AISafetyAtlas.SelfAwareness -- process composition and complete-awareness limits
import AISafetyAtlas.Oversight.Debate -- doubly-efficient debate (vendored; NOT on the root import)
```

Cross-surface consumer pattern (compositional boundary + nonzero regret +
preference certificate): `AISafetyAtlas.Examples.WorkbenchConsumers`. Primary
names live in each facade docstring; root `import AISafetyAtlas` remains
available.

`Oversight.Debate` is the one facade root `import AISafetyAtlas` does **not**
bring in: it wraps a vendored development that declares its names in the root
namespace, so it is imported on its own and audited separately. Its module
docstring gives the reason.

## Epistemic scope

A machine-checked proof establishes its encoded mathematical statement. It does
not by itself establish that the statement fully captures an informal AI-safety
claim. Math results and AI-system bridges are separate layers; bridges need
human review.

**Citation grades stay conservative:** do not raise `EXACT`/`EQUIVALENT` by
weakening fidelity. `RELATED` is a useful core with an explicit scope delta; it
does not by itself mean unfinished, and residual paper gaps remain documented.
A bridge may be `REVIEWED` while the formalization stays `RELATED` (e.g. robot).
See the [`v0.7 release scope`](docs/releases/v0.7.md) and
[`docs/guide/methodology.md`](docs/guide/methodology.md).

## Repository contents

- [`registry.yaml`](registry.yaml) records every result: claim rows carrying
  source provenance, and artifact rows for formalizations and public Lean
  surface the library develops or reproduces on its own account.
- [`AISafetyAtlas/`](AISafetyAtlas/) contains attributed Lean integrations.
- [`Main.lean`](Main.lean) is `atlas-check`: it reads a finite model as JSON and
  prints the verdict together with the declaration that certifies it, so a
  question about a particular model can be answered without writing Lean. Every
  checker behind it is paired with a theorem saying it agrees with the `Prop`.
  See the [guide](docs/guide/atlas-check.md) — including what the output is
  *not*, which is a proof term the kernel has checked for that instance.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) explains how to propose and verify changes.
- [`ROADMAP.md`](ROADMAP.md) presents the public strategy and contributor entry points.
- [`STATE.md`](STATE.md) reports the current phase, blockers, and next tasks.
- [`conjectures.yaml`](conjectures.yaml) records source-faithful conjecture
  statements that compile in Lean without a proof, together with settled rows;
  an open row asserts nothing, and a settled one names its proof.
- [`tasks.yaml`](tasks.yaml) is the maintained task board;
  [`docs/guide/contributor-tasks.md`](docs/guide/contributor-tasks.md) is
  generated from it.
- [`docs/`](docs/README.md) is split by role — start with the [documentation map](docs/README.md):
  - [`docs/guide/`](docs/guide/) — methodology, open work, model notes, tasks
  - [`docs/status/`](docs/status/) — generated coverage tables and indexes
  - [`docs/provenance/`](docs/provenance/) — discovery search + external reproduction
  - [`docs/bridges/`](docs/bridges/) — bridge review packages and evidence
  - [`docs/releases/`](docs/releases/) — release evidence notes

## Lean API

Downstream proofs need only the root import:

```lean
import AISafetyAtlas
```

The stable entry points are conventional theorem names under domain namespaces:

- `AISafetyAtlas.Computability.rice` and `rice_code_iff`
- `AISafetyAtlas.Computability.halting_problem`
- `AISafetyAtlas.SocialChoice.arrow`
- `AISafetyAtlas.SocialChoice.Utility.arrow`
- `AISafetyAtlas.Logic.chaitin_incompleteness` and `chaitin_bound`
- `AISafetyAtlas.Logic.godel_first_incompleteness` and `godel_second_incompleteness`
- `AISafetyAtlas.Logic.tarski_undefinability`
- `AISafetyAtlas.Logic.loeb`
- `AISafetyAtlas.Verification.rice`
- `AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier`
- `AISafetyAtlas.Verification.Robot.action_safety_unverifiable`
- `AISafetyAtlas.Compositional` — rectangularity, hyperproperties, and network symmetry
- `AISafetyAtlas.Wireheading` — objective, corruption, and goal-preservation cores
- `AISafetyAtlas.Preference` — preference-unidentifiability and override cores
- `AISafetyAtlas.Oversight.JointObservation` — `covers_iff_no_collision`, the certified
  finite checker `decideCoverage`, the repair boundary, and the bounded portfolio target
  (landscape `LAND-JOINTOBS-001`; see the
  [joint observation model](docs/guide/joint-observation-model.md))
- `AISafetyAtlas.Logic.lawvere_fixed_point` — the types-and-functions Lawvere
  fixed-point wrapper (not the categorical statement; see `CLM-LAWVERE-CCC-001`)
- `AISafetyAtlas.Learning.no_free_lunch` and `no_free_lunch_supervised` — finite NFL cores
- `AISafetyAtlas.Learning.Sharp.nfl_adaptive_iff_permInvariant` — the sharp form:
  performance is algorithm-independent **iff** the prior is closed under
  relabelling the search space. With `card_closedUnderPermutation_nonempty`
  (almost no prior is) this is the result that says where an NFL argument may be
  used at all
- `AISafetyAtlas.Control` — Ashby and Touchette–Lloyd behind one import.
  `ashby_variety_ge` and `ashby_logVariety_ge` are the law in
  counting and logarithmic form, `ashby_variety_ge_isSharp` says it is attained;
  `outcome_eq_comp` and `exists_strategy_forcing` are §11/14;
  `controlLoss_eq_condMutualInfo` identifies control loss with
  a conditional mutual information and `entropyReduction_le_of_openLoopBound`
  bounds feedback's advantage over open loop. Every one of those is in
  `namespace AISafetyAtlas.Control`, whichever of the ten modules declares it, so
  each is importable one at a time; see the facade docstring for the map
- `AISafetyAtlas.InformationTheory.Fano` and `.DataProcessing` — Fano's
  inequality at printed constants and the data-processing inequality with its
  equality case, both over an arbitrary probability space.
  `.ChannelCapacity` is the noiseless capacity, owned by neither
- `AISafetyAtlas.Combinatorics.PermInvariance` — what relabelling-invariance
  forces. `spectrum_eq_iff_mem_permOrbit` (the multiset of values is the complete
  invariant), `closedUnderPermutationEquivSet` (invariant families *are* families
  of multisets), and `exists_perm_rel_not_iff` (no non-trivial relation survives).
  Domain-neutral, reusable, and the shared half of the NFL result above
- `AISafetyAtlas.Knowledge` — start with the
  [knowability model](docs/guide/knowledge-model.md).
  `Knowable` in decoder form, `knowable_iff_no_collision`,
  `IndistinguishabilityWitness`, and the informativeness boundary `Knowable.mono` /
  `not_knowable_comp`. `JointObservation`'s coverage laws are this kernel applied to
  `q.observe`
- `AISafetyAtlas.Knowledge.Embedded` — restriction, inference maps, meshing, and the
  abstract self-measurement no-gos (`EQUIVALENT` to Breuer 1995 §3.5; see `LAND-SELFMEAS-002`)
- `AISafetyAtlas.Knowledge.Temporal` — `KnowableFrom` / `KnowableAt`,
  `CollisionAt`, `EvidenceMonotone`, `DelayedKnowable`. Keeps *knowing the state
  as of `s` from evidence at `t`* apart from *knowing the current state at `t`*, which
  is the difference distributed snapshots exploit
- `AISafetyAtlas.Knowledge.Ambiguity` — `ambiguity` counts the target values one
  observation leaves open. `card_image_le_of_knowable` is a counting obstruction that
  never names a colliding pair; `ambiguity_le_of_comp` says coarsening never lowers the
  shortfall. Finite counting only — no probability or entropy
- `AISafetyAtlas.Knowledge.SelfReference` — where the observation stops being an
  arbitrary map: the observer's model is a *component* of the state. Complete
  self-knowledge holds **iff** nothing else is in the state
  (`selfComplete_iff_subsingleton_rest`), so it is achievable only degenerately
- `AISafetyAtlas.Knowledge.Accumulation` — ambiguity about a *window* of targets.
  Widening never reduces it and never exceeds the product of the steps. Growth itself
  is not a theorem: it depends on dynamics, and both extremes are exhibited
- `AISafetyAtlas.SelfAwareness` — active observation-and-predictive-modelling of
  internal processes during a bounded horizon. `process_not_self_aware` is the
  local strict-extension result; `limited_self_awareness` lifts it through
  recursive process composition without assuming the awareness graph is acyclic

Every facade above carries a short primary-surface table and explicit non-claims
in its module docstring; read that before the declarations. Residual gaps are
recorded per cluster, not in one place: `Compositional`, `Wireheading`,
`Preference` and `Oversight.JointObservation` in the
[A1–A3/B1–B3/B7 re-verification](docs/provenance/a1-a3-b1-b3-b7-reverification.md),
and the `Knowledge` facades in the
[self-measurement kernel note](docs/provenance/self-measurement-kernel.md) and the
[landscape sweep](docs/provenance/embedded-self-knowledge-landscape.md). The
process-compositional BY-044 interpretation has its own
[source map and fidelity residual](docs/provenance/limited-self-awareness.md).

**Landscape declarations** — results the library develops or reproduces on its
own account rather than as coverage of a catalogued source. Seventeen rows carry
`root_import: true`; most are the `Knowledge`, `Oversight` and `Compositional`
entry points listed above. The full list, with the declarations each row owns, is
generated: [landscape index](docs/status/landscape-index.md), and how the rows
stand to one another is [relations](docs/status/relations.md).

The one that has no facade bullet above:

- `AISafetyAtlas.Explainability.attribution_impossibility` (DASH trilemma;
  not BY-029/BY-042 without a separate statement map)

Reproduced external formalizations that carry no Lean interface are pinned in
`registry.yaml`, listed in the
[landscape index](docs/status/landscape-index.md), and rebuilt with
`scripts/reproduce_isabelle.sh`:

- `Gibbard_Satterthwaite` (`LAND-GS-001`, Isabelle/HOL; Arrow-session
  provenance related to BY-007). Lean consumer interface:
  `AISafetyAtlas.SocialChoice.gibbard_satterthwaite` (`LAND-GS-002`, vendored
  SocialChoiceLean GS closure)
- `no_free_lunch_ML` (`LAND-NFL-001`, Isabelle/HOL; the Shalev-Shwartz–Ben-David
  PAC no-free-lunch — the formal core of "generalization needs inductive bias" —
  distinct from the Wolpert NFL survey rows BY-020/BY-021; see
  [CT-2 triage](docs/provenance/ct2-nfl-triage.md))

The Rice verification bridge concerns properties of partial input/output
behavior; `AgentBehavior` is a downstream consumer that models encoded agents
and total behavioral safety verifiers. The independent Robot bridge concerns
total reactive action traces under an explicit effective switching certificate
and reduces directly to the halting problem. The Logic layer covers Chaitin
(BY-015, vendored KolmogorovMathlib), classical Gödel I/II (BY-013, Foundation),
Tarski undefinability (BY-016), and Löb (BY-027); see
[logic incompleteness](docs/guide/logic-incompleteness.md). Neither classical nor
bridge theorem asserts that a particular AI system or practical verification
task satisfies its model. Generated checks in
`AISafetyAtlas.Examples.Registry` compile every registry-listed declaration
through the root import. The hand-written examples in
`AISafetyAtlas.Examples.PublicAPI` additionally protect the intended theorem
signatures; the explicit targets in `scripts/lean_build_targets.txt` also build
worked examples, most of which are intentionally outside the public root
import. The twelve `AISafetyAtlas.Examples.Causal.*` modules are the exception
and are on the root import.
Kernel axiom cleanliness of the headline surface is checked by
`scripts/check_print_axioms.py`.

External reproduction of the Kolmogorov pin (upstream checkout, not the
vendored tree):

```console
scripts/reproduce_chaitin.sh
```

## Get started

<!-- BEGIN GENERATED ROUTING -->
<!-- Generated by scripts/generate_registry_views.py; do not edit by hand. -->

| I have… | It goes in | Then |
|---|---|---|
| a pointer to a result, or a proof, that is not recorded here | the [discovery issue form](https://github.com/mbrcic/ai-safety-formalization-atlas/issues/new?template=known-formalization.yml) — we classify it and place it | nothing to install |
| a correction to a record you have already found | the ledger file that holds it | `scripts/setup.sh --pointer` |
| an open question and no proof | the [conjecture issue form](https://github.com/mbrcic/ai-safety-formalization-atlas/issues/new?template=conjecture.yml) | no Lean needed; the statement enters the ledger after it compiles |
| a proof to write, or any Lean change | the facade for your area (see Domain imports); for new coverage, dependencies, or public API, start with the [formalization proposal](https://github.com/mbrcic/ai-safety-formalization-atlas/issues/new?template=formalization-proposal.yml) | `scripts/setup.sh`, then build + gate + `check_print_axioms.py` |
| a change to a contributor task | `tasks.yaml` — never the generated Markdown | regenerate + gate |
| evidence that something does not exist | `novelty_checks` in `docs/provenance/formalization-search.json` | update search evidence, then regenerate + gate |
| a new source to catalogue | `source_catalog` in `registry.yaml`, with its `role`; add a `CLM-*` row with `original_source_refs` if it states a result | regenerate + gate |

**regenerate** `python3 scripts/generate_registry_views.py` · **gate** `./scripts/agent_gate.sh` · **build** `lake build`

Nothing here needs the whole picture: take the row that matches what you
have and ignore the rest.
<!-- END GENERATED ROUTING -->

No toolchain needed for the first row — the validators need only Python 3.9 or
newer and its standard library. One check reads a ledger through PyYAML and is
skipped with a notice if that is absent; `pytest` and `ty` are likewise optional
locally. CI installs all three, so none of them is optional on a pull request:

```console
scripts/setup.sh --pointer   # cheap validators only; no Lean toolchain
```

For anything touching Lean, one command provisions everything — it installs
[`elan`](https://lean-lang.org/install/manual/) if it's missing, fetches the
prebuilt Mathlib, builds, and runs the validators:

```console
scripts/setup.sh --quick   # fast path: toolchain + Mathlib cache + one example compiling
scripts/setup.sh           # full: whole build closure + validators (run before a Lean PR)
```

Zero local install: open the repo in **GitHub Codespaces** — or any editor's
[Dev Container](.devcontainer/devcontainer.json) — and the toolchain provisions
itself on first boot (via `--quick`, so the cold start stays short; run the full
`scripts/setup.sh` before submitting a Lean change).

<details>
<summary>What <code>scripts/setup.sh</code> runs, to do it by hand</summary>

```console
lake exe cache get   # fetch prebuilt Mathlib — skips an hours-long local compile
lake build
xargs lake build < scripts/lean_build_targets.txt
./scripts/agent_gate.sh
```
</details>

The repository pins Lean, Mathlib, and every transitive dependency:
[`lake-manifest.json`](lake-manifest.json) is the lock. Build from it directly —
do **not** run `lake update` unless you are deliberately bumping a dependency, as
it re-resolves floating revisions off the pinned set. Released Lean files follow
the [strict-trust and build-closure policy](docs/guide/methodology.md#new-proofs-and-bridges).

## Contributing

**There is always something to do.** [Get started](#get-started) routes what you
have to the one file it belongs in; bounded units are in
[contributor tasks](docs/guide/contributor-tasks.md).

Working with an LLM or agent: draft against a facade, then `lake build` →
`agent_gate.sh` → `check_print_axioms.py` (see [CONTRIBUTING](CONTRIBUTING.md)).
Green Lean is kernel validity of the encoding — not source match, model
adequacy, or system interpretation.

Full tracks and rungs: [CONTRIBUTING.md](CONTRIBUTING.md). Issue forms for
proposals that change coverage, dependencies, or the public Lean interface.

## License

Apache-2.0. Individual external formalizations remain subject to their own
licenses; the registry records those licenses when verified.
