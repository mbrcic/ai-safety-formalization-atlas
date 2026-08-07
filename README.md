# AI Safety Formalization Atlas

[![CI](https://github.com/mbrcic/ai-safety-formalization-atlas/actions/workflows/ci.yml/badge.svg)](https://github.com/mbrcic/ai-safety-formalization-atlas/actions/workflows/ci.yml)
[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/mbrcic/ai-safety-formalization-atlas?quickstart=1)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21483033.svg)](https://doi.org/10.5281/zenodo.21483033)

> **Quickstart:** [Open in Codespaces](https://codespaces.new/mbrcic/ai-safety-formalization-atlas?quickstart=1) — the toolchain provisions itself and one example compiles in minutes — then pick a [first task](docs/guide/contributor-tasks.md#open-now). Prefer local? `scripts/setup.sh --pointer` (docs only, no Lean) or `scripts/setup.sh --quick` (one example). Full detail: [Get started](#get-started).

**The open Lean workbench for formal AI-safety results.**

The Atlas develops, reproduces, and audits machine-checked AI-safety mathematics:
shared definitions, theorems, counterexamples, and reviewed interpretation
bridges. Researchers use it to sharpen and discover claims; engineers may use
public facade cores as **reference specifications** inside larger assurance
arguments. Runtime systems and product stacks normally remain downstream.

Most of AI safety lives in prose and scattered proofs. This repo puts
**ingredients and primitives** on one Lean surface so impossibility, possibility,
tradeoffs, and—when computable—governance or ethics claims can be formalized
without rebuilding foundations each time. Humans and proof agents work here
together.

**Bring a question.** Alignment, control, oversight, interpretability,
robustness—if you can make a safety property precise, this is where you turn it
into something machine-checked. The seed is the Brčić–Yampolskiy impossibility
survey ([CSUR](https://doi.org/10.1145/3603371)); it is an **on-ramp, not the
ceiling**. Possibility work is welcome (e.g. DeepMind debate reproduced as
[`LAND-DEBATE-001`](docs/provenance/debate-reproduction.md); continuous free
lunches BY-022 [open](docs/guide/contributor-tasks.md#open-now)).

## Who this is for

- **Lean formalizers and AI-safety theory researchers** (and proof agents)
  developing, reproducing, or auditing formal claims.
- **Formal-methods and safety engineers** using cores as reference
  specifications or to pressure-test assumptions in a larger assurance
  argument—not as a drop-in system safety certificate.
- **Contributors** willing to make a claim precise, including with help from
  formal-methods collaborators or agents.

A theorem is **not** a system safety case. Applying it to a real system needs a
scoped reviewed bridge where relevant, implementation evidence, and the rest of
the assurance argument. Bridge review validates a scoped interpretation; it does
not by itself prove operational safety.

## Workbench status

**Primary goal:** develop, reproduce, and machine-check formal AI-safety results
(including using shared foundations to discover new ones), for AI safety and
related computable governance/ethics. **Also:** keep cores usable as reference
specifications downstream. **Not a goal:** maximizing the fraction of survey
rows graded `EXACT`/`EQUIVALENT`, or growing a product monorepo in-tree.

<!-- BEGIN GENERATED REGISTRY SCOPE -->
| Metric | Current |
|---|---:|
| Survey rows with atlas Lean | **13 / 44** |
| … statement-match (`EXACT` / `EQUIVALENT`) | **7 / 44** |
| … workbench formalizations (`RELATED` only) | **6 / 44** |
| Reviewed AI-system bridges | **2** |

`EXACT`/`EQUIVALENT` = conservative citation grade (completely
formalization-covered source statements). `RELATED` = value-based scoped
formalization, with documented deltas; it does **not by itself** mean
unfinished, but postponed until justified (paper residuals stay in
provenance).
Survey rows are a seed inventory. Detail:
[formalization status](docs/status/formalization-status.md).
<!-- END GENERATED REGISTRY SCOPE -->

Published units must rebuild under documented commands and the axiom policy
([Validation](#validation)).

## Domain imports

Prefer a facade over the full root import when starting a proof:

```lean
import AISafetyAtlas.Preference    -- planner/reward limits, override, regret
import AISafetyAtlas.Wireheading   -- reward channels, self-modification
import AISafetyAtlas.Compositional -- rectangles, hyperproperties, networks
import AISafetyAtlas.Oversight.JointObservation -- coalition evidence, coverage, collision
```

Cross-surface consumer pattern (compositional boundary + nonzero regret +
preference certificate): `AISafetyAtlas.Examples.WorkbenchConsumers`. Primary
names live in each facade docstring; root `import AISafetyAtlas` remains
available.

## Epistemic scope

A machine-checked proof establishes its encoded mathematical statement. It does
not by itself establish that the statement fully captures an informal AI-safety
claim. Math results and AI-system bridges are separate layers; bridges need
human review.

**Citation grades stay conservative:** do not raise `EXACT`/`EQUIVALENT` by
weakening fidelity. `RELATED` is a useful core with an explicit scope delta; it
does not by itself mean unfinished, and residual paper gaps remain documented.
A bridge may be `REVIEWED` while the formalization stays `RELATED` (e.g. robot).
See the [`v0.4 release scope`](docs/releases/v0.4.md) and
[`docs/guide/methodology.md`](docs/guide/methodology.md).

## Repository contents

- [`registry.yaml`](registry.yaml) is the complete survey-result inventory.
- [`AISafetyAtlas/`](AISafetyAtlas/) contains attributed Lean integrations.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) explains how to propose and verify changes.
- [`ROADMAP.md`](ROADMAP.md) presents the public strategy and contributor entry points.
- [`STATE.md`](STATE.md) reports the current phase, blockers, and next tasks.
- [`landscape.yaml`](landscape.yaml) records non–Table-1 formalizations (never
  counted as survey statement-match).
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
  (landscape `LAND-JOINTOBS-001`, not a survey row; see the
  [joint observation model](docs/guide/joint-observation-model.md))

The three latter facades contain short primary-surface tables and explicit
paper-parity non-claims. Their source maps and residual gaps are recorded in the
[A1–A3/B1–B3/B7 re-verification](docs/provenance/a1-a3-b1-b3-b7-reverification.md).

**Landscape (not survey coverage):** recorded in
[`landscape.yaml`](landscape.yaml), also on the root import when marked
`root_import: true`:

- `AISafetyAtlas.Explainability.attribution_impossibility` (DASH trilemma;
  not BY-029/BY-042 without a separate statement map)

Reproduced external formalizations that carry no Lean interface are pinned in
[`landscape.yaml`](landscape.yaml), listed in the
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
worked examples that are intentionally outside the public root import.
Kernel axiom cleanliness of the headline surface is checked by
`scripts/check_print_axioms.py`.

External reproduction of the Kolmogorov pin (upstream checkout, not the
vendored tree):

```console
scripts/reproduce_chaitin.sh
```

## Get started

Two on-ramps — take the lowest one that fits.

**Just adding a pointer?** A source that might match a survey row — no Lean, no
proof, no toolchain. You need only Python 3:

```console
scripts/setup.sh --pointer   # runs the cheap validators; no Lean toolchain
```

Then add a lead under that row's `candidate_formalizations` in
[`registry.yaml`](registry.yaml) and open a pull request.

**Writing or building a proof?** One command provisions everything — it installs
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

**Join — there is always something to do.** Docs, citation checks, leads,
examples, agent-assisted Lean, new formal claims, or reproductions. The survey
is a seed inventory, not the only path.

- **No Lean?** CT-11, CT-12, CT-14, or docs fixes
  ([open now](docs/guide/contributor-tasks.md#open-now)).
- **With an LLM/agent?** Draft against a facade → `lake build` →
  `agent_gate.sh` → `check_print_axioms.py` (see [CONTRIBUTING](CONTRIBUTING.md)).
  Green Lean is kernel validity of the encoding, not source match or system
  interpretation.
- **Have a claim to formalize?** Domain imports above + primary surfaces; prefer
  reuse of primitives over reinventing foundations.

Full tracks and rungs: [CONTRIBUTING.md](CONTRIBUTING.md). Issue forms for
proposals that change coverage, dependencies, or the public Lean interface.

## License

Apache-2.0. Individual external formalizations remain subject to their own
licenses; the registry records those licenses when verified.
