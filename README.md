# AI Safety Formalization Atlas

[![CI](https://github.com/mbrcic/ai-safety-formalization-atlas/actions/workflows/ci.yml/badge.svg)](https://github.com/mbrcic/ai-safety-formalization-atlas/actions/workflows/ci.yml)

A Lean-centered map of machine-checked mathematics relevant to AI safety.

The initial collection tracks every result listed in Mario Brčić and Roman V.
Yampolskiy's *Impossibility Results in AI: A Survey* (ACM Computing Surveys,
DOI [`10.1145/3603371`](https://doi.org/10.1145/3603371), arXiv
[`2109.00484`](https://arxiv.org/abs/2109.00484)). It records where results have
been formalized, reuses maintained Lean declarations, and identifies genuine
formalization gaps.

## Current scope

<!-- BEGIN GENERATED REGISTRY SCOPE -->
The current registry has verified `EXACT` or `EQUIVALENT` formalization coverage for
**7 of 44** survey results. It records **1 additional result with a
`RELATED` formalization only**, outside headline coverage, and
**2 survey results with reviewed AI-system bridges**. It provides
infrastructure for further formalization; it does not claim complete formal
coverage. See the current [formalization status](docs/status/formalization-status.md).
<!-- END GENERATED REGISTRY SCOPE -->

## Epistemic scope

A machine-checked proof establishes its encoded mathematical statement. It does
not by itself establish that the statement fully captures an informal AI-safety
claim. Classical results and AI-safety bridge claims are documented as separate
layers, and uncertain semantic relationships are marked for human review.
**Reviewed AI-system bridges are not additional headline `EXACT`/`EQUIVALENT`
coverage** (e.g. the robot formalization remains `RELATED` only). See
[`docs/releases/v0.2.md`](docs/releases/v0.2.md) for the current release
non-claims.

## Repository contents

- [`registry.yaml`](registry.yaml) is the complete survey-result inventory.
- [`AISafetyAtlas/`](AISafetyAtlas/) contains attributed Lean integrations.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) explains how to propose and verify changes.
- [`ROADMAP.md`](ROADMAP.md) presents the public strategy and contributor entry points.
- [`STATE.md`](STATE.md) reports the current phase, blockers, and next tasks.
- [`landscape.yaml`](landscape.yaml) records non–Table-1 formalizations (never headline survey coverage).
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

## Build

Install Lean through [`elan`](https://lean-lang.org/install/manual/), then run:

```console
lake update
lake build
xargs lake build < scripts/lean_build_targets.txt
```

The repository pins both Lean and Mathlib. Released Lean files follow the
[strict-trust and build-closure policy](docs/guide/methodology.md#new-proofs-and-bridges).

## Contributing

Contributions in source verification, reproducibility, API review, bridge
design, and Lean implementation are welcome. Start with the
[contribution guide](CONTRIBUTING.md) and use the structured issue forms for
work that changes coverage, dependencies, or the public Lean interface.

## License

Apache-2.0. Individual external formalizations remain subject to their own
licenses; the registry records those licenses when verified.
