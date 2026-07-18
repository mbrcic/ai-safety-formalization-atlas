# AI Safety Formalization Atlas

A Lean-centered map of machine-checked mathematics relevant to AI safety.

The initial collection tracks every result listed in Mario Brčić and Roman V.
Yampolskiy's *Impossibility Results in AI: A Survey* (ACM Computing Surveys,
DOI [`10.1145/3603371`](https://doi.org/10.1145/3603371), arXiv
[`2109.00484`](https://arxiv.org/abs/2109.00484)). It records where results have
been formalized, reuses maintained Lean declarations, and identifies genuine
formalization gaps.

## Current scope

The v0.1 baseline has verified formalization records for **3 of 44** survey
results and **0 reviewed AI-system bridge theorems**. It provides infrastructure
for further formalization; it does not claim complete formal coverage. See the
current [formalization status](docs/formalization-status.md).

## Epistemic scope

A machine-checked proof establishes its encoded mathematical statement. It does
not by itself establish that the statement fully captures an informal AI-safety
claim. Classical results and AI-safety bridge claims are documented as separate
layers, and uncertain semantic relationships are marked for human review.

## Repository contents

- [`registry.yaml`](registry.yaml) is the complete survey-result inventory.
- [`AISafetyAtlas/`](AISafetyAtlas/) contains attributed Lean integrations.
- [`ROADMAP.md`](ROADMAP.md) presents the public strategy and contributor entry points.
- [`docs/methodology.md`](docs/methodology.md) defines evidence and review rules.
- [`docs/formalization-status.md`](docs/formalization-status.md) summarizes current coverage.
- [`docs/external-formalizations.md`](docs/external-formalizations.md) records reproducibility checks outside Lean.
- [`docs/formalization-search.md`](docs/formalization-search.md) records the pinned six-corpus discovery pass for every survey row.
- [`docs/open-work.md`](docs/open-work.md) lists unresolved review and formalization work.
- [`docs/release-v0.1.md`](docs/release-v0.1.md) records release-candidate evidence and the approval gate.
- [`STATE.md`](STATE.md) reports the current phase, blockers, and next tasks.

## Build

Install Lean through [`elan`](https://lean-lang.org/install/manual/), then run:

```console
lake update
lake build
```

The repository pins both Lean and Mathlib. Released Lean files contain no
`sorry`.

## License

Apache-2.0. Individual external formalizations remain subject to their own
licenses; the registry records those licenses when verified.
