# Contributing

Thank you for helping make formal mathematics relevant to AI safety easier to
find, verify, and reuse. Contributions may improve evidence, documentation, the
stable Lean interface, or carefully scoped bridge theorems.

## Before starting

For anything that changes formalization coverage, dependencies, or the public
Lean API, open a formalization proposal issue first. Small factual corrections
and documentation fixes may go directly to a pull request.

Read the [roadmap](ROADMAP.md), [methodology](docs/methodology.md), and
[public API and parsimony policy](AGENTS.md). In particular:

- reuse a maintained theorem before writing another proof;
- expose one canonical atlas declaration per result;
- justify any additional representation or proof by its unique downstream
  value;
- keep mathematical theorems separate from claims about AI systems; and
- treat search hits as leads, not verified formalizations.

## Development setup

Install Lean with [`elan`](https://lean-lang.org/install/manual/). The repository
pins its Lean toolchain and Mathlib revision. From the repository root, run:

```console
lake update
lake build
python3 scripts/validate_registry.py
python3 scripts/audit_release.py
```

Lean changes must compile without `sorry`, `admit`, or new axioms. If a change
only affects documentation or registry evidence, still run both Python checks.

## Evidence and registry changes

A verified formalization record needs an immutable version, exact module or
file, declaration name, relationship to the surveyed statement, license, and
reproduction status. Prefer primary sources. Do not infer coverage from a paper
title, repository description, or keyword match.

`docs/formalization-search.json` is generated evidence. When search terms or
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
Bridge interpretation remains subject to separate human review.

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
