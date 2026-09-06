# Contributor and Agent Guidance

Read this file before an autonomous change. Live phase: [`STATE.md`](STATE.md).
Agent map: [`docs/agent/INDEX.md`](docs/agent/INDEX.md). Human doc map:
[`docs/README.md`](docs/README.md). Methodology:
[`docs/guide/methodology.md`](docs/guide/methodology.md).

## Start

For a change, run `python3 scripts/preflight.py`, then read only the policies it
identifies. The script advises; [`scripts/agent_gate.sh`](scripts/agent_gate.sh)
performs the mechanical validation.

## Task-specific policy

| Work | Read |
|---|---|
| Context selection and repository navigation | [`context-budget.md`](docs/agent/policy/context-budget.md) |
| Public Lean API | [`lean-public-api.md`](docs/agent/policy/lean-public-api.md) |
| Lean parsimony | [`lean-parsimony.md`](docs/agent/policy/lean-parsimony.md) |
| Where to search before building, and what a novelty claim may cite | [`lean-reuse-sources.md`](docs/agent/policy/lean-reuse-sources.md) |
| Statement fidelity and toolchain drift | [`lean-statement-freeze.md`](docs/agent/policy/lean-statement-freeze.md) |
| Coverage, ledgers, and bridges | [`ledger-coverage.md`](docs/agent/policy/ledger-coverage.md) |
| Documentation ownership and generated views | [`ledger-documentation.md`](docs/agent/policy/ledger-documentation.md) |
| Branches, versions, and publication | [`workflow-branch-publication.md`](docs/agent/policy/workflow-branch-publication.md) |
| Lean proof exploration | [`lean-proving.md`](docs/agent/policy/lean-proving.md) |
| Validation | [`workflow-validation.md`](docs/agent/policy/workflow-validation.md) |
| Audience and wording | [`workflow-wording.md`](docs/agent/policy/workflow-wording.md) |
