# v0.1 Release

- Prepared: 2026-07-18
- Candidate branch: `agent-work`
- Approval ref: `e9fdfc06f2c599b00210eba17f66985bca4c002e`
- Publication status: approved for publication

## Objective evidence

| Criterion | Evidence | Status |
|---|---|---|
| Compiling Lean repository | `lake build` succeeds on the pinned toolchain | Passed |
| CI | `.github/workflows/ci.yml` builds Lean and audits registry/release data | Configured |
| Apache-2.0 | Root `LICENSE` | Passed |
| Complete survey inventory | `registry.yaml`: 44/44 Table 1 rows | Passed |
| Cross-framework discovery | 44/44 rows searched across six pinned corpora | Passed |
| Verified formalization records | 9 records | Passed |
| Lean facade or bridge theorems | 7 compiled declarations | Passed |
| Verified survey-row coverage | 3 of 44 results | Explicitly partial |
| Reviewed AI-system bridge theorems | 0 | Explicitly deferred |
| Worked example | Compiling fixed-input halting example, outside the public API | Passed |
| External reproduction | Rice and Arrow Isabelle/HOL sessions | Passed |
| Methodology | `docs/methodology.md` | Passed |
| Clear open work | `docs/open-work.md` | Passed |
| No incomplete Lean proofs | Release audit scans all released Lean files | Passed |
| Mandatory disclaimer | README epistemic-scope section | Passed |
| Private until approval | Authenticated Git remote reachable; anonymous URL returned 404 before approval | Passed |
| Mario approval | Approved for immutable ref `e9fdfc06f2c599b00210eba17f66985bca4c002e` | Passed |

Run the local release gates with:

```console
python3 scripts/validate_registry.py
python3 scripts/audit_release.py
lake build
```

External builds can be repeated independently with:

```console
scripts/reproduce_isabelle.sh all
```

## Approval boundary

Approval should cover the README framing, high-profile relationship labels,
worked-example presentation, and decision to publish. Approval does not convert
all `HUMAN_REVIEW` bridge fields into accepted AI-safety claims.
