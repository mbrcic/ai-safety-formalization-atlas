# Historical adversarial reviews

These files record past adversarial review rounds against earlier trees. They
are **historical process artifacts**, not live tasking or acceptance criteria.

## For agents

**Do not load this directory by default.** Prefer:

- [`STATE.md`](../STATE.md) — current phase and coverage snapshot
- [`docs/guide/open-work.md`](../docs/guide/open-work.md) — research queue
- [`docs/guide/contributor-tasks.md`](../docs/guide/contributor-tasks.md) — bounded work units
- [`docs/agent/INDEX.md`](../docs/agent/INDEX.md) — cheap navigation

Read a **single** named review only when the maintainer cites a round or finding
(for example “round 7 integrity item R7-x”). Do not re-litigate historical
rounds into new commits unless asked. Do not load the whole directory.

## Round index (open one file only)

| File | Round | Focus |
|---|---|---|
| [`adversarial-review-2026-07-18.md`](adversarial-review-2026-07-18.md) | 1 | v0.1 RC full-repo review |
| [`adversarial-review-2026-07-18-round2.md`](adversarial-review-2026-07-18-round2.md) | 2 | Follow-up / disposition |
| [`adversarial-review-2026-07-19-round3.md`](adversarial-review-2026-07-19-round3.md) | 3 | Continued remediation |
| [`adversarial-review-2026-07-19-round4.md`](adversarial-review-2026-07-19-round4.md) | 4 | Continued remediation |
| [`adversarial-review-2026-07-19-round5-purpose-plan.md`](adversarial-review-2026-07-19-round5-purpose-plan.md) | 5 | Purpose / plan alignment |
| [`adversarial-review-2026-07-19-round6.md`](adversarial-review-2026-07-19-round6.md) | 6 | Integrity / coverage claims |
| [`adversarial-review-2026-07-19-round7-integrity.md`](adversarial-review-2026-07-19-round7-integrity.md) | 7 | Integrity |
| [`adversarial-review-2026-07-19-round8-prepublic.md`](adversarial-review-2026-07-19-round8-prepublic.md) | 8 | Pre-public |
| [`adversarial-review-2026-07-19-round9-prepublic.md`](adversarial-review-2026-07-19-round9-prepublic.md) | 9 | Pre-public |

Live work lives in `STATE.md` and the guide docs, not in these rounds.

## For humans

Round notes remain useful for release archaeology and purpose/plan checks. They
are intentionally outside `docs/` so they are not mixed with methodology,
status tables, or bridge packages. Archiving older rounds off the default
branch is optional maintainer hygiene; while present, treat them as read-only
history.
