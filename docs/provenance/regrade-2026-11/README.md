# Regrade 2026-11: published provenance

The statement-by-statement source audit (`docs/provenance/source-coverage-audit.md`) was regraded for
v0.10.0: blind grading by several models, grounded adjudication where they split or a ruling applied,
author rulings on readings print does not settle, then migration to SPEC v6
(`docs/guide/scope-grading.md`).

| Path | What it holds |
|---|---|
| `final-grades.tsv` | the final scope and coverage of every graded row, and what decided it |
| `RULINGS-PENDING.md` | the author's rulings register (ruled and still open) |
| `ADJUDICATION-LOG.md` | the adjudication briefs and rulings, in order |
| `spec/` | SPEC v5 and v6, the mapping between them, and the reviews of the spec |
| `v6-impact/` | the v6 pass: rulings given to graders, prompts, grounded adjudications (`adjudication/`), Lean transfer and closure records, `OUTCOME.md` |
| `scripts/fix_audit_tallies.py` | regenerates the audit's section tallies |

Not published: raw grader transcripts, grading packets, the per-source working notes ("source cards"),
intermediate grading rounds, referee and
cross-check records, and the per-grader aggregates. The Lean that the grades rest on is in the
library, `docs/provenance/refutations/` and `docs/provenance/transfers/`.
