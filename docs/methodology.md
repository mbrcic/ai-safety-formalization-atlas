# Methodology

## Evidence order

For each survey result:

1. Identify the survey row and cited original source.
2. Search Mathlib and other maintained Lean repositories.
3. Search maintained formalizations in other proof assistants.
4. Reproduce external builds where practical.
5. Attempt a new Lean proof only when the result is missing, useful, and tractable.

Records distinguish an exact statement from an equivalent, related,
dependency-only, or unclear formalization. A repository name or search hit is
not enough: verified records include the version, module/file, declaration, and
license.

## Parsimony and source roles

A survey result is counted once regardless of how many provers, proofs, or
representations establish it. Formalization records are evidence records, not
additional theorem-coverage claims.

For the public Lean API, select one canonical maintained result when one is
available and expose only the atlas aliases and bridges needed by downstream
work. If no maintained package is available, use a pinned, licensed, audited
source and record that the atlas assumes its version-migration burden. An
alternative proof remains provenance unless it adds a documented capability
such as a stronger statement, a required representation, an explicit
composable reduction, useful constructive content, or necessary dependency
independence.

Research reports and literature surveys are discovery inputs. Claims from them
enter the verified registry only after checking a primary source, an immutable
revision, the declaration itself, the license, and, where practical, a local
build.

## Formal-library discovery evidence

Every survey row receives a case-insensitive, Unicode-normalized token and
phrase search across pinned snapshots of Mathlib, Isabelle AFP, the Rocq
Library of Undecidability, HOL4, HOL Light, and the Agda standard library. The
query terms, corpus versions, per-query file counts, and representative
candidate paths are retained in
[`formalization-search.json`](formalization-search.json).

A candidate path is not a verified formalization. It must be compared at the
statement level and, where practical, built in its native prover before being
added to a registry `formalizations` list. Conversely, zero phrase hits are only
scoped negative search evidence; they do not prove that no formalization exists.
The evidence is rebuilt with `scripts/update_formalization_search.py`; the
registry validator rejects drift between its queries, candidate corpora, and
the generated evidence.

## Progress and bridge status

`progress_status` deliberately has only two values. `MAPPED` means the survey
row and its discovery evidence are recorded but the atlas exposes no Lean
declaration for it. `LEAN_AVAILABLE` means the row exposes at least one compiled
atlas Lean declaration. External reproduction is recorded on each formalization
record rather than duplicated in progress status.

`ai_bridge_status` is separate. `HUMAN_REVIEW` means no theorem connecting the
mathematics to an AI-system claim has passed semantic review. It is not a
general progress state.

## Theorem layers

1. Existing mathematical theorem.
2. Atlas-facing Lean interface.
3. AI-safety bridge theorem.
4. Claim about an AI system or safety architecture.

Layers 3 and 4 require semantic review. A proof at layer 1 does not silently
inherit an AI-safety interpretation.

## New proofs and bridges

Before `NEW_PROOF` or `BRIDGE` work, add a statement-intent note beside the Lean
file. The note states objects and domains, assumptions, quantifier order,
intended conclusion, and differences from the source or informal claim.

Released Lean modules must build without `sorry`. Novelty, priority,
first-formalization, real-system implications, and exact capture of informal
claims are never asserted without human review.

## Blocking policy

Stop work on one theorem after three materially different failed approaches, a
plausible counterexample, an unresolved statement choice, or 20% of an
autonomous work batch. Record the blocker and pivot to reusable work.
