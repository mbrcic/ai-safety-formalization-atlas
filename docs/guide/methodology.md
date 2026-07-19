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

Headline formalization coverage counts a survey result only when at least one
reproduced record is `EXACT` or `EQUIVALENT`. A `RELATED` result is reported
separately and does not increase that count. This prevents a new atlas bridge
that is still under semantic review from being presented as equivalent to a
verified formalization of the surveyed statement.

Formalization licenses use SPDX identifiers. Repository URLs and any recorded
source locators must be syntactically valid HTTP(S) locations. A source locator
may remain absent when the cited bibliography does not provide a verified
online location; the validator does not invent one. Every `reproduced: true`
record names its build environment and command.

External records use an immutable upstream revision or content-addressed
archive. A formalization stored in this repository uses version `IN_TREE`:
its source is resolved in the same immutable checkout or release tag as the
registry record. This avoids an impossible self-reference in which a commit
would need to contain its own hash. Publication audits should establish the
reachability of the registry's release ref, which then anchors every `IN_TREE`
record in that tree.

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

Relevant formalizations outside the survey inventory are recorded in
[`landscape.yaml`](../../landscape.yaml) (machine-readable) and narrated in the
external-evidence documentation. The generated
[landscape index](../status/landscape-index.md) lists them. Landscape entries do **not**
enter survey-coverage counts. A landscape result may appear on the public Lean
root import (for example attribution impossibility) only when it is listed in
`landscape.yaml` with `root_import: true`. Promoting a landscape item into
`registry.yaml` as survey coverage still requires the normal admission checks.

## Formal-library discovery evidence

Every survey row receives a case-insensitive, Unicode-normalized token and
phrase search across pinned snapshots of **six classical corpora**: Mathlib,
Isabelle AFP, the Rocq Library of Undecidability, HOL4, HOL Light, and the Agda
standard library. This is a **baseline classical corpus pass**, not a complete
search of all formalizations: third-party Lean packages (for example
FormalizedFormalLogic/Foundation, KolmogorovMathlib, SocialChoiceLean, DASH)
are outside those trees and must be recorded via `candidate_formalizations` or
`landscape.yaml` when discovered manually. The query terms, corpus versions,
per-query file counts, and representative candidate paths are retained in
[`formalization-search.json`](../provenance/formalization-search.json).

A candidate path is not a verified formalization. It must be compared at the
statement level and, where practical, built in its native prover before being
added to a registry `formalizations` list. Conversely, zero phrase hits are only
scoped negative search evidence for the six corpora; they do not prove that no
formalization exists anywhere. The evidence is rebuilt with
`scripts/update_formalization_search.py`; the registry validator rejects drift
between its queries, candidate corpora, and the generated evidence.

## Progress and bridge status

`progress_status` deliberately has only two values. `MAPPED` means the survey
row and its discovery evidence are recorded but the atlas exposes no Lean
declaration for it. `LEAN_AVAILABLE` means the row exposes at least one compiled
atlas Lean declaration. External reproduction is recorded on each formalization
record rather than duplicated in progress status.

`ai_bridge_status` is separate and has a defined lifecycle vocabulary:
`HUMAN_REVIEW`, `STATEMENT_REVIEWED`, and `REVIEWED`. `HUMAN_REVIEW` (the
default) means no theorem connecting the mathematics to an AI-system claim has
passed semantic review. `STATEMENT_REVIEWED` means a maintainer has reviewed and
accepted the encoded mathematical statement of the bridge, but not its
AI-system interpretation. `REVIEWED` means both the mathematical statement and
the AI-system interpretation have passed maintainer review. It is not a general
progress state. Any status other than `HUMAN_REVIEW` requires a `bridge_review`
record (`reviewer`, `date`, `statement_reviewed`, `interpretation_reviewed`,
`evidence`); a `HUMAN_REVIEW` row must carry none. The v0.1 release shipped all
rows at `HUMAN_REVIEW`, and that historical snapshot is asserted only by the
immutable release audit (`scripts/audit_release_v0_1.py` via
[`v0.1.md`](../releases/v0.1.md)), not by ordinary current-state validation, so a genuine
future graduation can be recorded without editing a timeless validator.

A result may also carry `candidate_formalizations`: structured, non-coverage
leads for a formalization that has been discovered but not yet accepted. Each
lead records `repository`, `revision`, `framework`, `license`, `declaration`,
`inspection_state` (`UNVERIFIED`/`SOURCE_INSPECTED`/`REPRODUCED`),
`relationship_review` (`PENDING`/`EXACT`/`EQUIVALENT`/`RELATED`/`DISTINCT`/
`UNCLEAR`), and `notes`. A candidate lead never substitutes for a
`formalizations` record and never changes headline coverage; promotion still
requires reproduction and statement-level classification.

Each entry in `lean_artifact.declarations` classifies one atlas declaration as
`REFERENCE`, `WRAPPER`, `NEW_PROOF`, or `BRIDGE` and records its source
declaration(s). Classification is per declaration because one survey result may
expose both a thin wrapper and a nonredundant representation bridge.

Current status tables and registry declaration-presence checks are generated by
`scripts/generate_registry_views.py`. The separate hand-written public-API
examples protect statement shapes that cannot be inferred from registry names.

## Theorem layers

1. Existing mathematical theorem.
2. Atlas-facing Lean interface.
3. AI-safety bridge theorem.
4. Claim about an AI system or safety architecture.

Layers 3 and 4 require semantic review. A proof at layer 1 does not silently
inherit an AI-safety interpretation.

### Which declarations need bridge review?

| Declaration type | Bridge review (`ai_bridge_status`)? |
|---|---|
| `WRAPPER` / `REFERENCE` of classical math | **No** by default — classical content is not an AI-system claim. Row may still carry `HUMAN_REVIEW` until any BRIDGE on that row is reviewed. |
| `BRIDGE` with AI-facing vocabulary (agents, verifiers, safety specs, robots, …) | **Yes** before treating the row as `STATEMENT_REVIEWED` or `REVIEWED`. |
| `NEW_PROOF` of classical math only | Usually no AI bridge review unless an AI-system reading is asserted. |
| Landscape entries | Not survey `ai_bridge_status`; document scope in landscape notes / literature map. |

**Row-level status:** `ai_bridge_status` is per survey result. When a row mixes
wrappers and bridges, a `REVIEWED` status documents the **AI-facing bridge(s)**
named in `bridge_review.evidence`, not a re-review of every upstream classical
proof. State that clearly in the evidence file and release notes (see v0.2).

## New proofs and bridges

Before `NEW_PROOF` or `BRIDGE` work, add a statement-intent note beside the Lean
file. The note states objects and domains, assumptions, quantifier order,
intended conclusion, and differences from the source or informal claim.

Released Lean modules must build without `sorry`, `admit`, axioms, direct
`sorryAx`, or proof-producing shortcuts that extend the trusted base such as
`native_decide` and `@[implemented_by]`. The current-state validator masks
comments and strings, self-tests these cases, and enforces this strict-trust
policy over every atlas Lean source. Novelty, priority, first-formalization,
real-system implications, and exact capture of informal claims are never
asserted without human review.

## What validators prove (and do not)

CI and the ordinary validator suite prove a **bounded** perimeter. Passing
validation means:

- registry schema, licenses, URL syntax, and reproduction *fields* are present;
- generated views (`formalization-status`, atlas index, landscape index, README
  scope, `Registry.lean`, STATE snapshot) match source data;
- every atlas Lean module is built (root import or explicit target manifest);
- banned tokens (`sorry`, `admit`, project-local `axiom`, `sorryAx`,
  `native_decide`, `implemented_by`) are absent from atlas sources after
  comment/string masking;
- named atlas declarations in the registry elaborate (`#check` via
  `Registry.lean`);
- headline atlas theorems are kernel axiom-clean up to the three standard
  classical axioms (`scripts/check_print_axioms.py` / `#print axioms`).

Validators do **not** prove:

1. that a relationship label (`EXACT` / `EQUIVALENT` / `RELATED`) is
   semantically correct relative to the survey informal claim — that is human
   statement review;
2. that a well-typed theorem matches the intended informal or paper statement
   beyond elaborating under the given name;
3. that `source_declarations` (including Isabelle or external Lean names)
   exist outside the atlas build;
4. that `reproduced: true` commands were executed in this CI run (Isabelle and
   external Lean reproduces are offline / Docker scripts);
5. that Lake dependencies (Mathlib, Foundation) are free of project-external
   axioms beyond what `#print axioms` reports for the atlas wrapper theorems.

"Validators pass" therefore never means "coverage labels and AI-safety
interpretations are approved." Those remain under `ai_bridge_status` and human
review.

## Blocking policy

Stop work on one theorem after three materially different failed approaches, a
plausible counterexample, an unresolved statement choice, or 20% of an
autonomous work batch. Record the blocker and pivot to reusable work.
