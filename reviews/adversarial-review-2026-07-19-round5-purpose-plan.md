# Adversarial Review — Round 5 (purpose and plan)

Date: 2026-07-19  
Scope: committed `agent-work` tree at `0263711`; untracked editor/agent files and
uncommitted experimental modules were not treated as repository deliverables.  
Primary comparison: `README.md`, `ROADMAP.md`, `STATE.md`, the project
methodology, and the two private planning documents one directory above the
repository. The detailed plan's governing aims are a reliable formalization
map, a coherent and parsimonious Lean interface, and foundations for Mario's
future theorems. It also says to reuse before proving, distinguish mathematical
proof from AI-system interpretation, and expand beyond the initial survey only
when concrete work justifies the complexity.

This review complements rather than replaces round 4. Round 4 correctly found
that the immediate round-3 mechanical defects were fixed. The question here is
harder: does the resulting repository now advance its stated research purpose,
and do its own progress claims use the same bar as its plan?

## Verdict

The repository is a strong and unusually honest **v0.1 foundation**, but the
post-v0.1 branch is not yet a completed first research milestone. Its registry,
provenance discipline, stable facade, and build invariants are credible. Its
decisive layer—a semantically reviewed theorem connecting reusable mathematics
to an explicit AI-system model—still has zero results.

The immediate recommendation is **continue, but do not broaden theorem coverage
yet**. First repair the bridge-review lifecycle, correct one overstated roadmap
checkpoint, and bring the robot theorem through actual domain/semantic review.
After that, improve the atlas surface and open a small operational contributor
queue. The project should not optimize for 44/44 Lean coverage.

## What holds up under adversarial inspection

- The original v0.1 plan is substantially fulfilled and in several respects
  exceeded: all 44 survey rows are inventoried, there are 10 verified
  formalization records, 9 atlas declarations across 4 survey results, and 3
  reproduced external coverage records.
- Parsimony is real rather than rhetorical. Rice and Arrow reuse maintained
  mathematics; the utility Arrow result adds a representation interface rather
  than a duplicate core proof; the robot theorem has a distinct total-trace
  model and an explicit switching certificate.
- Epistemic boundaries are strong. The robot result is classified `RELATED`,
  does not inflate headline coverage, states that only the conditional
  halting-reduction core is checked, and excludes bounded systems, incomplete
  verification, and real-world ethical conclusions.
- The round-3 recurring defect classes were addressed structurally. Registry
  validation, generated-view drift checks, import/build closure, strict-trust
  scanning, and ancestry-safe `IN_TREE` evidence now agree.
- The committed tree passes the relevant checks: `validate_registry.py`,
  `generate_registry_views.py --check`, `validate_current_state.py`, the root
  `lake build` (905 jobs), and the explicit target-manifest build (908 jobs).

These are meaningful accomplishments. The findings below concern the gap
between a sound foundation and the project the plan ultimately describes.

## Findings

### R5-1 — Major: ordinary validation makes bridge graduation impossible

`scripts/validate_registry.py:147-148` requires every result's
`ai_bridge_status` to remain exactly `HUMAN_REVIEW`, with the explicitly
historical error text "for v0.1". This validator is part of ordinary current
state validation, not only the immutable v0.1 release audit.

At the same time:

- `docs/guide/methodology.md:89-91` defines `HUMAN_REVIEW` as meaning that no
  AI-system bridge has passed semantic review;
- `scripts/generate_registry_views.py:67-69` counts a reviewed bridge as any
  status other than `HUMAN_REVIEW`;
- the public roadmap identifies the bridge layer as the main prospective
  AI-safety research value; and
- the current headline correctly reports zero reviewed bridges.

Therefore the first successful semantic review cannot be recorded without
editing a supposedly timeless validator. This is the same release/current-state
coupling that the audit split was intended to remove, and it freezes the
project's highest-value metric at zero.

**Required correction:** define an explicit bridge-review vocabulary and
validate membership and required evidence, rather than forcing one value.
For example, keep `HUMAN_REVIEW` and add a carefully defined `REVIEWED` status,
or separate mathematical-statement review from AI-interpretation review. Keep
the all-`HUMAN_REVIEW` v0.1 assertion only in `audit_release_v0_1.py`.

Note on the fix, verified independently: the release audit already pins the
v0.1 snapshot — `docs/releases/v0.1.md:25` carries the immutable evidence line
`| Reviewed AI-system bridge theorems | 0 | Explicitly deferred |`, which
`audit_release_v0_1.py` checks. So relaxing `validate_registry.py:147-148` is
safe: the v0.1 all-`HUMAN_REVIEW` invariant survives in the release audit, and
only the *current-state* validator needs to stop forcing the value. The correct
change is therefore one-sided: replace the forced-value check with a defined
status vocabulary plus required `bridge_review` evidence. (Earlier drafts of
this note said the audit held no snapshot and that a snapshot had to be added;
that was wrong — the release-doc line is the snapshot.)

### R5-2 — Moderate: the utility/value-alignment checkpoint overstates what was achieved

`ROADMAP.md:91-98` says success means that the utility API supports at least one
"substantive downstream theorem," then marks the work implemented because the
utility-facing Arrow theorem supplies that use.

The theorem is substantive and useful. However, the repository-wide uses of
`AISafetyAtlas.SocialChoice.Utility.arrow` are only the generated declaration
check and the hand-written API smoke example. Inside `Utility.lean`, private
representation machinery is built and immediately consumed to prove the same
module's public Arrow bridge. No separate theorem consumes a stable utility
foundation, and no current theorem concerns value alignment, value comparison
between principals, or lottery/expected-utility infrastructure.

Calling this "downstream" is defensible only in the narrow sense that Arrow is
downstream of private helpers in the same implementation. It is not evidence
that the public utility API has supported independent downstream research, and
the heading "utility and value-alignment foundations" makes the checkpoint
sound broader than it is.

**Required correction:** either describe the checkpoint narrowly as a completed
utility-facing social-choice bridge while leaving the reusable/value-alignment
success criterion open, or require a distinct theorem/module that imports and
uses the public utility vocabulary for a concrete result. Do not add vNM or a
larger utility dependency merely to satisfy the wording.

### R5-3 — Moderate: the structured map cannot represent its best manually discovered lead

The repository has done valuable source inspection of
`AlexeyMilovanov/kolmogorov-complexity-lean` at pinned revision
`005ac4c81eefe09642ef561057199d489cd79485`. `docs/provenance/external-formalizations.md`
calls it a strong BY-015 candidate and records relevant Chaitin declarations,
license, toolchain, scope, and caveats. `docs/guide/open-work.md` calls it the leading
candidate.

But BY-015 still has `formalizations: []` and `candidate_corpora: []` in
`registry.yaml`, while the generated `docs/provenance/formalization-search.md` shows
"none | 0". That row is not literally false: it reports only the pinned
six-corpus phrase search, and the methodology states that this is scoped
negative evidence. The problem is structural: the machine-readable atlas has
no first-class place for a strong manually discovered lead that is not yet
accepted as coverage. Its best current Chaitin information is trapped in prose
and a free-text note.

**Required correction:** add a non-coverage structure such as
`candidate_formalizations` or `external_leads`, with repository, revision,
framework, license, source-inspection/reproduction state, proposed declaration,
and relationship-review state. Generate a view that distinguishes fixed-corpus
hits from manually verified leads. Acceptance as a formalization record should
remain behind the current reproduction and statement-matching gate.

### R5-4 — Moderate: the "atlas" is complete as data but not yet usable as an atlas

`registry.yaml` is a complete inventory, but the public generated status page
shows only the four rows that already have Lean artifacts. The only generated
44-row human-facing view is the formal-library search table, which exposes
search terms, corpus hits, and counts—not each result's claim, sources,
relationship status, candidate leads, bridge state, and next action.

Consequently a researcher can verify that all 44 rows exist, but cannot browse
the promised landscape without reading and searching a large registry file.
This falls short of the detailed plan's first value proposition: a reliable map
that saves researchers time. Deferring a website until a reviewed bridge is
reasonable; deferring a useful generated full-registry view is not.

**Required correction:** generate a compact full atlas view (one table or
per-result Markdown pages) directly from the registry. Include the informal
claim, source, formalization relationship, Lean/external status, bridge review,
candidate leads, and open work. Keep the static website deferred until usage
justifies it.

### R5-5 — Moderate: contributor readiness is documented but not operational

The repository has good contribution instructions and issue templates, and the
README invites contributions. However, the GitHub repository currently has
zero open issues and zero open pull requests. `docs/guide/open-work.md` is a useful
research backlog, but it does not provide bounded contributor tasks with owners,
acceptance criteria, and review dependencies.

For a project explicitly intended to develop in public and attract
collaborators, this leaves a gap between "contributors are welcome" and work a
new contributor can safely take. This does not justify elaborate governance;
the detailed plan correctly defers that until multiple regular contributors.

**Required correction:** open a small queue, not a new process layer. Good first
issues are: Chaitin clean-room reproduction and statement comparison; AFP No
Free Lunch triage; robot switching-certificate/domain review; Rice consumer
design; bridge-status schema; candidate-lead schema; and the generated full
atlas view. Each should state what counts as evidence and what does not change
coverage.

## Strategic status against the detailed plan

| Plan outcome | Honest current state |
|---|---|
| Reliable map of existing formalizations | Strong inventory and provenance; weak browsing and incomplete structured candidate representation |
| Coherent, parsimonious Lean interface | Achieved for the current small surface; Rice verification still needs a real consumer or eventual removal |
| Foundation for Mario's future theorems | Promising but not demonstrated by a reviewed downstream theorem |
| Survey-first v0.1 | Done |
| Reuse before proving | Done consistently in reviewed work |
| Explicit theorem/interface/bridge/system-claim layers | Designed and documented well; bridge graduation workflow is broken |
| Utility and value-alignment foundation | Utility-facing Arrow bridge done; broader/reusable success criterion not yet met |
| Precise verification/containment limit | Conditional machine-checked core exists; semantic and paper-model review still pending |
| Public collaboration | Repository is prepared, but there is no operational work queue |
| Careful broader expansion | Correctly not yet attempted at breadth |

The private detailed plan is therefore **not all done**, nor should it be: it is
a multi-phase plan extending well beyond v0.1. The v0.1 release phase is done.
The current post-v0.1 phase has produced credible bridge candidates and strong
infrastructure, but has not yet satisfied the plan's decisive reviewed-
downstream-use criterion.

## Highest-leverage next sequence

1. Remove the permanent all-`HUMAN_REVIEW` gate and define review evidence.
2. Reword the utility checkpoint so completion claims match the actual theorem.
3. Obtain maintainer and domain review of the robot theorem's statement,
   switching-construction boundary, and `RELATED` classification; record the
   result using the repaired lifecycle.
4. Decide whether `Verification.rice` has a concrete downstream theorem. Keep it
   only if the stable semantic-to-code interface earns its maintenance cost.
5. Add structured candidate leads and generate a complete human-facing atlas.
6. Open 6–8 bounded GitHub issues from the existing research backlog.
7. Only then choose the next theorem. Chaitin is a strong low-friction reuse
   candidate; a reviewed AI-system bridge remains strategically more important
   than raising the raw survey-coverage count.

## Bottom line

There is no reason to reverse course. The repository's strongest asset is its
epistemic constitution, and the post-v0.1 mechanical work now supports that
constitution well. The risk is subtler: declaring implementation checkpoints
complete because code compiles, while the plan's actual success conditions are
semantic review, downstream reuse, researcher usability, and public
collaboration.

Fix the lifecycle that currently forbids success, graduate one bridge through
real review, and make the full map usable. That would turn the current strong
foundation into the beginning of the research institution described by the
plan.

## Independent verification addendum

A second reviewer re-ran the load-bearing checks in this review against the
`0263711` tree. No factual errors were found; the following were confirmed:

- **R5-1** — `validate_registry.py:147-148` unconditionally fails any result
  whose `ai_bridge_status != "HUMAN_REVIEW"` (error text: "must remain
  HUMAN_REVIEW for v0.1"); `docs/guide/methodology.md:89` and
  `generate_registry_views.py:68` agree on the intended meaning. The v0.1
  snapshot is separately pinned by the immutable release-doc line
  `docs/releases/v0.1.md:25`, which the release audit checks, so relaxing the
  current-state validator is safe (see the remedy note above).
- **R5-3** — `registry.yaml` BY-015 carries `formalizations: []` and
  `formal_library_search.candidate_corpora: []`; the
  `AlexeyMilovanov/kolmogorov-complexity-lean` lead exists only in the free-text
  `notes` field and `docs/provenance/external-formalizations.md`. Confirmed structural gap.
- **R5-4** — `generate_registry_views.py` writes only `docs/status/formalization-status.md`
  and `README.md`; no per-result or full 44-row human-facing view is generated
  besides the fixed-corpus search table. Confirmed.
- **R5-5** — `gh issue list --state open` returns empty; no operational queue
  exists. Confirmed.

The most consequential finding remains **R5-1**: the project's highest-value
metric (reviewed bridges) is pinned at zero by a validator that runs on every
working tree, not just the frozen release. Everything else is refinement.

## Resolution (implemented 2026-07-19)

The structural findings were fixed on the working tree; all four validators and
the manifest `lake build` remain green.

- **R5-1 — fixed.** `validate_registry.py` now validates `ai_bridge_status`
  against a defined vocabulary (`HUMAN_REVIEW`/`STATEMENT_REVIEWED`/`REVIEWED`)
  and requires a well-formed `bridge_review` record (reviewer, date, two review
  flags, evidence) for any graduated status, with consistency checks. The forced
  "must remain HUMAN_REVIEW for v0.1" check is gone; the v0.1 snapshot stays in
  the release audit. Seven lifecycle cases were unit-tested (clean HUMAN_REVIEW
  accepts; stray review rejects; graduation without/with evidence rejects/
  accepts; inconsistent flags reject).
- **R5-2 — fixed.** The ROADMAP utility checkpoint is reworded to "partially
  implemented": the utility-facing Arrow bridge is done, but the reusable-
  foundation / value-alignment success criterion is stated as still open.
- **R5-3 — fixed.** A structured `candidate_formalizations` schema was added and
  validated; the Chaitin BY-015 lead (repo, revision, declaration, license,
  inspection state, review state) is now first-class registry data, not prose.
- **R5-4 — fixed.** `generate_registry_views.py` now emits `docs/status/atlas-index.md`,
  a generated 44-row human view (claim, source relationship, bridge state,
  candidate-lead count).
- **R5-5 — partially addressed.** `docs/guide/contributor-tasks.md` records bounded
  tasks with acceptance evidence and non-goals. Creating the public GitHub
  issue queue from it is an outward-facing action left to the maintainer.

Methodology and CONTRIBUTING were updated to document the bridge lifecycle and
the candidate-lead schema.
