# Staged `AGENTS.md` migration ledger

> Review record, not agent instruction. Do not add this file to default agent
> context or treat it as a second policy source.

## Baseline

The sole migration source is `upstream/main:AGENTS.md` at commit
[`470069d18beb62597aaea47a264e5703941f1859`](https://github.com/mbrcic/ai-safety-formalization-atlas/blob/470069d18beb62597aaea47a264e5703941f1859/AGENTS.md)
(617 lines, 38,496 bytes). It includes lines 248–276, “Conditional results,
and the debt they create,” added by upstream
[`#56`](https://github.com/mbrcic/ai-safety-formalization-atlas/commit/87b4c4c7ace15d8f3cc175c66782f75df55086c6).
That section transfers with `Statement freeze`; it is not a later policy
addition to this migration.

## Quick review

The ten non-overlapping transfers below cover every instruction line from 8
through 617 of the baseline. No instruction wording, command, number, caveat,
or example was deleted, compressed, or rewritten. The only source-text
normalizations are 19 relative Markdown-link paths (each preserves its resolved
target) and one terminal empty line in nine destination files.

The destination names use task-category prefixes only; this phase does not
combine policy files or alter the transferred text.

| Baseline lines | Destination | Mechanical normalization |
|---|---|---|
| 8–157 | [`context-budget.md`](policy/context-budget.md) | 17 links; terminal empty line |
| 158–183 | [`lean-public-api.md`](policy/lean-public-api.md) | terminal empty line |
| 184–215 | [`lean-parsimony.md`](policy/lean-parsimony.md) | 1 link; terminal empty line |
| 216–380 | [`lean-statement-freeze.md`](policy/lean-statement-freeze.md) | terminal empty line; includes upstream #56 (lines 248–276) |
| 381–418 | [`ledger-coverage.md`](policy/ledger-coverage.md) | 1 link; terminal empty line |
| 419–441 | [`ledger-documentation.md`](policy/ledger-documentation.md) | terminal empty line |
| 442–452 | [`workflow-branch-publication.md`](policy/workflow-branch-publication.md) | terminal empty line |
| 453–494 | [`lean-proving.md`](policy/lean-proving.md) | terminal empty line |
| 495–611 | [`workflow-validation.md`](policy/workflow-validation.md) | terminal empty line |
| 612–617 | [`workflow-wording.md`](policy/workflow-wording.md) | none |

## Refactor invariants

- Until a transfer commit says otherwise, the source text remains the only
  authoritative instruction.
- A transfer records the exact source range, destination, and every deliberate
  edit. "Verbatim" means no wording, rule, command, caveat, number, or example
  changed; Markdown path normalization is listed separately.
- Do not remove text merely to shorten the root. A deliberate removal needs a
  review reason and a separate disposition.
- Do not mix a mechanical transfer with new security policy, vendor adapters,
  prompt-design guidance, dependency changes, or unrelated validation changes.
- `scripts/preflight.py` currently slices named headings from `AGENTS.md` at
  runtime. A move of a referenced heading must update that routing in the same
  commit and prove the new route prints the same obligation.

## Source inventory

Ranges are inclusive. A parent heading's range intentionally includes its child
rows; the overlap makes the hierarchy visible rather than implying duplicate
content. This inventory was recorded before relocation; its statuses below show
the current state while preserving the baseline locations for review.

| # | Current heading | Lines | `preflight.py` consumer | Status |
|---:|---|---:|---|---|
| 1 | `Context budget (agents)` | 8–157 | — | Moved; links and EOF normalized |
| 2 | `Start here (small by design)` | 10–36 | — | Moved with `Context budget` |
| 3 | `Do not read by default` | 37–54 | — | Moved with `Context budget` |
| 4 | `Lean surface rule` | 55–81 | `lean-library` | Moved with `Context budget` |
| 5 | `Examples layout rule` | 82–109 | `lean-examples` | Moved with `Context budget` |
| 6 | `Tactics and search surface` | 110–126 | — | Moved with `Context budget` |
| 7 | `Every library module needs a worked model` | 127–146 | `lean-library`, `lean-examples` | Moved with `Context budget` |
| 8 | `Cheap vs full validation` | 147–157 | — | Moved with `Context budget` |
| 9 | `Public Lean API` | 158–183 | — | Moved; content unchanged, EOF normalized |
| 10 | `Parsimony (formalizations)` | 184–215 | `lean-library` | Moved; link and EOF normalized |
| 11 | `Statement freeze` | 216–380 | `lean-library` | Moved; content unchanged, EOF normalized |
| 12 | `Conditional results, and the debt they create` | 248–276 | — | Moved with `Statement freeze`; added by upstream #56 |
| 13 | `The layer a text diff cannot reach` | 277–380 | — | Moved with `Statement freeze` |
| 14 | `Coverage, landscape, and bridges` | 381–418 | `ledger` | Moved; link and EOF normalized |
| 15 | `Documentation layout` | 419–441 | `generated`, `docs` | Moved; content unchanged, EOF normalized |
| 16 | `Branch, version, and publication` | 442–452 | — | Moved; content unchanged, EOF normalized |
| 17 | `Proving: tactic order and the exploration target` | 453–494 | — | Moved; content unchanged, EOF normalized |
| 18 | `Validation` | 495–611 | `tooling` | Moved; content unchanged, EOF normalized |
| 19 | `The \`--fast\` lane (\`--lean\` is the old name)` | 513–611 | included by `Validation` | Moved with `Validation` |
| 20 | `Audience and wording` | 612–617 | `docs` | Moved verbatim |

## Transfer receipt template

Each future transfer adds one row here before its source block is removed:

| Source range | Destination | Status | Deliberate edits | Routing and validation evidence |
|---|---|---|---|---|
| _Example: lines 000–000_ | _path and heading_ | _verbatim / link-normalized / rewritten / removed_ | _none or exact reason_ | _exact command and result_ |

| `470069d:AGENTS.md` lines 419–441 | [`ledger-documentation.md`](policy/ledger-documentation.md) | Content verbatim; EOF normalized | One terminal blank line removed | Normalized `cmp` and `preflight` output comparison |
| `470069d:AGENTS.md` lines 381–418 | [`ledger-coverage.md`](policy/ledger-coverage.md) | Content verbatim; link and EOF normalized | One relative link and one terminal blank line normalized | Normalized `cmp`, path check, and `preflight` output comparison |
| `470069d:AGENTS.md` lines 442–452 | [`workflow-branch-publication.md`](policy/workflow-branch-publication.md) | Content verbatim; EOF normalized | One terminal blank line removed | Normalized `cmp` and path check |
| `470069d:AGENTS.md` lines 612–617 | [`workflow-wording.md`](policy/workflow-wording.md) | Verbatim move | None | Exact `cmp` and `preflight` output comparison |
| `470069d:AGENTS.md` lines 453–494 | [`lean-proving.md`](policy/lean-proving.md) | Content verbatim; EOF normalized | One terminal blank line removed | Normalized `cmp` and path check |
| `470069d:AGENTS.md` lines 495–611 | [`workflow-validation.md`](policy/workflow-validation.md) | Content verbatim; EOF normalized | One terminal blank line removed | Normalized `cmp`, `preflight`, and full-gate output comparison |
| `470069d:AGENTS.md` lines 158–183 | [`lean-public-api.md`](policy/lean-public-api.md) | Content verbatim; EOF normalized | One terminal blank line removed | Normalized `cmp` and path check |
| `470069d:AGENTS.md` lines 184–215 | [`lean-parsimony.md`](policy/lean-parsimony.md) | Content verbatim; link and EOF normalized | One relative link and one terminal blank line normalized | Normalized `cmp`, path check, and `preflight` output comparison |
| `470069d:AGENTS.md` lines 216–380 | [`lean-statement-freeze.md`](policy/lean-statement-freeze.md) | Content verbatim; EOF normalized | One terminal blank line removed; includes upstream #56 section (lines 248–276) | Normalized `cmp`, `preflight`, and full-gate output comparison |
| `470069d:AGENTS.md` lines 8–157 | [`context-budget.md`](policy/context-budget.md) | Content verbatim; links and EOF normalized | 17 relative-link occurrences and one terminal blank line normalized | Path-resolved comparison, `preflight`, and full-gate output comparison |
