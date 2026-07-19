# Adversarial Review — Round 4 (R3 remediation)

Date: 2026-07-19
Scope: repository at `agent-work` (`0263711`), one commit after the round-3
HEAD (`9fa616f`): "fix: enforce formalization evidence invariants", touching
CI, validators, generated views, registry data, and seven documents. No Lean
source changes.
Method: as in rounds 1–3 — every fix verified against artifacts, and this
round primarily by *injection testing*: attempting the exact failures the new
invariants claim to prevent. Prior reviews: rounds 1–2
(`adversarial-review-2026-07-18*.md`), round 3
(`adversarial-review-2026-07-19-round3.md`).

## Verification performed

| Check | Result |
|---|---|
| All four validators (`validate_registry`, `generate_registry_views --check`, `validate_current_state`, `audit_release_v0_1`) | Passed |
| `xargs lake build < scripts/lean_build_targets.txt` | Passed, 908 jobs, `Examples.Robot` included |
| **Injection: orphan module** (`AISafetyAtlas/Orphan.lean`, imported by nothing) | Rejected, exit 1 |
| **Injection: `:= by sorry` appended to a released file** | Rejected, exit 1 |
| **Injection: registry `version` reverted to self-referential commit hash** | Rejected, exit 1 |
| **Injection: `Examples.Robot` dropped from the build-target manifest** | Rejected, exit 1 |
| Working tree after tests | Clean (all tamper artifacts restored) |

## Disposition of round-3 findings — all six addressed, each verified

- **R3-1 (example outside CI; recurring defect class)** — *fixed structurally,
  which is what round 3 asked for.* A single manifest
  (`scripts/lean_build_targets.txt`) now lists every intentionally-non-root
  module; CI consumes it directly (`xargs lake build < …`); and
  `validate_current_state.py` enforces the invariant: it parses every Lean
  file's imports (comment/string-masked), computes the root import closure with
  a self-tested traversal, and fails if any module is neither reachable from
  `AISafetyAtlas` nor named in the manifest — and separately fails if CI stops
  consuming the manifest. The orphan-module and dropped-target injections both
  fail loudly. This closes the defect *class*, not the instance.
- **R3-2 (rice "two layers" framing)** — *fixed by honesty rather than
  plumbing.* ROADMAP now says "two independent bridges over the computability
  facade", states that `rice` "has a root-import API contract but not yet a
  substantive domain-specific downstream theorem", and gives a technical reason
  for not routing Robot through the Rice interface (it would obscure the
  switching construction). README's API section was reworded to match
  ("independent Robot bridge … reduces directly to the halting problem"). The
  open question — whether `rice` earns its public slot — is now stated, not
  disguised. Acceptable resolution; the question itself remains open by
  admission.
- **R3-3 (RELATED counted as headline coverage)** — *fixed.* Coverage now
  requires a reproduced `EXACT`/`EQUIVALENT` record
  (`COVERAGE_RELATIONSHIPS`); the README block reads "3 of 44" with the robot
  row broken out as "1 additional result with a `RELATED` formalization only,
  outside headline coverage"; the status table gains a relationships column and
  an explanatory paragraph; CONTRIBUTING states the counting rule. The robot
  registry notes now say explicitly that RELATED "does not increase headline
  formalization coverage". This is the same bar the Chaitin candidate was held
  to — asymmetry resolved.
- **R3-4 (registry pinned a commit that squash publication would orphan)** —
  *fixed with a schema, not a patch.* Same-repository records now use
  `version: "IN_TREE"` (defined in CONTRIBUTING as "the same immutable checkout
  or release tag as the registry"), and `validate_registry.py` enforces both
  directions: an in-repository record with a commit hash fails ("must use
  version IN_TREE, not a self-referential commit" — verified by injection),
  and an external record using `IN_TREE` fails. The validator also checks the
  recorded module file exists and that the reproduction command actually builds
  it.
- **R3-5 (gate escapes)** — *fixed.* The forbidden-token scanner now includes
  `sorryAx`, `native_decide`, and `implemented_by`; the in-validator self-test
  suite gained forbidden and allowed cases for each; the appended-`sorry`
  injection on a real released file fails. Methodology and CONTRIBUTING now
  document the strict-trust policy (no trusted-base extensions) rather than
  just "no sorry".
- **R3-6/R3-7 (boundary visibility; release-doc silence; stale date)** —
  *fixed.* `docs/releases/v0.1.md` now carries the disclosure: the approval ref
  "belongs to private pre-squash local history and is not resolvable from the
  repository's public refs", with a pointer to the audit script — and the
  immutable-evidence audit still passes, so the pinned lines were not
  disturbed. The robot model document and registry notes now state the
  conditional character sharply ("the machine-checked result is … the
  conditional halting-reduction half of the paper theorem"; Lean "does not
  derive that certificate from behavioral nontriviality as the paper does").
  STATE's date and phase line are current.

## Remaining open items — all tracked, none hidden

These are not defects; each is now explicitly recorded in the repository's own
documents, which is the state rounds 1–3 pushed toward:

1. `Verification.rice` still has no downstream consumer (ROADMAP admits it;
   STATE's next tasks carry the decision).
2. The robot bridge's paper-model correspondence and interpretation remain
   `HUMAN_REVIEW` — a maintainer task, not a repository change.
3. The v0.1 approval anchor remains publicly unresolvable by deliberate,
   now-documented choice; the "ancestry-safe public attestation" decision
   stays with the maintainer. Note the disclosure sentence reaches public
   readers only when this delta lands on `main`.
4. AFP `No_Free_Lunch_ML` triage and the Chaitin-candidate reproduction are the
   two cheapest paths to a fourth (genuine, `EXACT`/`EQUIVALENT`) covered row.

## Minor observations (no action required)

- The import parser recognizes `import` and `public import`; a hypothetical
  `meta import` edge would be missed — but the failure direction is safe (a
  genuinely reachable module would be flagged as uncovered, loudly).
- The build instructions (`xargs lake build < …`) assume a POSIX shell;
  Windows contributors will need the equivalent one-liner.
- A reproduced `DEPENDENCY_ONLY`/`UNCLEAR` record would appear in the total
  records count but in neither headline bucket; cosmetic today since none
  exist.

## Verdict

Round 4 is the first round with **no new findings above minor**. Every round-3
finding was closed at the invariant level rather than the instance level —
manifest + closure check instead of a one-word CI patch, `IN_TREE` schema
instead of a rewritten hash, counting rule instead of a hand-edited number —
and all four injection tests failed loudly. The recurring-defect-class pattern
called out in round 3 was answered with exactly the right kind of fix. What
remains is review work only a human maintainer can do: the robot bridge's
semantic sign-off, the rice-interface decision, and the public approval
attestation.
