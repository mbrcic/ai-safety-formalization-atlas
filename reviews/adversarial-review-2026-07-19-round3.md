# Adversarial Review — Round 3 (robot-verification bridge and R2 remediation)

Date: 2026-07-19
Scope: repository at `agent-work` (`9fa616f`), eight commits after the round-2
HEAD (`fb00d38`): the R2-1–R2-5 remediation, the new reactive robot-verification
bridge (`AISafetyAtlas.Verification.Robot`), its registry row, and the
algorithmic-information candidate record.
Method: same as rounds 1–2 — every checkable claim re-executed against
artifacts, none accepted from documents or commit messages. Prior reviews:
`adversarial-review-2026-07-18.md`, `adversarial-review-2026-07-18-round2.md`.

## Verification performed

| Check | Result |
|---|---|
| `lake build` of CI target list (PublicAPI, Registry, HaltingExample) | Passed, 907 jobs, exit 0 |
| `lake build AISafetyAtlas.Examples.Robot` (separate, not in CI list) | Passed, exit 0 |
| `validate_registry.py` / `generate_registry_views.py --check` / `validate_current_state.py` / `audit_release_v0_1.py` | All passed |
| Hardened `sorry` gate, adversarial injection tests (10 cases incl. `:= sorry`, `by sorry`, `exact sorry`, `admit`, `axiom`, comment/string/nested-comment negatives) | All caught / correctly allowed; only a direct `sorryAx` term call escapes the scanner (see R3-5) |
| `lakefile.toml` `warningAsError = true` | Present; full build passes under it |
| `action_safety_unverifiable` proof | Hand-checked from source; sound (composition of computable maps, iff-chain to non-halting, complement, contradiction with `halting_problem`) |
| `Examples/Robot.lean` non-vacuity witness | Hand-checked; sound (`evaln` pacing, `evaln_complete`/`evaln_sound` both directions) |
| Cited paper (van Leeuwen & Wiedermann UU-PCS-2021-02) | Fetched from the pinned archive.org locator; Theorem 1 and Corollary 1 statements extracted and compared (see R3-6) |
| Chaitin candidate (`AlexeyMilovanov/kolmogorov-complexity-lean` @ `005ac4c8…`) | Repo exists; pinned rev = current `main` HEAD; `chaitinBound`/`chaitinIncompleteness`/`chaitinGeneralized` present at claimed file; full-tree scan of all 79 `.lean` files found no `sorry`/`admit`/`axiom`; `lean-toolchain` = v4.31.0 and license Apache-2.0, both as documented |
| Approval-anchor audit output | Reports `anchor local-only (available only in local history; not publicly reproducible)` |
| README generated scope block | "4 of 44", "0 reviewed AI-system bridges" — matches registry |

## Disposition of round-2 findings

- **R2-1 (dangling public approval ref)** — *mitigated, deliberately left open.*
  `audit_release_v0_1.py` now resolves the ref with `git cat-file`/
  `for-each-ref` and classifies reachability; on this clone it honestly prints
  "local-only … not publicly reproducible". The team chose transparency over
  publishing the pre-squash ancestry, and STATE's next-task 3 explicitly tracks
  an "ancestry-safe public v0.1 approval attestation" pending maintainer
  authorization. That is a defensible resolution. Residual gap: the *release
  document itself* on public `main` was not amended — a reader of
  `docs/releases/v0.1.md` who does not run the audit script still sees an
  approval ref with no indication it cannot be resolved publicly (see R3-7).
- **R2-2 (`sorry` gate cannot catch normal forms)** — *fixed well.* The new
  `lean_code_without_comments_or_strings` masker plus an unanchored
  `\b(sorry|admit|axiom)\b` scan catches every adversarial form tested,
  correctly ignores comments (including nested block comments), docstrings,
  and string literals, and the validator now self-tests its own scanner against
  forbidden and allowed examples on every run — a genuinely good pattern.
  Independently, `warningAsError = true` promotes the build-time
  "declaration uses 'sorry'" warning to an error. Defense in depth; both
  layers verified.
- **R2-3 (halting example outside CI build closure)** — *fixed.* CI's build
  step now names `AISafetyAtlas.Survey.BrcicYampolskiy.HaltingExample`;
  verified in the 907-job build. However the fix was not applied as a policy —
  the very next commit reintroduced the same gap for the new example file (R3-1).
- **R2-4 (open-work NFL guidance contradicted own evidence)** — *fixed.* The
  NFL item now targets statement-level triage of AFP `No_Free_Lunch_ML` with a
  concrete acceptance gate.
- **R2-5 (unverifiable operational claims)** — *fixed.* "Protected `main`",
  the visibility-history claim, and the "independent code re-review reports no
  findings" sentence were all removed rather than papered over.
- **R2-6 (`Verification.rice` needs a real downstream test)** — *not resolved;
  now actively obscured by framing.* See R3-2.

## The new robot-verification bridge: what was checked

`action_safety_unverifiable` is sound. The statement is honest about its
load-bearing hypothesis: `SwitchingConstruction` is an explicit certificate
that the program class can computably embed a halting computation and switch
behavior, and both the module docstring and
`docs/guide/robot-verification-model.md` say plainly that this is where the paper's
unbounded-memory and program-composition assumptions enter, that the
conclusion does not automatically apply to bounded program classes, and that
the registry relationship is `RELATED`, not `EXACT`.

Against the fetched paper: Theorem 1 states that no algorithmic procedure can
tell, given an arbitrary robot with potentially unbounded memory, whether its
actions always satisfy a non-trivial property P; Corollary 1 restricts the
input to structured programs. The atlas verifier (`decide : Program → Bool`,
total computable, correct on `structured`) matches the corollary's shape. The
substantive difference, correctly disclosed but worth stating sharply: in the
paper, the switching construction is *derived* from the non-triviality of P
plus the expressive power of the structured robot programming language
(Definitions 2–3); in the atlas it is *assumed*. The machine-checked content is
therefore the reduction half of Theorem 1 — the modeling half, that realistic
robot program classes actually admit such a construction, is exactly the part
that remains formalized nowhere. The `RELATED` classification and the pending
human review are the right labels for that situation, and the non-vacuity
example (`evaln`-paced behavior over `Code`) legitimately shows the certificate
is realizable for at least one program class, albeit the one where the theorem
collapses to the halting problem itself.

## New findings

### R3-1 (moderate): The new example file repeats the exact defect fixed one commit earlier

`AISafetyAtlas/Examples/Robot.lean` — the non-vacuity witness for the new
bridge — is imported by nothing (verified by grep over all `.lean` files) and
absent from CI's explicit build list, so it is outside every build CI runs.
This is the same defect class as R2-3, reintroduced in commit `540c2b4`, which
landed *after* the R2-3 fix (`caae75f`). Compounding it, the registry's robot
formalization record documents
`build_command: lake build AISafetyAtlas.Verification.Robot AISafetyAtlas.Examples.Robot`
and `reproduced: true` — the recorded reproduction command is one that CI does
not execute. A Mathlib bump can silently break the file that the model
document calls the proof "that the interface is non-vacuous."

Fix: add the module to the CI build list, and prefer a structural guard over
per-file patching — e.g. a validator check that every `.lean` file under
`AISafetyAtlas/` is reachable from the root import or named in the CI build
step. Two instances of the same defect in consecutive rounds justify the
invariant, not another one-word patch.

### R3-2 (moderate): `Verification.rice` still has no consumer; the "two layers" framing overstates the relationship

ROADMAP now describes the verification checkpoint as "implemented … in two
layers", with `action_safety_unverifiable` as "the downstream" of
`Verification.rice`. Verified against the source: `Robot.lean` imports
`AISafetyAtlas.Verification` but uses nothing from it — not
`BehavioralProperty`, not `Holds`, not `HasVerifier`, not `rice`. Its proof
reduces directly to `AISafetyAtlas.Computability.halting_problem`. The import
supplies transitive access only; the two bridges are siblings over the
computability facade, not layers.

Round 2's test for `rice` — specify a concrete downstream use or keep the
bridge local — is therefore still unmet, and the current wording makes it
*look* met. Either restate the ROADMAP checkpoint ("two independent bridges
over the computability facade"), or make Robot genuinely consume the rice
interface (e.g. derive the verifier-nonexistence from `HasVerifier` on a
behavioral property induced by `compile`), or revisit whether `rice` belongs in
the public surface at all. What should not survive review is a claimed
layering that the import graph contradicts.

### R3-3 (moderate): Headline coverage counts a self-authored `RELATED` bridge identically to exact external matches

README now reports "verified formalization records for **4 of 44** survey
results". The fourth row's only record is the atlas's own
`action_safety_unverifiable`: authored in this repository two commits ago,
classified `RELATED` (not `EXACT`/`EQUIVALENT`), with paper correspondence
explicitly still under `HUMAN_REVIEW`. The count logic in
`generate_registry_views.py` (`covered = any formalizations record`) makes no
distinction by relationship or origin, so a related in-house corollary moves
the headline number exactly as much as a verified exact external formalization
of the survey result.

The asymmetry is visible in the same batch of commits: the Chaitin candidate is
explicitly *not* counted "until statement-level comparison" classifies it —
while the robot row self-counts on the day it was written, before the review
that STATE lists as its next task. Recommendation: either gate coverage
counting on relationship ∈ {EXACT, EQUIVALENT} (with `RELATED` rows counted
separately, e.g. "+1 related atlas bridge pending review"), or annotate the
headline. The current number is defensible only with a definition of
"coverage" looser than the one the repository applies to external candidates.

### R3-4 (minor): Registry pins the robot record to a commit that the stated publication workflow will orphan

The robot formalization record pins
`version: 540c2b45339c7a3223886d0ad13f69073665f66e` in its own repository.
Verified: no remote ref contains that commit — it exists only in the local
`agent-work` history. The repository's own publication policy is to land work
on `main` as a squashed reviewed delta, which means this hash will never be
publicly resolvable, recreating the R2-1 dangling-anchor pattern inside
registry data. The validators check URL syntax and SPDX licenses but not hash
reachability. Fix: at publication time rewrite self-referential `version`
fields to the published commit, and add a release-audit check that every
in-repo record's pinned version is reachable from a public ref.

### R3-5 (minor): Residual escapes of the incomplete-proof gate

The hardened scanner misses a direct `sorryAx` term-level call (verified by
test); it is caught only by the second layer (`warningAsError` on the
"declaration uses 'sorry'" build warning). Neither layer addresses
kernel-trust extensions such as `native_decide` or `@[implemented_by]`, which
can smuggle unverified computation into proofs without any warning. No current
file uses any of these (verified by grep). For a repository whose value
proposition is machine-checked rigor, a scanner line for
`sorryAx|native_decide|implemented_by` is cheap insurance.

### R3-6 (minor): The machine-checked half vs. the claimed theorem — keep the boundary visible in the registry row

The registry row's `notes` and the model document are careful, but the
declaration name `action_safety_unverifiable` and the survey-row status
`LEAN_AVAILABLE` will travel further than the caveats. The paper's Theorem 1 is
an unconditional impossibility (given its robot model); the Lean theorem is
conditional on a `SwitchingConstruction` instance whose existence for any
robot-like program class other than raw `Code` is unproven. This is exactly
what `RELATED` + `HUMAN_REVIEW` are for — the finding is only that the pending
human review should confirm the *name* and *status vocabulary* do not outrun
the conditional statement, per the project's own separate-theorem-from-
interpretation principle.

### R3-7 (minor): Release document still silent about its anchor's reachability

`docs/releases/v0.1.md` was not amended in this round (no diff since
`fb00d38`); the honest "local-only" disclosure lives only in the audit
script's output. A public reader of the release document alone still receives
an approval ref they cannot resolve, with no note saying so. One sentence in
the document ("this ref attests to private pre-squash history and is not
publicly resolvable; see the audit script output") closes the gap without
publishing anything. STATE.md's "Updated: 2026-07-18" header is also stale
relative to the 2026-07-19 commit.

## What held up under attack

- **The remediation was real and fast.** Five of six round-2 findings were
  fixed within a day, verified against artifacts; the sorry-gate fix in
  particular went beyond the ask (masking, self-tests, and a build-level
  second layer).
- **The new proof is correct and its weakest point is labeled.** Both new Lean
  files hand-check sound; the load-bearing `SwitchingConstruction` assumption
  is stated in the docstring, the model document, and the ROADMAP rather than
  buried; the classification is `RELATED`, not an overclaim.
- **The paper trail supports independent checking.** The archived locator
  served the actual paper; Theorem 1/Corollary 1 could be compared directly.
  Swapping the dead-prone `cs.uu.nl` URL for the archive.org snapshot was the
  right call.
- **The Chaitin candidate record is accurate in every checkable detail** —
  repository, revision (= upstream `main`), declarations, clean source scan,
  toolchain, license — and is correctly *not* counted as coverage. This is the
  discipline R3-3 asks the robot row to match.
- **The audit tells the truth about the anchor.** "local-only … not publicly
  reproducible" printed by the repository's own release audit is the honesty
  norm working, even where the underlying gap remains.

## Recommended actions, in order

1. Add `AISafetyAtlas.Examples.Robot` to CI and add a structural
   every-file-reachable check so this class of defect cannot recur (R3-1).
2. Resolve the rice-consumer question honestly: reword the "two layers"
   checkpoint or make Robot actually consume the interface (R3-2).
3. Decide and document what counts toward headline coverage; gate or annotate
   `RELATED` self-authored rows (R3-3).
4. At publication, rewrite self-referential registry versions to the published
   commit and audit their public reachability (R3-4).
5. Extend the scanner to `sorryAx`, `native_decide`, `@[implemented_by]`
   (R3-5).
6. Add the one-sentence reachability note to `docs/releases/v0.1.md` and
   refresh the STATE date (R3-7).
