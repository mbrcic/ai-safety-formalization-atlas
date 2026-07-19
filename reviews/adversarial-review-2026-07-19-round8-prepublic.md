# Adversarial review — round 8 (pre-public / pre-0.2)

**Date:** 2026-07-19  
**Branch:** `agent-work` (vs `main`, ~33 commits; focus also on tip commits
`bba7593`…`4e906ba`)  
**Stance:** adversarial but truthful — assume a skeptical public reader, a
hostile formal-methods reviewer, and a careless AI-safety skimmer.  
**Purpose:** harden before push/PR of a 0.2-class release.

---

## Executive verdict

| Dimension | Assessment |
|---|---|
| **Machine-checked core** | **Strong.** `lake build AISafetyAtlas` green; axiom check 15 decls ⊆ classical triple; registry/landscape/current-state validators green. |
| **Claim hygiene (new bridges)** | **Good with residual risk.** BY-012 / BY-033 reviews are real, scoped, and documented. RELATED robot cut is honest. Overclaim risk is **reader misuse** and **stale docs**, not silent EXACT fraud. |
| **Inventory / map** | **Stronger than v0.1.** Landscape, paper-coverage, literature-first map, docs taxonomy, bridge lifecycle are real product. |
| **Public-release readiness** | **Not ship-shaped yet** for a versioned **0.2** without: release note + version bump, stale-doc scrub, a few **honest-but-sharp** claim fixes, and maintainer push/PR. Content is close; process packaging is not. |

**Bottom line:** The new work is a serious atlas upgrade (bridges, reviews,
map tooling). It is **defensible to publish** if release notes and a short
hardening pass fix the issues below. It is **not** defensible to push as
“0.2” while `lakefile`/`CITATION` still say `0.1.0` and ROADMAP/open-work still
say robot is `HUMAN_REVIEW`.

---

## What was verified this round

| Check | Result |
|---|---|
| `validate_registry.py` | Pass (44 results, 2 `REVIEWED` bridges) |
| `generate_registry_views.py --check` | Pass |
| `validate_current_state.py` | Pass |
| `validate_landscape.py` | Pass (5 entries) |
| `audit_release_v0_1.py` | Pass (historical; local-only approval anchor) |
| `check_print_axioms.py` | Pass (15 decls) |
| `lake build AISafetyAtlas` | Pass (Foundation rebuild noise only) |
| Coverage counts from registry | EXACT/EQUIVALENT **7**; RELATED-only **1** (BY-033); `REVIEWED` **2** (BY-012, BY-033); rest `HUMAN_REVIEW` **42** |

---

## Strengths (do not break these)

1. **Transparent robot RELATED.** CT-3 + model doc + allowed/forbidden claims
   make the SPA/certificate cut hard to miss if you open the evidence. That is
   the correct posture for public AI-safety readers.

2. **AgentBehavior is the right primary AI-facing story.** Rice packaging under
   agent vocabulary, fully reviewed, with misuse tests. Melo/Alfonseca as
   packaging (not new theorems) is the right abstraction.

3. **Separation of layers.** Registry relationship vs `ai_bridge_status` vs
   literature map vs landscape vs headline coverage — when consistent, this
   prevents “7 of 44” from swallowing RELATED or lit packaging.

4. **Operational gates.** CI path (registry, landscape, views `--check`,
   current-state, lake, build targets, axioms) matches what a public repo needs.

5. **No fabricated bridge_review.** Named reviewer, dates, evidence files;
   interpretation flags match schema.

---

## Findings (severity-ordered)

### P0 — fix before calling it public 0.2

#### R8-1. Version still 0.1.0; no v0.2 release artifact

- **Evidence:** `lakefile.toml` / `CITATION.cff` = `0.1.0`; only
  `docs/releases/v0.1.md`; STATE still says package stays 0.1.0 until authorized.
- **Risk:** Pushing `main` without a version story looks like silent content
  churn or false “still 0.1” when bridges and map changed materially.
- **Fix:** Author `docs/releases/v0.2.md` (scope + non-claims), bump both version
  files, update STATE “package version” line, tag only after squash merge.

#### R8-2. Stale public-facing claims that contradict the tip of the branch

| Location | Stale claim | Reality |
|---|---|---|
| `ROADMAP.md` (~robot bridges) | remain `HUMAN_REVIEW` (CT-3 …) | BY-033 is `REVIEWED` (RELATED formalization) |
| `docs/guide/open-work.md` | Every bridge `HUMAN_REVIEW`; CT-3 still to graduate; AgentBehavior interpretation `HUMAN_REVIEW` | BY-012 and BY-033 fully `REVIEWED` |
| Possibly other narrative docs | “first bridge still pending” tone | Two reviewed bridges |

- **Risk:** First-time reader hits ROADMAP/open-work and concludes the project
  is lying or abandoned mid-review — worse than incomplete math.
- **Fix:** Scrub ROADMAP / open-work / any “blocked CT-3” language in one pass
  before PR. Prefer “open work = NFL, more lit rows” over “bridges unreviewed.”

#### R8-3. Uncommitted? (cleared if tip is `4e906ba`)

At review time working tree may be clean for product files; ensure PR includes
robot `REVIEWED` commit `4e906ba` and literature map `4b0da3d`. Tool noise
(`.claude/`, `**/CLAUDE.md`) must **not** enter the public tree.

---

### P1 — fix before or immediately after public 0.2 (claim / map integrity)

#### R8-4. BY-012 `REVIEWED` applies to the **whole survey row**, including pure math wrappers

- **Evidence:** One `ai_bridge_status` per result. BY-012 carries WRAPPER Rice +
  BRIDGE `Verification.rice` + BRIDGE AgentBehavior; status is `REVIEWED`.
- **Risk:** Reader thinks “Rice’s theorem itself was AI-interpretation reviewed”
  rather than “the agent packaging was.”
- **Fix (docs, not schema):** In release note and BY-012 notes, state clearly
  that **`REVIEWED` refers to the AI-facing bridges** (`Verification.rice` /
  AgentBehavior), not a novel review of Mathlib Rice’s classical content.
  Medium-term: consider per-declaration bridge status (schema change — not
  required for 0.2 if release note is sharp).

#### R8-5. Alfonseca / BY-025 “packaging” overstates registry reality

- **Evidence:** `related-literature.md` marks Alfonseca as **`packaging`** via
  AgentBehavior and survey **BY-025**, but BY-025 is **`MAPPED`**, no
  `lean_artifact`, still `HUMAN_REVIEW`.
- **Risk:** Literature map says “addressed by packaging”; survey row says “no
  Lean.” Hostile reader: “you claim containment is packaged but BY-025 is empty.”
- **Truthful split:** Method is the same as Melo; **registry coverage of BY-025
  is not.** Packaging is *available pattern*, not *row-level LEAN_AVAILABLE*.
- **Fix:** Change Alfonseca “How addressed” to e.g. `packaging-pattern` /
  `indirect` with note: “AgentBehavior covers the Rice pattern; BY-025 has no
  dedicated declaration or row formalization.” Do **not** imply BY-025 is
  formalized.

#### R8-6. “2 survey results with reviewed AI-system bridges” can be misread as 2 EXACT coverage wins

- **Evidence:** README generated scope correctly separates 7 EXACT/EQUIVALENT,
  1 RELATED, 2 reviewed bridges.
- **Risk:** Social/media paraphrase collapses to “two more results formalized.”
- **Fix:** In `docs/releases/v0.2.md` and README epistemic paragraph, one
  explicit sentence: reviewed bridges ≠ headline coverage; robot is RELATED-only.

#### R8-7. LAND-MELO-001 + BY-012 double-hook for the same packaging

- **Evidence:** Landscape entry points at AgentBehavior; BY-012 also owns it;
  literature map third.
- **Risk:** Low if notes stay consistent; medium if counts are hand-summed
  (“3 formalizations of Melo”).
- **Fix:** Release note: Melo is related lit + landscape pointer + BY-012
  packaging — **one** formal object.

---

### P2 — harden soon (quality / maintainability)

#### R8-8. Other public Lean bridges remain `HUMAN_REVIEW`

Utility Arrow, Logic aliases, Attribution landscape, etc. appear on root import
and README API list without bridge review.

- **Risk:** “We review bridges” vs unreviewed Utility Arrow / attribution
  reading.
- **Fix:** Release note: only BY-012 and BY-033 have completed AI-bridge review;
  other API entries are classical wrappers or landscape until reviewed.
  Optionally mark non-AI-facing wrappers as not requiring bridge review in
  methodology (already mostly true — clarify).

#### R8-9. Bridge evidence is maintainer self-review

- **Evidence:** Reviewer = package maintainer for both `REVIEWED` rows.
- **Risk:** External skeptic: “no independent domain review.”
- **Truthful response:** Fine for 0.2 if disclosed; not fraud. Stronger 0.3
  story: second reviewer on robot interpretation.
- **Fix:** One sentence in v0.2 release: reviews are maintainer statement +
  scoped interpretation acceptance; external domain review welcome.

#### R8-10. `open-work.md` / ROADMAP drift shows process debt

Multiple adversarial rounds produced findings; remediation outran narrative
docs. **Validators do not check ROADMAP freshness.**

- **Fix:** Either generate a “reviewed bridges” snippet into ROADMAP or treat
  ROADMAP as rarely updated strategy and point “status” only to STATE +
  formalization-status (and enforce that in AGENTS).

#### R8-11. Foundation dependency noise and rebuild cost

Build replays large Foundation graph; upstream linter warnings.

- **Risk:** CI time / flaky contributor experience, not soundness.
- **Fix:** Document expected first-build cost; optional CI cache (lean-action
  usually handles). Not a 0.2 blocker if CI is green.

#### R8-12. v0.1 approval anchor remains local-only

- **Evidence:** audit script discloses non-public reproducibility of approval
  commit.
- **Risk:** Already known; hostile reader may fixate.
- **Fix:** v0.2 release anchors on **public squash commit** after merge, not
  pre-squash private history.

#### R8-13. No automated link check for docs paths after taxonomy move

Many relative links; moves were careful but not link-tested.

- **Fix:** Optional `lychee` or simple path-existence script in CI later.

#### R8-14. Candidate NFL / observability leads still UNVERIFIED

Fine for 0.2; do not let release language imply “candidates = coverage.”

---

### P3 — observations (not blockers)

- **Grammar:** README “2 survey results with reviewed…” is fine; earlier “1
  survey results” bug appears fixed for pluralization path.
- **Reviews/ folder size:** Many adversarial reports — good for history;
  consider `reviews/README.md` index for newcomers.
- **Self-review of interpretation drafts:** User-edited then agent-finalized —
  evidence trails are adequate if CT-3 / BY-012 files remain the canonical
  allowed claims.

---

## Focus: tip commits (literature + reviews)

| Commit | Assessment |
|---|---|
| `bba7593` AgentBehavior, landscape, docs split, Melo | High value; packaging honesty good |
| `50a344c` BY-012 REVIEWED | Appropriate; watch R8-4 whole-row status |
| `4b0da3d` literature-first map | Right design; R8-5 Alfonseca wording |
| `4e906ba` BY-033 REVIEWED + RELATED | Correct dual label; strongest part of pre-public story if release note is clear |

---

## Attack scenarios (and current defense)

| Attacker claim | Defense quality |
|---|---|
| “You formalized robot ethics exactly.” | **Strong** if they open CT-3 / model doc; **weak** if they only see BY-033 name “Unverifiability of robot ethics” |
| “Two more survey results are fully formalized.” | **Medium** — README separates RELATED; title of BY-033 still invitation to misread |
| “Containment (BY-025) is formalized.” | **Weak** under current literature map packaging language (R8-5) |
| “Self-reviewed, worthless.” | **Medium** — disclose maintainer review; don’t claim external peer review |
| “Still 0.1 with huge delta.” | **Strong attack** until R8-1 fixed |
| “Trust violated / sorry / axioms.” | **Strong defense** — gates exist and pass |

---

## Recommended hardening checklist (ordered)

### Must before public 0.2 PR

1. [ ] Commit clean product tree (no CLAUDE/tool caches).
2. [ ] `docs/releases/v0.2.md` with scope, 7/44, RELATED robot, 2 reviewed bridges, non-claims.
3. [ ] Bump `lakefile.toml` + `CITATION.cff` to `0.2.0`.
4. [ ] Scrub **ROADMAP** + **open-work** stale HUMAN_REVIEW / CT-3 blocked language.
5. [ ] Fix Alfonseca/BY-025 “packaging” wording (R8-5).
6. [ ] Re-run full gate (registry, views, current-state, landscape, axioms, lake, build targets).
7. [ ] Maintainer-authorized push + PR; squash merge; public commit is the provenance anchor.

### Should soon after

8. [ ] Clarify BY-012 `REVIEWED` = AI bridges, not “Mathlib Rice re-audited.”
9. [ ] Methodology note: which declaration types require bridge review.
10. [ ] Optional external review invite for robot interpretation.
11. [ ] Link/path smoke test in CI.

### Explicitly not required for 0.2

- CT-2 NFL completion  
- Robot EXACT SPA formalization  
- BY-025 dedicated Lean theorem  
- Second independent domain reviewer  
- Opening full GitHub issue queue  

---

## Suggested 0.2 one-paragraph truth

> v0.2 is a map and process release: 7/44 headline EXACT/EQUIVALENT formalizations
> (unchanged count class from post-v0.1 math work), one RELATED robot formalization
> with a transparent certificate cut, two survey rows with maintainer-reviewed
> AI-facing bridges (Rice/agent packaging; robot observer core), landscape ledger
> and literature-first map for packaging claims (Melo-style), and role-split docs.
> It does not claim complete survey coverage, exact robot-paper fidelity, or that
> real systems are unverifiable.

---

## Scorecard

| Area | Score (1–5) | Note |
|---|---:|---|
| Soundness of Lean surface | 5 | Gates green |
| Honesty of robot RELATED | 5 | Best-in-repo transparency |
| Honesty of lit map | 3 | Alfonseca packaging overshoot |
| Doc freshness | 2 | ROADMAP/open-work lag |
| Release packaging | 2 | Still 0.1.0, no v0.2 note |
| Public misuse resistance | 4 | Good evidence files; title risk remains |
| **Overall pre-public** | **3.5** | **Ship after P0 scrub; not raw push** |

---

## Closing

The branch **earns** a public 0.2 if you treat 0.2 as **map + reviewed bridges +
honest RELATED robot**, not as “survey mostly formalized.” The adversarial
failure mode is **stale narrative and version drift**, not a hidden `sorry`.
Fix R8-1–R8-5, then push under explicit maintainer authorization.

---

## Resolution (same day)

| ID | Status |
|---|---|
| R8-1 | **Fixed.** `docs/releases/v0.2.md`; version **0.2.0** in lakefile + CITATION; STATE updated |
| R8-2 | **Fixed.** ROADMAP + open-work scrubbed for CT-3 / HUMAN_REVIEW staleness |
| R8-3 | Tool noise gitignored (`.claude/`, `**/CLAUDE.md`, …) |
| R8-4 | **Fixed.** BY-012 notes + bridge evidence + methodology: REVIEWED = AI bridges |
| R8-5 | **Fixed.** Alfonseca → `packaging-pattern`; BY-025 MAPPED clarified |
| R8-6 | **Fixed.** README epistemic + v0.2 non-claims |
| R8-7 | **Fixed.** v0.2 Melo “one formal object” note |
| R8-8 | **Fixed.** open-work / v0.2: only BY-012/033 REVIEWED; other API unreviewed as AI bridges |
| R8-9 | **Fixed.** v0.2 discloses maintainer review; invites external follow-on |
| R8-10 | **Fixed.** ROADMAP points status to STATE + formalization-status |
| R8-12 | **Fixed.** v0.2 anchors public squash, not private v0.1 ancestry |
| R8-13 | **Fixed.** `scripts/check_docs_paths.py` + CI step; broken links repaired |

Remaining for maintainer only: authorize push/PR/merge of 0.2.
