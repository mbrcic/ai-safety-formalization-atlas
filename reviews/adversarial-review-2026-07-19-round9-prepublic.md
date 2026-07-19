# Adversarial review — round 9 (pre-public re-check)

**Date:** 2026-07-19  
**Branch:** `agent-work` (~33 commits ahead of `main`)  
**Focus:** tip product commits + **uncommitted** R8 hardening tree  
**Stance:** adversarial but truthful  
**Prior:** round 8 (`reviews/adversarial-review-2026-07-19-round8-prepublic.md`)

---

## Executive verdict

| Dimension | Round 8 | Round 9 |
|---|---|---|
| Lean / gates | Strong | **Still strong** — full gate green including docs paths + build targets |
| Claim hygiene (bridges) | Good residual risk | **Improved** — v0.2 note, Alfonseca packaging-pattern, BY-012 scope, README epistemic |
| Doc freshness | Weak (ROADMAP/open-work) | **Improved** — scrubbed; residual risk is process (no auto-freshness) |
| Release packaging | Missing 0.2 | **Present in working tree** (`0.2.0`, `docs/releases/v0.2.md`) — **not yet committed** |
| Public-ship readiness | Not ship-shaped | **Ship-shaped after commit + maintainer push/PR** |

**Bottom line:** Round-8 P0/P1 items appear **implemented in the working tree**. The
dominant remaining failure mode is **operational**, not mathematical: **pushing
without committing the hardening delta**, or merging a PR that omits
`v0.2.md` / version bumps / open-work scrub. Content honesty is now at a level
suitable for public 0.2 **if** the uncommitted tree is committed and the PR is
complete.

**Overall pre-public score: ~4.2 / 5** (was ~3.5 after round 8).

---

## Verification performed

| Check | Result |
|---|---|
| `validate_registry.py` | Pass |
| `validate_landscape.py` | Pass |
| `generate_registry_views.py --check` | Pass |
| `validate_current_state.py` | Pass |
| `check_docs_paths.py` | Pass (125 links) |
| `check_print_axioms.py` | Pass (15 decls) |
| `audit_release_v0_1.py` | Pass (historical) |
| `xargs lake build < scripts/lean_build_targets.txt` | Pass |
| Version files | `0.2.0` in lakefile + CITATION (working tree) |
| `docs/releases/v0.2.md` | Present, untracked until commit |
| Coverage recount | EXACT/EQUIVALENT **7**; RELATED-only **1**; `REVIEWED` **2** |

**Git reality:** product hardening (version bump, v0.2 note, ROADMAP/open-work,
Alfonseca wording, methodology, gitignore, CI path check) is largely
**uncommitted** (`git status` dirty + untracked `v0.2.md`, round-8 review,
`check_docs_paths.py`). Tip commit remains `4e906ba` (robot REVIEWED).

---

## Round-8 re-audit

| ID | Round-9 status |
|---|---|
| R8-1 version + release note | **Remediated in tree** — must commit |
| R8-2 ROADMAP/open-work stale | **Remediated in tree** |
| R8-3 tool noise | **Remediated** — gitignore; do not force-add |
| R8-4 BY-012 whole-row REVIEWED | **Remediated** — notes + evidence + methodology |
| R8-5 Alfonseca packaging | **Remediated** — `packaging-pattern`, BY-025 MAPPED |
| R8-6 reviewed ≠ coverage | **Remediated** — README + v0.2 |
| R8-7 Melo double-count | **Remediated** in v0.2 non-claims |
| R8-8 other API unreviewed | **Disclosed** in open-work / v0.2 |
| R8-9 self-review | **Disclosed** in v0.2 |
| R8-10 / R8-12 / R8-13 | **Remediated** as listed in R8 resolution appendix |

No regression found that re-opens a fixed R8 item **in the working tree**.
Regression risk is **shipping the last committed tip without the working tree**.

---

## New / residual findings

### P0 — block public 0.2 until done

#### R9-1. Hardening delta is not committed

- **Evidence:** dirty `lakefile.toml`, `CITATION.cff`, ROADMAP, open-work,
  registry notes, CI, gitignore; untracked `docs/releases/v0.2.md`,
  `scripts/check_docs_paths.py`, round-8 report.
- **Attack:** “Public PR is 0.1.0 content + partial reviews; local laptop has
  0.2 story.” Or CI on PR lacks path check because workflow change uncommitted.
- **Fix:** Single coherent commit (or two: product + reviews) of the entire
  hardening tree before push. **Do not** push only through `4e906ba`.

#### R9-2. Publication still requires human authorization (not a bug)

- **Evidence:** v0.2 status “pending maintainer authorization.”
- **Note:** Correct. Not a code defect. Checklist item for the human: explicit
  push/PR/merge after R9-1.

---

### P1 — fix before or with the 0.2 PR (honesty polish)

#### R9-3. Unreviewed `BRIDGE`: Utility Arrow (BY-007)

- **Evidence:** `AISafetyAtlas.SocialChoice.Utility.arrow` is type `BRIDGE`;
  row `ai_bridge_status` is still `HUMAN_REVIEW`.
- **Risk:** README API lists Utility Arrow next to reviewed AgentBehavior/Robot;
  skimmer assumes all listed API is AI-reviewed.
- **Truth:** Utility Arrow is a **representation bridge** (order → utility), not
  an AI-system interpretation package. Methodology now says BRIDGE with
  AI-facing vocabulary needs review; Utility is grey-zone.
- **Fix (light):** One sentence in v0.2 / README Lean API: Utility Arrow is a
  math representation bridge, not an AI-bridge review. Optional later:
  leave `HUMAN_REVIEW` explicitly for non-AI bridges or split vocabulary.

#### R9-4. Survey **names** still invite overclaim

| Row | Name | Tension |
|---|---|---|
| BY-033 | “Unverifiability of robot ethics” | Formalization is RELATED conditional core; ethics is instance of *P* |
| BY-027 | “Löb's theorem (unverifiability)” | Wrapper only, `HUMAN_REVIEW`; “unverifiability” is survey framing |

- **Risk:** Title-only readers overclaim despite excellent bridge packages.
- **Fix:** Already mitigated in evidence files; optional: registry `name`
  softens for public (breaking change for citations) — **not required** if v0.2
  non-claims stay prominent. Prefer **no rename** in 0.2; keep non-claims.

#### R9-5. Large delta vs `main` (~33 commits)

- **Risk:** Reviewer fatigue; accidental inclusion of noise; hard to audit.
- **Defense:** Project policy is squash merge — good.
- **Fix:** PR description = paste v0.2 one-paragraph truth + gate list; do not
  ask reviewers to read 33 commit messages.

#### R9-6. No automated freshness check for ROADMAP / open-work

- **Risk:** Round 8–style drift returns after next sprint.
- **Fix (optional 0.2.1):** lightweight check that open-work does not contain
  forbidden stale phrases, or generate “reviewed bridges” from registry into a
  marked section. Not blocking if human owns PR description.

---

### P2 — post-0.2 hardening (not blockers)

#### R9-7. Attribution landscape on root import without AI-bridge lifecycle

`Explainability.attribution_impossibility` is public API + landscape; no
`ai_bridge_status` (not a survey row). Fine if landscape notes stay tight;
add literature/landscape “not AI-reviewed” if readers confuse it with BY-012.

#### R9-8. Maintainer self-review only

Disclosed. External review still optional; do not overclaim peer review.

#### R9-9. Foundation rebuild / CI duration

Build targets pass; first CI may be slow. Operational, not soundness.

#### R9-10. `CITATION.cff` `date-released: 2026-07-19` before public merge

Minor; update date on actual publish day if you care about citation metadata
strictness.

#### R9-11. v0.1 audit still references old script names in places?

`docs/releases/v0.1.md` still shows `audit_release.py` in a run block — historical
doc; may confuse. Low priority: add note “historical; use audit_release_v0_1.py”.

---

### P3 — positives (preserve)

1. Dual labeling robot: **RELATED** formalization + **REVIEWED** scoped bridge is
   the correct public story.
2. Literature-first map + packaging / packaging-pattern vocabulary is usable.
3. Docs path CI is a real upgrade from round 8.
4. Gates match what a hostile formal-methods reviewer will run.
5. Epistemic README + v0.2 non-claims align with actual registry counts.

---

## Attack scenarios (updated)

| Attack | Round 9 defense |
|---|---|
| “Robot ethics formalized exactly” | Strong if CT-3/v0.2 read; title risk remains |
| “Containment formalized (BY-025)” | **Much stronger** after packaging-pattern wording |
| “Still 0.1 with huge features” | **Fixed in tree**; fails if uncommitted |
| “Self-reviewed worthless” | Disclosed; acceptable for map release |
| “CI doesn’t match claims” | Strong once hardening committed (path check + views) |
| “Utility Arrow is AI-reviewed” | **Weakest residual** API-list skimming (R9-3) |

---

## Ship checklist (actionable)

### Must before push

1. [ ] **Commit** all R8/R9 hardening (version, v0.2.md, scrub, Alfonseca, methodology, gitignore, CI path check, reviews).
2. [ ] Re-run full gate on clean tree after commit.
3. [ ] PR body = v0.2 paragraph + “gates run” + “RELATED robot / 7 of 44 / 2 reviewed bridges”.
4. [ ] Explicit maintainer authorization to push/PR; squash merge to `main`.
5. [ ] Confirm no `CLAUDE.md` / `.claude` in the commit.

### Optional with PR (light)

6. [ ] One README/v0.2 sentence on Utility Arrow = representation bridge, not AI review.
7. [ ] Fix v0.1.md historical audit command name (footnote).

### Not required for 0.2

- NFL CT-2, BY-025 Lean, robot EXACT, external peer review, issue queue.

---

## Scorecard

| Area | Score | Note |
|---|---:|---|
| Soundness | 5 | Builds + axioms |
| Bridge honesty | 5 | RELATED + packages |
| Lit map honesty | 4.5 | packaging-pattern fixed |
| Doc freshness | 4 | Scrubbed; uncommitted |
| Release packaging | 4.5 | Complete in tree; uncommitted |
| Misuse resistance | 4 | Title risk; Utility skim |
| **Ship readiness** | **4.2** | **Commit → authorize → PR** |

---

## Closing

Round 9 finds **no new soundness holes** and confirms **round-8 remediations
present in the working tree**. The project is **ready for a public 0.2** in
substance. The only adversarial “gotcha” left is shipping the **wrong git
snapshot**. Commit the hardening batch, gate once more, then push under
explicit authorization.
