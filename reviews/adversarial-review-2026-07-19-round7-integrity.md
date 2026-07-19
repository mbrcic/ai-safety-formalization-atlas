# Adversarial Review — Round 7 (artifact integrity, kernel trust, validator soundness)

Date: 2026-07-19
Scope: committed `agent-work` tree at `77a6cec`. Untracked editor/tooling files
(`**/CLAUDE.md`, `.serena/`, `.claude/`, `.tokensave/`) are not deliverables and
were excluded.

This round **complements** round 6, which is a strategy/purpose review (is the
post-v0.1 work moving the metric the roadmap treats as decisive?). Round 7 asks
a narrower, mechanical question round 6 did not fully execute: **do the
artifacts actually check out at the kernel and declaration level, and what can
the validator suite actually prove?** Round 6 ran `lake build` and confirmed
"pass"; this round ran `#print axioms` on every headline declaration,
ground-truthed all 12 Lean formalization records against their source, and
attacked the validators for blind spots. Duplicate-topic findings (BY-027
label, DASH license) are deferred to round 6 rather than restated.

Method: four parallel adversarial verifiers re-executing claims against
artifacts. One owned `lake` (full build, per-declaration `#print axioms`,
sorry/axiom scan); three read-only verifiers resolved every registry record to
source, audited epistemics compliance, and audited provenance/validator
soundness. Two upstream licenses were fetched live. Actionable claims re-checked
by hand.

## Verdict

At the artifact level the post-v0.1 additions are **clean and honestly
labeled**. Every one of the 12 claimed Lean declarations resolves at its stated
module and namespace and is genuinely proven; the whole library builds with
`EXIT=0`; and every audited atlas theorem is **kernel-verified axiom-clean**
(`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`, zero project-local
axioms). The two records most exposed to overstatement — the vendored Chaitin
proof and the robot bridge — hold up: Chaitin is a real derivation with a
*proven* quantitative core, not a stub; the robot theorem is genuinely
conditional and conservatively labeled `RELATED`.

No integrity defect was found. The three findings below are: one stale
hand-maintained count (concrete, fix in minutes), one systemic and largely
inherent limit on what CI can prove (document it; one cheap hardening
available), and one minor vendoring-license nit. Governance is unchanged: **not
for `main` without maintainer authorization**.

## Verification performed (this round)

| Check | Result |
|---|---|
| `lake build` over library + `scripts/lean_build_targets.txt` closure | `EXIT=0`, 1275 jobs, no `error:` |
| `#print axioms` on 10 headline declarations | All exactly `[propext, Classical.choice, Quot.sound]` |
| `sorry`/`admit`/`native_decide`/`axiom`/`sorryAx`/`implemented_by` in 22 tracked atlas `.lean` | Zero (one `admit` textual hit is docstring prose) |
| Project-local `axiom` declarations anywhere in tree | Zero |
| 12 Lean formalization records resolved to source path + namespace | All EXIST + PROVEN |
| `validate_registry.py` / `generate_registry_views.py --check` / `validate_current_state.py` | Pass / Pass / Pass |

### Per-declaration ground-truth (all resolve + proven)

| Record | Label | Declaration @ module | Verdict |
|---|---|---|---|
| BY-007 | EQUIVALENT | `AISafetyAtlas.Upstream.Arrow.Impossibility` @ `Upstream/Arrow.lean:449` | proven, 0 sorry |
| BY-012 | EQUIVALENT / EXACT | `ComputablePred.rice` / `rice₂` @ Mathlib `Halting.lean:33/43` | proven |
| BY-013 | EQUIVALENT / RELATED | `…Arithmetic.exists_true_but_unprovable_sentence` @ `Incompleteness/First.lean:58`; `…consistent_unprovable` @ `Second.lean:11/18` | proven (namespace hand-confirmed) |
| BY-014 | EXACT / RELATED×2 | `ComputablePred.halting_problem{,_re,_not_re}` @ `Halting.lean:65/61/68` | proven |
| BY-015 | EQUIVALENT | `Kolmogorov.FormalSystem.chaitinIncompleteness` @ `Upstream/KolmogorovMathlib/Complexity/Chaitin.lean:253` | proven, real body |
| BY-016 | EQUIVALENT | `…Arithmetic.undefinability_of_truth` @ `Incompleteness/Tarski.lean:21` | proven |
| BY-027 | EQUIVALENT | `…Arithmetic.löb_theorem` @ `Incompleteness/Löb.lean:16` | proven (delegates to `ProvabilityAbstraction.löb_theorem`) |
| BY-033 | RELATED | `AISafetyAtlas.Verification.Robot.action_safety_unverifiable` | proven, conditional, reduces to `halting_problem` |

Isabelle records (BY-007 ×2, BY-012 `Rice_2`) are **not** vendored in-tree; they
are fetched from hash-pinned AFP archives by `scripts/reproduce_isabelle.sh`.
Honest as `reproduced`, but "verified" for these rests on executing the external
build, not on in-repo bytes.

## What holds up

- **Kernel trust is real, not just token-scanned.** Round 6 confirmed the build
  is green and the strict-trust grep rejects cheat tokens. This round adds the
  stronger check the grep cannot make: `#print axioms` on the explainability
  pair, the robot bridge, Chaitin, and the four Foundation Gödel/Tarski/Löb
  wrappers all show exactly the three standard classical axioms. The claimed
  axiom base and the actual kernel axiom base coincide.
- **"Non-skeletal" is confirmed at the declaration level.** Round 6 asserted the
  Logic layer compiles from attributed sources; this round confirms each named
  declaration actually exists and is proven, closing the gap between "the module
  builds" and "the specific cited theorem is the one that is proven."
- **Chaitin is a derivation, not an axiom dressed as a theorem.** Its core
  `chaitinBound` is a proven `public theorem`, not an assumed structure field;
  `FormalSystem` carries only legitimate hypotheses (soundness, c.e. theorem
  set, correct parser). The `EQUIVALENT` label is defensible at the math level.

## Findings

### R7-1 — MEDIUM — `STATE.md` declaration count is stale (13/6 vs 15/8)

`STATE.md:14` reads "Atlas Lean theorem declarations integrated: **13 across 6
survey results**." The registry-generated source of truth disagrees:
`docs/status/formalization-status.md:14` renders "**15 across 8** survey results," and
`AISafetyAtlas/Examples/Registry.lean` contains **15** `#check` lines. The count
grew when the Foundation and Chaitin declarations landed and `STATE.md` was not
updated.

Root cause is structural and general: only `README.md` (scope block),
`docs/status/formalization-status.md`, `docs/status/atlas-index.md`, and `Registry.lean` are
generated from the registry and diff-checked in CI. `STATE.md` and `ROADMAP.md`
are hand-maintained and **unguarded** — nothing reconciles their counts to the
registry, so drift is silent. The 13/6 line is a live instance. (The frozen v0.1
numbers in `audit_release_v0_1.py` are deliberately historical, not this drift.)

Fix: correct `STATE.md:14` to "15 across 8," and add a lightweight
reconciliation check (or a generated snippet) so a hand-maintained count cannot
diverge from the registry unnoticed. This is the concrete, ship-now item of the
round.

### R7-2 — MEDIUM (systemic, largely inherent) — validators prove symbol existence, not statement correctness

Credit first: the suite is stronger than a metadata linter. Because
`Registry.lean`'s `#check` list is generated from the registry, diff-checked,
and then `lake build`-elaborated in CI, a fabricated *atlas* declaration name
turns CI red. That is a genuine soundness property.

But the machine-checkable perimeter ends at "the symbol exists and elaborates."
A false formalization claim of these shapes passes all validators green:

1. **Relationship label is never semantically verified.**
   `EXACT`/`EQUIVALENT`/`RELATED` is checked only for vocabulary membership
   (`validate_registry.py:307`). A record mislabeled `EXACT` when it is really
   `RELATED` — which directly inflates the headline "7 of 44" — passes green.
   (This is the machine-side counterpart of round 6's R6-5/R6-2, which argue the
   *semantics* of specific labels; here the point is that CI cannot catch such a
   mislabel at all.)
2. **`#check` proves well-typedness, not correspondence.** A vacuous, weaker, or
   mis-stated theorem that elaborates passes; the statement→survey-claim map is
   entirely human-asserted.
3. **`source_declarations` are never checked.** Only `atlas_declaration` gets a
   `#check`; upstream names (Isabelle `Arrow`, `DASHImpossibility.*`) are never
   verified to exist.
4. **`reproduced: true` is unenforced.** No validator runs the reproduce scripts
   (they need Docker/Isabelle/network); the evidence lives only as prose in
   `docs/provenance/external-formalizations.md`.
5. **Axiom-cleanliness is textual in CI, not kernel-level.** "Strict trust"
   rests on grepping banned tokens, not on `#print axioms`. This round ran the
   kernel check by hand and it was clean — but CI does not run it, so a
   `#check`ed declaration whose proof happened to pull an extra axiom would not
   be flagged.

Items 1–4 are largely inherent to the trust model — semantic capture is exactly
what `HUMAN_REVIEW` gates — and are not defects to "fix." The recommendation is
to **state this perimeter explicitly** in the methodology so "validators pass"
is never read as "the labels are semantically correct." Item 5, by contrast, is
cheap to close: add a CI step that `#print axioms` the atlas headline
declarations and asserts the set is a subset of the three standard axioms. That
converts the strongest trust claim in the project from a grep into a kernel
check.

### R7-3 — LOW — vendored Apache-2.0 subtrees ship no co-located LICENSE copy

The hand-vendored `AISafetyAtlas/Upstream/Arrow.lean` and
`AISafetyAtlas/Upstream/KolmogorovMathlib/` trees preserve per-file attribution
(and, for Kolmogorov, the upstream copyright header) but include no copy of the
upstream Apache-2.0 LICENSE/NOTICE within the vendored subtree
(`find AISafetyAtlas/Upstream -iname 'LICENSE*'` → empty). Apache-2.0 §4 asks a
redistributor to retain the license text alongside redistributed source. The
atlas's own root LICENSE is Apache-2.0, so this is internally consistent and
low-risk, but strictly a vendoring compliance nit. This extends round 6's R6-10,
which flagged only the DASH/attribution license; the same gap applies to the
Arrow and Kolmogorov subtrees. Fix: drop an
`AISafetyAtlas/Upstream/<pkg>/LICENSE` (or a NOTICE pointing at the shared root
license) into each vendored subtree.

## Deferred to round 6 (confirmed, not restated)

- **BY-027 `EQUIVALENT` is the softest headline label** — round 6 R6-5. This
  round's epistemics pass independently reached the same conclusion (the note
  "Classified EQUIVALENT to the survey's Löb/unverifiability row" fuses the
  math-equivalence and the AI-framed row in one clause). Round 6's re-triage
  recommendation stands; no separate action here.
- **DASH provenance rests on `CITATION.cff` only (LICENSE 404)** — round 6 R6-10.
  Re-confirmed by live fetch at the pin; transparently disclosed in
  `docs/provenance/external-formalizations.md`. Watch for an upstream LICENSE addition.
- **Four coverage rows couple to one Foundation pin** — round 6 R6-6. This round
  additionally notes the 68 build warnings are all Foundation-side (no atlas
  proof file warns), which reinforces R6-6's "trusted/build surface" point.

## Recommendations (priority order)

1. **Fix R7-1 now** — `STATE.md:14` → "15 across 8"; add a count-reconciliation
   guard so hand-maintained docs cannot silently drift from the generated views.
2. **Harden R7-2 item 5** — add a CI `#print axioms` assertion over the atlas
   headline declarations (cheap; upgrades the axiom-clean claim from grep to
   kernel), and document the rest of the validator perimeter in the methodology.
3. **Fix R7-3** — add LICENSE/NOTICE copies to the vendored `Upstream/` subtrees.
4. Strategy items (bridge graduation, dual-ledger, dead candidate schema, etc.)
   are round 6's domain and are not re-opened here.

## Governance note

This review does not authorize promotion to `main`. Per `STATE.md`, post-v0.1
work stays local on `agent-work` and requires explicit maintainer authorization
plus domain/semantic review of the robot-verification bridge before any public
branch. The findings above are merge-quality observations for the maintainer,
not a sign-off.

## Appendix — prior review chain

| Round | File | Focus |
|---|---|---|
| 1–2 | `adversarial-review-2026-07-18*.md` | Early integrity |
| 3 | `…-round3.md` | Mechanical defect classes |
| 4 | `…-round4.md` | Injection tests of R3 fixes |
| 5 | `…-round5-purpose-plan.md` | Purpose vs plan; lifecycle; candidates; atlas view |
| 6 | `…-round6.md` | Post-Logic/attribution/GS honesty and strategy |
| 7 | this file | Artifact integrity, kernel-level axiom trust, validator soundness |

## Resolution (implemented 2026-07-19)

| ID | Disposition |
|---|---|
| R7-1 | **Fixed.** STATE generated snapshot block; counts 16 decls / 8 rows; markers guarded in current-state validation |
| R7-2 | **Fixed.** Methodology “What validators prove”; CI runs `scripts/check_print_axioms.py` (15 decls ⊆ classical 3) |
| R7-3 | **Fixed.** `AISafetyAtlas/Upstream/LICENSE`, per-subtree LICENSE copies, `LICENSE-NOTICE` |
