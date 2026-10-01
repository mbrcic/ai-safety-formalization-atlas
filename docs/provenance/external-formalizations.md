# External Formalizations

External developments are pinned separately from normal CI and are labelled by
evidence level. A source-inspected candidate is not treated as reproduced or as
survey coverage. Isabelle sessions use immutable source archives and an
immutable prover image; the adjacent Lean vNM development uses an immutable Git
revision and an atlas-supplied build harness. Run the reproduced Isabelle
sessions with:

```console
scripts/reproduce_isabelle.sh all
```

## Isabelle/HOL: Rice's theorem

- Upstream: [AFP — Recursion Theory I](https://www.isa-afp.org/entries/Recursion-Theory-I.html)
- Author: Michael Nedzelsky
- License: BSD-3-Clause (AFP BSD License)
- Release: `2026-02-06`, compatible with Isabelle2025-2
- Archive SHA-256: `b5314c859ce3b2876ef01151f394c1a5e6b234b0fc6563698dbb0250c73cd3f8`
- Session: `Recursion-Theory-I`
- Theory: `RecEnSet.thy`
- Declarations: `Rice_1`, `Rice_2`, `Rice_3`
- Coverage relationship: `Rice_2` is `EQUIVALENT` to the survey's ordinary
  Rice-theorem row. It states that every nonempty, nonuniversal index set is
  not computable.
- Additional value: `Rice_1` supplies an explicit one-reduction, and `Rice_3`
  supplies a semantic c.e.-set interface. They are reproduced provenance and
  possible future interfaces, not two additional survey-result coverage claims.
- Migration decision: do not port `Rice_2`, because Mathlib already supplies
  the canonical Lean result. Defer `Rice_1` and `Rice_3` until a downstream
  reduction or c.e.-set proof requires their additional structure.
- Local reproduction: passed on 2026-07-18 in 8 seconds of session time.

Command:

```console
scripts/reproduce_isabelle.sh rice
```

## Isabelle/HOL: Arrow and Gibbard–Satterthwaite

- Upstream: [AFP — Arrow and Gibbard-Satterthwaite](https://www.isa-afp.org/entries/ArrowImpossibilityGS.html)
- Author: Tobias Nipkow
- License: BSD-3-Clause (AFP BSD License)
- Release: `2026-02-06`, compatible with Isabelle2025-2
- Archive SHA-256: `8174c738b42203100170ff25f3c9fc2c6d16d8556fbaff205c0eaa98a3813da7`
- Session: `ArrowImpossibilityGS` (one session; one reproduction builds all three theories)
- Theories and declarations:
  - `Thys/Arrow_Order.thy`: `Arrow`
  - `Thys/Arrow_Utility.thy`: `dictator`
  - `Thys/GS.thy`: `Gibbard_Satterthwaite` (and locale form `GS.Gibbard_Satterthwaite`)
- Survey coverage: Arrow theorems are `EQUIVALENT` for **BY-007** (registry).
  **Gibbard–Satterthwaite is not a separate Table-1 survey ID** in the current
  44-row map; it is recorded here as **social-choice landscape / Arrow-session
  provenance**. Statement: non-manipulable, onto social choice function ⇒
  dictatorial (`∃i. dict f i`), derived as a corollary of Arrow (Nisan-style).
- Local reproduction: `scripts/reproduce_isabelle.sh arrow` rebuilds the whole
  session (including `GS.thy`). Passed on 2026-07-18; re-run green on
  **2026-07-19** (`ArrowImpossibilityGS` finished ~5s wall after image/start:
  `Arrow_Order`, `Arrow_Utility`, `GS` all 100%).
- **Integration:** Isabelle `Gibbard_Satterthwaite` is landscape `LAND-GS-001`
  (not a Table-1 BY ID). “Reproduced” means the pinned AFP session rebuilds via
  the script below — it is **not** CI-integrated. Lean consumers should use
  `AISafetyAtlas.SocialChoice.gibbard_satterthwaite` (`LAND-GS-002`, next
  section), not an Isabelle→Lean port. Atlas Arrow remains CC Liang + utility
  bridge (distinct lineage from SocialChoiceLean).

Command:

```console
scripts/reproduce_isabelle.sh arrow
```

## Lean 4: Gibbard–Satterthwaite (SocialChoiceLean) — vendored landscape

Classical GS (resolute voting rules), landscape only — **not** survey Table-1
coverage. Lean interface is first-class for atlas consumers; Isabelle twin
remains `LAND-GS-001`.

- Upstream: [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean)
- Port pin: [`mbrcic/SocialChoiceLean`](https://github.com/mbrcic/SocialChoiceLean)
  branch `port/lean-4.31` revision **`74f491b`** (Lean/Mathlib **v4.31.0**)
- License: **MIT** (`vendor/SocialChoiceLean/LICENSE`)
- Atlas module: `AISafetyAtlas/Upstream/GibbardSatterthwaite.lean` (single-module
  packaging of the GS closure; multi-file mirror under
  `vendor/SocialChoiceLean/`)
- Facade: `AISafetyAtlas.SocialChoice.gibbard_satterthwaite` (`LAND-GS-002`)
- Statement: for `3 ≤ |A|`, resolute + unanimous + strategy-proof ⇒
  dictatorial (`∃ d, ∀ P, f P = {topChoice P d}`)
- Axioms: `[propext, Classical.choice, Quot.sound]` only
  (`scripts/check_print_axioms.py`)
- Scope: classical GS only — not the rest of SocialChoiceLean
- Provenance note: upstream README describes substantial AI-assisted authorship
  under Dominik Peters; treat as source-inspected community Lean

### 4.31 port path (2026-07-19)

Initial force of upstream master (4.27-class) onto Mathlib `v4.31.0` failed on
`InductionStepCase2` (`Prefers` → `.lt` instance-path drift). The port adds
`GSShim.lean` ballot-level congruence and routes profile equalities through it;
full GS (BaseCase/Common/Case1/Case2/Main) builds green under the atlas pin and
is vendored as above. Isabelle AFP reproduce path is unchanged.

## Lean 4: Attribution impossibility (DASH / XAI landscape)

AI-safety-native Lean formalization of an attribution trilemma. **Not** survey
coverage for BY-042 (unfairness of explainability) or BY-029 (unexplainability)
without a separate statement map — those survey claims are different informal
theorems.

- Upstream: [`DrakeCaraker/dash-impossibility-lean`](https://github.com/DrakeCaraker/dash-impossibility-lean)
- Authors: Drake Caraker, Bryan Arnold, David Rhoads (`CITATION.cff`)
- DOI: [10.5281/zenodo.19468379](https://doi.org/10.5281/zenodo.19468379)
- **Software license (SPDX):** `Apache-2.0`, as declared for
  `type: software` in upstream `CITATION.cff` at the pin
  (`license: Apache-2.0`). That is the license used for atlas provenance of the
  **Lean formalization**.
- **Paper vs code:** the Zenodo deposit for the same DOI is typed as a
  *preprint* with license **CC-BY-4.0**. That covers the publication PDF, not
  a substitute for the software SPDX. Do not conflate the two.
- **Caveat:** at the pin there is still **no root `LICENSE` file** and GitHub’s
  license API field is empty. `CITATION.cff` is accepted as the author-published
  SPDX signal for the software; a root `LICENSE` matching Apache-2.0 would
  strengthen external clarity but is not required to re-open the “unknown
  license” block.
- Revision inspected: `7ec3ef9813a7642fdabe5b73c71d1bed4d5488e2`
- Toolchain at pin: Lean `v4.29.0-rc8` (atlas is on `v4.33.0` — no dependency)
- Principal declaration: `DASHImpossibility.attribution_impossibility`
  in `DASHImpossibility/Trilemma.lean`
  - Under the **Rashomon property** (symmetric features admit models ranking
    them opposite ways), no ranking that is **faithful** to every model’s
    attribution order can also be **stable** across those models (and thus
    cannot be complete for all pairs while remaining fixed).
- Also of interest: `attribution_impossibility_weak` (implication faithfulness);
  GBDT-specific layers use **axioms** `gbdtModelBundle` / `gbdtBehaviorBundle`
  in `Defs.lean` (architecture scaffolding). Core trilemma proof is
  hypothesis-driven (`hrash : RashimonProperty` upstream; atlas corrects the
  spelling to `RashomonProperty`), not those axioms.
- Trust scan at pin: no `sorry` / `admit` under `DASHImpossibility/`.
- **Atlas integration (2026-07-19):** the **core trilemma** is ready to use as
  `AISafetyAtlas.Explainability.attribution_impossibility` (and `_weak`),
  vendored axiom-free under `AISafetyAtlas/Upstream/Attribution/Trilemma.lean`
  from the upstream statement/proof. Full upstream GBDT axiom layers are **not**
  vendored (strict-trust). This is **not** BY-042/BY-029 survey coverage without
  a separate statement map. Atlas + upstream software: Apache-2.0.

## Lean 4: TCSLib Fourier-analytic Arrow theorem

This is a source-inspected alternative Arrow representation, not an additional
coverage claim and not a current atlas dependency.

- Upstream: [`Shilun-Allan-Li/tcslib`](https://github.com/Shilun-Allan-Li/tcslib)
- License: Apache-2.0
- Revision: `502287d7f8d84c33421c71ce5495b08f097c47a5`
- Upstream environment: Lean 4.25.0, Mathlib revision
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, and PFR revision
  `e1095d58`.
- Module: `TCSlib.BooleanAnalysis.ArrowTheorem`
- Principal declaration: `ArrowTheorem.arrow_theorem`.
- Representation: a Kalai-style Fourier proof for three alternatives, modelling
  pairwise aggregation by an odd, `±1`-valued Boolean function; unanimity and
  acyclicity imply that the function is a dictatorship.
- Unique possible value: reusable Boolean-function, Fourier-weight, correlation,
  and influence machinery for future quantitative social-choice or learning
  results. This is materially different infrastructure, but the current atlas
  does not need it.
- Local status: source-inspected on 2026-07-19, not reproduced by the atlas.
- Integration decision: retain as provenance and a possible future interface.
  Do not add TCSLib merely to obtain a second Arrow proof. Reconsider only when
  a named downstream theorem requires its Fourier-analytic structure, then
  assess the old toolchain and additional dependency cost first.

The pinned theorem source is
[`TCSlib/BooleanAnalysis/ArrowTheorem.lean`](https://github.com/Shilun-Allan-Li/tcslib/blob/502287d7f8d84c33421c71ce5495b08f097c47a5/TCSlib/BooleanAnalysis/ArrowTheorem.lean).

## Lean 4: von Neumann–Morgenstern expected utility

This is adjacent utility-foundation evidence, not coverage of an additional
Brcic–Yampolskiy survey row.

- Upstream: [`jingyuanli-hk/vNM-Theorem-pub`](https://github.com/jingyuanli-hk/vNM-Theorem-pub)
- Author: Jingyuan Li
- License: Apache-2.0
- Revision: `89ed1680170bcf947f77bd26cdf614c1ce02222c`
- Modules and declarations:
  - `Theorem.lean`: `vNM.vNM_theorem` (expected-utility representation)
  - `Unique.lean`: `vNM.utility_uniqueness` (positive-affine uniqueness)
- Reproduction environment: Lean 4.31.0 and Mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- Local reproduction: `vNM01.Unique` passed on 2026-07-19 (1,545 jobs) at the
  4.31.0 pin (which matched the atlas toolchain at the time; the atlas moved to
  v4.33.0 on 2026-08-31 and this external lane was not re-run), with nonfatal
  source linter or deprecation warnings and no incomplete-proof tokens found by
  the source scan.
- Packaging caveat: the upstream revision contains raw Lean modules but no
  `lakefile` or `lean-toolchain`. The reproduction script supplies a pinned
  temporary Lake project, fetches a clean dependency tree, and builds the
  terminal module explicitly. It never reuses the atlas's local checkouts.
- Integration decision: keep this development as verified provenance for now.
  Do not add a dependency or copy its lottery vocabulary until a named
  downstream theorem requires expected-utility-over-lotteries infrastructure.
  The current atlas utility bridge concerns finite social aggregation and does
  not duplicate the vNM theorem.

Command:

```console
scripts/reproduce_vnm.sh
```

## Lean 4: algorithmic information theory and Chaitin incompleteness

Reproduced external coverage for survey row **BY-015** (Chaitin incompleteness).
This is not only a registry record: the atlas also exposes thin Logic wrappers
over a vendored import closure (see below).

- Upstream:
  [`AlexeyMilovanov/kolmogorov-complexity-lean`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean)
- Author: Alexey Milovanov
- License: Apache-2.0
- Revision: `005ac4c81eefe09642ef561057199d489cd79485`
- Package: `KolmogorovMathlib`
- Module: `KolmogorovMathlib.Complexity.Chaitin`
- Principal declaration: `FormalSystem.chaitinIncompleteness`
- Supporting declarations (not separate coverage claims):
  - `FormalSystem.chaitinBound`: every sound r.e. system has a constant `c`
    such that it never proves a true `K(x) > L` bound with `L > c`;
  - `chaitinGeneralized`: incompleteness for any general system that can
    express all co-r.e. relations (via an `Expresses` interface).
- Reproduction environment (pinned upstream toolchain): Lean 4.31.0 and Mathlib
  commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`v4.31.0`). This was also
  the atlas's own toolchain when it was recorded; the atlas moved to v4.33.0 on
  2026-08-31 and the vendored closure was migrated with it, while this external
  lane still reproduces upstream at its own pin. The vendored closure builds at the
  same pin without source edits.
- Local reproduction (2026-07-19):
  - trust scan over the vendored Chaitin sources: no `sorry`, `admit`, `axiom`,
    `sorryAx`, `native_decide`, `implemented_by`, or `@[extern]`;
  - `lake build` of the Chaitin modules succeeded at the pinned revision.
- Reusable upstream scope (not fully vendored): partial decompressors, plain
  and prefix conditional Kolmogorov complexity, universal decompressors,
  invariance, incompressibility, uncomputability, Kraft inequalities, and
  algorithmic probability and statistics.

### Statement-level comparison (BY-015 / survey-ref-039)

Survey informal claim (registry): a finitely specified formal theory cannot
prove arbitrarily high lower bounds on Kolmogorov complexity. The survey cites
Chaitin's *Information, Randomness And Incompleteness* (1987 collection) as
`survey-ref-039`; it does not pin a single theorem number.

Upstream encoded statement (types as printed at the pinned revision):

- `chaitinBound`: for an optimal universal machine `U` and any
  `FormalSystem U`, there exists `c` such that every enumerated proven bound
  `K(x) > L` satisfies `L ≤ c`.
- `chaitinIncompleteness`: under the same hypotheses, there exist `x` and `L`
  with `K(x) > L` true and `¬ provable (exprKGt x L)`.

`FormalSystem` packages: a computable enumerator of theorems equal to
provability, a computable parser for formulas of the form `K(x) > L`, and
soundness of those proven bounds against `plainKNat U`. That is the standard
information-theoretic form of Chaitin's incompleteness theorem, matching the
survey's informal claim at the mathematical content level.

**Relationship: `EQUIVALENT` (not `EXACT`).** Reasons not to claim exactness:
the formalization is over an abstract r.e. sound system, not a concrete
arithmetic theory (e.g. PA); plain Kolmogorov complexity relative to an
optimal conditional decompressor is fixed by the library; and the survey
citation is a collected-works pointer rather than a one-line statement
identity. The content is still the classical Chaitin bound/incompleteness
pair for complexity lower bounds, so headline coverage is appropriate.

**Integration decision:** BY-015 is covered by the external pin and by thin
atlas wrappers `AISafetyAtlas.Logic.chaitin_incompleteness` and
`chaitin_bound`. Upstream is **not** a Lake dependency: Lean `module`
packages cannot import non-module libraries, so the import closure for
Chaitin is vendored under `AISafetyAtlas/Upstream/KolmogorovMathlib/` with
`module` / `public` / `@[expose]` adaptations only. Do not mirror the full
upstream API.

The pinned source for Chaitin is
[`KolmogorovMathlib/Complexity/Chaitin.lean`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/005ac4c81eefe09642ef561057199d489cd79485/KolmogorovMathlib/Complexity/Chaitin.lean).

Command:

```console
scripts/reproduce_chaitin.sh
```

## Lean 4: Gödel, Tarski, and Löb (Foundation)

Classical arithmetic incompleteness/undefinability from a single **Lake
dependency** (module library — no vendoring):

- Upstream:
  [`FormalizedFormalLogic/Foundation`](https://github.com/FormalizedFormalLogic/Foundation)
- License: Apache-2.0
- Revision: `30a16ffa93d79d73ab4d02427fa00f50e039bf29`
- Toolchain: Lean 4.33.0 / Mathlib `v4.33.0` (matches the atlas pin).

| Survey | Module | Declaration | Relationship | Atlas alias |
|---|---|---|---|---|
| BY-013 | `…Incompleteness.First` | `exists_true_but_unprovable_sentence` | `EQUIVALENT` | `Logic.godel_first_incompleteness` |
| BY-013 (companion) | `…Incompleteness.Second` | `consistent_unprovable` | `RELATED` | `Logic.godel_second_incompleteness` |
| BY-016 | `…Incompleteness.Tarski` | `undefinability_of_truth` | `EQUIVALENT` | `Logic.tarski_undefinability` |
| BY-027 | `…Incompleteness.Löb` | `löb_theorem` | `EQUIVALENT` | `Logic.loeb` |

### Statement notes

- **BY-013:** survey “true unprovable statements” ↔ Gödel I; Gödel II is a
  different theorem (`T ⊬ Con(T)`), recorded `RELATED` on the same row so it is
  not double-counted.
- **BY-016:** survey “truth not definable in the language” ↔
  `undefinability_of_truth` (no arithmetic \(\tau\) with
  \(\mathbb{N}\models\sigma \leftrightarrow \mathbb{N}\models\tau[\ulcorner\sigma\urcorner]\)).
- **BY-027:** survey Löb/unverifiability ↔ classical Löb schema
  \(T\vdash\mathrm{Prov}(\sigma)\to\sigma \Rightarrow T\vdash\sigma\). The informal
  “cannot prove own soundness” reading is the usual consequence of this schema
  under the theorem’s hypotheses, not a weaker separate statement.

**Trust base.** Atlas Logic wrappers depend on the standard classical axioms
only (no `sorry` in the atlas closure). Foundation rebuilds with
`lake build AISafetyAtlas`.

Coverage policy: [`logic-incompleteness.md`](../guide/logic-incompleteness.md).
Chaitin vendor layout:
[`AISafetyAtlas/Upstream/KolmogorovMathlib/README.md`](../../AISafetyAtlas/Upstream/KolmogorovMathlib/README.md).

## Isabelle/HOL: CondNormReasHOL (Parfit mere addition; landscape)

- Upstream: [AFP — CondNormReasHOL](https://www.isa-afp.org/entries/CondNormReasHOL.html)
- Authors: Xavier Parent, Christoph Benzmüller
- License: BSD-3-Clause (AFP)
- Release: `2026-02-06`; archive SHA-256
  `10c3aa794a3cafcfb08a784e11515933162a490b32fc0cdb0cf88f489accdb38`
- Session: `CondNormReasHOL` (HOL only)
- Landscape: `LAND-PE-001` — **RELATED** to BY-008 (population-ethics adjacent);
  **not** EXACT Arrhenius 2011
- Reproduce: `scripts/reproduce_isabelle.sh condnorm`
- Evidence: [`a1-condnorm-parfit-triage.md`](a1-condnorm-parfit-triage.md)

## Isabelle/HOL: Deep_Learning (network capacity / no-flattening family)

- Upstream: [AFP — Deep_Learning](https://www.isa-afp.org/entries/Deep_Learning.html)
- Author: Alexander Bentkamp
- License: BSD-3-Clause (AFP)
- Release: `2026-02-06`; entry archive SHA-256
  `018557d0041584239d603a7eb3700d07ed7eb2a2ca48f694820072003ebf430d`;
  full AFP tree for build SHA-256
  `b059edd46073479ee8dde45004c2346a7365e5d94cded49d27257cfea66c8879`
- Session: `Deep_Learning` (via full AFP `thys/`; deps include Jordan_Normal_Form,
  Polynomials, VectorSpace, …)
- Principal declarations: `fundamental_theorem_network_capacity` (+ `_v2`, `_v3`)
- Landscape: `LAND-DL-001` — **RELATED** to BY-035 informal no-flattening claim;
  not EXACT Lin–Tegmark–Rolnick 2017 citation alone
- Reproduce: `scripts/reproduce_isabelle.sh deep-learning`
- Evidence: [`a2-deep-learning-by035-triage.md`](a2-deep-learning-by035-triage.md)

## BY-001 Unobservability — AFP candidates cleared

Keyword AFP “observability” hits (FSM testing, protocol refinement) are
**DISTINCT** from Klamka control-theoretic unobservability. Candidates removed;
see [`a3-by001-unobservability-triage.md`](a3-by001-unobservability-triage.md).

**Superseded in part, 2026-09-11.** That verdict is still correct about the AFP
hits it inspected, and its closing sentence “nothing existing covers it” is not.
The six corpora behind it — `mathlib`, `isabelle-afp`, `rocq-undecidability`,
`hol4`, `hol-light`, `agda-stdlib` — contain no member for the wider Lean
ecosystem, so a Lean development outside Mathlib was invisible to it. One
exists; see the next section.

## Lean 4: LeanForControl — Kalman and Hautus criteria, adapted (BY-001, BY-002)

Surveyed and adapted 2026-09-11.
[`AnandGokhale/LeanForControl`](https://github.com/AnandGokhale/LeanForControl),
Apache-2.0, Lean `v4.30.0-rc2` + Mathlib `v4.30.0-rc2`, commit `c5cedca`
(2026-09-01), ~7.6k lines. “The intent of this repository is to build a database
of control theoretic proofs in lean.”

**Split, and only one half is usable here.**

| Tree | Lines | Axioms beyond the allowlist | Disposition |
|---|---|---|---|
| `LinearSystems/` | 918 | none; Mathlib and `Architect` only | **adapted in-tree** as `AISafetyAtlas.LinearSystems` |
| `Stability/`, `Comparison/`, `ODEs/`, `Dini/`, `Analysis/` | ~6.6k | seven custom `axiom`s | **not taken** |

The seven are `exists_unique_trajectory` and `scalar_ode_exists_interval` (ODE
existence and uniqueness — an assumed Picard–Lindelöf, which Mathlib proves),
`exists_classKLGlobal_of_stability_properties`,
`exists_classK_minorant_lipschitz`, `ClassK.exists_global_extension`,
`exists_strictMono_lower_bound`, and `exists_strictMono_upper_bound_global`.
Lyapunov, LaSalle and the class-K comparison library rest on them, so that half
would not pass `check_print_axioms.py`. The upstream README states the axioms
plainly; no `sorry` anywhere in the tree.

**What was adapted.** Observability and controllability matrices, both Kalman
rank criteria, the unobservable subspace, both Hautus eigenvalue tests over
`ℂ`, and the duality. Provenance per file header (upstream path, SHA-256, atlas
changes); notice in
[`AISafetyAtlas/Upstream/LICENSE-NOTICE`](../../AISafetyAtlas/Upstream/LICENSE-NOTICE);
registry row `LAND-LINSYS-001`. Adapted rather than vendored: the namespace,
module boundary and Mathlib version all move, and two proofs needed repair at
`v4.33.0`.

**Disposition against BY-001 and BY-002: the *adapted* layer is still not
coverage, and both rows are nonetheless covered.** The adapted layer is
algebraic — no trajectory, no solution, no output signal — so it does not state
“the state cannot be reconstructed from the outputs”, and its `TRIAGED_DISTINCT`
verdict was right about that. **What changed on 2026-09-20 is that the atlas
states it anyway, in modules that are not adapted from anywhere**, and on
2026-09-21 both rows were promoted to covered on the strength of those. The
verdicts are retired into the rows' notes, since policy rejects a statability
verdict on a row that carries Lean.
`AISafetyAtlas.LinearSystems.Dynamics` and `…Flow` are atlas-original and carry
print's two properties with each algebraic criterion proved equivalent to the
one named for it; the decisive reason building beat porting is that this
upstream development has an analysis layer and a reachability file that are not
connected to each other. Klamka 1972, which both rows cite, was obtained from
the maintainer and read on 2026-09-11; section 25 of the coverage audit grades
it statement by statement. Full reasoning:
[`by001-by002-linear-systems-triage.md`](by001-by002-linear-systems-triage.md).

## Lean 4: Tau Ceti — the Morse lemma in a Banach space (vendored)

Surveyed and vendored 2026-09-05. [`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti)
is a Lean library downstream of Mathlib, **incubated by the Lean FRO and the
Mathlib Initiative**, whose mathematics is AI-authored against human-written
roadmaps in a separate repository and reviewed against human-written rubrics in a
third. Apache-2.0. At the surveyed revision: 4,430 files, 1,022,170 lines, of
which nine contain `sorry` and none of those are under `Analysis/`.

It contains what the frontier-lab survey above did not find and what Mathlib does
not have: **the Morse lemma in a Banach space**, in the Palais form — near a
nondegenerate critical point there are coordinates in which a smooth function is
exactly its Hessian quadratic form.

Eight modules, 1,396 lines, are vendored under [`vendor/TauCeti/`](../../vendor/TauCeti/):
the Morse lemma and its dependency cone (Hadamard factorisation, averaged
Hessian, parametric integrals, second-derivative transformation, and an analytic
square root near `1` in a Banach algebra). The pin, the two-line backport, the
build and axiom state, and a **declaration-by-declaration statement-fidelity
audit** are in [`vendor/TauCeti/PROVENANCE.md`](../../vendor/TauCeti/PROVENANCE.md).

Vendored rather than required because Tau Ceti pins Lean `v4.34.0-rc2` on Mathlib
`master` while this repository pins `v4.33.0` through PFR, Foundation and
AddCombi, and Lake resolves one Mathlib for the whole build.

**Audit outcome: no fidelity defect found.** Two absences a consumer must carry
rather than assume are recorded there — `exists_congruence_of_symmetric_family`
does not claim its congruence family is invertible, and `exists_normal_form`
requires global `ContDiff ℝ ∞` and does not diagonalise the Hessian (Sylvester is
a separate step, held here as `hasLocalVolumeOrder_abs_of_diagonal`, which took
the diagonalisation as a hypothesis until `hasLocalVolumeOrder_abs_matrixQuadForm`
derived it from nondegeneracy and indefiniteness).

**What it does not contain**, and what MAIS-O77(b) needed: a splitting lemma for a
*degenerate* critical point (Gromoll–Meyer / Morse–Bott). Every theorem in the
vendored cone assumes nondegeneracy, and the O77 rung points are degenerate. That
absence upstream is unchanged; what changed is downstream of it. The atlas now
builds the splitting itself, as `exists_gromoll_meyer_splitting`, on top of the
vendored congruence family this section audits — so this paragraph records a gap
in the vendored package, not an obstacle to O77(b).

Beyond the vendored cone, the parts of Tau Ceti adjacent to this repository's
analysis layer are `Analysis/Calculus/{Sard, ImplicitFunctionTheorem,
InverseFunctionTheorem, ParametricFDeriv}`, `Analysis/Fredholm` (a
Lyapunov–Schmidt normal form), `Analysis/PositiveDefinite`, and
`Probability/{Kernel, Martingale, Moments, Ergodic}`. It reaches **none** of the
logic, computability, social-choice, information-theory or causal layers: searches
for entropy, KL divergence, conditional independence, d-separation, concentration
inequalities and singular values return zero files. It is a pure-mathematics
substrate, not a safety library, which is the division this repository wants.

## Lean 4: audieleon/goodhart — Skalse and Ng, reproduced and read (BY-037)

Reproduced 2026-07-28, statements read 2026-09-10.
[`audieleon/goodhart`](https://github.com/audieleon/goodhart) at revision
`29128f3f9bcafb30d019682b63c1b582bcadf7b9` — re-cloned on the reading date and
still that revision. Apache-2.0, no `NOTICE` file. It is a Python reward-analysis
tool with a Lean proof tree beside it; the tool's rules link to the theorems.
It is the strongest of four Lean leads catalogued on BY-037 and the only
`REPRODUCED` external Lean body outside the six pinned corpora, which is why it
belongs here.

**Reproduction.** Built independently in an isolated elan 4.2.3 toolchain at the
repository's own pins — Lean `v4.30.0-rc2`, Mathlib
`9268b22206b0425419498769f780a91dee03bcf3` — with `lake exe cache get` then
`lake build`: 3,313 jobs, exit 0. Axiom audit on `skalse_theorem1`,
`skalse_theorem3_only_if`, `skalse_corollary3`, `ng_vstar_shaped`,
`ng_qstar_shaped` and `ng_shaping_preserves_optimal` reports only
`[propext, Classical.choice, Quot.sound]` for each. No `sorryAx`.

**The tree.** 3,237 lines under `proofs/GoodhartProofs/`: a basic file of
arithmetic reward traps; an MDP layer carrying a finite MDP with `PMF`-valued
transitions and the Ng–Harada–Russell potential-shaping results; and a Skalse
layer of 1,351 lines across four files.

### Statement-level comparison against Skalse et al. (NeurIPS 2022)

Its model is the paper's linear algebra without the paper's reduction to it.
Values are inner products, `value R F = ∑ i, R i * F i`, and policies are plain
vectors — a `Finset (Fin d → ℝ)` in the finite files, an arbitrary `Set` in the
open-set file. The docstrings call these occupancy measures; nothing constrains
them to be any. Whether that widens or narrows the paper depends on the file.

| Declaration | Printed statement | Verdict |
|---|---|---|
| `skalse_theorem1` | Theorem 1 | **Faithful core, missing reduction.** Over an open set with both rewards non-trivial, unhackable implies equivalent — the paper's conclusion, in the coordinates its proof works in. The printed theorem quantifies over MDPs and concludes for policy sets containing an open set; Propositions 1–2 and Lemma 1, which carry an MDP there, are absent. Nothing ties the dimension to the state-action count. |
| `skalse_existence_two`, `skalse_existence_general` | Theorem 2 | **Not Theorem 2.** Both are self-labelled weak versions and both produce a witness that is trivial on the policy set — the general one uses the zero reward. Definition 1's convention and Theorem 2's own wording exclude exactly those witnesses. |
| `skalse_existence_nontrivial_three` | Theorem 2, three-policy case | **A special case with supplied structure.** Needs three policies with three distinct values and a second reward that opposes one pair and is neutral on another. The paper derives the existence of such a direction; here it is a hypothesis. |
| `skalse_theorem3_only_if` | Theorem 3, one direction | **Content assumed, not derived.** The hypothesis is that every equality-preserving reward is a scalar multiple of the first — a restatement of the printed dimension condition failing, not a consequence of it. The linear-algebra bridge that makes Theorem 3 a theorem is what is missing. |
| `skalse_theorem3_if`, `skalse_corollary3` | Theorem 3 other direction, Corollary 3 | **Three-policy instances.** Same supplied structure as above; not the printed iff, and not Corollary 3's quantifier over finite policy sets. |
| `two_policy_nontrivial_impossible`, `two_policy_strong_impossible` | — | **A refutation of the printed Theorem 2 on a two-element policy set**, and the most valuable declarations in the tree. With the true reward non-trivial there, a non-trivial unhackable proxy must be equivalent to it. The paper's proof has an off-by-one in its trivial-subspace dimension count; the argument is written out in [`by037-by038-goodhart-campbell-plan.md`](by037-by038-goodhart-campbell-plan.md) and was reached there from the printed proof, independently of this repository. |

On the Ng side, the registry's earlier assessment stands after reading Theorem 1
in the source: `ng_necessity_lemma3` proves an algebraic action-dependent
ordering reversal, while Ng's necessity clause asserts that for a
non-potential-based shaping function there *exist* proper transition
probabilities and a reward function under which no optimal policy of the shaped
MDP is optimal in the original. The sufficiency half is the better match.

### Maintenance signals

Two of its own READMEs disagree. The root one claims 24 rules backed by
machine-verified Lean including formalizations of Ng 1999 and Skalse 2022, and
separately records the three-policy correction; the one under `proofs/` says of
Skalse "Not yet formalized. Future work." The tree contains the Skalse files, so
the root README and the tree agree and the `proofs/` README is stale. The
companion paper its `CITATION.cff` names — *Catching Goodhart's Law Before
Training: Static Reward Analysis with Formal Guarantees*, Sheridan, 2026 —
carries no venue, DOI or URL there, and no such paper was found by search on
2026-09-10.

### Disposition: cited, not vendored, not depended on

Not depended on: it pins Lean `v4.30.0-rc2` on Mathlib `9268b222` while this
repository pins `v4.33.0` on `db584cd6`, and Lake resolves one Mathlib for the
whole build. Not vendored: both projects are Apache-2.0 and the upstream has no
`NOTICE`, so a port would incur only §4(a)–(c), but the port would be worth
roughly 230 of 1,351 Skalse lines and would carry declarations whose names
promise more than their statements deliver into a tree whose discipline is
catching exactly that. Read as a reference proof when the atlas builds its own
Skalse layer; nothing here is copied and no attribution obligation is incurred.

## Prove2Me / Formalpedia — Jordan form exists, outside every repository (2026-09-12)

Searched while looking for Klamka's eq (5), the block-count bound recorded as the
one open half of section 25 of [`source-coverage-audit.md`](source-coverage-audit.md).

**What the repository search found: nothing.** A GitHub code search — run
unfiltered, after calibrating it against a string known to be in
`AnandGokhale/LeanForControl` — returns **no Jordan normal form in Lean
anywhere**. Every hit for `jordan_normal_form` is a reference to the Isabelle
AFP theory of that name or an entry in a list of axiom labels. Mathlib carries
generalized eigenspaces, `minpoly`, and nilpotency, and no Jordan or Weyr block
structure at the pinned revision. The only Lean `IsControllable` outside the
adapted `LinearSystems` track is quantum Lie-algebra controllability in
`Vilin97/lean-pool`, a different notion.

**What [Prove2Me](https://prove2.me) has.** Its library
[Formalpedia](https://beta.prove2.me/formalpedia) held 63,432 theorems, 58,292
Lean-checked, when this was written. Proved there, from a Hefferon *Linear
Algebra* chapter-five mission:

* a **string basis for a nilpotent linear map** — the cyclic decomposition, over
  an arbitrary field;
* a **Jordan basis** for a linear map on a finite-dimensional complex space;
* the vocabulary of similarity, Jordan blocks and Jordan matrices, over a
  commutative ring;
* the classical formula recovering the number of blocks of each size from the
  kernel dimensions of the powers of `A - μ I`.

Their own note on the first of these says Mathlib "does not provide a string
basis, a cyclic decomposition for a nilpotent map, or Jordan canonical form;
this statement fills that gap". Separately, a Bertsekas mission carries
linear-systems control theory over the reals — observability in the sense of
Bertsekas Definition 4.1.1, the unobservable-subspace consequence, and the
algebraic Riccati fixed point. A search for `Hautus` there returns **zero**.

**What was submitted, and what it is not.** Eq (5) is not in that library, so it
was filed as an open problem:

* `JordanBound.algMult_le_geomMult_mul_index` —
  [prove2.me/theorems/c576bd1e-5241-42c6-ba34-7bca4e94e329](https://prove2.me/theorems/c576bd1e-5241-42c6-ba34-7bca4e94e329)
* the algebraic multiplicity of an eigenvalue is at most the geometric
  multiplicity times the index, which is Klamka's eq (5) cleared of its division
* environment `mathlib_rev 0df444a`, Lean `v4.33.1`, the platform default

**What was contributed upward, stated and proved.** The two supporting lemmas
the Hautus pencil bound needed are atlas-original, domain-neutral linear
algebra, and Formalpedia did not hold them. Both were submitted as statements
and then closed with the atlas's own proofs, in the same environment:

* `MatrixBlockRank.rank_fromCols_le` —
  [prove2.me/theorems/ebcc89ce-abb1-475c-970a-e10eff78a363](https://prove2.me/theorems/ebcc89ce-abb1-475c-970a-e10eff78a363),
  status `Proved`
* `MatrixBlockRank.rank_fromRows_le` —
  [prove2.me/theorems/9d952a8a-96f3-4f01-8307-10e7b6b71f17](https://prove2.me/theorems/9d952a8a-96f3-4f01-8307-10e7b6b71f17),
  status `Proved`

Both are `rank_fromCols_le` and `rank_fromRows_le` of
`AISafetyAtlas.LinearSystems.MatrixLemmas`, transcribed to standalone form —
the vertical case inlines the horizontal one as a private lemma so each file
compiles alone. **This is also a portability result the atlas gets for free:**
the proofs were written against Mathlib `db584cd` at Lean `v4.33.0` and the
platform checked them unchanged against `0df444a` at `v4.33.1`.

**What was not offered upward.** The Hautus characterisations themselves,
the Kalman rank criteria and the controllability/observability duality are
Anand Gokhale's mathematics, adapted here under Apache-2.0; the platform's
statements and proofs are immutable and credit is permanent to the submitter,
so nothing derived from that work has been uploaded.

**This is a request, not a dependency, and not coverage.** The atlas builds at
Lean `v4.33.0` against Mathlib `db584cd`; the platform's environments are
`v4.33.1`, `v4.30.0` and `v4.29.0-rc3`, and it does not support reuse across its
own environments, let alone into this repository. Anything proved there would
have to be **ported**, and until it is, section 25's six `Partial` rows stay
`Partial`. Nothing in the tree depends on the outcome.

**A note on the corpus sweep this exposes.** The six corpora of
[`formalization-search.json`](formalization-search.json) are `mathlib`,
`isabelle-afp`, `rocq-undecidability`, `hol4`, `hol-light` and `agda-stdlib`.
Formalpedia is a seventh kind of place — a library that is not a repository and
not a proof assistant's standard corpus — and no recorded sweep reaches it. That
is the same gap as the one recorded for `BY-001` and `BY-002` in
[`by001-by002-linear-systems-triage.md`](by001-by002-linear-systems-triage.md),
one step further out.

## Isabelle reproduction environment

- Official image: `makarius/isabelle:Isabelle2025-2`
- Image digest: `sha256:9bd33b183c399327c5d554fc8cde27c29b5d2b20cdc6fe7a604caa3f951018fc`
- Isabelle version reported by the image: `Isabelle2025-2`
- Host architecture used: `x86_64`

The scripts verify archive hashes before extraction. Successful builds establish
the cited Isabelle statements; they do not establish a direct AI-safety bridge.

## Frontier-lab Lean corpora — watchlist (surveyed 2026-09-05)

Not vendored, not depended on, not graded against. Recorded because three
organisations began publishing large Lean 4 developments in August–September
2026 and a later atlas gap may be answered by one of them. Re-survey before
building any analysis or number-theory layer from scratch.

The selection rule this list is kept under is the atlas's ingestion rule:
take a result when it is a **building block used often enough** to repay the
cost of importing it, and leave it upstream when it is expensive *and*
unlikely to be reused — the frontier register is for the latter, and a thing
that is hard but broadly reusable is better waited for than built here.

| Source | Content | Licence | Toolchain |
|---|---|---|---|
| [`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem) | FLT (Frey–Serre–Ribet–Wiles). 45,945 files: `Definitions/` 1,450, `Theorems/` 14,974, `P2M/` 29,513 single-lemma Mathlib-adjacent files | Apache-2.0 | Lean 4.33.1 / Mathlib `v4.33.0` — the atlas's own line |
| [`anthropics/formal-math`](https://github.com/anthropics/formal-math) | `zeta23/`: more than two thirds of the zeros of ζ are simple and on the critical line (Alpöge–Furman, arXiv:2608.13637) | Apache-2.0 | `v4.33.0-rc2` |
| [`openai/PrimeGaps186`](https://github.com/openai/PrimeGaps186) | DHL[40,2] and gap ≤ 186, **conditional on three declared `axiom`s**, plus a Python numerical certificate | Apache-2.0 | — |
| [`openai/LongGapsBetweenPrimes`](https://github.com/openai/LongGapsBetweenPrimes) | one long-gap bound | Apache-2.0 | — |
| [`axiommath/*`](https://github.com/orgs/axiommath/repositories) | ~30 paper-artifact repositories: q-series, partitions, prime gaps, zero-free regions, a `PrimeNumberTheoremAnd` fork | mixed; **several carry no licence file** | — |

### What the survey found, and did not

Searched all three organisations for the terms the atlas's open work needs.
Zero hits, organisation-wide, for `Morse`, `MorseLemma`, `localInverse`,
`IsBoundedBilinearMap`, `RLCT`, `singular learning`, and `HasStrictFDeriv`
inside `P2M/`. `Laplace` returns eleven hits, all Laplace *transform inversion*
in the PNT fork — not Laplace's method or Watson's lemma. The `QuadraticForm`
entries in `P2M/` are ternary forms over `ℚ_p`; `Gaussian` is Gauss sums;
the 182 `Matrix` entries are Hecke and Galois-representation matrices.

So none of it reaches the singular-learning layer.

**Two claims made in the first version of this section were wrong, and are
corrected here rather than quietly edited.** It said that no corpus supplied a
Banach-space analytic inverse function theorem "that Mathlib also lacks", and
that no Morse lemma existed anywhere. Both are false.

*Mathlib has the Banach-space analytic inverse function theorem.* It is
`OpenPartialHomeomorph.analyticAt_symm'` in
`Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`: if an open partial
homeomorphism is analytic at a point with invertible derivative, its inverse is
analytic at the image. Composed with `HasStrictFDerivAt.toOpenPartialHomeomorph`
that is exactly the analytic local inverse, in any Banach space, at the pinned
revision. The original search looked in
`Mathlib/Analysis/Calculus/InverseFunctionTheorem/`, where the only analytic
statement is the scalar `AnalyticAt.analyticAt_localInverse` — a directory-scoped
search that missed a result filed under `FDeriv/`. The lesson is the one this
repository already applies to sources: a negative result from a scoped search is
a statement about the scope, not about the library.

*A Morse lemma exists.* See the Tau Ceti section below.

One item is adjacent in kind and worth knowing about:
`formal-math/zeta23/Zeta23/LinAlg/Inertia.lean` proves `posIndex_conj_le`
(inertia under pull-back) and `posIndex_add_le` for Hermitian matrices. The
atlas gets what it needs from Mathlib's
`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`, so importing this
would be duplication under **Parsimony** unless a consumer appears that the
Mathlib route cannot serve.

### The transferable part is the verification stack, not the theorems

- [`leanprover/comparator`](https://github.com/leanprover/comparator) (Apache-2.0)
  with an independent Rust kernel, [`nanoda`](https://github.com/ammkrn/nanoda_lib)
  (Apache-2.0), replays an exported environment: FLT reports
  `Checked 1052234 declarations with no errors`. This is a **second kernel**,
  which `lake exe axiom-audit` is not — the audit runs the same kernel that
  produced the proof.
- The Palomar submission layout (`Challenge.lean` / `Solution.lean` /
  `comparator.json` / `formalization.yaml`, `Challenge` restricted to Mathlib)
  lets the comparator confirm that the proved statement *and every constant it
  mentions* match the challenge. MAIS candidate submissions are Palomar-shaped,
  so `formal-math/.github/scripts/comparator-check.sh` mechanises part of the
  statement-versus-proof check the atlas currently performs by reading.
- `fermats-last-theorem/FinalCheck.lean` makes axiom drift a **build** failure
  via `#guard_msgs in #print axioms`, where the atlas checks axioms out of band.
- `openai/PrimeGaps186` discharges conditionality as declared `axiom`s with the
  condition in the README headline. The atlas uses hypotheses and a `FRONTIERS`
  row. Their form leaves a footprint in `#print axioms`; ours does not, which is
  the reason `AGENTS.md` insists a clean axiom print is not evidence. Recorded
  as a contrast, not as a recommendation to switch.
