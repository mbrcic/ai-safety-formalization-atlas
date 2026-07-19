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
- **Integration decision (closed 2026-07-19):** Isabelle
  `Gibbard_Satterthwaite` is the **reproduced landscape formalization** for GS
  (Isabelle only; no Lean interface; landscape id `LAND-GS-001` in
  [`landscape.yaml`](../../landscape.yaml); not a Table-1 BY ID). “Reproduced”
  means the pinned AFP session rebuilds via the script below — it is **not**
  CI-integrated and not importable from Lean. Do not port GS from Isabelle into
  Lean. Atlas Arrow remains CC Liang + utility bridge. A Lean GS facade is
  **not** planned unless upstream becomes a boring 4.31+ dependency (see below).

Command:

```console
scripts/reproduce_isabelle.sh arrow
```

## Lean 4: Gibbard–Satterthwaite (SocialChoiceLean) — deficient, not used

Existing Lean formalization of classical GS (not a survey-row coverage claim).
**Not an atlas dependency.** Kept only as inspected landscape evidence.

- Upstream: [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean)
- Domain supervisor: Dominik Peters (CNRS / LAMSADE, computational social choice)
- License: **MIT** (stated in README; no separate LICENSE file in tree at pin)
- Revision inspected: `0331c7b237994e10cd893e17945a8445e2422e17` (clone HEAD 2026-07-19)
- Toolchain at pin: Lean `v4.27.0-rc1`; lakefile pins Mathlib to **`master`**
  (not an immutable Mathlib rev — blocks strict atlas reproduction until pinned)
- Module: `SocialChoice.Impossibilities.GibbardSatterthwaite.Main`
- Principal declaration: `SocialChoice.gibbard_satterthwaite`
  - For `3 ≤ |A|`, resolute, unanimous, strategy-proof voting rules are
    dictatorial (`∃ d, ∀ P, f P = {topChoice P d}`).
- Trust scan (sources at pin): no `sorry` / `admit` in `SocialChoice/`.
- Provenance note: README describes substantial AI-assisted (“vibe-proving”)
  authorship under Dominik Peters; treat as **source-inspected community Lean**,
  not peer-reviewed formalization paper-grade, **not atlas-canonical**.

### 4.31 force experiment (2026-07-19) — closed

Tried path (1): force SocialChoiceLean onto Lean/Mathlib `v4.31.0` (atlas pin)
in an isolated clone (`/tmp/socialchoice-431`). Outcomes:

- `lake update` to Mathlib `v4.31.0` succeeded.
- After ballot-equality proof repair (class-valued `LinearOrder` + `simp` no
  longer rewrites Prefers instances on 4.31): **BaseCase**, **Common**, and
  **InductionStepCase1** built green.
- **InductionStepCase2** (~1.8k lines) still had ~70 errors of the same class;
  **Main** blocked. No full GS green build under 4.31.
- Dual-toolchain / side-by-side 4.33 was rejected earlier (Lake is one toolchain;
  atlas pin stays 4.31).

### Integration decision (final for this cycle)

Per atlas policy (prefer Lean; use other provers when Lean is missing or
deficient): **Lean GS is deficient under the atlas pin.** The reproduced
landscape formalization is Isabelle `Gibbard_Satterthwaite` via
`scripts/reproduce_isabelle.sh arrow` (not a Lean research interface). **Do
not** vendor SocialChoiceLean, **do not** add
`AISafetyAtlas…gibbard_satterthwaite` until upstream is a boring 4.31+ pin with
a green full GS build (or a reworked human-owned proof). **No Isabelle→Lean
port.** Reopen only if a named consumer needs a Lean statement.

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
- Toolchain at pin: Lean `v4.29.0-rc8` (atlas is on `v4.31.0` — no dependency)
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
Brčić–Yampolskiy survey row.

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
  4.31.0 pin (matching the atlas toolchain after the downgrade), with nonfatal
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
  commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`v4.31.0`). This is now
  also the atlas's own toolchain, so the vendored closure builds in-tree at the
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
- Revision: `b47cf447255addf88a5d72781d0d29641948eb6e`
- Toolchain: Lean 4.31.0 / Mathlib `v4.31.0` (matches the atlas pin).

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

## Isabelle reproduction environment

- Official image: `makarius/isabelle:Isabelle2025-2`
- Image digest: `sha256:9bd33b183c399327c5d554fc8cde27c29b5d2b20cdc6fe7a604caa3f951018fc`
- Isabelle version reported by the image: `Isabelle2025-2`
- Host architecture used: `x86_64`

The scripts verify archive hashes before extraction. Successful builds establish
the cited Isabelle statements; they do not establish a direct AI-safety bridge.
