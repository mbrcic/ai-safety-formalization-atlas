# AI safety literature map (how addressed)

Literature-first view: **AI-safety papers** (specs, impossibility notes, applied
computability claims) and **how the atlas addresses them**. Basics only—for
coverage estimation and triage.

This is **not** the survey theorem inventory. Table-1 BY rows and classical
sources are generated in
[`../status/paper-coverage.md`](../status/paper-coverage.md). Some papers below
also appear there as survey results; they still belong here as **literature** so
AI-safety reading lists can be scanned in one place.

## Policy

- One shared map. Do **not** add a dedicated guide per paper by default.
- Dedicated statement maps only for large fidelity gaps (robot SPA model note
  is enough; do not fork a second guide for every similar paper).
- Prefer precise decision problems over informal slogans.
- Optional structure: `atlas-ref-*` catalog keys, thin `LAND-*` rows when useful.
- Addressing a paper here does **not** by itself increase headline
  `EXACT`/`EQUIVALENT` survey coverage.

**How addressed?**

| Value | Meaning |
|---|---|
| `none` | Not addressed |
| `packaging` | See **What “packaging” means** below — **and** the survey/landscape row that owns the Lean object is identified |
| `packaging-pattern` | Same classical pattern is available under atlas vocabulary, but **this survey row has no dedicated Lean artifact** (do not treat as row formalized) |
| `related-formal` | Lean/Isabelle formalization related to the paper’s claim; not EXACT paper fidelity |
| `survey-exact` | Survey row with reproduced EXACT/EQUIVALENT classical theorem the paper rests on |
| `full` | Rare: formalization claimed EXACT/EQUIVALENT to *this* paper’s statement |

## What “packaging” means

**Packaging** = the atlas already has (or reuses) the **classical theorem**, and
exposes it under **names and types** that match how an AI-safety paper *uses*
that theorem—without claiming a line-by-line formalization of that paper.

Typical shape:

1. **Classical core** — e.g. Rice or halting in Mathlib / Foundation (survey
   math row such as BY-012).
2. **Thin vocabulary layer** — e.g. `Agent`, `SafetySpec`,
   `BehavioralSafetyVerifier`, `no_behavioral_safety_verifier`.
3. **Paper** — states the same pattern with a **named property** (I/O judge
   “alignment”, containment, harm, …).

Then we say the paper is addressed by **packaging**: a reader can find the
machine-checked limit under AI-safety-facing names, and the notes say which
paper-shaped claim that matches.

| Packaging **is** | Packaging **is not** |
|---|---|
| Reusing Rice/halting under agent vocabulary | A new proof of Rice for each paper |
| Matching the paper’s *pattern* (programs + nontrivial *P* + no total decider) | EXACT fidelity to the paper’s prose, definitions, or figures |
| Enough for coverage estimation (“this lit is covered by AgentBehavior”) | A claim that every informal slogan in the paper is a theorem |
| Shared by Melo-style and Alfonseca-style notes when only *P*’s name changes | Automatic coverage of robot SPA / switching constructions (`related-formal`) |

**Example:** Melo and Alfonseca both reduce to Rice on a nontrivial property of
programs. The atlas packages that once as AgentBehavior / `Verification.rice`.
Melo’s *P* ≈ “always passes I/O judge”; Alfonseca’s *P* ≈ containment/harm.
Neither requires a second copy of Rice—only a row in this map stating which
*P* and which hook.

**Contrast:** van Leeuwen & Wiedermann is **`related-formal`**: there is a
dedicated robot bridge with an extra certificate (`SwitchingConstruction`), not
only a rename of Rice.

## Literature → atlas

| Paper (AI safety lit) | Catalog | Decision problem (1 line) | How addressed | Atlas hook | Survey row? | Notes |
|---|---|---|---|---|---|---|
| Melo, Máximo, Soma, Castro, [arXiv:2408.08995](https://arxiv.org/abs/2408.08995) (2024; Sci. Rep. 2025) | `atlas-ref-melo-2024` | Whether an arbitrary program always satisfices a fixed non-trivial I/O judge is undecidable (Rice / halting) | packaging | `AgentBehavior.no_behavioral_safety_verifier` · `LAND-MELO-001` | no (related lit only) | Property = “always passes judge”; **same Rice pattern as Alfonseca**, different named property |
| Alfonseca et al., *Superintelligence cannot be contained* (JAIR 2021) | `survey-ref-056` | Perfect containment of a superintelligent program is undecidable; Rice on non-trivial TM properties (e.g. harm) | packaging-pattern | Pattern only: AgentBehavior / Rice **if** containment is modeled as a nontrivial extensional code property | **BY-025** (`MAPPED`, no Lean artifact) | **≈ Melo in method**, different *P*. **Do not read as BY-025 formalized.** No containment-named declaration; survey row still open. |
| van Leeuwen & Wiedermann, *Impossibility Results for the Online Verification of Ethical and Legal Behaviour of Robots* (UU-PCS-2021-02, 2021) | `survey-ref-069` | No total algorithmic observer for always-*P* on robots with potentially unbounded memory, for non-trivial robot property *P* (Thm 1 / Cor 1) | related-formal | `Robot.action_safety_unverifiable` | **BY-033** | Cousin with **switching construction**; SPA via certificate; CT-3 2026-07-19: keep **RELATED**, bridge **REVIEWED** (scoped interpretation); model [`robot-verification-model.md`](robot-verification-model.md); CT-3 [`../bridges/ct3-robot-review-package.md`](../bridges/ct3-robot-review-package.md) |

Add rows when triaging further AI-safety impossibility / verification papers.
One line per decision problem and short notes.

### Same family, different inventory role

| Literature | Pattern | Role in atlas |
|---|---|---|
| **Melo et al.** | Rice + *P* = non-trivial I/O judge satisfaction | Not Table-1. **Packaging** via AgentBehavior (core math BY-012). |
| **Alfonseca et al.** | Rice + *P* = containment / harm / … | Table-1 **BY-025** still **MAPPED**. Same **pattern** as AgentBehavior/Rice if *P* fits; **not** row-level packaging or LEAN_AVAILABLE. |
| **van Leeuwen & Wiedermann** | Non-trivial always-*P* + effective switching τ → no total observer | Table-1 **BY-033**. **Related-formal** robot bridge. |

Melo ≈ Alfonseca in method (Rice on a non-trivial property of programs); they differ
in **which property** is named and in survey packaging. Robot adds construction
structure. Do not merge into one formalization claim.

## Condensed fidelity (only when useful)

### Melo et al. / Alfonseca et al. (Rice + named property)

Same pattern; swap the property name.

| Notion | Melo | Alfonseca | Atlas packaging |
|---|---|---|---|
| Agent as program/TM | yes | yes | `Agent` ≔ `Code` |
| Non-trivial property *P* | I/O judge always satisfied | containment / harm / … | `SafetySpec` + `SpecNontrivial` (if *P* is extensional on behavior/codes) |
| Total decider for all programs | yes | yes (containment problem) | `BehavioralSafetyVerifier` |
| Undecidability | Rice | Rice (their Cor. on containment; also cite Rice on harm) | `no_behavioral_safety_verifier` / `Verification.rice` |
| Extra material | always-halting architectures | superintelligence narrative, simulation arguments | not formalized |

### van Leeuwen & Wiedermann (robot)

| Notion | Atlas | Match |
|---|---|---|
| Always-*P* on action traces | `AlwaysSatisfies` | related |
| Structured programs / SPA | `structured` predicate only | weak |
| Non-trivial *P* (Def. 3) + τ construction | `SwitchingConstruction` (assumed) | related (not derived) |
| No total observer | `¬ Nonempty Verifier` | yes (conditional) |
| Unbounded memory, ethics instance | interface + docs | not mechanized as ethics |

Full model note: [`robot-verification-model.md`](robot-verification-model.md).

## How to estimate coverage

1. **AI safety lit addressed?** → this table (`how addressed` column).  
2. **Survey theorem inventory?** → [`paper-coverage.md`](../status/paper-coverage.md).  
3. A paper can appear in both (e.g. robot = lit here + BY-033 there); count
   **formalization status once** on the survey row for headline metrics.

## Pointers

- Survey/paper formalization table: [`../status/paper-coverage.md`](../status/paper-coverage.md)
- BY-012 review: [`../bridges/review-by-012-agentbehavior.md`](../bridges/review-by-012-agentbehavior.md)
- Robot model / CT-3: [`robot-verification-model.md`](robot-verification-model.md),
  [`../bridges/ct3-robot-review-package.md`](../bridges/ct3-robot-review-package.md)
- Lean: `AgentBehavior.lean`, `Verification/Robot.lean`
