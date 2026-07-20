# A2 — AFP `Deep_Learning` vs BY-035 (no-flattening / depth separation)

Pattern-A triage of Bentkamp’s AFP formalization of deep-vs-shallow network
expressiveness (Cohen et al. style) against survey BY-035.

## Upstream pin

| Field | Value |
|---|---|
| Entry | [Deep_Learning](https://www.isa-afp.org/entries/Deep_Learning.html) |
| Author | Alexander Bentkamp |
| Release | AFP `2026-02-06` (Isabelle2025-2) |
| Full AFP archive (build) | `https://isa-afp.org/release/afp-2026-02-06.tar.gz` |
| Full AFP SHA-256 | `b059edd46073479ee8dde45004c2346a7365e5d94cded49d27257cfea66c8879` |
| Entry-only archive (source pin) | `https://isa-afp.org/release/afp-Deep_Learning-2026-02-06.tar.gz` |
| Entry-only SHA-256 | `018557d0041584239d603a7eb3700d07ed7eb2a2ca48f694820072003ebf430d` |
| Session | `Deep_Learning` (parent `HOL-Probability`; AFP deps: `Jordan_Normal_Form`, `Polynomial_Interpolation`, `Polynomials`, `VectorSpace`, …) |
| Principal declarations | `fundamental_theorem_network_capacity`, `_v2`, `_v3` in `DL_Fundamental_Theorem_Network_Capacity.thy` |
| License | BSD-3-Clause (AFP) |
| Reproduce | `scripts/reproduce_isabelle.sh deep-learning` |

Why full AFP for reproduce: the entry’s `ROOT` pulls multiple AFP sessions; the
single-entry tarball alone does not supply them. The harness builds against the
pinned full release tree (`thys/`) for a boring green session build.

## What is formalized

Abstract (AFP): formalization of Cohen et al. (2015) theoretical evidence for
**superiority of deep over shallow** networks; simplifications/generalizations
for Isabelle’s type system; libraries for tensors, rank, Lebesgue measure,
multivariate polynomials.

Headline theorems (paraphrase of Isabelle statements):

- Almost everywhere (Lebesgue) on weight space, a deep model’s associated
  tensor has CP-rank at least \(r^{N/2}\).
- Almost everywhere, there is **no** shallow network with intermediate width
  \(Z < r^{N/2}\) that matches the deep model on all inputs of the prescribed
  shape (`fundamental_theorem_network_capacity_v2` / `_v3`).

This is the classical **depth separation / no-flattening** style result:
functions efficiently realized by deep nets require shallow nets with
inefficiently large intermediate size (for almost all weights).

## Relationship to survey BY-035

| Field | Value |
|---|---|
| BY-035 name | No-flattening theorems for deep learning |
| Informal claim | Some functions efficiently represented by deep networks require inefficiently large shallow representations. |
| Survey source | `survey-ref-072` (as recorded in registry) |

**Verdict: RELATED (strong statement-level kinship), not automatic EXACT for every cited paper under BY-035.**

- Matches the **informal claim** of BY-035 (deep vs shallow capacity / no free
  flatten into small shallow nets).
- Formal object is the **Cohen–Bentkamp network-capacity theorem** (measure-theoretic
  almost-everywhere statement on weights), not a blanket formalization of every
  paper that may appear under survey-ref-072.
- Landscape id: `LAND-DL-001`. Does **not** by itself increase headline
  EXACT/EQUIVALENT survey coverage unless later promoted with full source map.

Registry: BY-035 notes updated to point at this triage; no EXACT formalization
row until a dedicated source-by-source map is written.

## Reproduction

```text
scripts/reproduce_isabelle.sh deep-learning
# Full AFP 2026-02-06 pin; session Deep_Learning
```

Log path for this integration: implementer scratch
`deep-learning-build.log` (and/or harness stdout).

## Non-goals

- No Lean port of tensors / Lebesgue development.
- No claim that all deep-learning theory in the survey is covered.
