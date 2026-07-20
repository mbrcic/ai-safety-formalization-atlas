# SocialChoiceLean GS provenance (vendored)

| Field | Value |
|---|---|
| Upstream | https://github.com/DominikPeters/SocialChoiceLean |
| Fork / port | https://github.com/mbrcic/SocialChoiceLean branch `port/lean-4.31` |
| Pin revision | `74f491b` |
| License | MIT (upstream README; text in `LICENSE`) |
| Principal declaration | `SocialChoice.gibbard_satterthwaite` |
| Atlas facade | `AISafetyAtlas.SocialChoice.gibbard_satterthwaite` |
| Scope | Classical GS only. Not the full SocialChoiceLean package. |

## Atlas adaptations

* Dropped `Meta.lean` / `@[scAxiom]` (doc tooling only).
* `Unanimity.lean`: definition only (dropped Meta-dependent preservation lemma).
* `Strategyproofness.lean`: `updateProfile` + `ResoluteStrategyproofness` only.
* Includes the 4.31 `GSShim.lean` ballot-level congruence helpers from the port.

## Packaging note

The GS proof is redistributed **inlined** as a single public module,
`AISafetyAtlas/Upstream/GibbardSatterthwaite.lean` (imports Mathlib only), which
is part of the `AISafetyAtlas` Lake library and compiles in the atlas 4.31 build
closure. There is **no** separate `SocialChoice` Lake library and no `require` on
this directory in `lakefile.toml`.

This `vendor/SocialChoiceLean/` tree is the original multi-file upstream source,
kept for **provenance and MIT attribution only** — it is not a build target. The
original multi-file non-module layout is not importable from the AISafetyAtlas
module package; collapsing to one public module preserves proof tactics without
per-def `@[expose]` across a graph of files.
