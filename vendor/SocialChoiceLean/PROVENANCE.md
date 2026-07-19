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
* Built as a separate Lake library (`SocialChoice` in `lakefile.toml`) so proofs
  stay outside the AISafetyAtlas public-module boundary (same pattern as the
  Foundation dependency).
* Includes the 4.31 `GSShim.lean` ballot-level congruence helpers from the port.

## Packaging note

Multi-file non-module Lake lib is not importable from the AISafetyAtlas module
package. Collapsing to one public module preserves proof tactics without
per-def `@[expose]` across a graph of files.
