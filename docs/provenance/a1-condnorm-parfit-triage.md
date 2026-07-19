# A1 — AFP `CondNormReasHOL` (Parfit mere addition; not Arrhenius BY-008)

Pattern-A triage of the Isabelle AFP entry that keyword-search surfaced for
BY-008 (`population ethics`). Statement-level classification only; no Lean
port.

## Upstream pin

| Field | Value |
|---|---|
| Entry | [CondNormReasHOL](https://www.isa-afp.org/entries/CondNormReasHOL.html) |
| Authors | Xavier Parent, Christoph Benzmüller |
| Release | AFP `2026-02-06` (Isabelle2025-2) |
| Archive | `https://isa-afp.org/release/afp-CondNormReasHOL-2026-02-06.tar.gz` |
| SHA-256 | `10c3aa794a3cafcfb08a784e11515933162a490b32fc0cdb0cf88f489accdb38` |
| Session | `CondNormReasHOL` (parent: `HOL` only) |
| License | BSD-3-Clause (AFP) |
| Theories | `DDLcube`, `mere_addition_opt`, `mere_addition_lewis`, `mere_addition_max` |
| Reproduce | `scripts/reproduce_isabelle.sh condnorm` |
| Companion paper | arXiv:2308.10686 |

## What is formalized

1. **Åqvist system E** for preference-based conditional obligation, via shallow
   embedding in Isabelle/HOL (metalogical correspondence lemmas `T1`–`T14` and
   related in `DDLcube.thy`).
2. **Use-case encodings of Parfit’s mere addition paradox** (a smaller form of
   the repugnant conclusion), under several betterness/transitivity variants
   (`mere_addition_*.thy`).

This is machine-checked **normative / deontic logic** applied to a classic
population-ethics *paradox*, not a full population-axiology impossibility
theorem in the Arrhenius style.

## Relationship to survey BY-008

| Item | Content |
|---|---|
| Survey source | Arrhenius 2011, “The Impossibility of a Satisfactory Population Ethics” (`survey-ref-032`) |
| Survey informal claim | No population axiology simultaneously satisfies the cited set of adequacy conditions |
| CondNorm content | Conditional obligation + mere-addition / RC-style encoding |

**Verdict: RELATED (adjacent), not EXACT or EQUIVALENT to BY-008.**

- Same *domain* (population ethics / value of variable populations).
- **Different theorem:** Parfit mere addition / repugnant-conclusion analysis ≠
  Arrhenius multi-condition impossibility package cited by Brcic–Yampolskiy.
- Landscape id: `LAND-PE-001`. Does **not** raise survey headline coverage.

## Reproduction log (2026-07-19)

```text
scripts/reproduce_isabelle.sh condnorm
# docker makarius/isabelle@sha256:9bd33b183c399327c5d554fc8cde27c29b5d2b20cdc6fe7a604caa3f951018fc
# sha256sum --check OK on archive
Finished CondNormReasHOL (0:00:07 elapsed time, exit 0)
theories: DDLcube, mere_addition_lewis, mere_addition_opt, mere_addition_max 100%
```

## Non-goals

- No Lean facade / `AISafetyAtlas` import.
- No claim that Arrhenius 2011 is machine-checked.
- Voigt “Theory X” Isabelle work (if any) is out of scope for this triage.
