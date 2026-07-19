# Logic incompleteness layer

This note names the incompleteness and undefinability results exposed under
`AISafetyAtlas.Logic` and how they relate to the survey inventory. It is
documentation of **mathematical content and coverage policy**, not an AI-safety
claim.

## What the aliases are

| Atlas declaration | Mathematical content | Survey coverage |
|---|---|---|
| `Logic.chaitin_incompleteness` | Chaitin's incompleteness for plain Kolmogorov complexity: a sound r.e. system that can express \(K(x) > L\) cannot prove arbitrarily high true lower bounds | **BY-015** (`EQUIVALENT`) |
| `Logic.chaitin_bound` | The uniform bound form of the same theorem | Same BY-015 package (wrapper) |
| `Logic.godel_first_incompleteness` | Gödel's **first** incompleteness: true unprovable arithmetic sentence | **BY-013** (`EQUIVALENT`) |
| `Logic.godel_second_incompleteness` | Gödel's **second** incompleteness: \(T \nvdash \mathrm{Con}(T)\) | **BY-013 companion** (`RELATED`) |
| `Logic.tarski_undefinability` | Tarski: arithmetic truth is not arithmetically definable | **BY-016** (`EQUIVALENT`) |
| `Logic.loeb` | Löb: if \(T \vdash \mathrm{Prov}_T(\sigma)\to\sigma\) then \(T \vdash \sigma\) | **BY-027** (`EQUIVALENT`) |

Gödel, Tarski, and Löb aliases are **classical theorems for concrete arithmetic
theories** from FormalizedFormalLogic/Foundation (not abstract axiomatized
skeletons). Chaitin is from the vendored KolmogorovMathlib pin.

## Coverage policy for BY-013

`godel_first_incompleteness` is the statement match for **BY-013** Unprovability
and is counted as coverage. `godel_second_incompleteness` is a **distinct**
companion (`RELATED` on the same row) so it is documented without
double-counting.

## Naming traps

- **Chaitin** = \(K(x)>L\) bounds (BY-015), not Gödel II.
- **Gödel I** ≠ **Gödel II** ≠ **Löb** (three different theorems).
- **Tarski undefinability** is about *truth*, not *provability* (though the
  fixed-point engine is related).
- Atlas uses ASCII `loeb` for the public name; upstream uses `löb_theorem`.

## Provenance and build layout

- **Chaitin (BY-015):** vendored under
  `AISafetyAtlas/Upstream/KolmogorovMathlib/`; reproduce with
  `scripts/reproduce_chaitin.sh`.
- **Gödel I/II, Tarski, Löb:** Lake dependency
  `FormalizedFormalLogic/Foundation` @
  `b47cf447255addf88a5d72781d0d29641948eb6e` (Apache-2.0). Modules under
  `Foundation.FirstOrder.Incompleteness.{First,Second,Tarski,Löb}`.
- Public names live only in `AISafetyAtlas.Logic`.

### Correlated Foundation risk

BY-013 (Gödel I + II companion), BY-016 (Tarski), and BY-027 (Löb) all depend on
**one** pinned Foundation revision. A Lean bump, upstream rewrite, or pin move
can desynchronize three headline coverage rows together. Reproduce the Logic
surface with:

```console
scripts/reproduce_foundation.sh
```

Prefer not to add further Foundation-only survey wrappers without a named
downstream consumer. Foundation may emit compiler warnings; atlas
`warningAsError` applies to atlas packages, not necessarily to dependencies.

Details: [`external-formalizations.md`](../provenance/external-formalizations.md).

## What these theorems do *not* say

None of them, by themselves, asserts that a particular AI system is
unverifiable, unaligned, or unsafe. Connecting them to an AI-system model
remains a separate bridge layer under `ai_bridge_status` / human review
([methodology](methodology.md)).
