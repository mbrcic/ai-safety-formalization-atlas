# Where to look before you build it

`lean-parsimony.md` says to reuse a maintained Lean result before porting
another proof, and `ledger-coverage.md` says a claim that something does not
exist needs a `novelty_checks` record. Both rules are mandatory and neither
names a place to look. This file is that list.

## Search order

1. **The pins you already build against.** Everything in `lake-manifest.json` is
   on disk under `.lake/packages/` at a fixed revision, so a search there is
   free, offline, and reproducible. Search this first — most "Mathlib does not
   have it" claims die here.
2. **The vendored trees** under `vendor/`, which are in this repository and
   already audited.
3. **The wider Lean ecosystem**, below. Not dependencies; a search target and a
   reuse candidate, in that order.
4. **The non-Lean corpora**, when the claim is that *no* formalization exists
   rather than that Lean lacks one.

## Already on disk

| what | where | note |
|---|---|---|
| Mathlib | `.lake/packages/mathlib` | **the revision that matters is the one in `lake-manifest.json`**, not the older snapshot recorded under `corpora.mathlib` in `formalization-search.json`. Two Mathlib revisions appear in this repository and they are not the same |
| PFR, Foundation, AddCombi | `.lake/packages/` | additive combinatorics, first-order logic, entropy |
| `plausible`, `aesop`, `batteries` | `.lake/packages/` | tactics; `plausible` is measured but banned from commits |
| `LeanSearchClient` | `.lake/packages/` | already a dependency: `leansearch` and `loogle` queries from inside Lean |
| vendored | `vendor/` | in-tree, with a `PROVENANCE.md` recording scope and pin |

## Ecosystem candidates

Reuse candidates, none of them dependencies. Adding one is a maintainer
decision; searching one is not.

| library | covers | status |
|---|---|---|
| [`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti) | analysis downstream of Mathlib, incubated by the Lean FRO; Morse theory | partly vendored elsewhere in the project; the untouched parts are still worth searching |
| [`Jiyuan-Tan/CausalSmith`](https://github.com/Jiyuan-Tan/CausalSmith) | the `Causalean` package: structural causal models, interventions, graph separation, identification, potential outcomes, causal discovery, minimax estimation | **renamed from `CausalForge`.** Directly overlaps the causal substrate. Toolchain ahead of ours, periodically synced, and **no revision is pinned anywhere in this project** — pin one before citing a measurement against it |
| [`Lean-MoDS/StatsMLlib`](https://github.com/Lean-MoDS/StatsMLlib) | statistical learning and probability | candidate |
| [`lean-dojo/TorchLean`](https://github.com/lean-dojo/TorchLean) | autograd, code generation | candidate |
| [Formalpedia](https://prove2.me/formalpedia) | cross-system index of formalized results | an index, not a library — use it to find where a result lives, not as evidence of absence |

## What a novelty claim may cite

A `novelty_checks` record is evidence, so it must be reproducible by someone
who has only this repository and the revision you name.

**Evidence** is a content or phrase search over a tree pinned at a recorded
revision, with the corpus, the revision, the date, and *what the search did not
cover* all written down. That last field is not a formality: a phrase search
cannot find a declaration stated under a name none of the phrases match, and the
record has to say so.

**Not evidence**, however useful: `leansearch`, `loogle`, `lean-explore` and any
other semantic or type-pattern index. Their index revision is not pinned here,
so a miss is not reproducible and cannot support an absence claim.

Use them anyway, in the other direction. Semantic search attacks exactly the
weakness a phrase search admits to, so a semantic pass that also finds nothing
is worth running before you write the record — and worth mentioning in it as a
second, weaker check. It is finding something that matters: one hit and the
absence claim is simply wrong, which is the cheapest possible outcome.
