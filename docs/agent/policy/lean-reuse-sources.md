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

## Where the mathematics is

Reuse beats build, so the first question is *which library would already have
this*. These are unpacked under `.lake/packages/` at the revision in
`lake-manifest.json`, so searching them is free, offline and reproducible — and
a search here is the kind a `novelty_checks` record can cite.

**Mathlib is one library among these, not a synonym for "the Lean library".**
More than one result this project needed was absent from Mathlib and present, or
nearly present, next door. A contributor who reads "Mathlib does not have it" as
"Lean does not have it" stops one library too early.

| if your result is about | look in | revision |
|---|---|---|
| analysis, algebra, topology, measure theory, probability, linear algebra, order — the general body | [mathlib](https://github.com/leanprover-community/mathlib4) | `db584cd6d46c` |
| lists, arrays, basic data structures and the lemmas below Mathlib | [batteries](https://github.com/leanprover-community/batteries) | `4488d40d070b` |
| entropy inequalities, sumsets, the polynomial Freiman–Ruzsa development | [PFR](https://github.com/teorth/pfr) | `7d6404b79b11` |
| additive combinatorics | [AddCombi](https://github.com/leanprover-community/add-combi) | `a78c4546df6d` |
| first-order logic, provability, arithmetic, incompleteness | [Foundation](https://github.com/FormalizedFormalLogic/Foundation) | `30a16ffa93d7` |
| doubly-efficient debate, interactive protocols | `vendor/debate` | in-tree, see its `PROVENANCE.md` |
| social choice, Gibbard–Satterthwaite | `vendor/SocialChoiceLean` | in-tree, see its `PROVENANCE.md` |

The two `vendor/` trees are in this repository rather than under `.lake/`, and
are already audited.

## The rest of the manifest

Tooling and tactics. **No mathematics to reuse lives here** — searching them for
a theorem is a waste, and the split is the point of listing them apart. They are
named in full because "is X a dependency?" has one answer and a partial list
invites the wrong one.

[aesop](https://github.com/leanprover-community/aesop) `3448c0bcc5ce`, goal-directed proof search;
[plausible](https://github.com/leanprover-community/plausible) `b7eb3304aeae`, property testing — measured, and **banned from commits**, see `lean-proving.md`;
[Qq](https://github.com/leanprover-community/quote4) `92c15be17b7c`, typed quotations;
[LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) `5f4d51b81cbd`, which issues [leansearch](https://leansearch.net) and [loogle](https://loogle.lean-lang.org) queries from inside Lean — a way to search, not a thing to search;
[axiom-audit](https://github.com/SnO2WMaN/axiom-audit) `827e715d3923`, the axiom check this project did not write;
[checkdecls](https://github.com/PatrickMassot/checkdecls) `3d425859e73f`;
[doc-gen4](https://github.com/leanprover/doc-gen4) `aceca4eeb5a7`;
[import-graph](https://github.com/leanprover-community/import-graph) `16f02aa76428`;
[ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) `4be2e3d5087e`;
[leansqlite](https://github.com/leanprover/leansqlite) `6168b7549738`;
[Cli](https://github.com/leanprover/lean4-cli) `6130a47896ce`;
[UnicodeBasic](https://github.com/fgdorais/lean4-unicode-basic) `37e7d8cb7316`;
[BibtexQuery](https://github.com/dupuisf/BibtexQuery) `852edafa268e`;
[MD4Lean](https://github.com/acmepjz/md4lean) `31907cc18f48`.

**The Mathlib revision that matters is the one above**, from
`lake-manifest.json`. An older snapshot is recorded under `corpora.mathlib` in
`docs/provenance/formalization-search.json`; the two are not the same, and a
search citing the wrong one is not reproducible.

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
