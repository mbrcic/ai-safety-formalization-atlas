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
   reuse candidate, in that order. The candidate table further down is a
   *starting point and not the search* — run the code search in
   "Searching the ecosystem you have not heard of" before concluding anything
   is absent, because the table only lists libraries somebody already knew to
   add.
4. **The non-Lean corpora**, when the claim is that *no* formalization exists
   rather than that Lean lacks one. Recipe in "Finding the paper" below.

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
| [`Jiyuan-Tan/CausalSmith`](https://github.com/Jiyuan-Tan/CausalSmith) | the `Causalean` package: structural causal models, interventions, graph separation, identification, potential outcomes, causal discovery, minimax estimation | **renamed from `CausalForge`.** Directly overlaps the causal substrate. **Corrected 2026-09-10: this row said "no revision is pinned anywhere in this project", which stopped being true when `lakefile.toml` and `lake-manifest.json` began pinning a module-system fork of it.** Upstream is the unconverted source that fork tracks; a `module` file cannot import a non-`module` one, which is why the fork exists. Take a measurement against the pinned revision, not against upstream's moving head |
| [`Lean-MoDS/StatsMLlib`](https://github.com/Lean-MoDS/StatsMLlib) | statistical learning and probability | candidate |
| [`lean-dojo/TorchLean`](https://github.com/lean-dojo/TorchLean) | autograd, code generation, and **an `NN/Spec/RL/` subtree** carrying `MDP`, `ValueFunction` and `bellmanPolicy` over both measurable and finite-stochastic state spaces | candidate; the RL subtree was missed once because this row said only "autograd", **and the same failure then recurred twice in the two rows below** — see the Econlib and EconCSLib corrections of 2026-09-10. A row that describes a tree by its headline topic is how an absence claim gets written about a subtree nobody opened |
| [`danlyng/Econlib`](https://github.com/danlyng/Econlib) | "economic and political theory": `SocialChoice`, `GameTheory`, `MechanismDesign`, `Preferences`, and `Optimization/DynamicProgramming/` — seventeen files, with `Core/MDP.lean`, `Core/Bellman.lean`, `Core/BellmanOperator.lean`, `Core/Optimality.lean`, `Core/Stochastic.lean`, `Core/UnboundedOptimality.lean` and `Core/Weighted.lean`; separately `Math/Analysis/Blackwell.lean`, a **bounded fixed-point core on an arbitrary state type** | candidate, and the closest external tree to this project's sovereignty and power cluster. Apache-2.0. **Corrected 2026-09-10: this row said "not on the module system", and that is false — every file in the `DynamicProgramming` subtree opens with `module`, Blackwell.lean included.** The gap is the toolchain, `v4.29.0` against our `v4.33.0`, and that alone makes it a **port source rather than a dependency**. Its MDP structures carry a reward field and a discount with its bounds, so they are not the rewardless carrier `AISafetyAtlas.Decision.MDP` needs. **Costed 2026-09-11 in the section below, and the verdict splits the tree**: port `Math/Analysis/Blackwell.lean`, which is transition-agnostic and is the bounded-function widening; do not port `Optimization/DynamicProgramming/`, whose three carriers are deterministic-over-an-arbitrary-type, stochastic-over-`Fin n`, and measure-valued-over-`ℝ`, none of them ours |
| [`nikhgarg/EconCSLib`](https://github.com/nikhgarg/EconCSLib) (published as `AppliedModelingLib`) | `Foundations/Probability/MDP.lean` (a `PMF`-valued finite MDP **with a reward field**, randomized Markov policies, a controlled kernel, finite-horizon and Bellman-recursive optimal values, occupancy masses), `Foundations/Probability/StochasticRewardMDP.lean` whose boundedness field is `Set.Icc (0 : ℝ) 1`, and a ten-file `Learning/ReinforcementLearning/Preference/` subtree | candidate. Apache-2.0, toolchain `v4.30.0-rc2`, not on our toolchain, so a port source. **Added 2026-09-10 after `AISafetyAtlas.Decision.DiscountedValue` recorded that this tree had "no MDP, Bellman, value-iteration or discounting content at all" at a revision holding all of the above.** Over twenty files at that revision match `bellman`, `discount` or `ContractingWith` |
| [`audieleon/goodhart`](https://github.com/audieleon/goodhart) | `proofs/GoodhartProofs/MDP/` — `Defs.lean`, `Bellman.lean` (a `ContractingWith` route to `vPi` and `vStar`, sorry-free), `Shaping.lean`, `Undiscounted.lean` — and `proofs/GoodhartProofs/Skalse/` | Apache-2.0 with no upstream `NOTICE`; toolchain `v4.30.0-rc2`. Pinned as `REPRODUCED` in `registry.yaml` and adjudicated in `docs/provenance/by037-by038-goodhart-campbell-plan.md` D4 — **but D4's "do not port" is argued from its Skalse files and says nothing about the MDP subtree**, which is the nearest external match to `AISafetyAtlas.Decision.DiscountedValue` and was left out of that module's reuse survey |
| [Formalpedia](https://prove2.me/formalpedia) | cross-system index of formalized results | an index, not a library — use it to find where a result lives, not as evidence of absence |

## Costed reuse decisions

A row in the table above says a tree is a candidate. This section is where a
candidate becomes a decision, and a decision here must carry numbers: which
declarations, measured against ours from their *statements*, what the toolchain
delta actually is, and a verdict of the form "port these, they widen that" or
"build, because". A survey that stops at names is what produced the three
retractions dated 2026-09-10 in the table above.

### Bueno & Clarkson's Isabelle hyperproperty theories (2026-09-13) — **comparator only, permanently**

`HyperDefs.thy` and `Hyper.thy`, pinned in
the private literature store, are the only
other machine-checked treatment of Clarkson & Schneider's Theorem 2 and
Theorem 3. They were compared against `LAND-HYPER-002` on 2026-09-13; the
comparison is in the private manifest of 2026-09-13 §§4–5.

**The maintainer's decision, taken 2026-09-13, is that this code is a check and
never a component.** It is used *only* to compare the atlas's statements against
someone else's. It is not vendored, is not cited as a `formalizations` entry,
does not appear in `registry.yaml` beyond prose in a `notes` field, and **will
not become part of the atlas at any later date.**

So the licence question does not arise and must not be reopened: Eclipse Public
License v1.0 stays absent from this ledger's `spdx_license` vocabulary, and the
absence is a decision rather than an oversight. An agent that finds these files
and proposes vendoring them, relicensing around them, or adding EPL to the
vocabulary is re-litigating a settled call.

**What comparator-only permits**: reading the statements, reading the proofs,
counting the axioms, and writing what differs into a `notes` field or a
provenance note. **What it forbids**: copying a definition, porting a proof,
citing it as coverage, or listing it as a formalization of anything.

### `danlyng/Econlib` against `AISafetyAtlas.Decision.DiscountedValue` (2026-09-11)

Clone confirmed in-band at `003655ccf010cdf44c4f67d6675167b54ce0e9df`, **the same
revision the survey pins**, `leanprover/lean4:v4.29.0` against Mathlib tag
`v4.29.0`; ours is `v4.33.0` against `db584cd6…`. Apache-2.0, no upstream
`NOTICE`, so a port incurs §4(a)–(c) and not §4(d).

**Verdict: port `Math/Analysis/Blackwell.lean`. Do not port
`Optimization/DynamicProgramming/`.** This splits a claim the integration plan
made as one — that the seventeen-file subtree *"plus"* Blackwell.lean "already
are" the bounded-function widening gap 3 of `DiscountedValue.lean` owes. Only
Blackwell.lean is.

**Why the subtree is not it.** Its carriers were read, not grepped. There are
three, and none is ours:

| Econlib carrier | state type | transition | ours |
|---|---|---|---|
| `DetMDP S A [Nonempty S]` | arbitrary | **deterministic**, `S → A → S` | stochastic |
| `FinMDP n A` | `Fin n`, **finite** | stochastic, `FinDist`-valued | arbitrary type |
| `StochMDP` | **`ℝ`**, and actions `ℝ` too | measure-valued | arbitrary type |

`AISafetyAtlas.Decision.MDP` is `T : State → Action → PMF State` over an
arbitrary state type — stochastic *and* unconstrained. Econlib has stochastic, or
unconstrained, never both. `Core/Bellman.lean` builds its operator on `DetMDP`,
so its contraction and fixed-point theorems are statements about a deterministic
transition and do not transfer; what transfers is the method, and the method is
Blackwell.lean. Two further mismatches the integration plan already noted are
confirmed: the discount is a **structure field** with `β_nonneg` and `β_lt_one`,
so `β = 0` is admissible but the bounds travel with the carrier, and `reward` is
a field rather than a parameter — which is exactly what
`AISafetyAtlas.Wireheading.CRMDP` cannot use, since its reward ranges over a
class of environments.

**Why Blackwell.lean is it.** 301 lines, on the module system, and
**transition-agnostic** — it is about operators, not MDPs:

* `UniformBounded` and `abs_sub_le_of_monotone_discounting` carry **no instance
  on the state type at all**. The latter is Blackwell's sufficient condition —
  monotone plus discounting gives the sup-norm contraction estimate — which is a
  cheaper route than the direct Lipschitz bound `bellmanPolicyOp_contractingWith`
  takes, and a reusable one.
* The fixed-point layer — `liftBddFun`, `contractingWith_liftBddFun`,
  `bddFixedPoint`, `eq_bddFixedPoint`, `existsUnique_bdd_fixedPoint` — asks
  **`[Nonempty S]` and nothing else**. That is the whole distance from our
  `[Fintype State]`.
* **No topology on the state type is required**, which was the live risk. It
  defines `DState : Type u := S` as a `def` rather than an `abbrev` precisely so
  the synonym carries its own discrete topology instance without colliding with
  any topology `S` may have, then embeds bounded functions into
  `BoundedContinuousFunction DState ℝ`, complete under the sup norm. The
  manufactured topology is the trick worth taking.
* `existsUnique_bdd_fixedPoint` is stated for an **arbitrary** `T` with a
  boundedness-preservation hypothesis, not for a Bellman shape, so our stochastic
  operator plugs into it unchanged.

**Toolchain delta, measured rather than asserted.** Every Mathlib name
Blackwell.lean depends on was checked against `.lake/packages/mathlib` at our pin:

| name | at `db584cd6…` |
|---|---|
| `Mathlib.Topology.ContinuousMap.Bounded.Normed` (import) | present |
| `Mathlib.Topology.MetricSpace.Contracting` (import) | present |
| `BoundedContinuousFunction.mkOfDiscrete` | present, `Bounded/Basic.lean` |
| `ContractingWith.fixedPoint`, `fixedPoint_isFixedPt`, `fixedPoint_unique'` | present |
| `abs_sub`, in the form `|a - b| ≤ |a| + |b|` | **absent under that name** |

So the delta looked like **one lemma name, twice used**, each a one-line reproof
from `abs_add` and `abs_neg` — against an integration-plan estimate of three to
five days for "the Econlib port", an estimate that was pricing the seventeen-file
subtree this section declines.

**Ported 2026-09-16, and the measurement above was low by a factor of three.**
The table was built by checking names, and checking names finds the names you
thought to check. Compiling the file found:

| what broke | at `db584cd6…` |
|---|---|
| `abs_sub`, `\|a - b\| ≤ \|a\| + \|b\|` | absent, as the table says — restated once, used twice |
| `abs_add` | is `abs_add_le`; the reproof's *own* ingredient had moved |
| `rw [NNReal.coe_mk]` in `contractingWith_liftBddFun` | finds no pattern: the coercion of `⟨β, hβ₀⟩` is already `β`, so a `show` replaces the rewrite |
| `@[expose]` on an `abbrev` | a hard error, not a warning: "this declaration would be exposed by default" |

None of the four is mathematics and each is one line, so the *verdict* stands and
the port took under an hour. What does not stand is the method: a name-by-name
grep priced three of the four at zero, including one inside the repair the table
itself proposed. Read any future line of this kind as a lower bound.

The result is `AISafetyAtlas.Analysis.Blackwell`, with the consumer in
`AISafetyAtlas.Decision.BoundedValue` and the join `vPiBdd_eq_vPi`; registry row
`LAND-BELLMAN-BDD-001`, notice in `AISafetyAtlas/Upstream/LICENSE-NOTICE`.

**What it buys, and what it does not.** It buys gap 3: dropping `Fintype State`
from the value layer, in exchange for `Nonempty State` and a uniform bound on the
reward. It does **not** buy gaps 1 and 2 — that `vPi` is a stationary
deterministic policy's value where the carrier's `Policy` is history-dependent
and stochastic, and that `vPi` is defined as a fixed point rather than proved
equal to the discounted return along `MDP.run`. Those are unaffected by any
external tree and stay owed.

**Done 2026-09-16.** What the costing predicted about the binders was also not
quite right. It said porting "touches the `Fintype` binders of twelve
declarations in `DiscountedValue.lean`", and the binders cannot simply be
dropped: `ContractingWith γ (bellmanPolicyOp …)` is a statement about
`State → ℝ` as a metric space, which only typechecks when `State` is finite, so
the wider result is a statement about a *different* type and not the same
theorem with a binder removed. What actually happened is that three
**definitions** — `qVal`, `bellmanPolicyOp`, `bellmanOptOp` — lost the binder,
because none of them ever used it, and the wider fixed point is a new module
joined to the old one by `vPiBdd_eq_vPi`.

### `audieleon/goodhart`'s `MDP/` subtree, against the same module (2026-09-11)

Left out of `DiscountedValue.lean`'s reuse survey on the strength of D4 of
`by037-by038-goodhart-campbell-plan.md`, whose "port: no" argues only about that
repository's Skalse files; D4 is now scoped to say so. Clone confirmed in-band at
`29128f3f9bcafb30d019682b63c1b582bcadf7b9` from the repository root, the revision
`registry.yaml` pins as `REPRODUCED`. Apache-2.0, no upstream `NOTICE`,
`v4.30.0-rc2` against our `v4.33.0`.

**Verdict: do not port, and the reason is not quality.** `MDP/Bellman.lean` is
sorry-free and reaches its fixed points exactly as this module does, through
Mathlib's Lipschitz bound, `ContractingWith` and `ContractingWith.fixedPoint`.
It is the nearest external match there is. It is declined because **it is this
module's own scope in a less usable shape**, on four axes that were checked in
the file rather than assumed:

| axis | `audieleon/goodhart` `MDP/Defs.lean` | here |
|---|---|---|
| carrier | `structure FiniteMDP` **bundles** `S`, `A` and their `Fintype`, `DecidableEq`, `Inhabited` instances as fields | `MDP State Action` is parameterised, instances supplied by the consumer |
| reward | `R : S → A → S → ℝ` is a **structure field** | a parameter, which is what lets `Wireheading.CRMDP` range it over a class of environments |
| discount | `γ : ℝ` with `hγ_pos : 0 < γ` — **`γ = 0` is excluded** | `γ : ℝ≥0`, admitting `0` |
| module system | **zero `module` lines across all four files** | on the module system throughout |

Its transition is `PMF`-valued and its state space is finite, so it neither
widens the `Fintype` gap nor narrows anything: it sits at precisely this module's
restrictions. Porting it would mean unbundling the carrier, re-parameterising the
reward, relaxing the discount, and adding module annotations — which is writing
this module again, from a file that would then need its own fidelity audit.

**Cite: yes, and it already is.** Fourteen of this module's twenty-two
declarations correspond to one of its name for name and in the same order, which
is worth recording as independent corroboration of the route rather than as a
source to take code from. That is what the `REPRODUCED` pin in `registry.yaml`
says and it is the right grade.

## Searching the ecosystem you have not heard of

The candidate table above is curated, so it can only return libraries someone
already added to it. Most of the Lean 4 ecosystem is not in it and never will
be. Search the code host directly, and do it **before** writing that something
does not exist in Lean:

```bash
gh search code "structure MDP" --language=lean --limit 20
gh search code "Bellman"       --language=lean --limit 20
gh search repos "lean4 <topic>" --limit 10
```

Search for the **declaration shape**, not the topic name. `structure MDP` finds
libraries; "reinforcement learning" finds nothing, because nobody writes the
phrase in Lean source. Run two or three shapes a real implementation would have
to contain — a structure name, an operator name, a characteristic lemma name.

Two failure modes this catches, both observed:

* `lean-explore`, `leansearch` and `loogle` index Mathlib and a small set of
  packages. A miss there is **not** evidence about the ecosystem, only about the
  index. Read that as "not in Mathlib", never as "not in Lean".
* The candidate table's one-line summaries go stale. A library listed for one
  topic may have grown a subtree covering another, and the row will not say so.

## Finding the paper

For step 4, when the question is whether a result exists at all, or when a
source has to be pinned before anything is built on it. All three are free,
scriptable, and lawful:

| index | endpoint | good for |
|---|---|---|
| arXiv | `http://export.arxiv.org/api/query?search_query=all:"<phrase>"` | exact-phrase title search, version history, the preprint itself |
| OpenAlex | `https://api.openalex.org/works?search=<phrase>` | DOI, publication year, and whether an open copy exists (`open_access.oa_url`) |
| Semantic Scholar | `https://api.semanticscholar.org/graph/v1/paper/search?query=<phrase>&fields=title,year,externalIds,openAccessPdf` | citation counts, external ids, open PDF link. Rate-limits aggressively; expect HTTP 429 and retry |

Send a `User-Agent` with a contact address; OpenAlex and arXiv both ask for it.

**Only lawful routes.** A paper enters the private literature store
from the publisher, the author, a repository, an open-access index, or the user.
Sites that redistribute paywalled papers without a licence are not an option
here, whatever the convenience: the sources manifest is a provenance record and
has to be able to state where a file lawfully came from. When every index
reports the work closed, record that the green-route search was **exhausted**
and ask, rather than routing around it.

Then follow `download-papers-to-literature-dir`: file, sha256, a row in the
`SOURCES-*.md` manifest with metadata taken from the document itself, and only
then read it.

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
