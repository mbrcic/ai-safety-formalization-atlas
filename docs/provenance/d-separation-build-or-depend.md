# d-separation: build, depend, or vendor

**Status.** Assessment, 2026-08-21. **Blocker 1 closed 2026-08-31**: this
repository now pins `leanprover/lean4:v4.33.0`, the same Lean release
CausalForge pins, so the toolchain objection below no longer holds and the
"depend" option is live for the first time. The verdict is unchanged — it turned
on criteria 3 and 4, not on the toolchain — but the cost comparison has moved and
should be re-run when a consumer is ready. No code follows from it yet.
Written because the next increment on the causal layer needs d-separation, and
the honest first move is to look for it rather than to write it.

**Re-cost run 2026-09-09, and §1 below is retracted.** A consumer became ready —
Theorem 18, the instrumental control incentive — and reading print to state it
falsified this note's premise. **Theorem 18 needs no d-separation at all**, and
Theorem 14 needs no graph object of any kind. §1's *"each is stated over
d-separation … none can be **stated** without it"* was written from the
[coverage audit's](source-coverage-audit.md) paraphrases rather than from print,
and it is wrong for two of the four rows it names. §7 carries the corrected
per-theorem table and the re-run cost comparison; §1 is left standing with its
error visible, as this repository's convention requires.

**Read this together with [`causal-scope-open-work.md`](../guide/causal-scope-open-work.md),
and note that the two reach different verdicts for a reason.** That note also
assesses `CausalForge`, and concludes that the atlas's open *domain* and
*expectation-layer* axes should not be closed by hand because `Causalean.SCM`
already carries arbitrary measurable domains and a measure-valued exogenous
distribution. That conclusion is about the **SCM**. This note is about
**d-separation**, which is a predicate on a finite graph and needs none of that
generality — `Causalean.DAG` carries `[Fintype V]` exactly as `CID` does. The two
questions have the same upstream and different answers, and the verdict below is
the one that governs d-separation.

## 1. What needs it, by row

> **Retracted 2026-09-09. The paragraph below is wrong and is kept visible.**
> Its two errors are that Theorem 18's criterion is a plain directed path in `𝒢`
> and mentions no separation, and that Theorem 14 is not a graphical criterion.
> It also names the wrong four: the paper's four *sound and complete graphical*
> criteria are Theorems 9, **12**, 16 and 18, and Theorem 12 has no row in the
> coverage audit at all. See [§7](#7-re-cost-2026-09-09).

~~Four `No` rows in [section 8 of the coverage audit](source-coverage-audit.md)
are Everitt et al.'s incentive theorems — Theorems 9, 14, 16 and 18. Each is a
*sound and complete* graphical criterion, and each is stated over d-separation
(their Definition 6). None can be *stated* without it, which is criterion 1 of
the foundation test in [methodology](../guide/methodology.md): two blocked rows,
by id. There are four.~~

What is true, and what criterion 1 of the foundation test actually reads on, is
in [§7](#7-re-cost-2026-09-09): **two** blocked rows need d-separation to be
stated (Theorems 9 and 16), and a third (Theorem 12) needs it through the
minimal reduction. That still clears the criterion — it asks for two — but it
clears it on different rows than this section claimed.

A second group is further off: Pearl's do-calculus and the back-door criterion,
recorded as outside §1.3 in the same audit. Those need a `do`-expression
language as well, so they do not make d-separation urgent on their own.

## 2. What exists upstream

`github.com/Jiyuan-Tan/CausalSmith`, module namespace `Causalean`, Apache-2.0 —
the same licence this repository carries. The repository was named `CausalForge`
when sections 1 through 7 were written and was renamed between then and section
9; the old name redirects, and every earlier citation of it in this note should
be read as the same project.

Read at commit `0bc3544`, from a local clone. Not a pinned checkout, which is
the first thing any decision here would have to fix.

| what | detail |
|---|---|
| `Causalean.DAG.dSep` | pairwise disjointness plus absence of Bayes-Ball reachability from source to target given the conditioning set |
| decidability | `instance decDSep` — d-separation is *computable* there, by reachability and disjointness |
| size | 5,086 lines under `Graph/DSep/` alone: active paths, ancestral sets, Bayes Ball, ordered local SG, backdoor bridges |
| `sorry` | none in `Graph/` or `SCM/` |
| carrier | `DAG V` with `[DecidableEq V] [Fintype V]` — the same finiteness axis `AISafetyAtlas.Causal.CID` carries |
| beyond d-separation | global Markov for SCMs, identification (`SCM/ID`, `SCM/PartialID`), SWIGs, Markov equivalence |

This is a serious development and it is further along on d-separation than
anything this repository would write in a comparable effort.

## 3. What it does not give

**The incentive half.** Everitt's theorems are about a graph whose vertices are
partitioned into structure, decision and utility nodes. `Causalean` has no such
object: its DAGs are for identification, not for incentives. A dependency
supplies the `d`-separation predicate and none of the value-of-information,
value-of-control, response-incentive or instrumental-control-incentive
machinery.

**The completeness halves.** Each of Theorems 9, 14, 16 and 18 is *complete* as
well as sound, and a completeness proof is a construction of a witnessing SCIM.
Those constructions are this repository's work whatever happens here, because
they are about SCIMs, which is our object.

So the realistic saving is the soundness direction of four theorems, plus the
structural lemmas about paths that both directions read.

## 4. What blocks depending today

1. ~~**Toolchain.** CausalForge is `leanprover/lean4:v4.33.0`. This repository
   pins `v4.31.0` with Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, and
   that pin is load-bearing: `PFR` is pinned by commit to the same Mathlib, and
   [the entropy-compatibility work](../guide/methodology.md) exists to keep those
   two aligned. A `require` is not available without moving the whole stack.~~
   **Closed 2026-08-31.** The whole stack did move, for the reasons in
   [`toolchain-v4330-migration.md`](toolchain-v4330-migration.md): the atlas is
   on `leanprover/lean4:v4.33.0` with Mathlib
   `db584cd6d46c92f209a44c0f1c829460d327499d`, and `PFR` and `Foundation` were
   re-pinned to revisions that resolve against it. Both projects are now on the
   same Lean release. Whether they are on the *same Mathlib commit* is not
   checked here and would have to be before a `require` is attempted.
2. **Carrier mismatch.** `Causalean.DAG` is a structure with its own edge
   representation; `AISafetyAtlas.Causal.CID` carries `parents : V → Set V` and
   a `NodeKind` partition. Using their lemmas means a bridge and a proof
   that it preserves the predicate — real work, and the place a subtle error
   would hide.
3. **It vendors its own dependencies.** `FoML` and `optlib` are required
   alongside Mathlib, with a documented ordering constraint in its lakefile.
   That is three more pins to track for one predicate.

## 5. Verdict against the foundation test

Criterion 1 (two blocked rows, by id) is met — four. Criterion 2 (the gap is
upstream and recorded) is **not** met in the form the test asks for: the gap is
not that nobody has formalized d-separation, it is that the one formalization
found is on an incompatible toolchain. That is a different fact and it should be
recorded as one. Criteria 3 and 4 (theorems need a consumer in the same change
or the next; an expiry) both point the same way: d-separation should not land
here until an incentive theorem lands with it.

**Recommendation: do not depend, and do not build yet.** Neither is right today.

The three options, with what each costs, so the choice is made on numbers when
a consumer is ready:

* **Depend.** No longer blocked on the Lean toolchain: this repository moved to
  `v4.33.0` on 2026-08-31 for other reasons, which is the condition this bullet
  named. On the numbers here it is now the cheapest path by a wide margin, and
  Apache-2.0 permits it with attribution. What is left to check is the Mathlib
  commit and blocker 3, its three vendored pins.
* **Vendor the `DSep` subtree.** Apache-2.0 permits it with attribution and a
  `NOTICE`. 5,086 lines this repository would then own, maintain and re-verify
  against a Mathlib it was not written for. Cheap to copy, expensive to keep.
* **Build the fragment.** Bayes-Ball reachability over `CID.parents` plus the
  handful of lemmas one incentive theorem actually reads. Much smaller than
  5,086 lines because it is not a d-separation library — it is the part
  Theorem 9 needs. Fits the criterion-3 rule that theorem work arrives with its
  consumer.

The third is the one that matches how this repository has built every other
layer, and the assessment above is what makes that a decision rather than a
default. Recorded here so the next pass starts from it.

## 6. What was taken from CausalForge already

Not a theorem, a design. `scripts/generate_declaration_index.py` walks the
elaborated environment for the atlas the way `LibraryIndexCore.buildEntries`
walks it for `Causalean`, and `check_docstring_identifiers.py` now separates a
hard failure from an advisory the way that project's CI separates its
deterministic crosslink check from its warn-only knowledge-base lint. Both are
better than what this repository had, which is the only test that matters.

## 7. Re-cost 2026-09-09

Run because a consumer became ready. Two things moved: what the theorems
actually need, and what depending would actually cost. Both moved in the same
direction — **less**.

### 7.1 What each theorem needs, from print

Read from **arXiv:2102.01685v2** (15 Mar 2021), sha256
`e1d9324532870d4a2604a82a9e4865207b8e21cec94524bb662f3a0470b4ee45`, checked
against the AAAI-21 proceedings file at pp. 11487–11495. The two agree on every
definition and theorem number quoted below; v2 additionally carries the
appendices, which the proceedings version refers to and does not contain.

**Every statement here was read from 400 dpi page renders, not from the text
layer.** That is not caution for its own sake: this paper's AMS symbol fonts are
subset-embedded with no `ToUnicode` map, so `pdftotext` silently drops or
substitutes relational glyphs — and a criterion whose `≠` extracts as `=`, or
whose `⊥̸` extracts as `⊥`, transcribes into a statement that compiles and is the
negation of what was published. Five glyph-critical spots were re-rendered and
confirmed individually: the `⊥` of Definition 7's eq. (1), the `≠` of
Definition 17's eq. (2), the `⊥̸` of Lemma 27's eq. (4), the strict `<` of
Definition 15, and the `≮` closing Lemma 26.

| Thm | criterion, from print | graph object | d-separation? |
|---|---|---|---|
| 9, VoI | *"admits VoI for `X ∈ 𝐕 \ Desc^D` iff `X` is a requisite observation in `𝒢_{X→D}`"* | requisiteness + edge addition + `Desc` | **yes** — requisiteness *is* Definition 7's `X ⊥ 𝐔^D \| (Pa^D ∪ {D} \ {X})` |
| 12, RI | *"admits a response incentive on `X` iff the minimal reduction `𝒢^min` has a directed path `X ⇢ D`"* | directed path, **in `𝒢^min`** | **yes**, indirectly — `𝒢^min` (Def. 11) is built by a d-separation test per information link |
| 14 | *"all optimal policies `π*` are counterfactually unfair w.r.t. `A` iff `A` has a response incentive"* | **none** | **no** — a SCIM-level equivalence, stated at a fixed model, proved by support-set manipulation |
| 16, VoC | *"admits positive value of control for `X ∈ 𝐕 \ {D}` iff there is a directed path `X ⇢ 𝐔` in `𝒢^min`"* | directed path, **in `𝒢^min`** | **yes**, same route as 12 |
| 18, ICI | *"admits an instrumental control incentive on `X ∈ 𝐕` iff `𝒢` has a directed path from the decision `D` to a utility node `U ∈ 𝐔` that passes through `X`"* | directed path, in `𝒢`, **reflexive** | **no** |

Three details that only print settles, and that the audit's paraphrases lost:

* **Theorem 18 quantifies `X ∈ 𝐕`**, not `𝐕 \ {D}` — a deliberate contrast with
  Theorem 16 one page earlier — and Definition 3 defines a directed path as
  having *"length at least zero"*. So `X = D` and `X ∈ 𝐔` are in scope, and the
  criterion is over the **reflexive** transitive closure. `CID.IsDescendant` is
  already that relation, and already reflexive on purpose;
  `Model.properDescendants` would state a different and false theorem.
* **Theorem 18's soundness consumes one lemma**, their Lemma 20 (Galles & Pearl
  1997, Lemma 12: no directed path implies causal irrelevance) at an empty
  conditioning set. No collider reasoning, no do-calculus rule — despite the
  appendix's own summary table saying *"proved using do-calculus"*.
* **Theorems 12 and 16 consume Lemma 23** (Correa & Bareinboim 2020, sigma
  calculus Rule 3) and **Lemma 25**, both genuine d-separation arguments. That
  is what separates them from 18.

**Consequence for this note's question.** ICI can be stated and proved with the
reachability the atlas already has — and on 2026-09-09 it was, in
`AISafetyAtlas.Causal.Incentive`, both directions, with no d-separation anywhere
in it. VoI, RI and VoC cannot. The blocked-row
count that makes d-separation a foundation is 9, 12 and 16 — and 12 is a row the
coverage audit does not carry.

### 7.2 What depending would cost, re-measured

Re-read at commit `d070da2` (2026-09-01), from a fresh clone; the earlier read
was at `0bc3544` and that clone was not retained.

| | 2026-08-21 | 2026-09-09 |
|---|---|---|
| Mathlib commit | *"not checked here, and would have to be"* | **`db584cd6d46c92f209a44c0f1c829460d327499d` on both sides.** Identical. This repository resolves `v4.33.0` to it; CausalForge pins it by hash |
| blocker 3, vendored pins | *"`FoML` and `optlib` … three more pins to track for one predicate"* | **dissolved twice.** Both are now `path =` requires inside CausalForge's own tree, so a `require` adds no git pin beyond Mathlib; and the d-separation import closure reads **neither** |
| vendor size | *"5,086 lines under `Graph/DSep/`"* | **2,479 lines in 4 files** — `Graph/DAG` (488), `Graph/DSep/BayesBall` (418), `Graph/DSep/ActivePath` (743), `Graph/DSep/Separation` (830). Transitive closure of `Separation` + `BayesBall`, non-Mathlib external imports: **none** |
| vendor objection | *"re-verify against a Mathlib it was not written for"* | dead — same commit |
| `sorry` | *"none in `Graph/` or `SCM/`"* | none in the package; the single grep hit is a docstring naming an upstream one |
| package size, for scale | — | 1,095 files, ~309k lines. A `require` builds only the imported modules, so this is not the build cost; it is the maintenance surface a `require` points at |

§3 stands unchanged and was re-checked: there is still no CID, decision-node or
incentive object anywhere in `Causalean`. A dependency supplies the predicate
and none of the four incentive concepts.

§4.2, the carrier mismatch, is now the **only** real cost. `Causalean.DAG` is
`edge : V → V → Prop` with `decEdge` and `[DecidableEq V] [Fintype V]`;
`AISafetyAtlas.Causal.CID` is `parents : V → Set V` with the same acyclicity
phrasing (`¬ Relation.TransGen · v v`), so the bridge is `edge u v := u ∈
parents v` plus a decidability instance, and `dSep` takes `Finset V` where `CID`
takes `Set V`. Small, and the place a quiet error would sit.

### 7.3 Verdict, unchanged in form and different in content

**Still: do not depend and do not build yet — but for one reason instead of
four, and not for the row that prompted this run.**

* ~~*Build the fragment* is **struck as an option.** It was the recommendation
  because the other two were blocked; both objections that blocked them are
  gone, and writing Bayes-Ball reachability here when 2,479 verified
  Mathlib-only lines exist at the identical Mathlib commit is not defensible on
  the numbers.~~ **Un-struck the same day by [§8](#8-the-lake-spike-2026-09-09).**
  The numbers in that sentence are right and it drew the wrong conclusion from
  them, because it priced the options without checking that the cheapest one can
  be *built*. It cannot.
* *Depend* and *vendor* are now genuinely comparable, and the choice should be
  made when Theorem 9, 12 or 16 is the consumer — not before, by criterion 3.
  Depend costs a `require` on a 309k-line research package for one predicate;
  vendor costs 2,479 lines this repository owns, with `vendor/TauCeti` and
  [`external-formalizations.md`](external-formalizations.md) as the established
  template and `warningAsError = true` as the thing to check first.
* Theorem 18 is **not** that consumer and does not decide it. It is now proved
  without any of this, which is the concrete form of the correction: the option
  this note recommended — build the fragment by hand — would have been effort
  spent for a row that never needed it.

**This subsection was written before the spike in [§8](#8-the-lake-spike-2026-09-09)
and its cost comparison is superseded by it.** Everything it says about pins,
sizes and licences holds. What it missed is that *depend* is not available at
all, for a reason no cost comparison would surface.

## 8. The Lake spike, 2026-09-09

§7 re-costed the three options and made *depend* look cheapest by a wide margin.
It priced them without checking that the cheapest one can be built. This section
is the experiment, on a throwaway branch that was discarded; the atlas tree was
restored and rebuilt afterwards.

### 8.1 Everything the cost comparison predicted, confirmed

`lake update Causalean` at `d070da2137e054ed3b53c18e5e7653ce6b19cff3`:

| | result |
|---|---|
| existing pins | **none moved.** `mathlib` stayed at `db584cd6d46c92f209a44c0f1c829460d327499d` — this repository's `rev = "v4.33.0"` tag resolves to the very commit CausalForge pins by hash, so the two never competed. PFR, Foundation, AddCombi, aesop, batteries, Qq unchanged |
| Mathlib cache | not invalidated — *"No files to download / Already decompressed 8690 file(s)"* |
| `FoML`, `optlib` | enter the manifest with **no rev and no inputRev**: path dependencies inside the CausalForge checkout. Blocker 3 is empirically dead, not merely argued dead |
| require-order fragility their lakefile warns about | did not bite |
| build of `Causalean.Graph.DSep.Separation` | **18.6 s**, 734 jobs, warnings only |
| the carrier bridge (blocker 2) | **five lines, and it compiles.** `edge := fun u v ↦ u ∈ G.parents v`, `decEdge := Classical.propDecidable`, and `acyclic := G.acyclic` transfers *verbatim* — both sides are `¬ Relation.TransGen · v v`. `dSep` then inherits upstream's `Decidable` instance |

So every objection this note has ever raised against depending is gone, and the
bridge that §4.2 called *"real work, and the place a subtle error would hide"* is
a five-line structure literal.

### 8.2 And it cannot be done

**The atlas is on Lean's module system. CausalForge is not.**

```
error: cannot import non-`module` Causalean.Graph.DSep.Separation from `module`
error: cannot import non-`module` Spike from `module`
```

The restriction is one-directional, and therefore transitive:

| importer | imports | verdict |
|---|---|---|
| plain `.lean` file | `Causalean.*` **and** `AISafetyAtlas.*` | **works** — this is how the bridge above was compiled |
| `module` file | `Causalean.*` | refused |
| `module` file | a plain bridge file that imports `Causalean.*` | refused |

A bridge is therefore constructible and **unreachable**. Every consumer the
bridge exists for — `Causal.StructuralModel`, `Causal.Incentive`, and everything
that would state Theorems 9, 12 or 16 — is a `module`, and no arrangement of
intermediate files helps, because the barrier is on the *importing* side.

**Neither of this note's earlier checks would have found it.** The toolchain
matched, the Mathlib commit matched, and the package resolved and built. This is
a fourth blocker and it is the binding one.

### 8.3 A second finding, independent of the module system

CausalForge **does** carry do-calculus: `SCM/Do/Rule2.lean`, `Rule3.lean`,
`Rule3Conditional.lean`, `GlobalMarkov.lean`, `LocalMarkov.lean`,
`SemiGraphoid.lean`. That is the shape of Everitt's Lemmas 21–25, which
Theorems 12 and 16 consume and Theorem 18 does not.

**It is unusable at this repository's SCIM even if the module barrier vanished.**
Those results are stated over `Causalean.SCM N Ω` with `SWIGNode`,
`StandardBorelSpace`, `MeasureTheory.Measure` and
`ProbabilityTheory.CondIndepFun`. `AISafetyAtlas.Causal.SCM` is finite-domain and
deterministic-with-exogenous, and its `P(ε)` is a product of real-valued
marginals. Transferring them is a model bridge across exactly the
domain-and-expectation axis section 8 of the coverage audit records as open —
a research-scale change, not a `require`.

So §3 was right that a dependency supplies the predicate and none of the
incentive machinery. It should also have said: **and none of the probabilistic
machinery either, at our SCM.** The realistic saving from depending was always
the graph layer alone.

### 8.4 Verdict, revised

**Depend is unavailable** — on mechanism, not on cost. It becomes available if
and only if upstream adopts the module system, which is upstream's call and not
something to plan around. Section 9 asks the question rather than guessing at
the answer. Recorded here so the next pass does not re-derive the cost
comparison and reach §7's conclusion again.

**Vendor is possible and now costs a port.** The 2,479 lines would have to be
converted to `module` / `public import` / `public`, and `warningAsError = true`
turns their deprecated `push_neg` calls into hard errors. Mechanical, and it is
still a fork of a live upstream, which is the thing to weigh if that upstream
grows.

**Build the fragment is back**, and §7.3's striking of it is retracted above. Not
because the numbers moved — they did not — but because the two options that beat
it on numbers are blocked and expensive respectively, and because the part a
consumer needs is far smaller than 2,479 lines: most of `Graph/DSep/` is backdoor
bridges, ordered local SG and Markov equivalence, none of which Theorem 9 reads.

**The next measurement**, when Theorem 9 is the consumer, is which of
`Separation.lean`'s lemmas its soundness half actually reads — not the size of
that file.

## 9. What was asked upstream, and what upstream is, 2026-09-09

Section 8.4 left *depend* turning on a decision this repository does not get to
make. Rather than plan around a guess, the question was put to the maintainer:
[Jiyuan-Tan/CausalSmith#14](https://github.com/Jiyuan-Tan/CausalSmith/issues/14),
reporting the exact error, the transitive rule in the table above, and the
four-line `cidToDAG` bridge that shows the mathematical side is trivial. It also
notes that identical toolchains and identical Mathlib commits both pass and the
import still fails, so neither check a downstream normally runs would catch it.

Reading the answer, whenever it comes, is the only thing that moves *depend*.

**The answer, read 2026-10-05.** Upstream replied on 2026-09-13: commit
[`b60f54a6`](https://github.com/Jiyuan-Tan/CausalSmith/commit/b60f54a69a)
(2026-09-10) puts exactly the four files of the d-separation closure on the module
system, with the same mechanics and the same one forced visibility change
(`bbReachAux` made public); the differences from the fork are docstrings only.
Issue #14 was closed on 2026-10-02. **Only part of the library is converted:** the
rest of `Causalean` is still non-`module`, and upstream has said it plans to
convert it. For this repository the part that matters is done, and the `require` was
re-pointed from the fork to upstream commit `b60f54a6` on 2026-10-05. The two
pins share toolchain (v4.33.0), `lakefile.toml` and manifest (Mathlib `db584cd6`
and every transitive pin); `AISafetyAtlas.Causal.DSep`, its examples and the root
build against upstream, and the bridge theorems depend only on the standard
axioms.

### 9.1 What the upstream project is

Measured the same day, from the GitHub API rather than from the clone:

| | |
|---|---|
| name | `Jiyuan-Tan/CausalSmith`, renamed from `CausalForge` |
| created | 2026-07-20 |
| head of `main` | `d070da2137e054ed3b53c18e5e7653ce6b19cff3`, 2026-09-02 — the commit the spike pinned is still current |
| branches | one |
| contributors | one, 58 commits |
| stars / forks | 10 / 0 |
| open issues before #14 | none; the one issue ever filed was a stale-link report, closed |
| `.lean` files | 2,075 — 1,095 under `Causalean/`, the rest under `CausalSmith/` |
| toolchain | `leanprover/lean4:v4.33.0`, identical to this repository |
| module system | not adopted; the root `Causalean.lean` uses plain `import` |

The stated scope also widened: the description now reads *"A Formally Grounded,
Self-Improving Agentic Framework for Automated Research in Causal Inference"*,
and the recent commit stream is largely the papers site rather than the Lean
library, though the newest commit does carry a proof-automation layer.

This does not say the project will not grow — it is seven weeks old and active.
It says something narrower and more useful here: *large* and *pinnable* are
different axes. A single-author repository that renamed itself inside the window
this note was being written is not one to hard-pin, and that is an argument
against **vendor** specifically, which would fork it. It is not an argument
against depending later, if #14 is answered yes.

### 9.2 What this does not change

The build-the-fragment verdict of §8.4 stands, and §7.3's striking of it stays
retracted. Nothing measured here touched the numbers; it constrains *vendor*,
which was already the option nothing recommended.

## 10. The port, built and measured, 2026-09-09

Section 8.4 called *depend* unavailable on mechanism, and §9 put the question to
upstream rather than guess. Neither had to be the end of it: the barrier is a
property of upstream's source, and the source is Apache-2.0. So the port was
done, on a fork, and built.

**It works.** `AISafetyAtlas.Causal.DSepBridge`, a `module` file, imports
`Causalean.Graph.DSep.Separation` and compiles with no errors. The bridge is
what §8 predicted:

```lean
noncomputable def cidToDAG (G : CID V) : Causalean.DAG V where
  edge := fun u v ↦ u ∈ G.parents v
  decEdge := fun _ _ ↦ Classical.propDecidable _
  acyclic := G.acyclic
```

and `cidToDAG_edge` holds by `Iff.rfl`. The evidence branch is
`spike/causalean-module-fork`; the port is `mbrcic/CausalSmith@3b83b4f`, branch
`module-system-dsep`, from upstream `d070da21`.

### 10.1 How large the port is, which §8 got wrong

§8.4 costed vendoring at 2,479 lines and left the impression that the module
conversion would be repository-scale. It is neither. The Causalean-side import
closure of `Graph/DSep/Separation.lean` is **four files** — `Graph/DAG`,
`DSep/BayesBall`, `DSep/ActivePath`, `DSep/Separation` — 2,483 lines and 116
declarations, and it imports **nothing but Mathlib**: no `FoML`, no `optlib`,
no other part of `Causalean`. All seven Mathlib files it reads are themselves
already `module`, so nothing below needs converting either.

A partial port is sound because the restriction is one-directional, which the
spike had already established in the other direction: a non-`module` file may
import a `module` file. The remaining 1,091 files under `Causalean/` therefore
go on importing these four unchanged. That is a claim about their proofs, not
only their imports, so it was checked rather than asserted — see §10.3.

### 10.2 What the conversion is, and the one thing it costs

Per file: a `module` header, `public import` on the ten imports, and one
`@[expose] public section` after the module docstring. That is the pattern
Mathlib uses in 4,952 of its own files. No proof is touched and no declaration
is annotated individually.

Beyond that, exactly one change: `private def bbReachAux` becomes public. It is
forced, and the reason is the useful part of this section, because two rules
bite from opposite sides.

* An **exposed** public definition may not reference a private one — a consumer
  would have to elaborate a body naming something invisible to it. `bbReachable`
  is exposed and calls `bbReachAux`, so the first attempt failed with
  `BayesBall.lean:255:2: Unknown identifier bbReachAux`, plus ten cascading
  dot-notation errors downstream of it.
* A public but **unexposed** definition does not reduce **even inside its own
  file**. Sealing the file instead therefore broke upstream's own regression
  check, `example : y ∉ chainDAG.bbReachableVertices {w} {x} := by decide`, with
  `Tactic decide failed for proposition`; and in `ActivePath` it stopped
  `decUAdj` and `decIsCollider` from synthesizing.

So the closure must be exposed, and exposure requires that one helper to be
public. `bbReachAux` is the only private *definition* among the four files.
Every other private declaration there is a theorem, and proofs are not exposed,
so none of them moved.

The second rule is the one worth carrying forward past this note: **exposure is
not only about downstream visibility.** An unexposed definition is opaque to the
kernel in its own file, so `decide`, and any instance synthesis that must
reduce, will fail where it previously succeeded. That is invisible to a reader
of the diff and is what makes a mechanical-looking conversion require a build.

### 10.3 What was verified

| check | result |
|---|---|
| `module` consumer importing `Causalean.Graph.DSep.Separation` | builds, no errors |
| existing pins moved by `lake update` | none; the manifest diff is a pure addition |
| Mathlib cache | not invalidated |
| `FoML`, `optlib` | enter with no rev, as path dependencies inside the fork |
| the four ported files | build, warnings only, all the pre-existing deprecated `push_neg` |
| files directly importing the four | **13 of 13 build clean**, including `SCM/Examples` back-door, front-door and IV |

The last row is the one that had to be measured rather than argued: the import
being *accepted* says nothing about whether dependent proofs still elaborate
once four files stop exposing their bodies by default. They do.

### 10.4 What this does to the verdict

**Depend, on a fork, is what this repository did until 2026-10-05; since then it
depends on upstream** (see the note at the end of §9). That was a change of kind
from §8.4, which had *depend* blocked outright. The `require` in `lakefile.toml`
is pinned to upstream commit `b60f54a6` rather than to a branch, and
`AISafetyAtlas.Causal.DSep` carries the bridge; the spike branch that first
demonstrated it has been folded in and deleted. Earlier commits of this
repository pin the fork commit, so the fork branch stays reachable and is not
deleted.

**Depend, on upstream, turned on upstream, and upstream took the port** (see the
note at the end of §9). The port was not offered as a pull request unasked: [issue #14](https://github.com/Jiyuan-Tan/CausalSmith/issues/14)
asks the question, upstream has no Lean CI — the two workflows are `kb-lint` and
`site` — so a maintainer would have to build any PR by hand, and a four-file
diff arriving unrequested on a single-author repository inverts who carries that
cost. The port is offered in the issue instead.

**The first consumers landed the same day.** Definition 6 is
`AISafetyAtlas.Causal.DSep` and Definition 7 is `AISafetyAtlas.Causal.Requisite`,
both graded in §8 of the coverage audit, which moved from `9 Yes, 11 No` to
`11 Yes, 9 No`. Two findings came out of stating Definition 6 rather than
importing it, and neither would have appeared in a cost comparison:

* Upstream's `DAG.dSep` requires `X`, `Y` and `Z` pairwise disjoint **inside the
  definition**, where print's clause 3 answers on overlapping sets instead —
  a case the paper's footnote 5 flags as deliberate. Grading the import as
  Definition 6 would have been *Narrower* on an axis the source explicitly
  claims.
* Print does not fix the length convention for the undirected paths of
  Definition 6, and the reading is forced by that same footnote: the trivial
  path is what gives clause 3 content at `X ∩ Y`. Upstream reads it the same
  way, which is why the equivalence needs two disjointness hypotheses and not
  three.

So the dependency supplied the Bayes-Ball machinery and none of the fidelity,
which is the sharper version of what §3 and §8.3 each said once.

### 10.5 What the dependency did not supply, measured 2026-09-20

The split this section predicted — machinery imported, fidelity built — turned
out sharper than §10.4 states, and in a direction that matters for the next
decision. Everitt's Definition 6 bounds no vertex set and quantifies over *a set
of nodes*; upstream's `Causalean.DAG.IsActivePath` and `bbZAncestors` are
`Finset`-valued under `[Fintype V]` throughout. So the imported predicate could
not carry print's statement at all, and the coverage audit recorded the import
as a *reopening* of a vertex-set axis section 8 had closed a month earlier.

`AISafetyAtlas.Causal.CID.DSepSet` and `CID.DSepPath` are Definition 6 written
out on `Set V` — undirected edge, collider, chain-or-fork, path, three clauses —
with `CID.dSepSet_iff_dSep` and `CID.dSepPath_iff_dSep` proving the upstream
computation is what they come to on a `Fintype`. That is 718 added lines across
`Causal/DSep.lean` and `Causal/Requisite.lean`, and none of it is Bayes Ball:
the dependency still does every graph computation.

**Two things upstream turned out not to have.** `Nodup` occurs nowhere under
`Causalean/Graph/`, so the active-walk-to-active-path fact that Bayes-Ball
correctness rests on was not importable and is proved here as
`CID.dSepSet_iff_dSepPath`. And nothing upstream separates clause 3 from clauses
1 and 2, which the splice argument needs in order to preserve them
independently; `CID.not_blocked_iff_isActive` is that separation.

**This does not reverse §10.4.** Depend on the fork remains the decision, and
2,483 lines of Bayes Ball were not rewritten. What it revises is the estimate of
what depending buys: the fragment that would have had to be built is the
computation, and the computation is exactly the part that transferred. The
fidelity layer was written either way.

**Vendor stays the worst option** and §9.1's reasoning is unchanged.

**Build the fragment is no longer the default**, which is the real revision
here. §8.4 preferred it because the alternatives were blocked or expensive; one
of them is now neither. The remaining argument for building is independence from
a fork, and it should be weighed against 2,483 lines that already exist, carry
no `sorry`, and are Apache-2.0. The decision does not have to be made until
Theorem 9 is actually the consumer, and §8.4's next measurement — which of
`Separation.lean`'s lemmas its soundness half reads — is now answerable against
a working import rather than a hypothetical one.
