# d-separation: build, depend, or vendor

**Status.** Assessment, 2026-08-21. **Blocker 1 closed 2026-08-31**: this
repository now pins `leanprover/lean4:v4.33.0`, the same Lean release
CausalForge pins, so the toolchain objection below no longer holds and the
"depend" option is live for the first time. The verdict is unchanged — it turned
on criteria 3 and 4, not on the toolchain — but the cost comparison has moved and
should be re-run when a consumer is ready. No code follows from it yet.
Written because the next increment on the causal layer needs d-separation, and
the honest first move is to look for it rather than to write it.

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

Four `No` rows in [section 8 of the coverage audit](source-coverage-audit.md)
are Everitt et al.'s incentive theorems — Theorems 9, 14, 16 and 18. Each is a
*sound and complete* graphical criterion, and each is stated over d-separation
(their Definition 6). None can be *stated* without it, which is criterion 1 of
the foundation test in [methodology](../guide/methodology.md): two blocked rows,
by id. There are four.

A second group is further off: Pearl's do-calculus and the back-door criterion,
recorded as outside §1.3 in the same audit. Those need a `do`-expression
language as well, so they do not make d-separation urgent on their own.

## 2. What exists upstream

`github.com/Jiyuan-Tan/CausalForge`, module namespace `Causalean`, Apache-2.0 —
the same licence this repository carries.

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
