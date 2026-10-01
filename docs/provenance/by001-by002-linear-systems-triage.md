# BY-001 / BY-002 — a Lean candidate the corpus sweep could not see

**Date.** 2026-09-11. Triage of a formalization candidate for the two
control-theory rows, and a correction to what the earlier searches are evidence
for.

## The two rows

| Row | Informal claim | Cited source |
|---|---|---|
| BY-001 Unobservability | A system's internal state cannot in general be reconstructed from its observable outputs. | J. Klamka, "Uncontrollability and unobservability of multivariable systems," *IEEE Trans. Autom. Control* 17(5):725–726, 1972 (`survey-ref-021`) |
| BY-002 Uncontrollability of dynamical systems | (as titled) | same author, same year, same note |

Before today BY-001 read `TRIAGED_DISTINCT` with the note *"Nothing existing
covers it, so a fresh formalization is what this row is owed"*, and BY-002 read
`UNTRIAGED` with *"nobody has read the source against the tree"*.

## The candidate

[`AnandGokhale/LeanForControl`](https://github.com/AnandGokhale/LeanForControl),
Apache-2.0, Lean `v4.30.0-rc2`, commit `c5cedca` (2026-09-01). Its
`LinearSystems/` track formalizes, over a field and — for the eigenvalue tests
— over `ℂ`:

* the observability and controllability matrices and the **Kalman rank
  criteria**;
* the **Hautus** eigenvalue tests for both;
* the duality carrying each observability statement to its controllability
  counterpart;
* the unobservable subspace, and its triviality as a restatement of
  observability.

The rest of that development (Lyapunov stability, LaSalle, class-K comparison
functions, Gronwall) rests on seven custom `axiom`s — including an assumed
Picard–Lindelöf existence-uniqueness — and is out of scope here for that reason.

The `LinearSystems` track is in the atlas as of this commit, as
`AISafetyAtlas.LinearSystems`, hosted by `LAND-LINSYS-001`. That port is not
offered as coverage of either row; see the verdict below.

## Why the 2026-07-28 sweep did not find it

`docs/provenance/formalization-search.json` records six corpora: `mathlib`,
`isabelle-afp`, `rocq-undecidability`, `hol4`, `hol-light`, `agda-stdlib`.
**None of them is the wider Lean ecosystem.** A Lean development outside
Mathlib is invisible to that sweep by construction, so its `hit_count: 0` for
BY-002 and its ten Isabelle hits for BY-001 are evidence about those six
corpora and nothing else. The sweep's own `searched_on` date is kept as it
stands: this note does not amend a dated snapshot, it records what the snapshot
does not reach.

`docs/agent/policy/lean-reuse-sources.md` already names the wider Lean ecosystem
as search step 3. The gap is that the *recorded* sweep has no corpus for it.

The earlier A3 triage (`a3-by001-unobservability-triage.md`) remains correct on
its own terms — every AFP hit it inspected is a keyword false friend — and its
verdict was about those hits. The sentence "nothing existing covers it" reached
further than the search behind it did.

## Statement comparison

**Amended the same day: the source is now pinned and read.** The paragraph
below was written while IEEE Xplore would not serve the note — the DOI and the
Xplore record both returned empty content on 2026-09-11. **The user then
supplied the paper**, `klamka1972.pdf`, sha256
`fdaa652dc63e69a5bcae88cd679d2b7832d7e07fea0bf2c1a7acb18f6f0a2751`, and both
pages were read as rendered images. The comparison below was made against the
row's informal claim and a catalogue description; it is kept as written so the
inference is visible, and **the pages confirmed it**. The statement-by-statement
grading is now section 25 of `source-coverage-audit.md` — **10 Yes, 1 Partial,
6 No, 7 Beyond** as of 2026-09-20, from 0/1/16/4 when this line was first
written — and what print actually proves is recorded after the table.

| | BY-001 / BY-002 as the atlas states them | `LinearSystems` as ported |
|---|---|---|
| Object | a dynamical system, its outputs over time | a pair of matrices `(A, C)` or `(A, B)` |
| Claim | the state cannot in general be reconstructed from the outputs | observability is equivalent to a rank condition, and to a pencil condition at every `μ : ℂ` |
| Direction | an impossibility | a characterization |
| Trajectories | required to state it | absent from the port — and supplied since 2026-09-20 by `Dynamics` and `Flow`, which are not ported |

Two gaps follow, and they are independent.

1. **No dynamics — closed 2026-09-20, and the port is still not where it was
   closed.** `IsObservable A C` says no nonzero state is annihilated by every
   `C · Aᵏ`. The reading "the state cannot be reconstructed from the outputs"
   needs the bridge from output trajectories to that condition. That bridge was
   absent when this was written and is now `determinesStateOn_iff_isObservable`
   in `AISafetyAtlas.LinearSystems.Dynamics`, with
   `isCompletelyReachable_iff_isControllable` in `…Flow` on the controllability
   side. Both modules are atlas-original: the gap was closed by building, not by
   porting more. The port remains the algebra of the criterion.
2. **Not Klamka's theorems.** A catalogue description of the 1972 note said it
   gives a test built on the **minimal polynomial**, yielding **sufficient**
   conditions for uncontrollability and unobservability of linear time-invariant
   multivariable systems — so the note would state neither Kalman's rank
   characterization nor Hautus's, and the port would be adjacent to it rather
   than a rendering of it. **The pages confirm this**; see the section below.

## What print actually proves (added after reading, 2026-09-11)

Print's abstract: *"A simple test based on the properties of the minimal
polynomial yields the sufficient conditions for uncontrollability and
unobservability."* Its system is `ẋ = Ax + Bu`, `y = Cx` at the atlas's own
matrix shapes. Writing `nᵢ` for the multiplicity of the eigenvalue `λᵢ` in the
characteristic polynomial, `νᵢ` for its index — its multiplicity in the minimal
polynomial — `r` for the rank of `B` and `m` for the rank of `C`:

* **Theorem 1.** If `int[(nᵢ + νᵢ - 1)/νᵢ] > r` for some `i`, the system is
  uncontrollable.
* **Theorem 2.** The same with `m`, for unobservability. Print's proof is one
  sentence: *"It follows by duality."*
* **Corollaries 1–4.** The same bounds against the input dimension `p`, the
  output dimension `q`, `max (r, m)` and `max (p, q)`.

All six are **one-directional**. Print's engine is a Jordan-block count — the
number of blocks at `λᵢ` is at least `⌈nᵢ/νᵢ⌉` — fed into a criterion it quotes
from Chen and Desoer. The Kalman rank criterion and the Hautus test appear
nowhere in the two pages.

So both readings in the table above hold, and the second is now checked rather
than inferred: **the object is shared, the theorems are not.** Print reasons
about complete state controllability and observability, which is exactly the
property the ported criteria characterize; it proves six statements about that
property, and the atlas holds none of them.

## Verdict

**`CANDIDATE_LEAD` for both rows, and not coverage.** Unchanged by the reading,
and now resting on it.

* Not `TRIAGED_DISTINCT`: the candidate is in the same system class (linear
  time-invariant, multivariable) and about the same two properties, so the
  earlier "nothing existing covers it" no longer states the position.
* Not coverage, and not `EXTERNAL_ONLY`: neither the upstream development nor
  the atlas port proves reconstruction from outputs, and — now that the printed
  statements have been read — neither proves any of the six either.

**What the rows were owed, at the time this was written.** Both were owed
Theorem 1, Theorem 2 and the four corollaries — none of which the atlas then
stated; four of the six landed on 2026-09-13, see below — and the
ported criteria are the neighbouring development the rows may cite and must not
claim. The trajectory bridge is owed on top of that, and independently.

**A route, unpriced.** Theorem 1 looks close to what is now in the tree: the
number of Jordan blocks at `λᵢ` is the geometric multiplicity
`dim ker (A - λᵢ I)`, so a block count exceeding `rank B` drops the rank of the
Hautus pencil, and `isControllable_iff_hautus` converts that into
uncontrollability. Only the counting half — eq (5), that the block count is at
least `⌈nᵢ/νᵢ⌉` — needs machinery the atlas lacks, and Mathlib's generalized
eigenspaces are where to look for it. Nobody has tried this; the estimate is not
a price.

## The route was taken — 2026-09-13

`AISafetyAtlas.LinearSystems.BlockBound`. The estimate above was right about
where to look and wrong about what was needed: **no Jordan form, and no block
count.**

The counting half is two lemmas neither of which mentions an eigenvalue:

* `finrank_ker_comp_le` — the kernel of a composite is no larger than the two
  kernels together. Everything in `ker (f ∘ₗ g)` is carried by `g` into `ker f`,
  and what the carrying loses is `ker g`.
* `finrank_ker_pow_le` — its induction: `finrank (ker (g ^ k)) ≤ k * finrank (ker g)`.

**Neither is in Mathlib at the pinned revision.** Searched 2026-09-13, before
writing them: `loogle` for `Module.finrank _ (LinearMap.ker (_ ^ _))` and for
`Module.finrank _ (LinearMap.ker (LinearMap.comp _ _))` returned nothing, and a
natural-language search returned only `ker_pow_le_ker_pow_finrank`,
`exists_ker_pow_eq_ker_pow_succ` and `ker_pow_eq_ker_pow_finrank_of_le`, which
are about where the chain stops and not about how fast it grows.

What Mathlib *does* supply, and what made the rest short:
`LinearMap.finrank_maxGenEigenspace_eq` identifies `finrank` of the maximal
generalized eigenspace with `rootMultiplicity μ (charpoly f)` — print's `nᵢ` —
and `Module.End.maxGenEigenspace_eq` says the chain has stopped at
`maxGenEigenspaceIndex`. Applying `finrank_ker_pow_le` at `f - μ` between those
two is print's equation (2).

**One axis is wider than print and one was narrower**, and both are in the row's
`scope_delta`. Wider: the statements hold at *any* stabilizing exponent, print's
index being the least. The narrower axis was print's `νᵢ` being the multiplicity
in the **minimal** polynomial while the exponent here is the stabilization stage
of the generalized eigenspace chain — an identification print cites Zadeh and
Desoer for and does not prove.

**That axis closed on 2026-09-20.** `maxGenEigenspaceIndex_eq_rootMultiplicity_minpoly`
proves the identification, over an arbitrary field, with no Jordan form: the
chain has stopped at the multiplicity, and no smaller exponent stops it.
Mathlib was measured first and carries nothing of the kind — it relates a
*root* of the minimal polynomial to an eigenvalue and never the multiplicity to
the index. The four numbered results now also exist with print's own `νᵢ`
substituted, computed from `A` rather than supplied by the caller.

**Corollaries 3 and 4 were not restated** at print's antecedent, and the reason
given was that the conjunction form needs a stabilizing exponent for `A` and for
`Aᵀ` at once with nothing in the tree identifying those two. **That reason was
wrong, and they were restated on 2026-09-20 in four lines.** The conjunction
lemma already calls `finrank_ker_transpose_eq`, which collapses the two
eigenspace dimensions into one, so there is a single count to bound and print's
antecedent on `A` alone reaches it. The cost note had been written from the
shape of print's statement, which names both matrices, rather than from the
atlas's proof, which had already eliminated one of them.

**The trajectory bridge was the whole of what these rows claim, and it was
built on 2026-09-20.** This paragraph read, until 2026-09-21: *"The trajectory
bridge is still owed, and is the whole of what these rows claim. Print's
properties are complete state controllability and observability of a
differential system; this repository proves algebraic conditions that
characterize them and proves no equivalence with the dynamical definitions,
because it has none."* Every clause of that is now false, and the sweep is a day
later than the work — the same lag this document already records against
2026-09-13. `AISafetyAtlas.LinearSystems.Dynamics` defines `IsTrajectoryOn` and
`outputSignal`; `DeterminesStateOn` and `IsCompletelyReachable` are print's two
properties as properties; and `determinesStateOn_iff_isObservable` and
`isCompletelyReachable_iff_isControllable` are the two equivalences, which page
726 states and attributes to Chen and Desoer.
`AISafetyAtlas.Examples.LinearSystems.blind_not_determinesStateOn` and
`…deaf_not_isCompletelyReachable` are the two rows' informal claims at a
witness. **That question is settled: both rows were promoted to covered on
2026-09-21**, graded `EXACT`, and they own the two equivalences — a declaration
belongs to one row, so `LAND-LINSYS-001` gave them up and kept the algebraic
criteria. The scope note each row carries states the restriction its own
sentence does not: the theorems are about the finite-dimensional linear
time-invariant system over `ℂ`, print's object, not dynamical systems at large.

## What this note does not claim

That the port covers anything. That the sweep was run badly — it was run
against the corpora it names. That `LeanForControl` is the only Lean candidate:
the wider-ecosystem search that would answer *that* has still not been recorded
for these rows.
