# MAIS-O38: how the printed problem became a Lean statement

`prob:samples` — MAIS-A3 Problem 4.8, restated as open problem MAIS-O38 — is the
first MAIS row in this repository whose source is agenda **A3** and the first
with no causal content. This file records the path from those bytes to
`AISafetyAtlas.Conjectures.MAIS.maisO38_polynomialSamplesSuffice`, the searches
behind three absence claims, and the one place a submitted candidate influenced a
reading.

**Amended 2026-08-30, twice.** First, a second unwritten quantifier was found —
the *domain* of `k` — and is read the same way the first was, with the wider
reading carried beside it and refuted; see *The second unwritten quantifier*
below for why that refutation is a warning and not an answer.

Then **`prob:samples` was answered affirmatively.** CONJ-025 is `RESOLVED`.
`AISafetyAtlas.Examples.Conjectures.MAIS.maisO38_polynomialSamplesSuffice_holds`
proves the transcribed `Prop`, by way of the candidate submitted as MAIS issue
[#30](https://github.com/lionellevine/MAIS/issues/30). **The construction and the argument are the issue's, not the atlas's**; what
the atlas contributed is the transcription, the machine-check, and four
domain-neutral facts Mathlib does not carry that the proof needs. The issue said
it had been produced and checked entirely by AI systems with no human
verification — the machine-check is now that verification, and it found no gap.

## Source

| artifact | value |
|---|---|
| MAIS repository | `github.com/lionellevine/MAIS` |
| MAIS commit | `9dd29f8bf5ccd1e7701e300039b09ed4096b6516` |
| statement source | `agendas/A3/MAIS-A3.tex`, `\begin{problem}[\Oid{38}…]\label{prob:samples}` at line 290 |
| `agendas/A3/MAIS-A3.tex` sha256 | `146f0cc95a0a5eb0cf3b2660c32d591169b0e346571b80ee63723a9906371387` |
| `open-problems/MAIS-O38.md` sha256 | `cea6784554724ce4e67b8967a9fe6fba6959e70a32494dc97b0b8fd3685c4d43` |
| read | 2026-08-27 |

Both artifacts were fetched at the pinned commit and diffed against `main` on
2026-08-27: identical, so the pin and the current branch are not on different
problems. The agenda and the open-problem page state Problem 4.8 word for word
the same; the page adds one convention the agenda leaves implicit, *"Throughout,
a vector is `k`-sparse if at most `k` of its entries are nonzero"*, which is what
`IsKSparse` transcribes.

`MAIS-A3.tex` is the graded artifact, on the same footing `MAIS-A2.tex` has for
the causal rows. It is added to
[`mais-source-pin.md`](mais-source-pin.md) beside A2.

## Where the Lean lives

| what | declaration |
|---|---|
| the ledger row's statement | `AISafetyAtlas.Conjectures.MAIS.maisO38_polynomialSamplesSuffice` |
| the per-growth-law answer | `AISafetyAtlas.Conjectures.MAIS.O38PolynomialSampleAnswer` |
| print's *uniquely coded* | `AISafetyAtlas.Conjectures.MAIS.UniquelyCoded` |
| print's spark condition | `AISafetyAtlas.Conjectures.MAIS.SparkCondition` |
| the design predicate | `AISafetyAtlas.Conjectures.MAIS.GenericallyUniquelyCoding` |
| the strict-reading variant | `AISafetyAtlas.Conjectures.MAIS.maisO38_everyDimensionReading` |
| the unbounded-`k` variant | `AISafetyAtlas.Conjectures.MAIS.maisO38_unboundedSparsityReading` |
| its refutation | `AISafetyAtlas.Examples.Conjectures.MAIS.not_maisO38_unboundedSparsityReading` |
| the genericity lemma that spends | `AISafetyAtlas.Analysis.ae_eval_ne_zero_uncurry` |

Statement module `AISafetyAtlas/Conjectures/MAIS/O38.lean`; everything proved
about it is in `AISafetyAtlas/Examples/Conjectures/MAIS/O38.lean`. Neither is on
the atlas root import, like every other conjecture module.

## Interpretive choices

### 1. The unwritten quantifier over `m` — the only one that could move the grade

Print writes *"Let `k = k(m) → ∞` (say `k = ⌈m^α⌉` for some `α ∈ (0,1)`, or even
`k = ⌈log m⌉`) and `n ≥ 2k`. Do there exist `N` bounded by a polynomial in `m`
and `k`-sparse `x₁, …, x_N` such that for almost every `A` …"* and **never
quantifies `m`**. Both surrounding clauses are asymptotic, so the atlas reads the
missing quantifier at `Filter.atTop`.

What turns on it, as a theorem rather than an argument: under the strictest
alternative — a design demanded at *every* `m` — the printed sentence is false.
`AISafetyAtlas.Examples.Conjectures.MAIS.not_maisO38_everyDimensionReading`
refutes `maisO38_everyDimensionReading` with `k = fun m => m - 1` at `m = 1`,
where `k 1 = 0`, every code is the zero vector, the dataset is `{0}` and every
matrix `B` reproduces it. Print's own named family `k = ⌈log m⌉` has `k 1 = 0`
too, so the strict reading is not one print's own examples survive.

On the eventual reading, print's own hypothesis excludes that case and the atlas
supplies no condition of its own:
`AISafetyAtlas.Conjectures.MAIS.eventually_one_le_sparsity` derives `1 ≤ k m` for
large `m` from `k(m) → ∞`.

**If the other reading was right**, the row is a refuted statement about a
degeneracy at `m ≤ 1` rather than an open question, and the interesting content
of `prob:samples` would have no row at all.

### 2. Indexed family rather than set

Print writes the dataset `Y = {A x₁, …, A x_N}` with set braces and then states
*uniquely coded* index by index: `B x̄ᵢ = A xᵢ` **for all `i`**, and
`x̄ᵢ = D⁻¹P⁻¹xᵢ` at the matching index. `UniquelyCoded` takes an indexed family,
because a `Set` drops the pairing the printed condition relies on and silently
collapses repeated codes. **If the set reading was right**, the statement would
be weaker — a rival would be free to permute which datum it matches.

### 3. The a.e. quantifier as an implication

*"for almost every `A` satisfying the spark condition of order `k`"* is
transcribed as `∀ᵐ A, SparkCondition k A → UniquelyCoded k A x` rather than as an
a.e. statement for `volume.restrict {A | SparkCondition k A}`. The two agree
wherever the spark set is measurable and the implication needs no such side
condition, so no measurability obligation is incurred and none is hidden.

### 4. Polynomial coefficients in `ℕ`

*"`N` bounded by a polynomial in `m`"* is `∃ p : Polynomial ℕ, ∀ m, N m ≤ p.eval m`.
Real coefficients would be the literal reading and change nothing: a real
polynomial dominating a `ℕ`-valued function on `ℕ` is itself dominated there by
one with natural coefficients. The bound is required at every `m`, not merely
eventually, which makes the affirmative branch harder rather than easier.

## Assumptions not in print

**None.** `#check` on `maisO38_polynomialSamplesSuffice` shows two binders,
`Filter.Tendsto k Filter.atTop Filter.atTop` and `∀ m, 2 * k m ≤ n m`, which are
*"`k(m) → ∞`"* and *"`n ≥ 2k`"*. The definitional closure below the statement is
`O38PolynomialSampleAnswer`, `GenericallyUniquelyCoding`, `SparkCondition`,
`UniquelyCoded`, `IsKSparse`, `IsPermutationMatrix`, `IsInvertibleDiagonal` — all
transcriptions, none carrying a well-formedness field, a normalization, or a
domain restriction. No structure is involved, so there is no hidden field.

**No chart.** Every object is print's own: real matrices, real codes, Mathlib's
Lebesgue `volume`. `Matrix.of` is the identity equivalence and is present only
because Mathlib carries no `MeasureSpace` instance on `Matrix` (see below), not
because a representation stands in for the objects. There is therefore no
surjectivity obligation of the kind §4a of the formalization skill describes.

## Library capability, with the searches

Both claims below were checked by grep against the Mathlib source tree the atlas
builds from — `lake-manifest.json` rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
(`v4.31.0`) — not from documentation or memory.

**Mathlib has no `MeasureSpace` instance on `Matrix`.**

```console
$ grep -rn "MeasureSpace (Matrix\|MeasurableSpace (Matrix" .lake/packages/mathlib/Mathlib --include=*.lean
(no matches)
```

`Matrix m n α` is a `def`, not an `abbrev`, so the pi-type instance does not
apply through it. `GenericallyUniquelyCoding` therefore quantifies over
`Fin n → Fin m → ℝ`, whose `volume` is the `n·m`-fold product of Lebesgue
measure — print's *"Lebesgue measure on `ℝ^{n×m}`"* — and applies `Matrix.of`.

**Mathlib has no a.e.-nonvanishing lemma for a nonzero real polynomial in
several variables.**

```console
$ grep -rn "ae_ne_zero\|measure_zero.*polynomial\|zeroLocus.*volume" .lake/packages/mathlib/Mathlib --include=*.lean -i | grep -i polynom
(no matches)
$ grep -rln "MvPolynomial" .lake/packages/mathlib/Mathlib/MeasureTheory .lake/packages/mathlib/Mathlib/Analysis
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Polynomial.lean
```

The one file that pairs the two supplies analyticity of polynomial evaluation and
nothing about null sets. Mathlib carries only the finite-grid sibling,
`MvPolynomial.schwartz_zippel_totalDegree`.

**The gap is Mathlib's, and the atlas fills it.**
`AISafetyAtlas/Analysis/PolynomialGenericity.lean` is a domain-neutral module
supplying the a.e.-nonvanishing lemma in a Lebesgue null-set form
(`AISafetyAtlas.Analysis.volume_setOf_eval_eq_zero`), at an arbitrary finite
variable type (`AISafetyAtlas.Analysis.ae_eval_ne_zero_fintype`) and for any
additive Haar measure (`AISafetyAtlas.Analysis.ae_eval_ne_zero_addHaar`). It
mentions none of this problem's vocabulary and is written to be lifted upstream.
It reached `main` in commit `5ea693a` and this branch by merge; the grades below
now do rest on it, which is the change this file records.

**Mathlib has no measure-preserving form of currying at finite products.**

```console
$ grep -rn "measurePreserving.*[Cc]urry\|volume.*[Cc]urry" .lake/packages/mathlib/Mathlib --include=*.lean
.lake/packages/mathlib/Mathlib/Probability/Kernel/Representation.lean:77: (an unrelated `map_apply` rewrite)
$ grep -rn "piCurry" .lake/packages/mathlib/Mathlib/MeasureTheory --include=*.lean
… MeasurableSpace/Constructions.lean: measurable_piCurry, measurable_piCurry_symm
… MeasurableSpace/Embedding.lean: the `MeasurableEquiv.piCurry` and `MeasurableEquiv.curry` definitions
```

Everything Mathlib has is *measurability* of currying, plus the infinite-product
statements `ProbabilityTheory.infinitePi_map_piCurry` and
`infinitePi_map_piCurry_symm`, which are about `infinitePi` and not about
`volume` on a finite product. The list of measure-preserving pi equivalences in
`MeasureTheory/Constructions/Pi.lean` — `piCongrLeft`, `arrowProdEquivProdArrow`,
`sumPiEquivProdPi`, `piFinSuccAbove`, `piUnique`, `piFinTwo`, `finTwoArrow`,
`pi_empty`, `piFinsetUnion` — has no curry entry, and
`arrowProdEquivProdArrow` is a different equivalence: it splits
product-*valued* functions, not product-*indexed* ones. So the atlas writes it:
`AISafetyAtlas.Analysis.volume_measurePreserving_uncurry` and
`AISafetyAtlas.Analysis.volume_measurePreserving_curry`, with
`AISafetyAtlas.Analysis.ae_eval_ne_zero_uncurry` the composite that the spark
argument actually applies.

## What is proved, and what each proof does not settle

| declaration | says |
|---|---|
| `genericallyUniquelyCoding_two` | two one-sparse coordinate probes meet print's demand at `m = 2`, `k = 1`, every `n`, pointwise |
| `uniquelyCoded_two` | the pointwise core of it, at every dictionary with independent columns |
| `not_uniquelyCoded_of_sparsity_zero` | at `k = 0`, no design works at any nonzero dictionary |
| `not_genericallyUniquelyCoding_of_sparsity_zero` | the same at print's a.e. quantifier |
| `not_uniquelyCoded_of_full_sparsity` | at `m ≤ k` and `2 ≤ m`, no design works at any dictionary with injective `mulVec` |
| `not_uniquelyCoded_of_full_sparsity_spark` | the same stated against print's own spark hypothesis |
| `not_maisO38_everyDimensionReading` | the every-`m` reading of print is false |
| `SparkCondition.two_mul_le_rows` | print's `n ≥ 2k` is load-bearing: without it the spark condition is unsatisfiable once `2k ≤ m`, and the a.e. clause would hold vacuously for every design |
| `ae_sparkCondition` | when `2k ≤ n`, almost every matrix satisfies the spark condition of order `k` |
| `measure_setOf_sparkCondition_ne_zero` | the same as the non-nullity the ledger row asked for |
| `rows_gt_cols_of_full_sparsity_spark` | the full-sparsity route forces `m < n`, an undercomplete dictionary |
| `not_maisO38_unboundedSparsityReading` | the reading with `k` unbounded by `m` is **false** — a warning, not an answer |
| `exists_admissibleGrowthLaw` | the narrowed universal is not empty |

**Non-vacuity is discharged on both sides.** `genericallyUniquelyCoding_two`
inhabits the inner existential of `O38PolynomialSampleAnswer`, so `UniquelyCoded`
is not a predicate nothing satisfies and the printed question is not negative for
that reason. In the other direction `SparkCondition.two_mul_le_rows` shows the
outer hypothesis `n ≥ 2k` is what stops the a.e. clause from being satisfied by
an empty spark set, which would have made the affirmative branch free.

## The second unwritten quantifier: the domain of `k`

**What the full-sparsity finding turned out to be is a warning, not an answer.**
`k m = m` tends to infinity and `n m = 2 * m` satisfies `n ≥ 2k`, so nothing
print *writes* excludes this growth law, and at it no design is uniquely coded at
any matrix print's spark condition admits. The step that was missing — that the
spark-condition set is not null — is now `ae_sparkCondition`, so the reading with
`k` unbounded by `m` is refuted outright.

**Three reasons that is not an answer to `prob:samples`.** First, the argument
has no sparse-coding content: at `k = m` every vector in `ℝᵐ` is `k`-sparse, and
a single transvection reproduces any dataset with rescaled codes. Second,
`rows_gt_cols_of_full_sparsity_spark` shows print's own `n ≥ 2k` then forces
`m < n` — an *undercomplete* dictionary, while §2 of this very agenda places
superposition at `m > n`. Third, print's named families `k = ⌈m^α⌉` and
`k = ⌈log m⌉` are both `o(m)`; print says the question is open *"even at
`k = ⌈log m⌉`"*, and it stays open.

**So the domain of `k` is read, and the reading is recorded rather than argued.**
Print says what `k` tends to and never says what it ranges over, and two printed
phrases presuppose `k(m) < m`: *"`k`-sparse codes `xᵢ ∈ ℝᵐ`"* is no condition at
all once `m ≤ k`, and *"the spark condition of order `k`"* is Definition 4.1's
condition on a dictionary in `U_{n,m}`, a setting §2 places at `m > n`, giving
`2k ≤ n < m` already. `maisO38_polynomialSamplesSuffice` therefore carries
`∀ᶠ m in atTop, k m < m` — eventual, because print's own `k = ⌈m^α⌉` has
`k 1 = 1 = m` and a demand at every `m` would exclude a family print names. The
wider reading is `maisO38_unboundedSparsityReading`, it is false, and
`not_maisO38_unboundedSparsityReading` proves it. This is the same move, and the
same justification, as reading the `m`-quantifier at `Filter.atTop` in
Interpretive choice 1. `exists_admissibleGrowthLaw` checks the narrowing did not
empty the universal, and MAIS issue [#30](https://github.com/lionellevine/MAIS/issues/30) reads the domain as `1 ≤ k < m`
independently.

**No conflict with the bounds print quotes.** At `k = m` the classical counts
print names — `(k+1)binom(m,k)`, `k·binom(m,k)²`, `m(k-1)binom(m,k)+m` — collapse
to polynomials in `m`, which can look like a contradiction. It is not one: those
are uniqueness theorems for a sparsity that constrains, and none of them is
transcribed, checked, or asserted anywhere in this repository.

The three things that stood between the genericity lemma and this finding, all
now done:

1. a witness that the relevant `q × q` minor of `A_S` is a nonzero polynomial,
   which is where print's `n ≥ 2k` is spent — the witness is an embedded
   identity submatrix, in `ae_linearIndependent_col`, and the injection
   `S ↪ Fin n` it needs exists exactly because `S.card ≤ 2k ≤ n`;
2. a finite union over the index sets `S` — `MeasureTheory.ae_all_iff` over the
   countable `Finset (Fin m)`, in `ae_sparkCondition`;
3. a transport between `Fin n → Fin m → ℝ`, where `GenericallyUniquelyCoding`
   quantifies, and `(Fin n × Fin m) → ℝ`, where the genericity lemma is stated.
   Mathlib has `MeasurableEquiv.piCurry` but no measure-preserving form of it —
   the search is recorded above — so the atlas wrote
   `AISafetyAtlas.Analysis.volume_measurePreserving_curry`.

One further piece was needed and was not on the original list:
`AISafetyAtlas.Analysis.volume_ne_zero_pi_pi`. An almost-everywhere statement
refutes nothing over the zero measure, so the contradiction
`not_maisO38_unboundedSparsityReading` draws from `∀ᵐ A, False` has to know that
`volume` on `Fin (2m) → Fin m → ℝ` is not zero. That space carries no
`IsAddHaarMeasure` instance — the instance is on the flat `ι → ℝ` — so the fact
is transported across the same currying equivalence.

**`ae_sparkCondition` outlives the warning it was built for.** Print quantifies
over dictionaries *almost everywhere*, so any future answer to `prob:samples`,
affirmative or negative, has to know the spark-condition set is not null or its
own a.e. clause is vacuous. That obligation is now discharged for every `k` and
`n` with `2k ≤ n`, not only at the degenerate law, and it is the part of this
work that is worth something independently of the reading dispute.

## The submitted candidate, and exactly what it changed

[MAIS issue #30](https://github.com/lionellevine/MAIS/issues/30), *"MAIS-O38
candidate complete solution: `m³+2m` fixed codes suffice for every sparsity
`k < m`"*, filed 2026-08-26 by `26david26`, body sha256
`6e2db10eb10242c075ca331fcf87a604511b9b31df3d55a5c4b0d2d2d95d05ab` as read
2026-08-27, no comments. It says it was produced and checked entirely by AI
systems with no human verification.

### The candidate is transcribed and proved

Added 2026-08-30. `AISafetyAtlas.Conjectures.MAIS.o38PolynomialSampleCandidate`
transcribes the issue's Theorem 3, and
`AISafetyAtlas.Examples.Conjectures.MAIS.o38PolynomialSampleCandidate_holds`
proves it. Two chains carry that to the row:

| declaration | says |
|---|---|
| `maisO38_polynomialSamplesSuffice_of_candidate` | if the candidate is true, CONJ-025 is resolved affirmatively |
| `o38PolynomialSampleCandidate_of_forcing` | a design whose rivals are *forced* yields the candidate |
| `uniquelyCoded_of_forcing` | forcing data ⟹ print's Definition 1, i.e. the note's Steps 1, 3 and 4 |

The middle layer is what most of the work went into.
`AISafetyAtlas/Examples/Conjectures/MAIS/O38Candidate.lean` carries the note's
Lemma 7 in full (`cyclicWindow_injective`, `card_windows_containing`,
`card_windows_containing_pair`), the spark-condition uniqueness it rests on
(`sparse_eq_of_mulVec_eq`), print's (15)
(`mem_windowSpan_iff_support_subset`), the incidence count of Step 3
(`colDegree_le`, `exists_smul_col_of_colDegree_eq`, `sum_colDegree_ge`,
`colDegree_eq`), Step 4 (`exists_perm_smul_col`), and the design itself
(`o38Design`, `isKSparse_o38Design`).

**Lemma 6 and Lemma 8 are proved**, and with them the whole of the note's
Theorem 3. `ForcingData` isolates exactly what Lemma 6 delivers, so the layers
below it are independent of how it is proved.

`AISafetyAtlas/Analysis/NullImage.lean` and
`AISafetyAtlas/Analysis/MaximalMinor.lean` carry the machinery, written because
Mathlib has no semialgebraic dimension theory:

1. `volume_image_eq_zero_of_card_lt` — a locally Lipschitz image of a
   lower-dimensional space is null, via Mathlib's Hausdorff dimension API.
2. `volume_setOf_exists_forall_dotProduct_eq_zero` — `L` hyperplanes whose
   normals are a `C¹` function of one parameter with fewer than `L` coordinates
   meet almost no point. The charts are indexed by which coordinate each equation
   is solved for, and `Fin.insertNth` does the solving.
3. `exists_det_ne_zero_of_linearIndependent` — a rectangular matrix with
   independent columns has a nonzero maximal minor. Mathlib has only the square
   case. This is what turns *"these vectors are independent"* into *"this
   polynomial in the entries is nonzero"*, which a parametrized argument needs
   because a rational or chart-based witness would cost parameters and there are
   none to spare.
4. `measurableSet_exists_of_isClosed` — a projection along a σ-compact factor of
   a closed set is measurable. Lemma 8's Tonelli step needs the bad set, stated
   with an existential over rivals, to be measurable; the projection of a Borel
   set is analytic, and Mathlib has analytic sets but not their universal
   measurability.

**How the count works.** The rival dictionaries with columns in `im A` are
exactly `A · C` for `C` an `m × m` matrix, so they form an `m²`-parameter family
and `L = m² + 1` clears it by exactly one — there is no room for a further
parameter, which is why no basis of `im A` is needed anywhere and why the normals
must be *functions* of `C`. They are taken to be minors: for a column set `T'`
and a row set `R` with `|R| = |T'| + 1`, `det[B_{T'} | A_{Sₜ}e_j]_R` is linear in
the coefficient and polynomial in `C`, vanishes on the subspace that has to be
cut down, and is nonzero for some `(T', R)` exactly when it must be. Choosing
`(T', R)` is a finite discrete choice, absorbed by a finite union rather than by
a chart.

One simplification found while formalizing and worth recording: a rival with
columns in `im A` is `A · C` for `C` an `m × m` matrix, so the rivals form an
`m²`-parameter family with no basis of `im A` needed anywhere. That is why
`L = m² + 1` is the right constant, and it replaces the note's `dm` bound.

### The issue's influence on the transcription

**Corrected 2026-08-30.** The paragraph that stood here said the issue's only
influence was its range `1 ≤ k < m`, which is where the atlas looked for the
boundary of the non-degenerate sparsity range. That understated it, and the
correction is the point of this section. The issue contains **two** theorems.

**The first** is the candidate: `N = m³ + 2m` codes depending only on `m` and
`k`, for every `n ≥ 2k` and Lebesgue-almost every spark-condition `A`, at every
`1 ≤ k < m`. It is *stronger* than CONJ-025 asks, since its codes do not depend
on `n` where print fixes `n` before asking for codes.

**Transcribed and proved, 2026-08-30.** `o38PolynomialSampleCandidate` states it;
`Examples.Conjectures.MAIS.o38PolynomialSampleCandidate_holds` proves it; and
`maisO38_polynomialSamplesSuffice_of_candidate` carries it to `prob:samples` at
print's own quantifier. No `sorry`, no added axiom. CONJ-025 is `RESOLVED`
affirmatively, and it is the issue's argument that resolves it.

**The second** is labelled *boundary*: at `m ≥ 2`, `k ≥ m` and `n ≥ 2k`, no
finite list of `k`-sparse codes is uniquely coded at any spark-condition `A` —
and the issue says in terms that this *"settles the literal reading of the
question in which `k < m` is nowhere imposed."* That is the same statement as
`not_uniquelyCoded_of_full_sparsity_spark`, and the same reading finding this
file records under *The second unwritten quantifier*. The atlas proved it
independently, and marginally stronger — no `n ≥ 2k` hypothesis is needed, since
the spark condition at `m ≤ k` already forces `mulVec` injectivity — but the
statement, and the observation that it settles the literal reading, were filed
on 2026-08-26 and are the issue's. They are credited, not presented as the
atlas's own. `not_uniquelyCoded_of_sparsity_zero`, below the range, has no
antecedent in the issue.

**Superseded 2026-08-30, and the superseded text is kept because it was cited.**
The paragraph here read: *"the construction, the `N = m³ + 2m` bound, the
reduction to the spark condition, and the proof are not transcribed, not checked,
and not asserted anywhere in this repository … no coverage count, resolution, or
grade rests on the issue."* That was written on 2026-08-27 and was true then. It
stopped being true on 2026-08-30, when the construction was transcribed and the
proof went through, and it stayed on this page for hours afterwards — including
while this file was linked from the MAIS
[issue #30](https://github.com/lionellevine/MAIS/issues/30) thread as the
transcription record, where it contradicted the comment linking to it.

**Recorded rather than deleted, because the failure is the interesting part.** A
provenance note is a claim about the tree, and a claim about the tree has a shelf
life measured in commits. This one was falsified by the commit two files away and
nothing re-ran it. The two absence claims below are flagged for re-checking on a
Mathlib upgrade; nothing flagged *this* for re-checking on a change to the atlas's
own Lean, which is the shorter and likelier clock.

What still holds, and is a distinction worth keeping: **CONJ-025's statement is
print's quantifier order, not the issue's.** Print fixes `k` and `n` before asking
for codes, so the codes the row quantifies over may depend on `n`; the issue's
depend only on `m` and `k`. The row is resolved by an argument stronger than the
row demands.

## What a later reader should re-check

The three greps above, against whatever Mathlib revision the atlas has moved to.
Two of them are absence claims with a shelf life: the a.e.-nonvanishing lemma for
a nonzero real polynomial, and a measure-preserving form of currying at finite
products. Either landing *upstream* falsifies this file in the good direction —
it makes the corresponding part of
`AISafetyAtlas/Analysis/PolynomialGenericity.lean` a duplicate to retire rather
than a gap the atlas fills, and the module is written to be lifted, so that is
the intended end state. Neither would disturb the refutation, which does not
depend on where the lemma lives.

A `MeasureSpace` instance on `Matrix` landing upstream would falsify the first
grep and would simplify `GenericallyUniquelyCoding`; it would not change the
statement, since `Matrix.of` is the identity equivalence.
