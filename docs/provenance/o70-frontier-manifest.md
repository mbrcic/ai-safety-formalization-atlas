# MAIS-O70: the three frontier hypotheses, and everything that stands on them

Every O70 result that is not unconditional carries one or more of the hypotheses
below as a visible binder. This file is the manifest: for each, the exact
proposition, where it comes from, how the atlas's version compares with the
printed one, what the risk is, and — named individually, not by gate — every
declaration that consumes it.

**The three are not the same kind of thing.** `O70-EIGEN-LAW` and
`O70-EXACT-LOCAL` are results the *candidate solution* cites and the atlas
assumes in its place: the gap they mark is between the atlas and the candidate's
own citations. `O70-ZETA-BRIDGE` is a gap between the atlas and the **problem
statement's own primary definition** of the object under study — it is print,
not the candidate, that asserts the proposition, and the atlas works throughout
in the form print calls equivalent rather than the form print defines first. A
reader who groups all three together will misread the third.

**None of the three is proved anywhere in the atlas, and the atlas holds no
unconditional inhabitant of any of them.** No stress evidence below is a proof
that the antecedent is inhabited. `CONJ-026` is `OPEN`.

---

## O70-EIGEN-LAW

**Lean.** `AISafetyAtlas.SingularLearning.EigenvalueLawStatement`,
[`AISafetyAtlas/SingularLearning/EigenvalueLaw.lean`](../../AISafetyAtlas/SingularLearning/EigenvalueLaw.lean).

**Statement.** For every wide shape `k ≤ d` with `0 < k` there is a single
`Z > 0`, quantified *before* `ρ` and `T`, such that for all `ρ ≥ 0` and `T ≥ 0`

```
∫_{ℝ^{k×d}} e^{−‖X‖²_F} · det(1 + T·X Xᵀ)^{−ρ} dX  =  Z · J(k, T, (d−k−1)/2, ρ)
```

with `J` the integral over the full positive orthant `(0,∞)^k` of
`e^{−Σ sᵢ} · (∏ sᵢ^α) · |Vandermonde(s)| · ∏ (1 + T sᵢ)^{−ρ}`.

The frozen surface is `eigenvalueLawStatement_iff`, which is `Iff.rfl` and
expands `chamberJFull` into the orthant integral, the weight exponent, the
Vandermonde factor and the `(1 + T sᵢ)^{−ρ}` product, so none of those sits
behind the definition.

**Source.** The candidate (MAIS issue #3) cites Muirhead, *Aspects of
Multivariate Statistical Theory*, Theorems 3.2.1 and 3.2.17, after James (1954):
the real Wishart density together with the Jacobian of the eigenvalue
decomposition.

**Pinning gap: unpinned, and unpinnable from here.** Muirhead is a copyrighted
monograph — *Aspects of Multivariate Statistical Theory*, Robb J. Muirhead,
Wiley Series in Probability and Mathematical Statistics, John Wiley & Sons, 1982
(ISBN 0-471-09442-0), reissued by Wiley-Interscience in 2005 (ISBN
978-0-471-76985-9). It is not open access, no copy has been supplied, and none
was obtained, so it has **not** been fetched or hashed into the pinned
literature directory and nobody here has opened it. What is recorded, and
nothing beyond it: Theorem 3.2.1 is cited for the real Wishart density (going
back to Wishart, *Biometrika* 20A(1–2) (1928), 32–52) and Theorem 3.2.17 for the
Jacobian of the eigenvalue decomposition (going back to James, *Ann. Math.
Statist.* 25(1) (1954), 40–75), both said to be in the book's Chapter 3.2. The
candidate cites the 1982 Wiley printing; the 2005 reissue is recorded here only
so a reader who finds that printing knows it is a different object, and this
file has not checked that the two carry the same numbering.

**The candidate carries the same gap, and says so.** Its §13 states that the two
theorem numbers "follow standard citation practice for the 1982 edition and were
not checked against a printed copy", and that no page is given for James
"because none was verified". The numbers above are therefore a citation of a
citation, checked at neither end. That changes no grade:
`EigenvalueLawStatement` quantifies its constant existentially and never names
the multivariate-gamma value, so no atlas declaration would break if a number
were wrong — but no atlas declaration confirms one either, and the risk below
stays exactly where it is.

**Match grade.** *Narrower in shape, weaker in the constant.* Narrower: the
atlas quantifies only over wide shapes `k ≤ d`, which is all the O70 chain
consumes, where the cited source is stated without that restriction. Weaker: `Z`
is existentially quantified rather than given the source's explicit
multivariate-gamma value. For a hypothesis, weaker is the safe direction — the
atlas assumes less than the source supplies — but it also means no single
`(T, ρ)` can detect a wrong constant, which is why the evidence below is built
around ratios in which `Z` cancels.

The exponent `(d − k − 1)/2` is formed in `ℝ`. At `d = k = 1` it is `−1/2`;
formed with `ℕ`-subtraction it would be `0`, and `J(0)` would be `1` rather than
`Γ(1/2)`. The frozen statement distinguishes the two.

**Risk: high.** It is the analytic core of the residual-germ theorem, and it is
cited rather than derived.

**Consumers.** Seventeen named declarations take it as a hypothesis. The count and
every line number below were measured from the sources rather than carried in a
table; `hasZetaPoleOrder_o70Pair` is among them, and takes all three frontiers.

| declaration | file |
|---|---|
| `hasLocalVolumeOrder_residualGerm_table` | `Conjectures/MAIS/O70Proof.lean:249` |
| `hasLocalVolumeOrder_rrrLoss_canonical_table` | `Conjectures/MAIS/O70Proof.lean:300` |
| `hasLocalVolumeOrder_rrrLoss_canonical_table_all` | `Conjectures/MAIS/O70Proof.lean:417` |
| `isO70VolumeOrderTable_o70Pair` | `Conjectures/MAIS/O70Proof.lean:481` |
| `isO70RankTable_o70Pair` | `Conjectures/MAIS/O70Proof.lean:498` |
| `o70DependsOnRanksOnly_of_frontiers` | `Conjectures/MAIS/O70Proof.lean:504` |
| `isO70MinimizerCharacterization_o70Minimizers` | `Conjectures/MAIS/O70Proof.lean:533` |
| `hasZetaPoleOrder_o70Pair` | `Conjectures/MAIS/O70Proof.lean:590` |
| `gaussianLaplace_residualGerm_eq_chamber` | `SingularLearning/ResidualLaplace.lean:189` |
| `hasLocalVolumeOrder_residualGerm` | `SingularLearning/ResidualLaplace.lean:278` |
| `gaussianLaplace_residualGerm_eq_chamber_tall` | `SingularLearning/ResidualLaplace.lean:343` |
| `hasLocalVolumeOrder_residualGerm_tall` | `SingularLearning/ResidualLaplace.lean:365` |
| `hasLocalVolumeOrder_residualGerm_min` | `SingularLearning/ResidualLaplace.lean:378` |
| `eigenvalueLaw_normalisation` | `SingularLearning/EigenvalueLaw.lean:187` |
| `eigenvalueLaw_chamberJFull_pos` | `SingularLearning/EigenvalueLaw.lean:201` |
| `eigenvalueLaw_one_one` | `SingularLearning/EigenvalueLaw.lean:219` |
| `eigenvalueLaw_ratio` | `SingularLearning/EigenvalueLaw.lean:244` |

`eigenvalueLawStatement_iff` mentions it but is the frozen surface, not a
consumer, and the `EigenvalueLawStatement` definition itself is not one either.
The last four rows are stress evidence, not part of the O70 chain.
`hasZetaPoleOrder_o70Pair` is the one declaration in the atlas that takes all
three frontiers at once, so it appears in this table, in `O70-EXACT-LOCAL`'s and
in `O70-ZETA-BRIDGE`'s; it is not part of the P1/P2/P3 chain either.

`example`s are counted separately and are not in the table, because an example
is a use of the frontier and not something anything else can stand on.
Twenty-one take the hypothesis: twelve in
`Examples/Conjectures/MAIS/O70Proof.lean`, six in
`Examples/SingularLearning/ResidualLaplace.lean` and three in
`Examples/SingularLearning/EigenvalueLaw.lean`. One further example, in
`Examples/SingularLearning/EigenvalueLaw.lean`, restates the frozen surface, so
it states the proposition rather than assuming it.

**V7 stress evidence.**

* Proved anchors: `eigenvalueLaw_normalisation` (the `T = 0` normalisation),
  `eigenvalueLaw_chamberJFull_pos` (`J(0)` finite and positive, read off the
  proposition rather than assumed), `eigenvalueLaw_one_one` (the `1×1`
  specialization, pinning the `ℝ`-formed exponent), and `eigenvalueLaw_ratio`,
  the `Z`-free cross-multiplied identity that is the only anchor exercising
  `T > 0` and `ρ > 0`.
* Numerical probe:
  [`scripts/reproduce_eigenvalue_law_probe.py`](../../scripts/reproduce_eigenvalue_law_probe.py),
  stdlib only, deterministically seeded. At `k = 1` it is exact, pinning
  `Z = π^(d/2)/Γ(d/2)` and finding it constant across five `(T, ρ)` to machine
  precision at `d ∈ {1,2,3,5}`. At `k = 2` — the smallest shape whose
  Vandermonde is not `1` — it is Monte-Carlo, and it measures its own power:
  the ratio is constant to about `10⁻³` with the Vandermonde and moves by about
  `0.26` with it deleted.
* Cross-check against a frontier-free result:
  `AISafetyAtlas.SingularLearning.hasLocalVolumeOrder_residualGerm_one` proves the
  local pair of `x²y²` with no hypothesis at all, by an elementary split of one
  one-dimensional integral. The conditional chain reaches the same germ through
  the eigenvalue law, Proposition 8.9, the chamber calculus and the Tauberian
  bridge. `volumeOrder_unique` forces the two answers to agree, so the example in
  `Examples/Conjectures/MAIS/O70Proof.lean` *derives* `(1/2, 2)` from the two
  analytic facts rather than computing it — and had the chamber calculus or the
  exponent bridge been wrong at that shape, the same example would be a
  refutation of `EigenvalueLawStatement`. This is the only place where a
  consequence of the frontier is checkable against something proved without it.
* Limitations: the probe covers `k ∈ {1,2}` and `d ≤ 5`; its `k = 2` arm is
  statistical and rejects gross shape errors, not small ones. No anchor and no
  probe reaches `k > 2`, and the cross-check is at one shape.
  **None of this inhabits the proposition.**

---

## O70-EXACT-LOCAL

**Lean.** `AISafetyAtlas.Conjectures.MAIS.O70ExactLocalPairsExist`,
[`AISafetyAtlas/Conjectures/MAIS/O70.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70.lean).

**Statement.** The *value-free* existence claim: for all positive `M, N, H` and
every truth matrix `C` with a factorization `B * A = C`, there exist `lam` and
`m` with `HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A B) lam m`.
It asserts that *some* exact local pair exists and never what it is — assuming
the value would assume the candidate's own contribution.

The frozen surface is `o70ExactLocalPairsExist_iff` (`Conjectures/MAIS/O70.lean:818`), `Iff.rfl`,
which expands `HasExactLocalPair` rather than naming it, putting the degenerate
`(0,1)` branch, the countable exceptional set of radii and the radius quantifier
on the lock instead of behind it.

**Source.** The candidate's Definition 2.1 and Lemma 6.1(iv), narrowed to
clause (i) Step 4 only: the passage from the rightmost zeta pole to exact
constant-carrying volume asymptotics. The candidate's §13 names this as the single non-elementary
citation in the whole derivation. The E1 route of record is Greenblatt, *An
elementary coordinate-dependent local resolution of singularities and
applications*, J. Funct. Anal. 255 (2008), with the companion arXiv:0709.2496
Thm 1.1 giving the sublevel-set expansion directly.

**Match grade.** *Same quantifiers as print's existence claim, strictly weaker
in content.* Print's Lemma 6.1(i) supplies the exact asymptotics **and** the
value; the atlas assumes only that a pair exists. The quantification — every
`C`, every factorization — matches print. Weaker is again the safe direction.

**Pinning gap: the arXiv companions are pinned, the journal article is not.**
Two Greenblatt preprints are pinned by the sha256 digests below. The PDFs are
not redistributed with this repository.

| file | what it is | sha256 |
|---|---|---|
| `greenblatt-arxiv-v2-2008-resolution-of-singularities-asymptotic-expansions-of-integrals.pdf` | arXiv:0709.2496v2, 21 Sep 2008, 23 pp. Carries Thm 1.1 (the sublevel expansion), Thm 1.3 and Thm 1.4 (meromorphy). Published as *J. Anal. Math.* 111 (2010) 221–245, doi 10.1007/s11854-010-0016-1, which is paywalled and not pinned. | `5717cc959af9237dc1776aee293dbfd876eaf3421c81de5b1daac0b1759730c3` |
| `greenblatt-arxiv-v3-2015-constructive-elementary-local-resolution-of-singularities.pdf` | arXiv:1207.1902v3, 24 Mar 2015, 27 pp. No journal reference on arXiv. | `7fff982cb57a4d9f7ab19887d54efd9f9135c5b2243b63dd3047138b3cd0b323` |

**The journal article named in the Source paragraph is not on arXiv.**
Greenblatt, *An elementary coordinate-dependent local resolution of
singularities and applications*, *J. Funct. Anal.* 255(8) (2008) 1957–1994,
doi 10.1016/j.jfa.2008.08.006, is Elsevier, and a title search of arXiv returns
nothing. It is named, not pinned. The mitigation is that arXiv:0709.2496 quotes
its main theorem verbatim in its §2, as "Main Theorem of [Gr]", so the engine
the route runs on is legible from a pinned file even though the article is not.
That quotation is itself stated for a nonnegative smooth compactly supported
bump, which is the restriction the scope note below turns on.

**The candidate's own Step-4 citation is not Greenblatt.** The Source paragraph
names Greenblatt as the atlas's route of record. The candidate's §13 names
something else for the same step: "The precise source used here is Lin's
state-density calculus [16, Sec. 3.3–3.4, Proposition 3.15 and Theorem 3.16,
pp. 66–68]", where [16] is Shaowei Lin, *Algebraic Methods for Evaluating
Integrals in Bayesian Statistics*, PhD thesis, UC Berkeley, 2011, with companion
preprint arXiv:1003.5338. The thesis was not obtained and is **not** pinned; the
page numbers above are its. The companion preprint is pinned:

| file | what it is | sha256 |
|---|---|---|
| `lin-arxiv-v3-2017-ideal-theoretic-strategies-marginal-likelihood-integrals.pdf` | arXiv:1003.5338v3, 13 Feb 2017, 34 pp., *Ideal-Theoretic Strategies for Asymptotic Approximation of Marginal Likelihood Integrals*. Its numbering is not the thesis's: the state-density results here are Corollary 2.6 and Theorem 2.10, and this file has **not** checked that they are the thesis's Proposition 3.15 and Theorem 3.16. | `a162cf4eab3bdd41f6651a9c420413968288b6788141556b117fc0b1c6909765` |

**Scope delta: Greenblatt Thm 1.1 against what this frontier asserts.** Four
gaps, and one thing that is not a gap.

1. *The cutoff is smooth, and never a ball.* Thm 1.1 fixes a neighbourhood V of
   the origin and quantifies over a smooth φ supported in V; its integral is
   over the set of points of A at which every fᵢ lies strictly between 0 and t.
   `sublevelVolume` is the Lebesgue volume of the points of the open ball of
   radius δ about the germ point at which the germ is at most ε — a sharp
   Euclidean ball, no weight. Nothing in Thm 1.1 is stated for an indicator, so
   the frontier's radius quantifier and its countable exceptional set of radii
   have no counterpart in the theorem: it says nothing about δ because it has
   no δ.
2. *No positive leading constant.* Thm 1.1's coefficients are distributions in
   φ and are bounded from **above** only, by a constant times a finite sup of
   derivatives of φ. The theorem does not assert that the leading coefficient is
   nonzero, let alone positive. `HasExactLocalPair` demands a positive constant
   with the ratio tending to 1, so positivity is a step the theorem does not
   supply.
3. *The region is not a ball either.* Thm 1.1's region is an open set cut out by
   finitely many strict real-analytic inequalities, with the germ point required
   to lie on its **boundary**. A ball centred at the germ point has that point
   in its interior, so it is not an instance of the hypothesis as written.
4. *One germ, not a family.* Greenblatt is a germ statement at the origin for a
   fixed tuple of real-analytic functions. `O70ExactLocalPairsExist` quantifies
   over every positive shape and every truth matrix with a factorization.
   Instantiating a germ theorem at each member of that family is routine and
   nothing in the atlas does it.

Not a gap: real-analyticity. Thm 1.1 is stated for real-analytic functions and
the O70 germs are polynomial, so they are inside its class rather than outside
it. Nor does the frontier lose anything to Thm 1.1's exponents being pinned down
only as an arithmetic progression of positive rationals, since the frontier is
value-free.

Thm 1.4, the meromorphy half of the same route, carries the same smooth-φ
restriction; that matters at `O70-ZETA-BRIDGE` rather than here, and is recorded
in that section's pinning note.

**Nothing above is a proof.** Fetching a source does not inhabit a hypothesis.
The match grade and the risk immediately above and below are unchanged,
`O70ExactLocalPairsExist` is still assumed rather than proved, and `CONJ-026` is
still `OPEN`.

**Risk: high.** Its V7 package rules out the trivial satisfaction of the
hypothesis but offers no positive evidence that it holds, where the eigenvalue
law has four anchors and a probe that could have falsified it and did not.

**Consumers.** Six declarations take it as a hypothesis. The count and every
line number below were measured from the sources rather than carried in a table.

| declaration | file |
|---|---|
| `exactLocalPair_nondegenerate_of_frontier` | `Conjectures/MAIS/O70.lean:923` |
| `isO70RankTable_of_volumeOrder` | `Conjectures/MAIS/O70.lean:940` |
| `isO70RankTable_o70Pair` | `Conjectures/MAIS/O70Proof.lean:498` |
| `o70DependsOnRanksOnly_of_frontiers` | `Conjectures/MAIS/O70Proof.lean:504` |
| `isO70MinimizerCharacterization_o70Minimizers` | `Conjectures/MAIS/O70Proof.lean:533` |
| `hasZetaPoleOrder_o70Pair` | `Conjectures/MAIS/O70Proof.lean:590` |

`o70ExactLocalPairsExist_iff` mentions it but is the frozen surface, and the
`O70ExactLocalPairsExist` definition itself is not a consumer.

Two rows are in the table but not in the O70 chain. The first,
`exactLocalPair_nondegenerate_of_frontier`, takes the frontier only to read a
property off whatever witnesses it supplies, and asserts nothing about the
model — see the V7 section below. The last, `hasZetaPoleOrder_o70Pair`, takes
this frontier alongside the other two and restates P2's table in print's zeta
normalization; it is `O70-ZETA-BRIDGE`'s only consumer and is discussed there.
The remaining three are the chain.

Three `example`s take the hypothesis, all in
`Examples/Conjectures/MAIS/O70Proof.lean`; as above, examples are counted
separately and are not in the table.

`IsO70RankTable` is `CONJ-026`'s ledger-graded `lean` declaration, so this
frontier stands directly under the row's graded proposition, not under Gate
BExact alone.

**V7 stress evidence: the cheap branch is closed off, everywhere.**

The frontier is an existential, and `HasExactLocalPair` offers a free way to
satisfy it: the neutral branch `(lam, m) = (0, 1)`, available to any germ that
vanishes on a whole neighbourhood. If the O70 germs took that branch the
hypothesis would be true and worthless, and every theorem carrying it would be
carrying nothing.

`not_eventually_rrrLossCoords_eq_zero_of_pos` closes it off at **every** instance
the frontier quantifies over — every positive shape and every `(C, A, B)`, with
no factorization hypothesis needed. Perturbing along the all-ones directions
`(A + t·F, B + t·E)` makes the `(0,0)` entry of the residual a quadratic
`d + t·S + t²·H` whose leading coefficient is `H > 0`; vanishing on a ball of
radius `ε` would force `d = 0` at `t = 0` and then `H·ε² = 0` from `t = ±ε/2`.
`exactLocalPair_nondegenerate_of_frontier` reads off the consequence: any witness
the frontier supplies, anywhere, has `0 < lam` and `1 ≤ m`. Both are
kernel-checked at `{propext, Classical.choice, Quot.sound}` and neither adds an
axiom. `not_eventually_rrrLossCoords_eq_zero_of_pos` is unconditional outright —
a fact about the definitions, not about the frontier. The nondegeneracy theorem
does take the frontier as a binder, which is why it appears in the consumer
table, but it consumes it only to inspect the witnesses: if the frontier is
false it says nothing, so it is not evidence that the frontier holds.

Limitations. This shows the frontier cannot be satisfied *cheaply*; it does not
show it can be satisfied at all, and it says nothing about the *value* of any
pair. There is still no numerical probe, and no exact-pair anchor on a singular
member of the family — the only `HasExactLocalPair` inhabitants in the atlas are
the quadratic germs (`hasExactLocalPair_quadraticGerm` and its examples), which
are the regular case. **Nothing here inhabits the proposition**, and the
existence half of this package is still an open Gate BΘ item.

---

## O70-ZETA-BRIDGE

**Lean.** `AISafetyAtlas.Conjectures.MAIS.O70ZetaPoleBridge`,
[`AISafetyAtlas/Conjectures/MAIS/O70.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70.lean).
The definitions it is phrased in terms of — `zetaIntegral`,
`HasZetaRealAxisOrder` and `HasZetaPoleOrder` — are in
[`AISafetyAtlas/SingularLearning/ZetaPair.lean`](../../AISafetyAtlas/SingularLearning/ZetaPair.lean),
which since this revision holds definitions and a recorded counterexample and no
claim of its own.

**Not the same kind of frontier as the two above.** Those are results the
candidate cites. This one is the substitution the atlas makes for print's *own*
primary definition. `MAIS-A6.tex` `def:local` fixes `λ(w*)` and `m(w*)` as "the
threshold and pole order, in the sense of `thm:zeta`, of
`ζ_{w*}(z) = ∫_{B_ε(w*)} K(w)^z dw`", and only afterwards adds "Equivalently,
`λ(w*)` is the exponent in `eq:volume`", citing `[lau2023]`. `LocalPair.lean`
takes that second, volume, form as primary, and every O70 result in the atlas is
proved about `HasExactLocalPair`, which is the volume form. The proposition
below is that substitution. **Print asserts it; the atlas does not prove it.**

**The general form of this substitution is false, which is why the proposition
below is narrow.** Quantified over *every* germ: for every dimension,
every nonnegative `K` not vanishing on a whole neighbourhood of `w`, and every
`(lam, m)`, `HasExactLocalPair` would imply `HasZetaPoleOrder`. **That
proposition is false.** `HasExactLocalPair` constrains only the *leading*
behaviour of the sublevel volume — a ratio tending to `1` — so a radial germ
whose sublevel volume is `c · ε^lam · (1 + 1 / log (1 / ε))` still satisfies it
with pair `(lam, 1)`, while its zeta function acquires a **logarithmic branch
point** at `-lam` rather than a pole, and `HasZetaPoleOrder` fails. Neither
nonnegativity nor nondegeneracy repairs that. What was missing is the hypothesis
print itself carries: `def:local` speaks of a nonnegative **real-analytic** `K`,
and meromorphic continuation of the zeta function follows from resolution of
singularities, which needs the analyticity.

A false frontier is worse than an unproved one: every theorem standing on it is
*unapplicable* rather than merely conditional. So the proposition stated below is
quantified only over the germs the atlas actually applies it to. Those germs are
polynomial, hence real-analytic — a step that is now the Lean theorem
`analyticAt_rrrLossCoords` rather than this sentence, see the match grade below —
so the counterexample's mechanism does not reach them and the narrow form is not
known false. The counterexample itself is
recorded in `ZetaPair.lean` under "Why there is no general bridge here", and its
`ε → 0` half — that the logarithmic correction is invisible to the limit
`HasExactLocalPair` takes, so the germ really does keep the pair `(lam, 1)` — is
witnessed by an example in
[`AISafetyAtlas/Examples/SingularLearning/ZetaPair.lean`](../../AISafetyAtlas/Examples/SingularLearning/ZetaPair.lean).

**Statement.** At the O70 germs, and only there. For all positive `M, N, H`,
every truth matrix `C` with a factorization `B * A = C`, and every `(lam, m)`:
if `HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A B) lam m`,
then `HasZetaPoleOrder` holds of that same germ, point and pair — there is a
radius `δ > 0` and a function `Z : ℂ → ℂ` that agrees with the zeta integral
`zetaIntegral (rrrLossCoords M N H C) (matrixPairCoords A B) δ` on the real axis
to the right of `-lam`, is analytic at every `z` with `-lam < z.re`, and is
meromorphic at `-lam` with `meromorphicOrderAt Z (-lam) = -m`. The analyticity
clause is what "threshold" asserts — `-lam` is where the continuation *first*
fails to be analytic, not merely some pole somewhere — and the sign is Mathlib's
convention, in which a pole of order `m` has order `-m`. The quantifiers are
exactly those of `O70ExactLocalPairsExist`, so the two frontiers are stated over
the same family.

**It carries no side conditions, and does not need to.** A general form would
have to name nonnegativity and nondegeneracy as hypotheses. Neither appears
here. Nonnegativity is a property of the germs: `rrrLossCoords` is `rrrLoss` in
Euclidean coordinates and `rrrLoss_nonneg` is unconditional. Nondegeneracy comes
from the positivity already in the shape quantifiers: at `0 < M`, `0 < N`,
`0 < H` the loss vanishes on no neighbourhood of any point, by
`not_eventually_rrrLossCoords_eq_zero_of_pos`, which is unconditional and needs
no factorization hypothesis. So the neutral `(0, 1)` branch of
`HasExactLocalPair` — the one branch on which any such bridge is **false**
rather than unproved, since the zeta integral of the zero germ vanishes
identically for `x > 0` and its meromorphic order is `⊤`, not `-1` — is
unreachable at every instance this frontier quantifies over. `rem:conventions`
excludes the same germ. Both halves of that are pinned in
`Examples/SingularLearning/ZetaPair.lean`. The exclusion is therefore a fact
about the family rather than a clause a reader has to check.

The frozen surface is `o70ZetaPoleBridge_iff`
(`Conjectures/MAIS/O70.lean:725`), `Iff.rfl`, which expands *both*
`HasExactLocalPair` and `HasZetaPoleOrder` rather than naming them, so the
degenerate `(0,1)` branch, the countable exceptional set of radii, the
analyticity clause and the sign of the order all sit on the lock rather than
behind it. `scripts/check_statement_freeze.py` registers this surface as one of
the three it locks.

**Source, and why it is not proved here for print's domain.** Print asserts the
equivalence and cites `[lau2023]`. The candidate does not hide the same gap: its
Definition 2.1 also takes the volume form as primitive, and its Lemma 6.1 proves
the bridge — but clause (ii) supplies meromorphic continuation only for `C^∞`
compactly supported weights. For a **sharp ball**, which is print's literal
domain, it proves only a two-sided bound on the real axis, and draws its
conclusion about the pole order only "whenever this function does continue
meromorphically". So for a sharp ball the equivalence is proved neither by the candidate nor here: not
the atlas, not the candidate, and print asserts rather than argues it.

`ZetaPair.lean` states the candidate's actual sharp-ball result separately, as
`HasZetaRealAxisOrder`, so the three propositions can be told apart:

| | |
|---|---|
| `HasExactLocalPair` | the volume form; what the atlas proves |
| `HasZetaRealAxisOrder` | the real-axis two-sided bound; what the candidate proves for a sharp ball |
| `HasZetaPoleOrder` | print's primary definition; neither the candidate nor the atlas proves this for a sharp ball |

`HasZetaRealAxisOrder` is the real-axis shadow of a pole, not a pole: a function
can satisfy it and admit no meromorphic continuation at all. The atlas proves it
nowhere either — it is stated so that the shape of the gap is visible rather
than described.

**Match grade.** *One direction of print's "Equivalently", narrowed to the germs
that consume it.* Two narrowings, of different standing.

*Direction.* Print asserts an equivalence; the atlas assumes only volume ⟹ zeta,
which is the direction its results need and the weaker, safer thing for a
hypothesis to be.

*Germ class.* Print quantifies over every nonnegative real-analytic `K`, in every
dimension, at every point. The atlas quantifies over the O70 germs only. This
narrowing is not a convenience: the wider form *without* analyticity is false, as
above, and the wider form *with* analyticity is a general theory nothing in the
atlas consumes. Every
declaration below is at these germs, and they satisfy print's hypothesis rather
than dodging it. For a hypothesis, narrower is the safe direction — the atlas now
assumes strictly less than print asserts — but it also means this manifest says
nothing about the substitution outside that family, and a reader after print's
general equivalence will not find it stated here.

*That the germs are in print's class is now machine-checked, not argued.*
`def:local` takes the local pair of a nonnegative **real-analytic** `K`, and the
narrowing above is defensible only if the O70 germs are in that class. Both
adjectives are now Lean theorems, each unconditional:
`AISafetyAtlas.SingularLearning.rrrLoss_nonneg` for nonnegativity, and
`AISafetyAtlas.Conjectures.MAIS.analyticAt_rrrLossCoords`
([`AISafetyAtlas/Conjectures/MAIS/O70Proof.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70Proof.lean),
via `AISafetyAtlas.SingularLearning.analyticAt_rrrLoss_symm_coords` in
[`AISafetyAtlas/SingularLearning/LossAnalytic.lean`](../../AISafetyAtlas/SingularLearning/LossAnalytic.lean))
for real-analyticity, at every shape, every truth matrix and every point. The second adjective is not
left to the prose argument "those germs are polynomial, hence analytic" —
correct, but invisible to the build, and a missing analyticity hypothesis is
exactly what makes the general form false. It is kernel-checked.

**This does not move the grade, and does not lower the risk below.** It closes a
gap between the manifest's justification for the narrowing and what the atlas
actually proves; it says nothing about whether the bridge holds at these germs.
Being inside print's germ class is a necessary condition for the narrowed
substitution to be the one print asserts, not evidence that the substitution is
valid. `O70ZetaPoleBridge` is still assumed and still unproved.

**Pinning gap: closed — and closing it answered the sharp-ball question.**
`[lau2023]` is Lau, E., Furman, Z., Wang, G., Murfet, D., and Wei, S., *The
Local Learning Coefficient: A Singularity-Aware Complexity Measure*,
arXiv:2308.12108 (2023), published at AISTATS 2025, PMLR 258:244–252. Both are
pinned by the sha256 digests below and are not redistributed with this
repository.

| file | what it is | sha256 |
|---|---|---|
| `lau-furman-wang-murfet-wei-2025-published-aistats-local-learning-coefficient.pdf` | PMLR 258:244–252, 41 pp. The published version, and the canonical one. | `52471f5b48fb9ee33ec9c948835cd948691057d176d97d72991358322079bae7` |
| `lau-furman-wang-murfet-wei-arxiv-v2-2024-local-learning-coefficient.pdf` | arXiv:2308.12108v2, 30 Sep 2024, 37 pp. The form print cites. | `e3217285aa69d1d1e6968460638f3278b8a595ac579f125a93c70078b4863a62` |

Everything below was read in both. The passage it turns on — Appendix B,
"Well-definedness of the theoretical LLC" — is word for word the same in the two
files, so nothing here depends on which version print meant.

**Does `[lau2023]` prove meromorphic continuation for a sharp-ball cutoff?** Its
domain **is** the sharp ball. It proves nothing about it, and states no theorem.

*The sharp ball is the domain, on both sides of the equivalence.* Definition 1,
the volume side, takes the volume of the set of points of a closed ball about
the point at which the loss exceeds its value there by less than the tolerance,
integrated with no weight at all — the same object `sublevelVolume` denotes.
Appendix B, the zeta side, forms the local zeta function as an integral **over
that same closed ball**, against a prior density normalized on the ball. A bump
compactly supported in the interior appears nowhere in the paper. So the reading
that print's citation reaches only smooth compactly supported weights — the
reading the candidate's own Lemma 6.1(ii) invites — is **wrong** about
`[lau2023]`.

*But there is no theorem and no proof.* Appendix B is unnumbered prose. The only
numbered statements in the paper are Definition 1 (the volume form), Definition
2 (the estimator), Definition 3 (the zeta form) and Theorem 1, which is a
quotation of Aoyagi's deep-linear-network result. **No theorem or lemma in
`[lau2023]` states the equivalence**, and none proves the continuation.

*Appendix B delegates, in four steps.* (1) It observes that the parameter space
"is cut out by a finite number of inequalities between analytic functions, and
hence so is" the closed ball — that is, the ball is an admissible parameter
space for the framework being invoked. (2) "Assuming relative finite variance of
the local triplet, we can apply the discussion of Section A", whose Definition 3
asserts that the zeta function "can be analytically continued to a meromorphic
function on the complex plane with poles that are all real, negative and
rational", citing **Watanabe (2009), Theorem 6.6**. (3) With the *additional*
assumption that the point is at least as degenerate as any nearby minimiser, it
borrows Watanabe (2009, §3) for the local free-energy expansion. (4) "The
presentation of the LLC in terms of volume scaling given in the main text now
follows from (Watanabe, 2009, Theorem 7.1)."

*So the load moves one citation further out, to a book nobody here has opened.*
Watanabe, *Algebraic Geometry and Statistical Learning Theory*, Cambridge
Monographs on Applied and Computational Mathematics 25, Cambridge University
Press, 2009 — Theorem 6.6 for the continuation, Theorem 7.1 for the volume
scaling. That book is **not** pinned, and this file has **not** verified Theorem
6.6's hypotheses, nor that a closed ball satisfies them. Section A of
`[lau2023]` does record the framework it is invoking — a compact parameter space
defined by a finite set of real-analytic inequalities, and a prior density that
is a product of a positive smooth function with a nonnegative real-analytic one
— and a closed ball with unit weight has that shape. But "has the shape Lau et
al. describe" is not "is covered by Watanabe's theorem", and this file does not
claim the second.

*Corroboration that the sharp ball is not out of scope.* Lin's companion
preprint, pinned under `O70-EXACT-LOCAL` above, says the same thing in its own
numbering and sketches a proof that handles the boundary explicitly. Its
Corollary 2.6 asserts analytic continuation to the whole plane of the zeta
function of a real analytic function that vanishes somewhere on a **compact
semianalytic** set, against a *nearly analytic* weight — where semianalytic
means cut out by finitely many non-strict real-analytic inequalities and nearly
analytic means a product of a real-analytic function with a positive smooth one.
A closed Euclidean ball with the constant weight 1 is an instance of both; the
preprint even names the threshold taken against the constant unit function. Its
Lemma 2.4 is where the boundary inequalities are resolved alongside the germ,
which is precisely the step a smooth-cutoff argument never has to take. This is
a second, independently pinned source whose *stated* scope covers the sharp
ball.

*What this changes here, and what it does not.* It closes the pinning gap, and
it corrects a reading. It does nothing else, and four things stand between it
and `O70ZetaPoleBridge`:

* *The direction is still the other one.* `[lau2023]` runs zeta ⟹ volume: the
  pole defines the coefficient and the volume law is the consequence.
  `O70ZetaPoleBridge` assumes volume ⟹ zeta. Even at face value, the implication
  the atlas assumes is not the one Appendix B argues.
* *It carries hypotheses this frontier does not.* Relative finite variance and
  essential uniqueness for the local triplet, a prior positive at the point, and
  the point being at least as degenerate as any nearby minimiser.
  `O70ZetaPoleBridge` carries none of them — and for a hypothesis, carrying
  fewer is the **unsafe** direction: it is assumed at instances the source's own
  argument does not reach.
* *It says nothing about the analyticity clause.* `HasZetaPoleOrder` asks that
  the continuation be analytic everywhere to the right of the threshold and have
  `meromorphicOrderAt` equal to the negated multiplicity there. `[lau2023]`
  speaks only of "the largest pole" and its multiplicity, and states no
  threshold clause at all.
* *Greenblatt does not reach the sharp ball.* Thm 1.4 of arXiv:0709.2496, the
  meromorphy half of the route pinned under `O70-EXACT-LOCAL`, is stated for the
  integral of a power of the germ against a **smooth** φ supported in a fixed
  neighbourhood, over a region with the germ point on its boundary. On this
  question the two routes genuinely differ, and it is Greenblatt — not
  `[lau2023]`, and not Lin — that is confined to smooth compactly supported
  weights.

**No grade moves.** The match grade above, the risk below and the V7 finding
after it are unchanged. Pinning a source is not proving a proposition: nothing
here proves `O70ZetaPoleBridge` at the O70 germs or anywhere else, nothing here
inhabits it, and `CONJ-026` is still `OPEN`.

**Risk: high.** The other two, if false, break a derivation. This one, if false,
means every O70 result in the atlas is a true statement about a quantity that is
not the one `def:local` names — the whole chain would be sound and about the
wrong object. Against that: it is the direction print itself calls an
equivalence, the germs it is now asserted at satisfy print's own analyticity
hypothesis rather than sidestepping it, and the candidate proves the bridge for
a neighbouring weight class. What there is no route to, at present, is a proof
even at these germs, let alone for print's stated domain.

Narrowing away a *known-false* region lowers no risk: it produces no evidence
that what remains holds. It is also the caution this whole file rests on — a
frontier can be stated, locked and written up while false, with the defect in a
quantifier rather than in a proof, so that no build fails on it.

**Consumers.** One declaration takes it as a hypothesis. The count and the line
number below were measured from the sources.

| declaration | file |
|---|---|
| `hasZetaPoleOrder_o70Pair` | `Conjectures/MAIS/O70Proof.lean:590` |

`o70ZetaPoleBridge_iff` mentions it but is the frozen surface, not a consumer,
and the `O70ZetaPoleBridge` definition itself is not one either.

That row is not in the P1/P2/P3 chain, and nothing in that chain consumes this
frontier: it is the one place the atlas says anything at all in print's
*primary* normalization — it restates P2's table as a zeta pair and so carries
three binders where the rest of the chain carries two. Those three binders are
all three frontiers — `O70ZetaPoleBridge`, `EigenvalueLawStatement` and
`O70ExactLocalPairsExist` — so this same declaration appears in the consumer
tables of the two sections above as well.

One `example` takes the hypothesis, in
`Examples/Conjectures/MAIS/O70Proof.lean`; it is that theorem's semantic
instance at `M = N = H = 2`. As above, examples are counted separately and are
not in the table. The five examples in `Examples/SingularLearning/ZetaPair.lean`
take neither this frontier nor any other — they pin the reading of the
definitions: the `x = 0` value of the zeta integral, the two halves of the zero
germ, the sign of `meromorphicOrderAt` at `m = 2`, and the `ε → 0` half of the
counterexample.

**V7 stress evidence: the false region is out of scope, the conclusion is
inhabited on a model outside the frontier, and the proposition is not proved.**

There is no probe here, and no inhabitant of the frontier. What there is, is a
negative result, a shape, an external conclusion witness, and a germ-class check.

The negative result is the counterexample. It is not evidence *for* the
frontier; it is evidence about it, and it is the reason the frontier is
quantified the way it is. Its `ε → 0` half — the logarithmic correction being
invisible to the limit `HasExactLocalPair` takes, so the germ keeps the pair
`(lam, 1)` — is machine-checked in `Examples/SingularLearning/ZetaPair.lean`.
The other half, that the corresponding zeta function has a branch point at
`-lam` rather than a pole, is prose in `ZetaPair.lean` and is not formalized;
that asymmetry is why the counterexample is recorded as a finding and not as a
Lean refutation.

The shape is that the branch on which any such bridge is *false* is unreachable
at every instance this one quantifies over, and that this is established without
either of the other two frontiers.
`not_eventually_rrrLossCoords_eq_zero_of_pos` holds at every positive shape and
every `(C, A, B)` with no factorization hypothesis, and is unconditional
outright; `rrrLoss_nonneg` is unconditional too. In a general form these
would be side conditions the consumer had to discharge; here they follow from
the frontier's own quantifiers, so `hasZetaPoleOrder_o70Pair`
discharges nothing and there is no side condition left for a reader to check at
the call site. The same theorem that closes off `O70-EXACT-LOCAL`'s cheap branch
does this second job here.

The external conclusion witness is new, and it answers a narrower question that
was open: **is `HasZetaPoleOrder` reachable at all?** It is.
`AISafetyAtlas.SingularLearning.hasZetaPoleOrder_sqGerm`
([`AISafetyAtlas/SingularLearning/ZetaMonomial.lean`](../../AISafetyAtlas/SingularLearning/ZetaMonomial.lean))
proves `HasZetaPoleOrder` of the germ `K(x) = x₀²` on `EuclideanSpace ℝ (Fin 1)`
at the origin with pair `(1/2, 1)`, **with no hypothesis of any kind**. The zeta
function is computed exactly rather than estimated: `zetaIntegral_sqGerm` gives
`∫_{|t| < 1} |t|^{2x} dt = 2/(2x + 1)` on the unit ball for real `x > −1/2`, and
`zetaSq` is its continuation, analytic at every `z` with `−1/2 < z.re`,
meromorphic at `−1/2` with `meromorphicOrderAt zetaSq (−1/2) = −1` — so all three
clauses of `HasZetaPoleOrder`, the analyticity clause included, are discharged and
not just the pole. `AISafetyAtlas.Examples.SingularLearning.hasExactLocalPair_sq`
([`AISafetyAtlas/Examples/SingularLearning/LocalPair.lean`](../../AISafetyAtlas/Examples/SingularLearning/LocalPair.lean))
had already given the *same* germ the ball-volume pair `(1/2, 1)`, also
unconditionally. The two normalizations therefore demonstrably agree at a germ
the atlas can check, and the pairing is exhibited as an example in
[`AISafetyAtlas/Examples/SingularLearning/ZetaMonomial.lean`](../../AISafetyAtlas/Examples/SingularLearning/ZetaMonomial.lean).
Both theorems are kernel-checked at `{propext, Classical.choice, Quot.sound}`.

**What that is not.** `x₀²` is **not** a reduced-rank loss, so this is not an
instance of `O70ZetaPoleBridge`, is not a special case of it, and proves no part
of it. The frontier quantifies over `rrrLossCoords` at positive shapes; this germ
is outside that family, and nothing here narrows the gap between the atlas and the
proposition. What it establishes is strictly the vacuity point: the frontier's
conclusion is reachable, and is consistent with its hypothesis, somewhere the
atlas can verify. Before it, nothing in the atlas exhibited a single inhabitant of
`HasZetaPoleOrder` at any germ, so a reader could not tell a frontier that is
merely unproved from one whose conclusion nothing satisfies — and the general form fails at
exactly that: it asserts a conclusion its hypothesis admits germs that cannot
reach. That question is closed here. No other is.

The germ-class check is `analyticAt_rrrLossCoords`, recorded under the match grade
above: the germs the narrowed frontier is asserted at are now kernel-checked to
satisfy print's own nonnegative-real-analytic hypothesis, where before this was
prose. Like the external conclusion witness it is about the *setting* of the frontier
rather than its truth.

Limitations. All four of those are facts about *where* the bridge is asserted and
about what its conclusion can mean, not about whether it holds. The atlas holds no
inhabitant of `O70ZetaPoleBridge`, and none of `HasZetaRealAxisOrder` at any germ.
The one inhabitant of `HasZetaPoleOrder` it now has is at a germ outside the
frontier's family, and there is still no inhabitant of `HasZetaPoleOrder` at an
O70 germ — singular or regular. The candidate's proof covers a different weight
class than print's sharp ball, and `[lau2023]`, now pinned, yielded a correction
to a reading rather than a proof of anything — see the pinning note above. There
is no numerical probe, and unlike the eigenvalue law there is nothing here that
could have falsified the proposition and did not — what there is instead is a
*wider* proposition that is false. **Nothing here inhabits the proposition.**

**The fidelity rider.** The fidelity adjudication carried a rider requiring that
this substitution be stated in Lean and machine-visible rather than left as
prose. It is stated, and narrowly, for the reason above. What stands is
`O70ZetaPoleBridge`: a Lean constant with a frozen surface, quantified at the
germs it is used on, with `HasZetaPoleOrder` and `HasZetaRealAxisOrder` naming
print's definition and the candidate's sharp-ball result separately, and every
declaration standing on the substitution carrying it as a visible binder.
Stating it is not proving it, and stating it twice is not proving it either. The
rider is closed; the proposition is not discharged, and nothing above should be
read as evidence that it holds.

---

## Gate BExact is closed

The three clauses MAIS-O70 prints are now all inhabited in Lean, each under
`O70-EIGEN-LAW` and `O70-EXACT-LOCAL` and nothing else — in the volume
normalization throughout; `O70-ZETA-BRIDGE` is what carries P2 into print's
primary one, and no clause of the gate consumes it.
P1 is `o70DependsOnRanksOnly_of_frontiers`,
P2 is `isO70RankTable_o70Pair`, and P3 — the clause that was missing — is
`isO70MinimizerCharacterization_o70Minimizers`
(`Conjectures/MAIS/O70Proof.lean:533`), which inhabits
`IsO70MinimizerCharacterization o70Minimizers`
(`Conjectures/MAIS/O70.lean:786`). The three conjoined under the two frontiers,
and a semantic consequence of P3 at `M = N = H = 2`, are exhibited at the end of
`Examples/Conjectures/MAIS/O70Proof.lean`. The P3 theorem is kernel-checked at
`{propext, Classical.choice, Quot.sound}`.

What P3 says, and why it needed the exact-pair frontier: `IsO70MinimizerCharacterization`
quantifies over actual matrices and the actual exact local pair `(lam, m)` of a
factorization `B * A = C`, and asks that the stratum `⟨M, N, H, C.rank, A.rank,
B.rank⟩` lie in the given set exactly when `lam ≤ lam'` for every other point of
the zero fiber of the same `C` that has an exact pair. No table and no number
occurs in it. `IsO70AWValueStratumTable o70Pair o70Minimizers` — the table-level
version — holds by definitional unfolding and so carries no content. The proof on
file consumes both `EigenvalueLawStatement` and `O70ExactLocalPairsExist`, which
is why both appear in its binder list; that no route with less could inhabit it
is not claimed, and has no witness either way. The frontier is used in the `←`
direction, to produce an actual point of the fiber at the attaining stratum, and
it is assumed at full strength while this proof calls it once.

Two limits of the germ-level predicate are recorded in its own docstring and
repeated here, because the word "characterisation" would otherwise be read for
more than it carries. It does **not** pin the set: it probes `S` only at strata
realized by an actual factorization with positive dimensions, so `o70Minimizers`
with an inadmissible stratum adjoined satisfies it too — pinning every
`s : O70RankStratum` is `IsO70AWValueStratumTable`'s job, and the two predicates
are complementary rather than alternatives. And `HasExactLocalPair` occurs in it
in hypothesis position only, so were exact pairs to exist nowhere every `S` would
satisfy it vacuously. That is why the anti-vacuity witness matters: under the two
hypotheses `Set.univ` does *not* satisfy it, proved at the end of
`Examples/Conjectures/MAIS/O70Proof.lean`. Without that witness the P3 theorem
would be conditional on a proposition that, if false, makes its own conclusion
empty.

**Closing the gate discharged nothing.** Both hypotheses are still assumed, both
match grades and both risk levels above are unchanged, and both remain results
the candidate paper cites rather than proves. `CONJ-026` is `OPEN`. What is now
true is only that the atlas has no remaining O70 clause that is unstated or
unproved *given* the two citations: in the volume normalization, the gap between
the atlas and the printed theorem is exactly those two propositions and nothing
else. The normalization itself is the third gap, `O70-ZETA-BRIDGE`, and it is
not a citation of the candidate's but print's own "Equivalently".

---

## What is unconditional

For contrast, and so the conditional results are not read as covering more than
they do, these carry neither hypothesis:

* `o70_fiber_minimum_correct` — `awLambda` is a lower bound for the candidate
  table on every admissible rank stratum, and is attained.
* `o70_aw_value_strata_correct` — the minimiser-set characterisation *against
  the table*. The characterisation against the germs, which is print's own
  clause, is `isO70MinimizerCharacterization_o70Minimizers`, and it is
  conditional on both frontiers.
* `awLambda_le_of_factorization`, `awLambda_le_on_fiber` — the same bound
  carried to actual matrices.
* `isEliminationChart_of_feasible` — Theorem 5.1 at every feasible stratum.
* `not_eventually_rrrLossCoords_eq_zero_of_pos` — the O70 germs vanish on no
  neighbourhood of any point, at every positive shape and every `(C, A, B)`,
  with no factorization hypothesis. It does two jobs above and carries no
  frontier for either: it closes off `O70-EXACT-LOCAL`'s cheap branch, and it is
  why `O70-ZETA-BRIDGE` needs no nondegeneracy side condition — the branch on
  which that bridge would be false rather than unproved is unreachable at every
  instance it quantifies over.
* `analyticAt_rrrLossCoords` — the O70 germ is real-analytic at every point, at
  every shape and every truth matrix, with no hypothesis; via
  `analyticAt_rrrLoss_symm_coords`. With `rrrLoss_nonneg` it discharges both
  adjectives `MAIS-A6.tex` `def:local` requires of `K`, so the narrowing of
  `O70-ZETA-BRIDGE` to these germs is machine-checked to land inside print's own
  germ class. It is not evidence that the bridge holds.
* `hasZetaPoleOrder_sqGerm` — the germ `x₀²` on `EuclideanSpace ℝ (Fin 1)` has
  zeta threshold `1/2` and pole order `1`, with no hypothesis; its zeta integral
  is `2/(2x + 1)` on the unit ball by `zetaIntegral_sqGerm`. Paired with
  `hasExactLocalPair_sq`, which gives that same germ the ball-volume pair
  `(1/2, 1)`, it is the atlas's only place where print's zeta normalization and
  the volume normalization are both computed and agree. `x₀²` is not a
  reduced-rank loss, so this is not an instance of `O70-ZETA-BRIDGE` and proves
  no part of it; it settles only that the frontier's conclusion is reachable.
* the whole localization and Tauberian chain: `LayerCake`, `DyadicLocalization`,
  `TauberianLog`, `Tauberian`.

These are claims about the *candidate table* and about the analytic machinery,
never about the model's actual local learning coefficients.
