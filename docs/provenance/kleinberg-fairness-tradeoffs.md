# BY-010: how Kleinberg–Mullainathan–Raghavan's theorems became Lean statements

**Status.** First formalization of the row, 2026-08-31, the exact
characterization (Theorem 1.1). Extended 2026-09-04 with the approximate
characterization (Theorem 1.2) and §3's argument for it.

## The source

J. Kleinberg, S. Mullainathan, M. Raghavan, *Inherent Trade-Offs in the Fair
Determination of Risk Scores*, arXiv:1609.05807.

Read at **v2, 17 Nov 2016** — the version the survey cites and the one this note
pins. The model is §1.1, the theorem is §1.2, and the proof is §2. Page numbers
below are the arXiv v2 PDF's.

This is `survey-ref-034` in `registry.yaml`, one of the two sources `BY-010`
carries.

### The other source states a different causal claim

`BY-010` also cites `survey-ref-035`, K. K. Saravanakumar, *The Impossibility
Theorem of Machine Fairness — A Causal Perspective*, arXiv:2007.06024 (v2,
29 Jan 2021). It is **not a second statement of the Kleinberg–Mullainathan–
Raghavan result and is not graded here.** Its §4 opens by attributing the
statistical impossibility theorem to Kleinberg et al. (2016), then advances a
different claim over demographic parity, equalized odds and predictive parity:
under the report's causal assumptions, a data-generating process satisfying one
cannot satisfy either of the others. Figures 1–3 give the d-separation argument,
and §4.4 describes that argument as a proof, though the result is not isolated as
a numbered theorem.

Formalizing that reading is a different and larger piece of work: it is stated
over d-separation and conditional-independence metrics, which this tree does not
have. The Lean records on this row therefore cite `survey-ref-034` alone as their
content source. See
[`d-separation-build-or-depend.md`](d-separation-build-or-depend.md) for the
standing assessment of that gap.

## What print says

> **Theorem 1.1.** *Consider an instance of the problem in which there is a risk
> assignment satisfying fairness conditions (A), (B), and (C). Then the instance
> must either allow for perfect prediction (with `p_σ` equal to `0` or `1` for
> all `σ`) or have equal base rates.*

The model, §1.1:

| print | Lean |
|---|---|
| feature vector `σ`; `p_σ` the positive-class fraction at `σ` | `Instance.p : F → ℝ` with `0 ≤ p σ ≤ 1` |
| two groups `t`; `a_{tσ}` the frequency of `σ` in group `t`, `n_{tσ} = a_{tσ} N_t` | `Instance.n : Fin 2 → F → ℝ`, nonnegative |
| `N_t`, the size of group `t` | `Instance.N t = ∑ σ, n t σ` |
| `μ_t`, the expected number of group-`t` positives | `Instance.μ t = ∑ σ, n t σ * p σ` |
| bins `b` with scores `v_b` | `RiskAssignment.v : B → ℝ`, in `[0,1]` |
| `X_{σb}`, the fraction of `σ`-people sent to bin `b` | `RiskAssignment.X : F → B → ℝ`, nonnegative, rows summing to `1` |
| base rate of group `t` | `μ t / N t` |

The three conditions:

| print | Lean |
|---|---|
| (A) calibration within groups | `Calibrated`: `assignedPos I R t b = R.v b * assigned I R t b` |
| (B) balance for the negative class | `BalancedNegative`: `negativeScore I R 0 / (N 0 - μ 0) = negativeScore I R 1 / (N 1 - μ 1)` |
| (C) balance for the positive class | `BalancedPositive`: `positiveScore I R 0 / μ 0 = positiveScore I R 1 / μ 1` |

`assigned`, `assignedPos` and `assignedNeg` are print's `n_t^T X`, `n_t^T P X`
and `n_t^T (I - P) X` written as sums rather than as matrix products; the matrix
notation of §2 is presentation, and nothing in the argument uses a matrix
operation the sums do not.

## Where the Lean lives

| declaration | says |
|---|---|
| `AISafetyAtlas.Fairness.perfect_prediction_or_equal_base_rates` | Theorem 1.1 |
| `AISafetyAtlas.Fairness.print_perfectPrediction_of_populated` | print's own sentence, under the restrictive reading below |
| `AISafetyAtlas.Fairness.sum_score_eq_μ` | print's equation (2) |
| `AISafetyAtlas.Fairness.negativeScore_eq` | the score left for the negative class |
| `AISafetyAtlas.Fairness.perfect_of_negativeScore_eq_zero` | the `γ = 1` branch |
| `AISafetyAtlas.Fairness.approx_perfect_prediction_or_equal_base_rates` | Theorem 1.2, at print's explicit `f` |
| `AISafetyAtlas.Fairness.exists_slack_function` | Theorem 1.2 in print's own existential form |
| `AISafetyAtlas.Fairness.slack` | print's `f(ε) = √ε · max(1, 3√ε + 3/4)` |
| `AISafetyAtlas.Fairness.average_lower_bound` | §3's core bound on `γ` when the base rates are far apart |
| `AISafetyAtlas.Fairness.perfect_prediction_or_equal_base_rates_of_approx` | Theorem 1.1 re-derived as the `ε = 0` case |

Theorem 1.1 is in `AISafetyAtlas.Fairness.RiskAssignment`; Theorem 1.2 and the
`ε`-approximate conditions are in
`AISafetyAtlas.Fairness.ApproximateRiskAssignment`. Witnesses in the two mirror
modules under `AISafetyAtlas.Examples.Fairness`.

Reproduction:

```
lake build AISafetyAtlas.Fairness.RiskAssignment AISafetyAtlas.Examples.Fairness.RiskAssignment
lake build AISafetyAtlas.Fairness.ApproximateRiskAssignment AISafetyAtlas.Examples.Fairness.ApproximateRiskAssignment
```

Axioms for every declaration named here are within
`{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`.

## The one quantifier print leaves unwritten, and why it matters

§1.1 gives an instance *"a value `p_σ` for each feature vector, and distributions
`{a_{tσ}}` giving the frequency of the feature vectors in each group"*. It never
says whether a frequency may be zero in **both** groups. The two readings
disagree, and both are settled in the tree.

**Permissive** — the feature vectors are an index set and some may belong to
nobody. Then print's *"for all `σ`"* is **false**. An unpopulated `σ` is weighted
by `n t σ = 0` in every sum appearing in (A), (B) and (C), so no hypothesis
constrains its `p σ`.
`Examples.Fairness.RiskAssignment.not_print_perfectPrediction` exhibits the
instance: three feature vectors, group counts `(1,1,0)` and `(3,1,0)`, bins
scoring `0` and `1`, and `p σ₂ = 1/2` at the vector nobody has. It satisfies (A),
(B) and (C) with `0 < μ_t < N_t` in both groups, has base rates `1/2` and `1/4`,
and falsifies `∀ σ, p σ = 0 ∨ p σ = 1`.

**Restrictive** — every feature vector belongs to somebody. Then print's sentence
holds verbatim: `print_perfectPrediction_of_populated` derives it from the
theorem, and `Examples.Fairness.RiskAssignment.populated_print_perfectPrediction`
inhabits it on the two-vector instance obtained by deleting `σ₂`.

**The statement is made at the permissive reading**, so
`AISafetyAtlas.Fairness.PerfectPrediction` quantifies over the feature vectors
somebody has. That is the narrowing this row's `scope_delta` records, and it is
**forced, not chosen**: at the permissive reading the unrestricted sentence is
refuted in the tree, and at the restrictive one nothing is lost, because the
corollary recovers print's sentence exactly.

Reading this as a defect in the paper would be too strong. The permissive
instance is degenerate — an analyst would not put a feature vector nobody has
into an instance — and §1.1's phrase *"the number of feature vectors in the
instance"* can be read as excluding it. What the formalization establishes is
that the exclusion has to be **written**, because the data §1.1 specifies does
not imply it.

## Hypotheses this statement takes that print does not write

* **`0 < μ t` and `μ t < N t`, for both groups.** Print divides by `μ_t` in
  condition (C) and by `N_t − μ_t` in condition (B), so both classes are nonempty
  in both groups wherever the conditions are stated at all. In Lean these are
  hypotheses of the theorem rather than fields of the structure, because the
  structure is also the carrier of the definitions, and (A) alone needs neither.
* **`∑ b, X σ b = 1`.** Print says the `X_{σb}` *"define a mapping from people
  with feature vectors to bins"* and that people with a fixed `σ` may be
  *"divided among multiple bins"*, which is a distribution over bins. §2 uses it
  twice — at equation (2), where the vector `e` of all ones is applied on the
  right, and again in the `γ = 1` branch — so the requirement is print's, made
  explicit.
* **`v_b ≥ 0`.** Used in the `γ = 1` branch, where the vanishing of a sum of
  nonnegative terms is what forces each bin's contribution to vanish. Print's
  scores are probability estimates, so this is print's too.
* **`v_b ≤ 1` is retained and never used.** Same reason as the growth hypothesis
  in the MAIS-O38 row: print writes it, so dropping it would state something
  strictly stronger than print and change what the row is graded against.

## The proof, and the one step that needed care

§2's argument, unchanged in structure.

1. **Equation (2).** Calibration says `assignedPos t b = v b * assigned t b`, so
   summing the scores over bins gives `∑ b, assigned t b * v b = ∑ b, assignedPos t b`,
   and the right side telescopes to `μ t` because the rows of `X` sum to `1`.
   The total expected score handed to group `t` is exactly `μ t`.
2. **`γ`.** Condition (C) makes `positiveScore t / μ t` common to both groups;
   call it `γ`. So `positiveScore t = γ * μ t`, and by step 1 the negative class
   of group `t` receives `μ t * (1 - γ)`.
3. **Condition (B).** Substituting and clearing the two denominators gives
   `(1 - γ) * (μ 0 * N 1 - μ 1 * N 0) = 0`. The bracket is exactly print's
   `μ_1/(N_1−μ_1) = μ_2/(N_2−μ_2)` cleared, and it is equal base rates.
4. **`γ = 1`.** Print argues in prose: the negative class receives no score, so
   it sits in bins of score `0`; calibration keeps the positive class out of
   those bins; the positive class therefore sits in bins of positive score which
   contain no negative-class member, so calibration forces those scores to `1`;
   and one more application gives `p_σ ∈ {0,1}`.

   **Mechanized as a single pointwise identity instead.** For every group,
   feature vector and bin, `n t σ * p σ * (1 - p σ) * X σ b = 0`. In a bin of
   score `0`, calibration kills `assignedPos t b`, and every term of that sum is
   nonnegative, so `n t σ * p σ * X σ b = 0`; multiply by `1 - p σ`. In a bin of
   positive score, `assignedNeg t b = 0` by step 4's hypothesis, so
   `n t σ * (1 - p σ) * X σ b = 0`; multiply by `p σ`. Summing over bins and
   using the row sums leaves `n t σ * p σ * (1 - p σ) = 0`, which is perfect
   prediction wherever `n t σ ≠ 0`.

   This is the same argument, but it never has to name the sets *"bins of score
   zero"* and *"bins of positive score"*, and it produces the realized-vector
   quantifier directly rather than as an afterthought. It is also where the three
   nonnegativity hypotheses are consumed; nothing else in the proof uses them.

## §3 and Theorem 1.2: two things print gets wrong on the page

Theorem 1.2 relaxes each of (A), (B) and (C) by a multiplicative `ε` and
concludes an `f(ε)`-approximate form of one of the two cases. Print states it
existentially — *"there is a continuous function `f`, with `f(x)` going to `0` as
`x` goes to `0`"* — and then constructs one at the end of §3. The Lean carries
both: `slack` is print's construction, `approx_perfect_prediction_or_equal_base_rates`
is the theorem at that explicit witness, and `exists_slack_function` is print's
sentence as printed. The explicit form is the stronger one and is what everything
else uses.

The `ε`-approximate conditions, `WithinFactor ε x y` being `(1-ε)y ≤ x ≤ (1+ε)y`:

| print | here |
|---|---|
| (A′) | `WithinFactor ε (v b * assigned t b) (assignedPos t b)`, every `t` and `b` |
| (B′) | `WithinFactor ε (ν t) (ν u)`, both ordered pairs |
| (C′) | `WithinFactor ε (γ t) (γ u)`, both ordered pairs |
| `δ`-approximate perfect prediction | `1 - δ ≤ γ t`, both `t` |
| `δ`-approximately equal base rates | `|ρ 0 - ρ 1| ≤ δ` |

The two ordered pairs in (B′) and (C′) are print's *"we also require that these
hold when `μ₁` and `μ₂` are interchanged"*. That each primed condition is a
genuine relaxation of its unprimed one is checked in-tree at `ε = 0`:
`approxCalibrated_zero_iff`, `approxBalancedPositive_zero_iff` and
`approxBalancedNegative_zero_iff` are `iff`s, not implications.

### (A′) as printed is not a relaxation of anything

§3 prints

> `(1 − ε)[nᵀ_t XV]_b ≤ [nᵀ_t P X]_b ≤ (1 − ε)[nᵀ_t XV]_b`

with the **same** factor `(1 − ε)` on both sides. Read literally that forces
`[nᵀ_t P X]_b = (1 − ε)[nᵀ_t XV]_b`, an equality, and at `ε = 0` it is exactly
condition (A) — so Theorem 1.2 would be a restatement of Theorem 1.1 with extra
notation. That is plainly not what is meant.

The derivation immediately after, which produces print's (7)
`(1 − ε)μ_t ≤ μ̂_t ≤ (1 + ε)μ_t`, settles what was meant. It bounds
`μ̂_t = ∑_b [nᵀ_t XV]_b` above by `(1 + ε)μ_t` and below by `(1 − ε)μ_t`, where
`μ_t = ∑_b [nᵀ_t P X]_b`. So the approximated quantity is the score side, the
reference is the positive-class side, and the right-hand factor is `(1 + ε)`.
`ApproxCalibrated` is that use. Note this is **both** a sign repair and a
transposition of the display's two sides.

That derivation is not itself clean — its third line prints
`nᵀ_t XVe = ∑_b [nᵀ_t P X]_b`, which holds only under *exact* calibration and
should read `∑_b [nᵀ_t XV]_b`. So the reading adopted here is the one that makes
the six-line chain valid, not one copied off a correct line. A reviewer who
disagrees should say so: it changes the grade, and possibly the theorem.

This is the reason the Theorem 1.2 records are graded `RELATED` and not a
statement match: the Lean states a condition print's display does not state, on
the evidence of print's own proof.

### §3 divides by a quantity whose sign it never fixes

After (10), print writes

> `ρ₂/(1 − ρ₂) ≤ [(1 + ε − γ₁)/(1 − 2ε + ε² − γ₁)] · ρ₁/(1 − ρ₁)`

which requires `1 − 2ε + ε² − γ₁ > 0`. Nothing earlier in §3 excludes
`γ₁ ≥ (1 − ε)²`. The gap is harmless — that case has `γ₁ ≥ 1 − 2ε`, which is
already at least as strong as the bound the division is being used to reach — but
it has to be taken, and `core_bound` takes it as an explicit first branch. A
reader checking §3 against the Lean will find one case there that is not on the
page.

### Where the Lean is stronger than print

* Print says *"for all `ε > 0`"*; the Lean proves it for `ε ≥ 0`. At `ε = 0` the
  argument still closes, because the strictness of the base-rate gap survives the
  substitution `ρ_u ↦ ρ_t + √ε`. This is what lets
  `perfect_prediction_or_equal_base_rates_of_approx` re-derive Theorem 1.1
  through §3's argument rather than §2's — an independent check that the primed
  conditions and the approximate conclusions are the right relaxations.
* Print asks only that `f` be continuous with `f(x) → 0`; `slack` is exhibited,
  and `continuous_slack` and `tendsto_slack_zero` are proved of it.
* Print's algebra discards an `ε²` term and a `3ε^{3/2}ρ₁` term as it goes. The
  Lean keeps them: `core_bound`'s `hident` is an exact ring identity, and the two
  discarded terms appear as the named nonnegative quantities `hdrop₁` and
  `hdrop₂`. Print's final bound is recovered, not approximated.

### The two approximate conclusions are not the exact ones weakened

Print's `δ`-approximate perfect prediction is a statement about the risk
assignment — *"in each group, the average of the expected scores assigned to
members of the positive class is at least `1 − δ`"* — where its exact perfect
prediction is a statement about the instance, that every `p σ` is `0` or `1`.
They are different predicates over different data, and `ApproxPerfectPrediction`
accordingly takes the risk assignment as an argument where `PerfectPrediction`
does not.

One implication holds: `perfectPrediction_of_approx_zero` shows that at `δ = 0`,
under exact calibration, the approximate form gives print's exact one. **The
converse is false**, and `Examples.…ApproximateRiskAssignment.mixedBins` is the
counterexample — two feature vectors that settle every person's class, so
`PerfectPrediction` holds, collected into a single bin whose score calibration
forces to `1/2`, so `γ = 1/2` and no `δ < 1/2` approximate form holds. Anyone
reading the first disjunct of Theorem 1.2 as *"the instance nearly allows perfect
prediction"* should read that witness first.

`ApproxEqualBaseRates` has no such gap: at `δ = 0` it is `EqualBaseRates`, and
`approxEqualBaseRates_zero_iff` is an `iff`.

### Non-vacuity

A conditional is valid when nothing satisfies its hypotheses, and the
`ε`-approximate hypotheses are the ones that need inhabiting at a **positive**
`ε` — an exactly calibrated instance satisfies them for trivial reasons.
`nearMiss` is the witness that does not: one bin scoring `5/18` over two groups
with base rates `1/4` and `5/16`, meeting (A′), (B′) and (C′) at `ε = 1/9` while
`nearMiss_not_calibrated` shows (A) fails outright, so Theorem 1.1 says nothing
about it. It lands on the second disjunct, and
`nearMiss_not_approxPerfectPrediction` shows it lands there rather than
satisfying both.

## What is not mechanized

* **§1.2's converse observations.** Print notes that the two escape cases *are*
  achievable — a perfect-prediction instance and an equal-base-rate instance each
  admit an assignment meeting all three conditions. The two witnesses in
  `Examples/` exhibit exactly that, but as non-vacuity evidence for this theorem,
  not as a graded statement of print's remark.
* **The `> 2` group case.** Print says extending the definitions past two groups
  is straightforward; the Lean fixes `Fin 2`, as print's own statement does.
* **Everything after §2.** The statistical-parity discussion, the special cases
  of the model, and the algorithmic section are outside this row.

## What a later reader should re-check

1. That `Calibrated` is print's (A) and not the weaker *"calibrated in
   aggregate"* condition. Print quantifies over groups **and** bins; so does the
   Lean.
2. That the permissive/restrictive split above is still the only place the Lean
   and print differ. Any further hypothesis added to `Instance` or
   `RiskAssignment` is a schema event and re-grades the row.
3. That `v_le_one` is still unused **in the Theorem 1.1 proof**. It is used in
   the approximate layer, by `positiveScore_le_μ` and so by
   `perfectPrediction_of_approx_zero`. If a later proof in
   `Fairness/RiskAssignment.lean` starts using it, this note is wrong about which
   of print's hypotheses are load-bearing there.
4. That `ApproxCalibrated` still matches §3's *use* of (A′) rather than its
   printed display. If a future reader concludes the display is right and the
   proof is wrong, the Theorem 1.2 records need re-grading, not repair.
