# BY-010: how Kleinberg–Mullainathan–Raghavan's Theorem 1.1 became a Lean statement

**Status.** First formalization of the row, 2026-08-31. The exact
characterization only; the approximate one (Theorem 1.2) is not attempted and is
recorded below as a residual.

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

Witnesses in `AISafetyAtlas.Examples.Fairness.RiskAssignment`.

Reproduction:

```
lake build AISafetyAtlas.Fairness.RiskAssignment AISafetyAtlas.Examples.Fairness.RiskAssignment
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

## What is not mechanized

* **Theorem 1.2, the approximate characterization.** Print relaxes each of (A),
  (B) and (C) to an `ε`-approximate form and concludes an `f(ε)`-approximate form
  of perfect prediction or of equal base rates, for some continuous `f` with
  `f(x) → 0` as `x → 0`. Nothing here speaks to it, and the row claims nothing
  about it. This is the larger half of the paper's technical content and is the
  natural next target on this row.
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
3. That `v_le_one` is still unused. If a later proof starts using it, this note
   is wrong about which of print's hypotheses are load-bearing.
