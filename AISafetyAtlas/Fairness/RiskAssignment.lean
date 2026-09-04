module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Inherent trade-offs in the fair determination of risk scores

J. Kleinberg, S. Mullainathan and M. Raghavan, *Inherent Trade-Offs in the Fair
Determination of Risk Scores*, arXiv:1609.05807v2 (17 Nov 2016) — the source
cited by `BY-010` as `survey-ref-034`. This module carries **Theorem 1.1**, the
exact characterization, proved from §2's own argument.

## Primary surface

| declaration | says |
|---|---|
| `perfect_prediction_or_equal_base_rates` | Theorem 1.1: (A), (B) and (C) together force perfect prediction or equal base rates |
| `print_perfectPrediction_of_populated` | print's own sentence, once every feature vector is somebody's |
| `sum_score_eq_μ` | print's equation (2): calibration hands group `t` a total expected score of exactly `μ t` |
| `negativeScore_eq` | what condition (C) leaves for the negative class, `μ t * (1 - γ)` |
| `perfect_of_negativeScore_eq_zero` | the `γ = 1` branch: a negative class scoring zero forces `p σ ∈ {0, 1}` |

`Instance` and `RiskAssignment` are the two carriers; `Calibrated`,
`BalancedNegative` and `BalancedPositive` are print's (A), (B) and (C).
Non-vacuity witnesses live in `AISafetyAtlas.Examples.Fairness.RiskAssignment`.

## What print says

> **Theorem 1.1.** *Consider an instance of the problem in which there is a risk
> assignment satisfying fairness conditions (A), (B), and (C). Then the instance
> must either allow for perfect prediction (with `p_σ` equal to `0` or `1` for
> all `σ`) or have equal base rates.*

The model is §1.1. People carry a **feature vector** `σ`; `p σ` is the fraction
of people with that feature vector who belong to the positive class; each person
is in one of two **groups**, and `n t σ` counts the group-`t` people with feature
vector `σ`. A **risk assignment** is a set of bins, a score `v b` for each bin,
and a matrix `X σ b` giving the fraction of people with feature vector `σ` sent
to bin `b`. Derived: `N t = ∑ σ, n t σ` is the size of group `t`, and
`μ t = ∑ σ, n t σ * p σ` is the expected number of its members in the positive
class. The **base rate** of group `t` is `μ t / N t`.

The three conditions, §1.1, rendered as `Calibrated`, `BalancedNegative` and
`BalancedPositive`:

| print | here |
|---|---|
| (A) calibration within groups | `assignedPos I R t b = R.v b * assigned I R t b` |
| (B) balance for the negative class | `negativeScore I R 0 / (N 0 - μ 0) = negativeScore I R 1 / (N 1 - μ 1)` |
| (C) balance for the positive class | `positiveScore I R 0 / μ 0 = positiveScore I R 1 / μ 1` |

## The one quantifier print leaves unwritten

§1.1 fixes a value `p σ` for each feature vector and frequencies `a t σ` giving
how often it occurs in each group, and **never says whether a feature vector may
have frequency zero in both groups.** Both readings are settled here, and they
disagree.

* **Permissive** — the feature vectors are an index set, and some may belong to
  nobody. Then print's *"for all `σ`"* is **false**: an unpopulated `σ` is
  weighted by `n t σ = 0` in every sum of (A), (B) and (C), so nothing constrains
  its `p σ`. `Examples.Fairness.RiskAssignment.not_print_perfectPrediction`
  exhibits an instance meeting every hypothesis with `p σ₂ = 1/2`.
* **Restrictive** — every feature vector belongs to somebody. Then print's
  sentence holds verbatim, and `print_perfectPrediction_of_populated` derives it
  from what is proved here.

`PerfectPrediction` is stated at the permissive reading, quantified over the
feature vectors somebody has, because that is the reading §1.1's data admits and
the only one under which the theorem is true as printed. The restriction is
therefore forced rather than chosen, and the corollary shows nothing is lost
under the other reading. Everything else — the hypotheses, the quantifier order,
the disjunction — is print's, and `v_le_one` is retained though no step uses it
because print's scores are probability estimates.

## What the proof is

§2's argument, unchanged. Calibration makes the total expected score handed to
group `t` equal `μ t` (print's equation (2)), so writing `γ` for the common
value that (C) forces on the two ratios, the score reaching the negative class of
group `t` is `μ t * (1 - γ)`. Condition (B) then equates two such ratios, and
clearing denominators leaves `(1 - γ) * (μ 0 * N 1 - μ 1 * N 0) = 0`: either
`γ = 1`, or the base rates agree. The `γ = 1` branch says the negative class
receives no score at all; since every term is nonnegative it receives none in any
single bin, and calibration turns that into `n t σ * p σ * (1 - p σ) = 0` for
every group and feature vector — perfect prediction wherever anybody stands.

## What is not claimed

- **Theorem 1.2, the approximate version, is not here.** Print relaxes each
  condition to an `ε`-approximate form and concludes an `f(ε)`-approximate form
  of one of the two cases. Nothing in this module speaks to it.
- **No AI-system reading.** The declarations are about a population, a partition
  into two groups, and a matrix. Calling `X` a deployed classifier is an
  application line, not a theorem here.
- **Not a claim that either escape is desirable.** Print's two cases are perfect
  prediction and equal base rates; that they are the only ones is the result, and
  it says nothing about whether an instance should be pushed toward either.
-/

namespace AISafetyAtlas.Fairness

open Finset

variable {F B : Type*}

/-- An **instance** of the risk-assignment problem, §1.1: a value `p σ` for each
feature vector, and a count `n t σ` of the group-`t` people carrying it. Groups
are indexed by `Fin 2`, print's two groups. -/
public structure Instance (F : Type*) [Fintype F] where
  /-- The fraction of people with feature vector `σ` who are in the positive class. -/
  p : F → ℝ
  /-- The number of people in group `t` whose feature vector is `σ`. -/
  n : Fin 2 → F → ℝ
  p_nonneg : ∀ σ, 0 ≤ p σ
  p_le_one : ∀ σ, p σ ≤ 1
  n_nonneg : ∀ t σ, 0 ≤ n t σ

namespace Instance

variable [Fintype F]

/-- `N t` — the number of people in group `t`. -/
@[expose] public def N (I : Instance F) (t : Fin 2) : ℝ := ∑ σ, I.n t σ

/-- `μ t` — the expected number of group-`t` people in the positive class. -/
@[expose] public def μ (I : Instance F) (t : Fin 2) : ℝ := ∑ σ, I.n t σ * I.p σ

end Instance

/-- A **risk assignment**, §1.1: bins with scores `v`, and a rule `X` sending a
fraction `X σ b` of the people with feature vector `σ` to bin `b`. The rule sees
the feature vector and not the group. -/
public structure RiskAssignment (F B : Type*) [Fintype F] [Fintype B] where
  /-- The score attached to bin `b`, used as the probability estimate for everyone in it. -/
  v : B → ℝ
  /-- The fraction of people with feature vector `σ` who are assigned to bin `b`. -/
  X : F → B → ℝ
  v_nonneg : ∀ b, 0 ≤ v b
  v_le_one : ∀ b, v b ≤ 1
  X_nonneg : ∀ σ b, 0 ≤ X σ b
  /-- Everyone is assigned somewhere: the rule is a distribution over bins. -/
  X_sum : ∀ σ, ∑ b, X σ b = 1

variable [Fintype F] [Fintype B]

/-- The expected number of group-`t` people placed in bin `b`. -/
@[expose] public def assigned (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) (b : B) : ℝ :=
  ∑ σ, I.n t σ * R.X σ b

/-- The expected number of group-`t` people **in the positive class** placed in bin `b`. -/
@[expose] public def assignedPos (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) (b : B) : ℝ :=
  ∑ σ, I.n t σ * I.p σ * R.X σ b

/-- The expected number of group-`t` people **in the negative class** placed in bin `b`. -/
@[expose] public def assignedNeg (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) (b : B) : ℝ :=
  ∑ σ, I.n t σ * (1 - I.p σ) * R.X σ b

/-- The total expected score received by the group-`t` people in the positive class. -/
@[expose] public def positiveScore (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) : ℝ :=
  ∑ b, assignedPos I R t b * R.v b

/-- The total expected score received by the group-`t` people in the negative class. -/
@[expose] public def negativeScore (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) : ℝ :=
  ∑ b, assignedNeg I R t b * R.v b

/-- **Condition (A), calibration within groups.** For each group and each bin,
the expected number of that group's positive-class members in the bin is a
`v b` fraction of the expected number of that group's members in the bin. -/
@[expose] public def Calibrated (I : Instance F) (R : RiskAssignment F B) : Prop :=
  ∀ t b, assignedPos I R t b = R.v b * assigned I R t b

/-- **Condition (C), balance for the positive class.** The average expected score
received by a positive-class member is the same in both groups. -/
@[expose] public def BalancedPositive (I : Instance F) (R : RiskAssignment F B) : Prop :=
  positiveScore I R 0 / I.μ 0 = positiveScore I R 1 / I.μ 1

/-- **Condition (B), balance for the negative class.** The average expected score
received by a negative-class member is the same in both groups. -/
@[expose] public def BalancedNegative (I : Instance F) (R : RiskAssignment F B) : Prop :=
  negativeScore I R 0 / (I.N 0 - I.μ 0) = negativeScore I R 1 / (I.N 1 - I.μ 1)

/-- **Perfect prediction**, at the feature vectors somebody actually has. See the
module header for why print's unrestricted *"for all `σ`"* is not what is
proved. -/
@[expose] public def PerfectPrediction (I : Instance F) : Prop :=
  ∀ σ, (∃ t, I.n t σ ≠ 0) → I.p σ = 0 ∨ I.p σ = 1

/-- **Equal base rates**: the two groups hold the same fraction of positive-class
members. -/
@[expose] public def EqualBaseRates (I : Instance F) : Prop :=
  I.μ 0 / I.N 0 = I.μ 1 / I.N 1

/-! ## The identities calibration supplies -/

/-- Everyone in the positive class lands somewhere: summing over bins recovers
`μ t`. This is the left-hand side of print's equation (2). -/
public theorem sum_assignedPos (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) :
    ∑ b, assignedPos I R t b = I.μ t := by
  classical
  simp only [assignedPos, Instance.μ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← Finset.mul_sum, R.X_sum σ, mul_one]

/-- A bin's occupants split into the two classes. -/
public theorem assigned_eq_add (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) (b : B) :
    assigned I R t b = assignedPos I R t b + assignedNeg I R t b := by
  simp only [assigned, assignedPos, assignedNeg, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun σ _ ↦ by ring

/-- **Print's equation (2).** Under calibration the total expected score handed
to group `t` is exactly `μ t`, the expected number of its positive-class
members. -/
public theorem sum_score_eq_μ (I : Instance F) (R : RiskAssignment F B)
    (hA : Calibrated I R) (t : Fin 2) :
    ∑ b, assigned I R t b * R.v b = I.μ t := by
  rw [← sum_assignedPos I R t]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [hA t b]; ring

/-- The score reaching the negative class is what the positive class leaves. -/
public theorem negativeScore_eq (I : Instance F) (R : RiskAssignment F B)
    (hA : Calibrated I R) (t : Fin 2) :
    negativeScore I R t = I.μ t - positiveScore I R t := by
  have h : ∑ b, assigned I R t b * R.v b
      = positiveScore I R t + negativeScore I R t := by
    simp only [positiveScore, negativeScore, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ ↦ by rw [assigned_eq_add I R t b]; ring
  rw [sum_score_eq_μ I R hA t] at h
  linarith

/-! ## The `γ = 1` branch -/

/-- If the negative class of group `t` receives no score at all, then no bin
gives it any. -/
private theorem assignedNeg_mul_v_eq_zero (I : Instance F) (R : RiskAssignment F B)
    {t : Fin 2} (h : negativeScore I R t = 0) (b : B) :
    assignedNeg I R t b * R.v b = 0 := by
  classical
  have hnonneg : ∀ b ∈ (Finset.univ : Finset B), 0 ≤ assignedNeg I R t b * R.v b := by
    intro b _
    refine mul_nonneg (Finset.sum_nonneg fun σ _ ↦ ?_) (R.v_nonneg b)
    exact mul_nonneg (mul_nonneg (I.n_nonneg t σ) (by linarith [I.p_le_one σ]))
      (R.X_nonneg σ b)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 h b (Finset.mem_univ b)

/-- The pointwise consequence: in every bin, every feature vector contributes
`n t σ * p σ * (1 - p σ) * X σ b = 0`. A bin of score zero holds no
positive-class member (by calibration); a bin of positive score holds no
negative-class member (because the negative class receives nothing). -/
private theorem pointwise_zero (I : Instance F) (R : RiskAssignment F B)
    (hA : Calibrated I R) {t : Fin 2} (h : negativeScore I R t = 0) (σ : F) (b : B) :
    I.n t σ * I.p σ * (1 - I.p σ) * R.X σ b = 0 := by
  classical
  rcases eq_or_lt_of_le (R.v_nonneg b) with hv | hv
  · -- `v b = 0`: calibration forces the positive class out of this bin.
    have hpos : assignedPos I R t b = 0 := by rw [hA t b, ← hv]; ring
    have hnn : ∀ σ' ∈ (Finset.univ : Finset F), 0 ≤ I.n t σ' * I.p σ' * R.X σ' b :=
      fun σ' _ ↦ mul_nonneg (mul_nonneg (I.n_nonneg t σ') (I.p_nonneg σ')) (R.X_nonneg σ' b)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hpos σ (Finset.mem_univ σ)
    linear_combination (1 - I.p σ) * this
  · -- `v b > 0`: the negative class is absent from this bin.
    have hneg : assignedNeg I R t b = 0 := by
      have := assignedNeg_mul_v_eq_zero I R h b
      rcases mul_eq_zero.1 this with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hv)
    have hnn : ∀ σ' ∈ (Finset.univ : Finset F), 0 ≤ I.n t σ' * (1 - I.p σ') * R.X σ' b :=
      fun σ' _ ↦ mul_nonneg (mul_nonneg (I.n_nonneg t σ') (by linarith [I.p_le_one σ']))
        (R.X_nonneg σ' b)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hneg σ (Finset.mem_univ σ)
    linear_combination I.p σ * this

/-- A group whose negative class receives no score has `p σ ∈ {0, 1}` at every
feature vector its members carry. -/
public theorem perfect_of_negativeScore_eq_zero (I : Instance F) (R : RiskAssignment F B)
    (hA : Calibrated I R) {t : Fin 2} (h : negativeScore I R t = 0) (σ : F)
    (hσ : I.n t σ ≠ 0) : I.p σ = 0 ∨ I.p σ = 1 := by
  classical
  have hsum : ∑ b, I.n t σ * I.p σ * (1 - I.p σ) * R.X σ b = 0 :=
    Finset.sum_eq_zero fun b _ ↦ pointwise_zero I R hA h σ b
  rw [← Finset.mul_sum, R.X_sum σ, mul_one] at hsum
  have : I.p σ * (1 - I.p σ) = 0 := by
    rcases mul_eq_zero.1 (by linarith [hsum] : I.n t σ * (I.p σ * (1 - I.p σ)) = 0) with h' | h'
    · exact absurd h' hσ
    · exact h'
  rcases mul_eq_zero.1 this with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linarith)

/-! ## Theorem 1.1 -/

/-- **Kleinberg–Mullainathan–Raghavan, Theorem 1.1.** An instance carrying a risk
assignment that is calibrated within groups and balanced for both classes either
allows perfect prediction or has equal base rates.

The four numeric hypotheses are print's own: it divides by `μ t` in condition (C)
and by `N t - μ t` in condition (B), so both classes are nonempty in both groups.
`PerfectPrediction` is restricted to realized feature vectors; see the module
header. -/
public theorem perfect_prediction_or_equal_base_rates
    (I : Instance F) (R : RiskAssignment F B)
    (hμ : ∀ t, 0 < I.μ t) (hμN : ∀ t, I.μ t < I.N t)
    (hA : Calibrated I R) (hB : BalancedNegative I R) (hC : BalancedPositive I R) :
    PerfectPrediction I ∨ EqualBaseRates I := by
  classical
  have hμ0 : I.μ 0 ≠ 0 := ne_of_gt (hμ 0)
  have hμ1 : I.μ 1 ≠ 0 := ne_of_gt (hμ 1)
  -- (C) makes the two ratios equal; call the common value `γ`.
  obtain ⟨γ, hpos0, hpos1⟩ :
      ∃ γ : ℝ, positiveScore I R 0 = γ * I.μ 0 ∧ positiveScore I R 1 = γ * I.μ 1 := by
    refine ⟨positiveScore I R 0 / I.μ 0, by field_simp, ?_⟩
    rw [hC]; field_simp
  have hposg : ∀ t, positiveScore I R t = γ * I.μ t := by
    rw [Fin.forall_fin_two]; exact ⟨hpos0, hpos1⟩
  -- Rewrite (B) with the negative scores computed from calibration.
  have hne0 : I.N 0 - I.μ 0 ≠ 0 := by have := hμN 0; linarith
  have hne1 : I.N 1 - I.μ 1 ≠ 0 := by have := hμN 1; linarith
  have hBval : (I.μ 0 - γ * I.μ 0) * (I.N 1 - I.μ 1)
      = (I.μ 1 - γ * I.μ 1) * (I.N 0 - I.μ 0) := by
    have h0 := negativeScore_eq I R hA 0
    have h1 := negativeScore_eq I R hA 1
    rw [hpos0] at h0
    rw [hpos1] at h1
    rw [BalancedNegative, h0, h1, div_eq_div_iff hne0 hne1] at hB
    linear_combination hB
  -- Clearing the brackets leaves `(1 - γ) * (μ 0 * N 1 - μ 1 * N 0) = 0`.
  have hfac : (1 - γ) * (I.μ 0 * I.N 1 - I.μ 1 * I.N 0) = 0 := by linear_combination hBval
  rcases mul_eq_zero.1 hfac with hone | hbase
  · -- `γ = 1`: the negative class receives no score in either group.
    refine Or.inl fun σ ⟨t, hσ⟩ ↦ ?_
    have hγ1 : γ = 1 := by linarith
    have hz : negativeScore I R t = 0 := by
      rw [negativeScore_eq I R hA t, hposg t, hγ1]; ring
    exact perfect_of_negativeScore_eq_zero I R hA hz σ hσ
  · -- Equal base rates.
    refine Or.inr ?_
    have hN0 : I.N 0 ≠ 0 := by have := hμ 0; have := hμN 0; linarith
    have hN1 : I.N 1 ≠ 0 := by have := hμ 1; have := hμN 1; linarith
    rw [EqualBaseRates, div_eq_div_iff hN0 hN1]
    linarith

/-- **Print's sentence at the restrictive reading.** If every feature vector
belongs to somebody, the conclusion proved above is print's own unrestricted
*"`p_σ` equal to `0` or `1` for all `σ`"*. Nothing is lost by stating
`PerfectPrediction` over realized feature vectors; what the restriction buys is
that the theorem is also true when a feature vector belongs to nobody, which is
the case `Examples.Fairness.RiskAssignment.not_print_perfectPrediction`
refutes. -/
public theorem print_perfectPrediction_of_populated (I : Instance F)
    (hpop : ∀ σ, ∃ t, I.n t σ ≠ 0) (h : PerfectPrediction I) :
    ∀ σ, I.p σ = 0 ∨ I.p σ = 1 :=
  fun σ ↦ h σ (hpop σ)

end AISafetyAtlas.Fairness
