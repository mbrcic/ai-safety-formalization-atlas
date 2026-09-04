module

public import AISafetyAtlas.Fairness.ApproximateRiskAssignment

/-!
# Three instances that inhabit Theorem 1.2, and one that separates its first case

`AISafetyAtlas.Fairness.ApproximateRiskAssignment` proves that a risk assignment
meeting (A′), (B′) and (C′) forces one of two `slack ε`-approximate conclusions.
As with Theorem 1.1, a statement of that shape is valid the moment nothing meets
its hypotheses, so this module exhibits instances that do — and, unlike the exact
module, one of them meets them at a *positive* `ε` while failing the exact
conditions outright.

| witness | `ε` | (A′) (B′) (C′) | realizes | and refutes |
|---|---|---|---|---|
| `nearMiss` | `1/9` | hold; **(A) fails** | `ApproxEqualBaseRates` | `ApproxPerfectPrediction` |
| `separated` | `1/64` | hold, exactly | `ApproxPerfectPrediction` | `ApproxEqualBaseRates` |
| `mixedBins` | `1/64` | hold, exactly | `PerfectPrediction` | `ApproxPerfectPrediction` |

## Why `nearMiss` is the load-bearing one

One bin scoring `5/18`, and two groups whose base rates are `1/4` and `5/16`. A
single bin makes (B′) and (C′) hold exactly — everybody in either class of either
group receives the same score — so the whole content sits in (A′), which asks
that one score be within a factor `1 ± 1/9` of both base rates at once. It is,
and `5/18` is the only score that is: `(1 - 1/9) · 5/16 = 5/18` and
`(1 + 1/9) · 1/4 = 5/18` are the two binding constraints, and they meet.

No score is *exactly* calibrated for both groups, because the base rates differ,
so `nearMiss_not_calibrated` holds and Theorem 1.1 has nothing to say here.
Theorem 1.2 does, and what it says is the second disjunct: `slack (1/9) = 7/12`,
the base rates are `1/16` apart, and the positive classes average `5/18`, which
is below `1 - 7/12 = 5/12`. So the first disjunct is false and the theorem is not
being satisfied by accident.

## Why `mixedBins` is here

Print's `δ`-approximate perfect prediction is a statement about the risk
assignment — the positive class averages at least `1 - δ` — and its exact perfect
prediction is a statement about the instance, that every `p σ` is `0` or `1`.
`perfectPrediction_of_approx_zero` shows the first implies the second at `δ = 0`
under calibration. **The converse fails, and `mixedBins` is why.** Two feature
vectors settle every person's class, so `PerfectPrediction` holds; one bin
collects them all, so calibration forces that bin's score to `1/2` and the
positive class averages `1/2`, not `1`. An instance can therefore allow perfect
prediction while its risk assignment is nowhere near print's first approximate
case.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Fairness.ApproximateRiskAssignment

open AISafetyAtlas.Fairness

/-! ## Two values of `slack` -/

public theorem slack_one_ninth : slack (1 / 9) = 7 / 12 := by
  have h : Real.sqrt (1 / 9) = 1 / 3 := by
    rw [show (1:ℝ) / 9 = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [slack, h, max_eq_right (by norm_num)]
  norm_num

public theorem slack_one_sixtyfourth : slack (1 / 64) = 9 / 64 := by
  have h : Real.sqrt (1 / 64) = 1 / 8 := by
    rw [show (1:ℝ) / 64 = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [slack, h, max_eq_right (by norm_num)]
  norm_num

/-! ## `nearMiss`: approximate but not exact

Feature vector `σ₀` has `p = 1/2` and `σ₁` has `p = 1/8`. Group `0` is `(1, 2)`
and group `1` is `(1, 1)`, giving sizes `3` and `2`, positive-class expectations
`3/4` and `5/8`, and base rates `1/4` and `5/16`. -/

/-- `p σ₀ = 1/2`, `p σ₁ = 1/8`. -/
public noncomputable def nearMissP : Fin 2 → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 8

/-- Group `0` is `(1, 2)`; group `1` is `(1, 1)`. -/
public def nearMissN : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 2
  | 1, 0 => 1 | 1, 1 => 1

@[simp] private theorem nearMissP_zero : nearMissP 0 = 1 / 2 := rfl
@[simp] private theorem nearMissP_one : nearMissP 1 = 1 / 8 := rfl
@[simp] private theorem nearMissN_00 : nearMissN 0 0 = 1 := rfl
@[simp] private theorem nearMissN_01 : nearMissN 0 1 = 2 := rfl
@[simp] private theorem nearMissN_10 : nearMissN 1 0 = 1 := rfl
@[simp] private theorem nearMissN_11 : nearMissN 1 1 = 1 := rfl

/-- The instance: neither feature vector settles anybody's class. -/
public noncomputable def nearMiss : Instance (Fin 2) where
  p := nearMissP
  n := nearMissN
  p_nonneg := by intro σ; fin_cases σ <;> norm_num
  p_le_one := by intro σ; fin_cases σ <;> norm_num
  n_nonneg := by intro t σ; fin_cases t <;> fin_cases σ <;> norm_num

/-- One bin, scoring `5/18` — the only score within a factor `1/9` of both base
rates. -/
public noncomputable def nearMissAssignment : RiskAssignment (Fin 2) (Fin 1) where
  v := fun _ ↦ 5 / 18
  X := fun _ _ ↦ 1
  v_nonneg := by intro b; norm_num
  v_le_one := by intro b; norm_num
  X_nonneg := by intro σ b; norm_num
  X_sum := by intro σ; simp

@[simp] private theorem nearMiss_p : nearMiss.p = nearMissP := rfl
@[simp] private theorem nearMiss_n : nearMiss.n = nearMissN := rfl
@[simp] private theorem nearMissAssignment_v (b : Fin 1) :
    nearMissAssignment.v b = 5 / 18 := rfl
@[simp] private theorem nearMissAssignment_X (σ : Fin 2) (b : Fin 1) :
    nearMissAssignment.X σ b = 1 := rfl

@[simp] private theorem nearMiss_N_zero : nearMiss.N 0 = 3 := by
  simp [Instance.N, Fin.sum_univ_two]; norm_num

@[simp] private theorem nearMiss_N_one : nearMiss.N 1 = 2 := by
  simp [Instance.N, Fin.sum_univ_two]; norm_num

@[simp] private theorem nearMiss_mu_zero : nearMiss.μ 0 = 3 / 4 := by
  simp [Instance.μ, Fin.sum_univ_two]; norm_num

@[simp] private theorem nearMiss_mu_one : nearMiss.μ 1 = 5 / 8 := by
  simp [Instance.μ, Fin.sum_univ_two]; norm_num

public theorem nearMiss_mu_pos (t : Fin 2) : 0 < nearMiss.μ t := by
  fin_cases t <;> norm_num

public theorem nearMiss_mu_lt_N (t : Fin 2) : nearMiss.μ t < nearMiss.N t := by
  fin_cases t <;> norm_num

/-! ### The three approximate conditions, at `ε = 1/9` -/

@[simp] private theorem nearMiss_assigned (t : Fin 2) (b : Fin 1) :
    assigned nearMiss nearMissAssignment t b = nearMiss.N t := by
  simp [assigned, Instance.N]

@[simp] private theorem nearMiss_assignedPos (t : Fin 2) (b : Fin 1) :
    assignedPos nearMiss nearMissAssignment t b = nearMiss.μ t := by
  simp [assignedPos, Instance.μ]

public theorem nearMiss_approxCalibrated :
    ApproxCalibrated (1 / 9) nearMiss nearMissAssignment := by
  intro t b
  fin_cases t <;> fin_cases b <;> exact ⟨by norm_num, by norm_num⟩

@[simp] public theorem nearMiss_positiveAverage (t : Fin 2) :
    positiveAverage nearMiss nearMissAssignment t = 5 / 18 := by
  fin_cases t <;>
    simp [positiveAverage, positiveScore]

@[simp] public theorem nearMiss_negativeAverage (t : Fin 2) :
    negativeAverage nearMiss nearMissAssignment t = 5 / 18 := by
  fin_cases t <;>
    simp [negativeAverage, negativeScore, assignedNeg, Instance.N, Instance.μ,
      Fin.sum_univ_two] <;> norm_num

public theorem nearMiss_approxBalancedPositive :
    ApproxBalancedPositive (1 / 9) nearMiss nearMissAssignment := by
  intro t u _
  rw [nearMiss_positiveAverage, nearMiss_positiveAverage]
  exact ⟨by norm_num, by norm_num⟩

public theorem nearMiss_approxBalancedNegative :
    ApproxBalancedNegative (1 / 9) nearMiss nearMissAssignment := by
  intro t u _
  rw [nearMiss_negativeAverage, nearMiss_negativeAverage]
  exact ⟨by norm_num, by norm_num⟩

/-- **What the exact module cannot reach.** No single score is calibrated for two
groups with different base rates, so Theorem 1.1 does not apply to `nearMiss`
at all. -/
public theorem nearMiss_not_calibrated : ¬ Calibrated nearMiss nearMissAssignment := by
  intro h
  have h0 := h 0 0
  rw [nearMiss_assignedPos, nearMiss_assigned] at h0
  norm_num at h0

/-! ### Which disjunct `nearMiss` lands on -/

@[simp] private theorem nearMiss_baseRate_zero : baseRate nearMiss 0 = 1 / 4 := by
  rw [baseRate, nearMiss_mu_zero, nearMiss_N_zero]; norm_num

@[simp] private theorem nearMiss_baseRate_one : baseRate nearMiss 1 = 5 / 16 := by
  rw [baseRate, nearMiss_mu_one, nearMiss_N_one]; norm_num

/-- The second disjunct is realized: the base rates are `1/16` apart and
`slack (1/9) = 7/12`. -/
public theorem nearMiss_approxEqualBaseRates :
    ApproxEqualBaseRates (slack (1 / 9)) nearMiss := by
  rw [ApproxEqualBaseRates, slack_one_ninth, nearMiss_baseRate_zero,
    nearMiss_baseRate_one, abs_le]
  constructor <;> norm_num

/-- And the first is not: the positive classes average `5/18`, below the
`1 - 7/12 = 5/12` that approximate perfect prediction would need. -/
public theorem nearMiss_not_approxPerfectPrediction :
    ¬ ApproxPerfectPrediction (slack (1 / 9)) nearMiss nearMissAssignment := by
  intro h
  have h0 := h 0
  rw [slack_one_ninth, nearMiss_positiveAverage] at h0
  norm_num at h0

/-- Theorem 1.2 applied to `nearMiss`. -/
public theorem nearMiss_conclusion :
    ApproxPerfectPrediction (slack (1 / 9)) nearMiss nearMissAssignment
      ∨ ApproxEqualBaseRates (slack (1 / 9)) nearMiss :=
  approx_perfect_prediction_or_equal_base_rates nearMiss nearMissAssignment
    (by norm_num) nearMiss_mu_pos nearMiss_mu_lt_N
    nearMiss_approxCalibrated nearMiss_approxBalancedNegative
    nearMiss_approxBalancedPositive

/-! ## `separated`: the other disjunct

Two feature vectors, one certainly positive and one certainly negative, sorted
into a unit bin and a zero bin. Group `0` is `(1, 1)` and group `1` is `(1, 3)`,
so the base rates are `1/2` and `1/4` — further apart than
`slack (1/64) = 9/64`. -/

/-- `p σ₀ = 1`, `p σ₁ = 0`. -/
public def sepP : Fin 2 → ℝ
  | 0 => 1
  | 1 => 0

/-- Group `0` is `(1, 1)`; group `1` is `(1, 3)`. -/
public def sepN : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 1
  | 1, 0 => 1 | 1, 1 => 3

/-- Bin `0` scores `1`, bin `1` scores `0`. -/
public def sepV : Fin 2 → ℝ
  | 0 => 1
  | 1 => 0

/-- The certainly-positive vector goes to the unit bin, the certainly-negative
one to the zero bin. -/
public def sepX : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 0
  | 1, 0 => 0 | 1, 1 => 1

@[simp] private theorem sepP_zero : sepP 0 = 1 := rfl
@[simp] private theorem sepP_one : sepP 1 = 0 := rfl
@[simp] private theorem sepN_00 : sepN 0 0 = 1 := rfl
@[simp] private theorem sepN_01 : sepN 0 1 = 1 := rfl
@[simp] private theorem sepN_10 : sepN 1 0 = 1 := rfl
@[simp] private theorem sepN_11 : sepN 1 1 = 3 := rfl
@[simp] private theorem sepV_zero : sepV 0 = 1 := rfl
@[simp] private theorem sepV_one : sepV 1 = 0 := rfl
@[simp] private theorem sepX_00 : sepX 0 0 = 1 := rfl
@[simp] private theorem sepX_01 : sepX 0 1 = 0 := rfl
@[simp] private theorem sepX_10 : sepX 1 0 = 0 := rfl
@[simp] private theorem sepX_11 : sepX 1 1 = 1 := rfl

public def separated : Instance (Fin 2) where
  p := sepP
  n := sepN
  p_nonneg := by intro σ; fin_cases σ <;> norm_num
  p_le_one := by intro σ; fin_cases σ <;> norm_num
  n_nonneg := by intro t σ; fin_cases t <;> fin_cases σ <;> norm_num

public def separatedAssignment : RiskAssignment (Fin 2) (Fin 2) where
  v := sepV
  X := sepX
  v_nonneg := by intro b; fin_cases b <;> norm_num
  v_le_one := by intro b; fin_cases b <;> norm_num
  X_nonneg := by intro σ b; fin_cases σ <;> fin_cases b <;> norm_num
  X_sum := by intro σ; fin_cases σ <;> simp [Fin.sum_univ_two]

@[simp] private theorem separated_p : separated.p = sepP := rfl
@[simp] private theorem separated_n : separated.n = sepN := rfl
@[simp] private theorem separatedAssignment_v : separatedAssignment.v = sepV := rfl
@[simp] private theorem separatedAssignment_X : separatedAssignment.X = sepX := rfl

@[simp] private theorem separated_N_zero : separated.N 0 = 2 := by
  simp [Instance.N, Fin.sum_univ_two]; norm_num

@[simp] private theorem separated_N_one : separated.N 1 = 4 := by
  simp [Instance.N, Fin.sum_univ_two]; norm_num

@[simp] private theorem separated_mu (t : Fin 2) : separated.μ t = 1 := by
  fin_cases t <;> simp [Instance.μ, Fin.sum_univ_two]

public theorem separated_mu_pos (t : Fin 2) : 0 < separated.μ t := by simp

public theorem separated_mu_lt_N (t : Fin 2) : separated.μ t < separated.N t := by
  fin_cases t <;> norm_num

public theorem separated_calibrated : Calibrated separated separatedAssignment := by
  intro t b
  fin_cases t <;> fin_cases b <;> simp [assignedPos, assigned, Fin.sum_univ_two]

@[simp] private theorem separated_positiveAverage (t : Fin 2) :
    positiveAverage separated separatedAssignment t = 1 := by
  fin_cases t <;>
    simp [positiveAverage, positiveScore, assignedPos, Fin.sum_univ_two]

@[simp] private theorem separated_negativeAverage (t : Fin 2) :
    negativeAverage separated separatedAssignment t = 0 := by
  fin_cases t <;>
    simp [negativeAverage, negativeScore, assignedNeg, Fin.sum_univ_two]

public theorem separated_balancedPositive :
    BalancedPositive separated separatedAssignment := by
  have h0 := separated_positiveAverage 0
  have h1 := separated_positiveAverage 1
  rw [positiveAverage] at h0 h1
  rw [BalancedPositive, h0, h1]

public theorem separated_balancedNegative :
    BalancedNegative separated separatedAssignment := by
  have h0 := separated_negativeAverage 0
  have h1 := separated_negativeAverage 1
  rw [negativeAverage] at h0 h1
  rw [BalancedNegative, h0, h1]

public theorem separated_approxCalibrated :
    ApproxCalibrated (1 / 64) separated separatedAssignment :=
  approxCalibrated_of_calibrated separated separatedAssignment (by norm_num)
    separated_calibrated

public theorem separated_approxBalancedPositive :
    ApproxBalancedPositive (1 / 64) separated separatedAssignment :=
  approxBalancedPositive_of_balanced separated separatedAssignment (by norm_num)
    separated_mu_pos separated_balancedPositive

public theorem separated_approxBalancedNegative :
    ApproxBalancedNegative (1 / 64) separated separatedAssignment :=
  approxBalancedNegative_of_balanced separated separatedAssignment (by norm_num)
    separated_mu_lt_N separated_balancedNegative

@[simp] private theorem separated_baseRate_zero : baseRate separated 0 = 1 / 2 := by
  rw [baseRate, separated_mu, separated_N_zero]

@[simp] private theorem separated_baseRate_one : baseRate separated 1 = 1 / 4 := by
  rw [baseRate, separated_mu, separated_N_one]

/-- The first disjunct is realized, and at every `δ ≥ 0`: the positive class
scores a full `1` in both groups. -/
public theorem separated_approxPerfectPrediction :
    ApproxPerfectPrediction (slack (1 / 64)) separated separatedAssignment := by
  intro t
  rw [separated_positiveAverage]
  linarith [slack_nonneg (ε := (1 : ℝ) / 64)]

/-- And the second is not: `1/2` and `1/4` are `1/4` apart, wider than
`slack (1/64) = 9/64`. -/
public theorem separated_not_approxEqualBaseRates :
    ¬ ApproxEqualBaseRates (slack (1 / 64)) separated := by
  rw [ApproxEqualBaseRates, slack_one_sixtyfourth, separated_baseRate_zero,
    separated_baseRate_one, abs_le]
  intro h
  norm_num at h

/-- Theorem 1.2 applied to `separated`. -/
public theorem separated_conclusion :
    ApproxPerfectPrediction (slack (1 / 64)) separated separatedAssignment
      ∨ ApproxEqualBaseRates (slack (1 / 64)) separated :=
  approx_perfect_prediction_or_equal_base_rates separated separatedAssignment
    (by norm_num) separated_mu_pos separated_mu_lt_N
    separated_approxCalibrated separated_approxBalancedNegative
    separated_approxBalancedPositive

/-! ## `mixedBins`: perfect prediction without approximate perfect prediction

The same two certain feature vectors, one per group member, but a single bin
holding everybody. Calibration then forces that bin's score to `1/2`, and the
positive class averages `1/2` rather than `1`. -/

/-- Group `0` and group `1` are both `(1, 1)`. -/
public def mixN : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 1
  | 1, 0 => 1 | 1, 1 => 1

@[simp] private theorem mixN_00 : mixN 0 0 = 1 := rfl
@[simp] private theorem mixN_01 : mixN 0 1 = 1 := rfl
@[simp] private theorem mixN_10 : mixN 1 0 = 1 := rfl
@[simp] private theorem mixN_11 : mixN 1 1 = 1 := rfl

public def mixedBins : Instance (Fin 2) where
  p := sepP
  n := mixN
  p_nonneg := by intro σ; fin_cases σ <;> norm_num
  p_le_one := by intro σ; fin_cases σ <;> norm_num
  n_nonneg := by intro t σ; fin_cases t <;> fin_cases σ <;> norm_num

/-- One bin, holding everybody, scoring the fraction of positives in it. -/
public noncomputable def mixedBinsAssignment : RiskAssignment (Fin 2) (Fin 1) where
  v := fun _ ↦ 1 / 2
  X := fun _ _ ↦ 1
  v_nonneg := by intro b; norm_num
  v_le_one := by intro b; norm_num
  X_nonneg := by intro σ b; norm_num
  X_sum := by intro σ; simp

@[simp] private theorem mixedBins_p : mixedBins.p = sepP := rfl
@[simp] private theorem mixedBins_n : mixedBins.n = mixN := rfl
@[simp] private theorem mixedBinsAssignment_v (b : Fin 1) :
    mixedBinsAssignment.v b = 1 / 2 := rfl
@[simp] private theorem mixedBinsAssignment_X (σ : Fin 2) (b : Fin 1) :
    mixedBinsAssignment.X σ b = 1 := rfl

@[simp] private theorem mixedBins_N (t : Fin 2) : mixedBins.N t = 2 := by
  fin_cases t <;> simp [Instance.N, Fin.sum_univ_two] <;> norm_num

@[simp] private theorem mixedBins_mu (t : Fin 2) : mixedBins.μ t = 1 := by
  fin_cases t <;> simp [Instance.μ, Fin.sum_univ_two]

public theorem mixedBins_mu_pos (t : Fin 2) : 0 < mixedBins.μ t := by simp

public theorem mixedBins_mu_lt_N (t : Fin 2) : mixedBins.μ t < mixedBins.N t := by
  simp

public theorem mixedBins_calibrated : Calibrated mixedBins mixedBinsAssignment := by
  intro t b
  fin_cases t <;> fin_cases b <;>
    simp [assignedPos, assigned, Fin.sum_univ_two] <;> norm_num

/-- Every feature vector settles its holder's class, so the instance allows
perfect prediction in print's exact sense. -/
public theorem mixedBins_perfectPrediction : PerfectPrediction mixedBins := by
  intro σ _
  fin_cases σ
  · exact Or.inr rfl
  · exact Or.inl rfl

@[simp] private theorem mixedBins_positiveAverage (t : Fin 2) :
    positiveAverage mixedBins mixedBinsAssignment t = 1 / 2 := by
  fin_cases t <;>
    simp [positiveAverage, positiveScore, assignedPos, Fin.sum_univ_two]

/-- **The converse of `perfectPrediction_of_approx_zero` fails.** `mixedBins`
allows perfect prediction and is calibrated, yet its positive class averages
`1/2`, so print's approximate first case is false here for every `δ < 1/2`. -/
public theorem mixedBins_not_approxPerfectPrediction :
    ¬ ApproxPerfectPrediction (slack (1 / 64)) mixedBins mixedBinsAssignment := by
  intro h
  have h0 := h 0
  rw [slack_one_sixtyfourth, mixedBins_positiveAverage] at h0
  norm_num at h0

end AISafetyAtlas.Examples.Fairness.ApproximateRiskAssignment
