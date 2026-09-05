module

public import AISafetyAtlas.Fairness.RiskAssignment

/-!
# Two instances that inhabit Theorem 1.1, and one that bounds it

`AISafetyAtlas.Fairness.RiskAssignment` proves that a calibrated, balanced risk
assignment forces perfect prediction or equal base rates. A theorem of that shape
is valid the moment nothing satisfies its hypotheses, so this module exhibits
instances that do — one for each disjunct — and then uses the second to show that
print's unrestricted quantifier is not what can be proved.

| witness | (A) (B) (C) | realizes | and refutes |
|---|---|---|---|
| `equalRates` | hold | `EqualBaseRates` | `PerfectPrediction` |
| `perfect` | hold | `PerfectPrediction` | `EqualBaseRates` |

Neither disjunct is reached by accident: `equalRates` carries `p = 1/2` at a
feature vector everybody has, so it cannot be perfect prediction, and `perfect`
has base rates `1/2` and `1/4`.

## The unpopulated feature vector

`perfect` has three feature vectors and only two of them belong to anybody: `σ₂`
has `n t σ₂ = 0` in both groups and `p σ₂ = 1/2`. Every sum in conditions (A),
(B) and (C) weights `σ₂` by `n t σ₂`, so `σ₂` is invisible to all three — the
instance satisfies every hypothesis of Theorem 1.1 while `∀ σ, p σ = 0 ∨ p σ = 1`,
print's literal conclusion, is false at `σ₂`. `not_print_perfectPrediction` is
that refutation, and it is why `AISafetyAtlas.Fairness.PerfectPrediction`
quantifies over the feature vectors somebody has. The restriction is forced, not
chosen.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Fairness.RiskAssignment

open AISafetyAtlas.Fairness

/-! ## An instance with equal base rates

One feature vector held by everybody, one bin. Half of each group is in the
positive class, so the single bin scores `1/2` and each condition is an
identity. -/

/-- Everyone shares one feature vector, at which half the people are positive. -/
public noncomputable def equalRates : Instance (Fin 1) where
  p := fun _ ↦ 1 / 2
  n := fun _ _ ↦ 2
  p_nonneg := by intro σ; norm_num
  p_le_one := by intro σ; norm_num
  n_nonneg := by intro t σ; norm_num

/-- One bin, scoring the common positive-class fraction. -/
public noncomputable def equalRatesAssignment : RiskAssignment (Fin 1) (Fin 1) where
  v := fun _ ↦ 1 / 2
  X := fun _ _ ↦ 1
  v_nonneg := by intro b; norm_num
  v_le_one := by intro b; norm_num
  X_nonneg := by intro σ b; norm_num
  X_sum := by intro σ; simp

@[simp] private theorem equalRates_p (σ : Fin 1) : equalRates.p σ = 1 / 2 := rfl
@[simp] private theorem equalRates_n (t : Fin 2) (σ : Fin 1) : equalRates.n t σ = 2 := rfl
@[simp] private theorem equalRatesAssignment_v (b : Fin 1) :
    equalRatesAssignment.v b = 1 / 2 := rfl
@[simp] private theorem equalRatesAssignment_X (σ b : Fin 1) :
    equalRatesAssignment.X σ b = 1 := rfl

@[simp] private theorem equalRates_N (t : Fin 2) : equalRates.N t = 2 := by
  simp [Instance.N]

@[simp] private theorem equalRates_mu (t : Fin 2) : equalRates.μ t = 1 := by
  simp [Instance.μ]

public theorem equalRates_calibrated : Calibrated equalRates equalRatesAssignment := by
  intro t b
  simp [assignedPos, assigned]

public theorem equalRates_balancedPositive :
    BalancedPositive equalRates equalRatesAssignment := by
  simp [BalancedPositive, positiveScore, assignedPos]

public theorem equalRates_balancedNegative :
    BalancedNegative equalRates equalRatesAssignment := by
  simp [BalancedNegative, negativeScore, assignedNeg]

public theorem equalRates_mu_pos (t : Fin 2) : 0 < equalRates.μ t := by simp

public theorem equalRates_mu_lt_N (t : Fin 2) : equalRates.μ t < equalRates.N t := by
  simp

/-- The second disjunct is realized. -/
public theorem equalRates_equalBaseRates : EqualBaseRates equalRates := by
  simp [EqualBaseRates]

/-- And the first is not, so this witness pins the second disjunct rather than
satisfying the conclusion by satisfying both. -/
public theorem equalRates_not_perfect : ¬ PerfectPrediction equalRates := by
  intro h
  rcases h 0 ⟨0, by simp⟩ with h' | h' <;> · simp at h'

/-- Theorem 1.1 applied to the equal-base-rate witness. -/
public theorem equalRates_conclusion :
    PerfectPrediction equalRates ∨ EqualBaseRates equalRates :=
  perfect_prediction_or_equal_base_rates equalRates equalRatesAssignment
    equalRates_mu_pos equalRates_mu_lt_N equalRates_calibrated
    equalRates_balancedNegative equalRates_balancedPositive

/-! ## An instance with perfect prediction and unequal base rates

Three feature vectors — one certainly negative, one certainly positive, and one
nobody has — and two bins scoring `0` and `1`. Group `0` is `(1, 1, 0)` and group
`1` is `(3, 1, 0)`, so the base rates are `1/2` and `1/4`. -/

/-- `p σ₀ = 0`, `p σ₁ = 1`, and `p σ₂ = 1/2` at the feature vector nobody has. -/
public noncomputable def pVal : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1 / 2

/-- Group `0` is `(1, 1, 0)`; group `1` is `(3, 1, 0)`. -/
public def nVal : Fin 2 → Fin 3 → ℝ
  | 0, 0 => 1 | 0, 1 => 1 | 0, 2 => 0
  | 1, 0 => 3 | 1, 1 => 1 | 1, 2 => 0

/-- Bin `0` scores `0`, bin `1` scores `1`. -/
public def vVal : Fin 2 → ℝ
  | 0 => 0
  | 1 => 1

/-- The certainly-negative feature vector goes to the zero bin, the
certainly-positive one to the unit bin, and the unpopulated one to the zero
bin. -/
public def XVal : Fin 3 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 0
  | 1, 0 => 0 | 1, 1 => 1
  | 2, 0 => 1 | 2, 1 => 0

@[simp] private theorem pVal_zero : pVal 0 = 0 := rfl
@[simp] private theorem pVal_one : pVal 1 = 1 := rfl
@[simp] private theorem pVal_two : pVal 2 = 1 / 2 := rfl
@[simp] private theorem nVal_00 : nVal 0 0 = 1 := rfl
@[simp] private theorem nVal_01 : nVal 0 1 = 1 := rfl
@[simp] private theorem nVal_02 : nVal 0 2 = 0 := rfl
@[simp] private theorem nVal_10 : nVal 1 0 = 3 := rfl
@[simp] private theorem nVal_11 : nVal 1 1 = 1 := rfl
@[simp] private theorem nVal_12 : nVal 1 2 = 0 := rfl
@[simp] private theorem vVal_zero : vVal 0 = 0 := rfl
@[simp] private theorem vVal_one : vVal 1 = 1 := rfl
@[simp] private theorem XVal_00 : XVal 0 0 = 1 := rfl
@[simp] private theorem XVal_01 : XVal 0 1 = 0 := rfl
@[simp] private theorem XVal_10 : XVal 1 0 = 0 := rfl
@[simp] private theorem XVal_11 : XVal 1 1 = 1 := rfl
@[simp] private theorem XVal_20 : XVal 2 0 = 1 := rfl
@[simp] private theorem XVal_21 : XVal 2 1 = 0 := rfl

/-- The instance: two populated feature vectors with certain outcomes, and one
that nobody has. -/
public noncomputable def perfect : Instance (Fin 3) where
  p := pVal
  n := nVal
  p_nonneg := by intro σ; fin_cases σ <;> simp
  p_le_one := by intro σ; fin_cases σ <;> norm_num [pVal]
  n_nonneg := by intro t σ; fin_cases t <;> fin_cases σ <;> simp

/-- The assignment: score `0` for the certainly-negative bin, `1` for the
certainly-positive one. -/
public def perfectAssignment : RiskAssignment (Fin 3) (Fin 2) where
  v := vVal
  X := XVal
  v_nonneg := by intro b; fin_cases b <;> simp
  v_le_one := by intro b; fin_cases b <;> simp
  X_nonneg := by intro σ b; fin_cases σ <;> fin_cases b <;> simp
  X_sum := by intro σ; fin_cases σ <;> simp [Fin.sum_univ_two]

@[simp] private theorem perfect_p : perfect.p = pVal := rfl
@[simp] private theorem perfect_n : perfect.n = nVal := rfl
@[simp] private theorem perfectAssignment_v : perfectAssignment.v = vVal := rfl
@[simp] private theorem perfectAssignment_X : perfectAssignment.X = XVal := rfl

@[simp] private theorem perfect_N_zero : perfect.N 0 = 2 := by
  simp [Instance.N, Fin.sum_univ_three]; norm_num

@[simp] private theorem perfect_N_one : perfect.N 1 = 4 := by
  simp [Instance.N, Fin.sum_univ_three]; norm_num

@[simp] private theorem perfect_mu (t : Fin 2) : perfect.μ t = 1 := by
  fin_cases t <;> simp [Instance.μ, Fin.sum_univ_three]

public theorem perfect_calibrated : Calibrated perfect perfectAssignment := by
  intro t b
  fin_cases t <;> fin_cases b <;> simp [assignedPos, assigned, Fin.sum_univ_three]

public theorem perfect_balancedPositive : BalancedPositive perfect perfectAssignment := by
  simp [BalancedPositive, positiveScore, assignedPos, Fin.sum_univ_two, Fin.sum_univ_three]

public theorem perfect_balancedNegative : BalancedNegative perfect perfectAssignment := by
  simp [BalancedNegative, negativeScore, assignedNeg, Fin.sum_univ_two, Fin.sum_univ_three]

public theorem perfect_mu_pos (t : Fin 2) : 0 < perfect.μ t := by simp

public theorem perfect_mu_lt_N (t : Fin 2) : perfect.μ t < perfect.N t := by
  fin_cases t <;> simp

/-- The first disjunct is realized, at every feature vector somebody has. -/
public theorem perfect_perfectPrediction : PerfectPrediction perfect := by
  intro σ hσ
  obtain ⟨t, ht⟩ := hσ
  fin_cases σ
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (by fin_cases t <;> rfl) ht

/-- And the second is not: the base rates are `1/2` and `1/4`. -/
public theorem perfect_not_equalBaseRates : ¬ EqualBaseRates perfect := by
  simp [EqualBaseRates]

/-- Theorem 1.1 applied to the perfect-prediction witness. -/
public theorem perfect_conclusion :
    PerfectPrediction perfect ∨ EqualBaseRates perfect :=
  perfect_prediction_or_equal_base_rates perfect perfectAssignment
    perfect_mu_pos perfect_mu_lt_N perfect_calibrated
    perfect_balancedNegative perfect_balancedPositive

/-! ## The restrictive reading, inhabited

Drop the unpopulated feature vector and the same data becomes an instance in
which every feature vector belongs to somebody. Print's unrestricted sentence
then holds verbatim, by `print_perfectPrediction_of_populated`. -/

/-- `p σ₀ = 0`, `p σ₁ = 1`: two feature vectors, both populated. -/
public def pPop : Fin 2 → ℝ
  | 0 => 0
  | 1 => 1

/-- Group `0` is `(1, 1)`; group `1` is `(3, 1)`. -/
public def nPop : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 1
  | 1, 0 => 3 | 1, 1 => 1

/-- Each feature vector goes to its own bin. -/
public def XPop : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 0
  | 1, 0 => 0 | 1, 1 => 1

@[simp] private theorem pPop_zero : pPop 0 = 0 := rfl
@[simp] private theorem pPop_one : pPop 1 = 1 := rfl
@[simp] private theorem nPop_00 : nPop 0 0 = 1 := rfl
@[simp] private theorem nPop_01 : nPop 0 1 = 1 := rfl
@[simp] private theorem nPop_10 : nPop 1 0 = 3 := rfl
@[simp] private theorem nPop_11 : nPop 1 1 = 1 := rfl
@[simp] private theorem XPop_00 : XPop 0 0 = 1 := rfl
@[simp] private theorem XPop_01 : XPop 0 1 = 0 := rfl
@[simp] private theorem XPop_10 : XPop 1 0 = 0 := rfl
@[simp] private theorem XPop_11 : XPop 1 1 = 1 := rfl

/-- The same instance as `perfect` with the unpopulated feature vector removed. -/
public def populated : Instance (Fin 2) where
  p := pPop
  n := nPop
  p_nonneg := by intro σ; fin_cases σ <;> simp
  p_le_one := by intro σ; fin_cases σ <;> simp
  n_nonneg := by intro t σ; fin_cases t <;> fin_cases σ <;> simp

/-- The same assignment, on two bins. -/
public def populatedAssignment : RiskAssignment (Fin 2) (Fin 2) where
  v := vVal
  X := XPop
  v_nonneg := by intro b; fin_cases b <;> simp
  v_le_one := by intro b; fin_cases b <;> simp
  X_nonneg := by intro σ b; fin_cases σ <;> fin_cases b <;> simp
  X_sum := by intro σ; fin_cases σ <;> simp [Fin.sum_univ_two]

@[simp] private theorem populated_p : populated.p = pPop := rfl
@[simp] private theorem populated_n : populated.n = nPop := rfl
@[simp] private theorem populatedAssignment_v : populatedAssignment.v = vVal := rfl
@[simp] private theorem populatedAssignment_X : populatedAssignment.X = XPop := rfl

@[simp] private theorem populated_N_zero : populated.N 0 = 2 := by
  simp [Instance.N, Fin.sum_univ_two]; norm_num

@[simp] private theorem populated_N_one : populated.N 1 = 4 := by
  simp [Instance.N, Fin.sum_univ_two]; norm_num

@[simp] private theorem populated_mu (t : Fin 2) : populated.μ t = 1 := by
  fin_cases t <;> simp [Instance.μ, Fin.sum_univ_two]

public theorem populated_calibrated : Calibrated populated populatedAssignment := by
  intro t b
  fin_cases t <;> fin_cases b <;> simp [assignedPos, assigned, Fin.sum_univ_two]

public theorem populated_balancedPositive :
    BalancedPositive populated populatedAssignment := by
  simp [BalancedPositive, positiveScore, assignedPos, Fin.sum_univ_two]

public theorem populated_balancedNegative :
    BalancedNegative populated populatedAssignment := by
  simp [BalancedNegative, negativeScore, assignedNeg, Fin.sum_univ_two]

/-- Every feature vector belongs to somebody. -/
public theorem populated_isPopulated : ∀ σ, ∃ t, populated.n t σ ≠ 0 := by
  intro σ
  fin_cases σ <;> exact ⟨0, by simp⟩

/-- **Print's unrestricted sentence, holding verbatim on a populated instance.**
This is the restrictive reading of §1.1, and it is inhabited. -/
public theorem populated_print_perfectPrediction :
    ∀ σ, populated.p σ = 0 ∨ populated.p σ = 1 :=
  print_perfectPrediction_of_populated populated populated_isPopulated
    (by
      rcases perfect_prediction_or_equal_base_rates populated populatedAssignment
          (by intro t; simp) (by intro t; fin_cases t <;> simp)
          populated_calibrated populated_balancedNegative populated_balancedPositive with h | h
      · exact h
      · exact absurd h (by simp [EqualBaseRates]))

/-! ## What the unpopulated feature vector rules out -/

/-- **Print's literal conclusion is false on an instance satisfying every
hypothesis.** Theorem 1.1 reads *"perfect prediction (with `p_σ` equal to `0` or
`1` for all `σ`)"*. The instance `perfect` satisfies (A), (B) and (C) with both
classes nonempty in both groups, has unequal base rates, and carries
`p σ₂ = 1/2`. So the unrestricted quantifier cannot be proved, and
`AISafetyAtlas.Fairness.PerfectPrediction` restricts to realized feature vectors
for that reason. -/
public theorem not_print_perfectPrediction :
    ¬ (∀ σ, perfect.p σ = 0 ∨ perfect.p σ = 1) := by
  intro h
  rcases h 2 with h' | h' <;> · simp at h'

end AISafetyAtlas.Examples.Fairness.RiskAssignment
