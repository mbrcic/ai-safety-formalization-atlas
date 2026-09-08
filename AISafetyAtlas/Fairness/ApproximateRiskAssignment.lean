module

public import AISafetyAtlas.Fairness.RiskAssignment
public import Mathlib.Analysis.Real.Sqrt

/-!
# The approximate trade-off

J. Kleinberg, S. Mullainathan and M. Raghavan, *Inherent Trade-Offs in the Fair
Determination of Risk Scores*, arXiv:1609.05807v2 (17 Nov 2016) — the source
cited by `BY-010` as `survey-ref-034`. This module carries **Theorem 1.2**, the
approximate characterization, proved from §3's own argument. Theorem 1.1 and the
model it is stated over are in `AISafetyAtlas.Fairness.RiskAssignment`.

## Primary surface

| declaration | says |
|---|---|
| `approx_perfect_prediction_or_equal_base_rates` | Theorem 1.2 at print's explicit `f`: the `ε`-approximate conditions force one of the two `slack ε`-approximate conclusions |
| `exists_slack_function` | Theorem 1.2's existential form for the approximate predicates reconstructed from the proof, with a continuous `f` vanishing at `0` |
| `slack` | print's `f ε = √ε · max (1) (3√ε + 3/4)`, read off the end of §3 |
| `perfect_prediction_or_equal_base_rates_of_approx` | Theorem 1.1 recovered as the `ε = 0` case, through the exact library statement |
| `average_lower_bound` | §3's core: a group whose base rate is lower by more than `√ε` has its positive class scoring at least `1 - 2ε - (3/4)√ε` |

`ApproxCalibrated` is the reading of print's (A′) reconstructed from the proof, while
`ApproxBalancedNegative` and `ApproxBalancedPositive` implement the repaired
(B′) and (C′) averages. `ApproxPerfectPrediction` and
`ApproxEqualBaseRates` are the two approximate conclusions. Non-vacuity
witnesses live in `AISafetyAtlas.Examples.Fairness.ApproximateRiskAssignment`.

## What print says

> **Theorem 1.2.** *There is a continuous function `f`, with `f(x)` going to `0`
> as `x` goes to `0`, so that the following holds. For all `ε > 0`, and any
> instance of the problem with a risk assignment satisfying the `ε`-approximate
> versions of fairness conditions (A), (B), and (C), the instance must satisfy
> either the `f(ε)`-approximate version of perfect prediction or the
> `f(ε)`-approximate version of equal base rates.*

Writing `γ t` for the average expected score reaching the positive class of
group `t` (`positiveAverage`) and `ν t` for the same over the negative class
(`negativeAverage`), §3's conditions are:

| print | here |
|---|---|
| (A′), as reconstructed from the proof of (7) | `WithinFactor ε (v b * assigned t b) (assignedPos t b)`, every `t` and `b` |
| (B′) | `WithinFactor ε (ν t) (ν u)`, both ordered pairs |
| (C′) | `WithinFactor ε (γ t) (γ u)`, both ordered pairs |
| `δ`-approximate perfect prediction | `1 - δ ≤ γ t` for both `t` |
| `δ`-approximately equal base rates | `|μ 0 / N 0 - μ 1 / N 1| ≤ δ` |

`WithinFactor ε x y` is print's `(1 - ε) y ≤ x ≤ (1 + ε) y`. The two ordered
pairs in (B′) and (C′) are print's *"we also require that these hold when `μ₁`
and `μ₂` are interchanged"*.

## Four things read off print rather than copied

**(A′) is reconstructed from the proof, not copied from the display.** §3 prints

> `(1 - ε)[nᵀ_t XV]_b ≤ [nᵀ_t P X]_b ≤ (1 - ε)[nᵀ_t XV]_b`

with `(1 - ε)` on both sides. Read literally, this forces
`[nᵀ_t P X]_b = (1 - ε)[nᵀ_t XV]_b`; it is exact calibration only when
`ε = 0`, not for positive `ε`. It therefore does not make Theorem 1.2 a
restatement of Theorem 1.1. The four lines that use it — the derivation of
`(1 - ε) μ t ≤ μ̂ t ≤ (1 + ε) μ t`, print's (7) — bound `[nᵀ_t XV]_b` above and
below by `(1 ± ε)[nᵀ_t P X]_b`. Accordingly `ApproxCalibrated` uses
`(1 - ε) P ≤ S ≤ (1 + ε) P`, with the score side `S` as the approximated
quantity and the positive-class side `P` as the reference. This is a defensible
reconstruction of the proof's use, with the display's two sides transposed; it is
neither the literal display nor equivalent to it. `approxCalibrated_zero_iff`
confirms that this reconstruction collapses to `Calibrated` at `ε = 0`.

**(B′) and (C′) also need a notational repair.** On PDF p. 12, the displayed
fractions use `n_t` throughout the numerators, including in the term for the
other group. The Lean definitions use each group's own score average and its
group-indexed denominator (`negativeAverage` divides by `N t - μ t`, and
`positiveAverage` by `μ t`), and the swapped requirement swaps the whole group
expression. Thus the Lean `ApproxBalancedNegative` and
`ApproxBalancedPositive` are the group-indexed reading needed by the argument,
not a literal transcription of that display.

**The approximate conclusions are not the exact ones weakened.** Print's
`δ`-approximate perfect prediction is a statement about `γ`, not about `p`, so
`ApproxPerfectPrediction` takes the risk assignment as an argument where
`PerfectPrediction` does not. The two are connected at `δ = 0` by
`perfectPrediction_of_approx_zero`, which is what licenses reading the first
disjunct as a form of print's first case.

**§3 divides by a quantity without fixing its sign.** The chain after print's
(10) divides by `1 - 2ε + ε² - γ₁` to reach `ρ₂/(1 - ρ₂) ≤ …`, and nothing
before it excludes `γ₁ ≥ (1 - ε)²`. The case is harmless — it is the case in
which the positive class already scores high enough for the conclusion — but it
has to be taken, and `average_lower_bound` takes it. `nlinarith` closes the
remaining polynomial inequality after `ε` is replaced by `s ^ 2`.

## What is not claimed

- **Not §4.** Print's algorithmic section — the loss-minimising risk assignment
  under equal base rates — is not here. Theorems 1.1 and 1.2 are the paper's only
  numbered theorems, so with this module the row carries both.
- **`slack` is print's `f`, not an optimal one.** Nothing here says no smaller
  continuous `f` works; print makes no such claim either.
- **No AI-system reading.** As in the exact module, the declarations are about a
  population, a partition into two groups, and a matrix.
-/

namespace AISafetyAtlas.Fairness

open Finset

variable {F B : Type*} [Fintype F] [Fintype B]

/-! ## The approximate conditions -/

/-- `x` lies within a multiplicative `ε` of `y`: print's `(1 - ε) y ≤ x ≤ (1 + ε) y`.
At `ε = 0` this is equality, which is what makes each primed condition below a
relaxation of its unprimed counterpart. -/
@[expose] public def WithinFactor (ε x y : ℝ) : Prop :=
  (1 - ε) * y ≤ x ∧ x ≤ (1 + ε) * y

/-- `γ t` — the average expected score reaching the positive class of group `t`. -/
@[expose] public noncomputable def positiveAverage (I : Instance F) (R : RiskAssignment F B)
    (t : Fin 2) : ℝ :=
  positiveScore I R t / I.μ t

/-- `ν t` — the average expected score reaching the negative class of group `t`. -/
@[expose] public noncomputable def negativeAverage (I : Instance F) (R : RiskAssignment F B)
    (t : Fin 2) : ℝ :=
  negativeScore I R t / (I.N t - I.μ t)

/-- `ρ t` — the base rate of group `t`. -/
@[expose] public noncomputable def baseRate (I : Instance F) (t : Fin 2) : ℝ := I.μ t / I.N t

/-- **Condition (A′).** Calibration holds to within a multiplicative `ε` in every
bin of every group. See the module header: the direction is the one §3's proof
uses, not the one its display prints. -/
@[expose] public def ApproxCalibrated (ε : ℝ) (I : Instance F) (R : RiskAssignment F B) : Prop :=
  ∀ t b, WithinFactor ε (R.v b * assigned I R t b) (assignedPos I R t b)

/-- **Condition (C′).** The two groups' positive-class averages agree to within a
multiplicative `ε`, in both directions. -/
@[expose] public def ApproxBalancedPositive (ε : ℝ) (I : Instance F)
    (R : RiskAssignment F B) : Prop :=
  ∀ t u, t ≠ u → WithinFactor ε (positiveAverage I R t) (positiveAverage I R u)

/-- **Condition (B′).** The two groups' negative-class averages agree to within a
multiplicative `ε`, in both directions. -/
@[expose] public def ApproxBalancedNegative (ε : ℝ) (I : Instance F)
    (R : RiskAssignment F B) : Prop :=
  ∀ t u, t ≠ u → WithinFactor ε (negativeAverage I R t) (negativeAverage I R u)

/-- **`δ`-approximate perfect prediction.** In each group the positive class
averages a score of at least `1 - δ`. Print states its first approximate
conclusion this way, over the risk assignment rather than over `p`. -/
@[expose] public def ApproxPerfectPrediction (δ : ℝ) (I : Instance F)
    (R : RiskAssignment F B) : Prop :=
  ∀ t, 1 - δ ≤ positiveAverage I R t

/-- **`δ`-approximately equal base rates.** -/
@[expose] public def ApproxEqualBaseRates (δ : ℝ) (I : Instance F) : Prop :=
  |baseRate I 0 - baseRate I 1| ≤ δ

/-- **Print's `f`**, read off the last line of §3:
`f ε = √ε · max (1) (3√ε + 3/4)`. The `max` with `1` is what makes `√ε ≤ f ε`,
which is the branch of the proof that returns approximately equal base rates. -/
@[expose] public noncomputable def slack (ε : ℝ) : ℝ :=
  Real.sqrt ε * max 1 (3 * Real.sqrt ε + 3 / 4)

/-! ## The relaxation collapses at `ε = 0` -/

/-- At `ε = 0`, `WithinFactor` is equality. -/
public theorem withinFactor_zero_iff {x y : ℝ} : WithinFactor 0 x y ↔ x = y := by
  constructor
  · rintro ⟨h₁, h₂⟩; linarith
  · rintro rfl; exact ⟨by linarith, by linarith⟩

/-- `WithinFactor` is reflexive on a nonnegative value for any nonnegative `ε`. -/
public theorem withinFactor_self {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    WithinFactor ε x x :=
  ⟨by nlinarith, by nlinarith⟩

/-- (A′) at `ε = 0` is (A). -/
public theorem approxCalibrated_zero_iff (I : Instance F) (R : RiskAssignment F B) :
    ApproxCalibrated 0 I R ↔ Calibrated I R := by
  simp only [ApproxCalibrated, Calibrated, withinFactor_zero_iff]
  exact ⟨fun h t b ↦ (h t b).symm, fun h t b ↦ (h t b).symm⟩

/-- (C′) at `ε = 0` is (C). -/
public theorem approxBalancedPositive_zero_iff (I : Instance F) (R : RiskAssignment F B) :
    ApproxBalancedPositive 0 I R ↔ BalancedPositive I R := by
  simp only [ApproxBalancedPositive, BalancedPositive, withinFactor_zero_iff]
  constructor
  · intro h; exact h 0 1 (by decide)
  · intro h t u _
    fin_cases t <;> fin_cases u <;> simp_all [positiveAverage]

/-- (B′) at `ε = 0` is (B). -/
public theorem approxBalancedNegative_zero_iff (I : Instance F) (R : RiskAssignment F B) :
    ApproxBalancedNegative 0 I R ↔ BalancedNegative I R := by
  simp only [ApproxBalancedNegative, BalancedNegative, withinFactor_zero_iff]
  constructor
  · intro h; exact h 0 1 (by decide)
  · intro h t u _
    fin_cases t <;> fin_cases u <;> simp_all [negativeAverage]

/-- Approximately equal base rates at `δ = 0` is equal base rates. -/
public theorem approxEqualBaseRates_zero_iff (I : Instance F) :
    ApproxEqualBaseRates 0 I ↔ EqualBaseRates I := by
  rw [ApproxEqualBaseRates, EqualBaseRates, abs_nonpos_iff, sub_eq_zero, baseRate, baseRate]

/-! ## Elementary bounds on the two averages -/

public theorem assignedPos_nonneg (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) (b : B) :
    0 ≤ assignedPos I R t b :=
  Finset.sum_nonneg fun σ _ ↦
    mul_nonneg (mul_nonneg (I.n_nonneg t σ) (I.p_nonneg σ)) (R.X_nonneg σ b)

public theorem assignedNeg_nonneg (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) (b : B) :
    0 ≤ assignedNeg I R t b :=
  Finset.sum_nonneg fun σ _ ↦
    mul_nonneg (mul_nonneg (I.n_nonneg t σ) (by linarith [I.p_le_one σ])) (R.X_nonneg σ b)

public theorem positiveScore_nonneg (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) :
    0 ≤ positiveScore I R t :=
  Finset.sum_nonneg fun b _ ↦ mul_nonneg (assignedPos_nonneg I R t b) (R.v_nonneg b)

public theorem negativeScore_nonneg (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) :
    0 ≤ negativeScore I R t :=
  Finset.sum_nonneg fun b _ ↦ mul_nonneg (assignedNeg_nonneg I R t b) (R.v_nonneg b)

/-- The positive class cannot average more than a score of `1`, because no bin
carries more. -/
public theorem positiveScore_le_μ (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) :
    positiveScore I R t ≤ I.μ t := by
  rw [← sum_assignedPos I R t]
  refine Finset.sum_le_sum fun b _ ↦ ?_
  nlinarith [assignedPos_nonneg I R t b, R.v_le_one b]

public theorem positiveAverage_nonneg (I : Instance F) (R : RiskAssignment F B)
    (hμ : 0 < I.μ t) : 0 ≤ positiveAverage I R t :=
  div_nonneg (positiveScore_nonneg I R t) hμ.le

public theorem positiveAverage_le_one (I : Instance F) (R : RiskAssignment F B)
    (hμ : 0 < I.μ t) : positiveAverage I R t ≤ 1 :=
  (div_le_one hμ).2 (positiveScore_le_μ I R t)

/-- **Print's `δ = 0` case.** A calibrated assignment whose positive class averages
a full score of `1` in group `t` leaves that group's negative class nothing, and
`perfect_of_negativeScore_eq_zero` turns that into `p σ ∈ {0, 1}`. This is what
connects `ApproxPerfectPrediction` back to `PerfectPrediction`. -/
public theorem perfectPrediction_of_approx_zero (I : Instance F) (R : RiskAssignment F B)
    (hμ : ∀ t, 0 < I.μ t) (hA : Calibrated I R) (h : ApproxPerfectPrediction 0 I R) :
    PerfectPrediction I := by
  refine fun σ ⟨t, hσ⟩ ↦ perfect_of_negativeScore_eq_zero I R hA ?_ σ hσ
  have h1 : (1 : ℝ) ≤ positiveAverage I R t := by simpa using h t
  have h2 : positiveScore I R t = I.μ t := by
    have := (one_le_div (hμ t)).1 h1
    exact le_antisymm (positiveScore_le_μ I R t) this
  rw [negativeScore_eq I R hA t, h2]; ring

/-! ## Every exact instance is an approximate one -/

/-- (A) implies (A′) for every `ε ≥ 0`. -/
public theorem approxCalibrated_of_calibrated (I : Instance F) (R : RiskAssignment F B)
    {ε : ℝ} (hε : 0 ≤ ε) (h : Calibrated I R) : ApproxCalibrated ε I R := fun t b ↦ by
  rw [← h t b]; exact withinFactor_self hε (assignedPos_nonneg I R t b)

/-- (C) implies (C′) for every `ε ≥ 0`. -/
public theorem approxBalancedPositive_of_balanced (I : Instance F) (R : RiskAssignment F B)
    {ε : ℝ} (hε : 0 ≤ ε) (hμ : ∀ t, 0 < I.μ t) (h : BalancedPositive I R) :
    ApproxBalancedPositive ε I R := by
  intro t u _
  have heq : positiveAverage I R t = positiveAverage I R u := by
    fin_cases t <;> fin_cases u <;> simp only [positiveAverage] <;>
      first | rfl | exact h | exact h.symm
  rw [← heq]
  exact withinFactor_self hε (positiveAverage_nonneg I R (hμ t))

/-- (B) implies (B′) for every `ε ≥ 0`. -/
public theorem approxBalancedNegative_of_balanced (I : Instance F) (R : RiskAssignment F B)
    {ε : ℝ} (hε : 0 ≤ ε) (hμN : ∀ t, I.μ t < I.N t) (h : BalancedNegative I R) :
    ApproxBalancedNegative ε I R := by
  intro t u _
  have heq : negativeAverage I R t = negativeAverage I R u := by
    fin_cases t <;> fin_cases u <;> simp only [negativeAverage] <;>
      first | rfl | exact h | exact h.symm
  rw [← heq]
  refine withinFactor_self hε (div_nonneg (negativeScore_nonneg I R t) ?_)
  have := hμN t; linarith

/-! ## `slack`, print's `f` -/

public theorem slack_nonneg {ε : ℝ} : 0 ≤ slack ε :=
  mul_nonneg (Real.sqrt_nonneg ε) (le_trans zero_le_one (le_max_left _ _))

public theorem sqrt_le_slack {ε : ℝ} : Real.sqrt ε ≤ slack ε :=
  le_mul_of_one_le_right (Real.sqrt_nonneg ε) (le_max_left _ _)

public theorem slack_zero : slack 0 = 0 := by simp [slack]

public theorem continuous_slack : Continuous slack := by
  unfold slack; fun_prop

/-- Print's *"`f(x)` going to `0` as `x` goes to `0`"*. -/
public theorem tendsto_slack_zero : Filter.Tendsto slack (nhds 0) (nhds 0) := by
  simpa [slack_zero] using continuous_slack.tendsto 0

/-! ## The numerical core of §3 -/

/-- The polynomial heart of §3, with `ε` presented as `s ^ 2` so that every
inequality below is polynomial in `s`.

`key` is print's (10) after both sides are written in terms of base rates. The
hypothesis-free case that print omits is the first branch: when `g` already
exceeds `(1 - s ^ 2) ^ 2` the conclusion holds outright, and it is exactly the
case in which print's division by `1 - 2ε + ε² - γ₁` is not licensed. -/
private theorem core_bound {s ρ₀ ρ₁ g : ℝ}
    (hs0 : 0 ≤ s) (hρ₀0 : 0 < ρ₀) (hρ₀1 : ρ₀ < 1) (hρ₁1 : ρ₁ < 1)
    (hgap : ρ₀ + s < ρ₁)
    (key : ((1 - s ^ 2) ^ 2 - g) * (ρ₁ / (1 - ρ₁)) ≤ (1 + s ^ 2 - g) * (ρ₀ / (1 - ρ₀))) :
    1 - 2 * s ^ 2 - 3 * s * ρ₀ * (1 - ρ₀) ≤ g := by
  have h1ρ₀ : (0:ℝ) < 1 - ρ₀ := by linarith
  have h1ρ₁ : (0:ℝ) < 1 - ρ₁ := by linarith
  have hρ₁0 : (0:ℝ) < ρ₁ := by linarith
  have hs1 : s < 1 := by linarith
  have hsq1 : s ^ 2 ≤ 1 := by nlinarith
  have hcube : 0 ≤ s * ρ₀ * (1 - ρ₀) := mul_nonneg (mul_nonneg hs0 hρ₀0.le) h1ρ₀.le
  rcases le_or_gt ((1 - s ^ 2) ^ 2) g with hbig | hsmall
  · -- The case print does not take: `γ` already clears `(1 - ε)²`, so the bound is free.
    nlinarith [sq_nonneg (s ^ 2)]
  -- The case print takes: `(1 - ε)² - γ > 0`, so its division is licensed.
  · have hA : 0 < (1 - s ^ 2) ^ 2 - g := by linarith
    have hC : 0 < 1 + s ^ 2 - g := by nlinarith
    -- Clear the two denominators of print's (10).
    have hcross : ((1 - s ^ 2) ^ 2 - g) * ρ₁ * (1 - ρ₀)
        ≤ (1 + s ^ 2 - g) * ρ₀ * (1 - ρ₁) := by
      have e₁ : ((1 - s ^ 2) ^ 2 - g) * (ρ₁ / (1 - ρ₁)) * ((1 - ρ₁) * (1 - ρ₀))
          = ((1 - s ^ 2) ^ 2 - g) * ρ₁ * (1 - ρ₀) := by field_simp
      have e₂ : (1 + s ^ 2 - g) * (ρ₀ / (1 - ρ₀)) * ((1 - ρ₁) * (1 - ρ₀))
          = (1 + s ^ 2 - g) * ρ₀ * (1 - ρ₁) := by field_simp
      have := mul_le_mul_of_nonneg_right key
        (by positivity : (0:ℝ) ≤ (1 - ρ₁) * (1 - ρ₀))
      rwa [e₁, e₂] at this
    -- Push `ρ₁` down to `ρ₀ + s` on the left and up on the right, keeping strictness
    -- so that the `s = 0` case closes by contradiction rather than by division.
    have hstrict : ((1 - s ^ 2) ^ 2 - g) * (ρ₀ + s) * (1 - ρ₀)
        < (1 + s ^ 2 - g) * ρ₀ * (1 - ρ₀ - s) := by
      have hleft : ((1 - s ^ 2) ^ 2 - g) * (ρ₀ + s) * (1 - ρ₀)
          < ((1 - s ^ 2) ^ 2 - g) * ρ₁ * (1 - ρ₀) := by
        nlinarith [mul_pos (mul_pos hA h1ρ₀) (sub_pos.2 hgap)]
      have hright : (1 + s ^ 2 - g) * ρ₀ * (1 - ρ₁)
          ≤ (1 + s ^ 2 - g) * ρ₀ * (1 - ρ₀ - s) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_pos hC hρ₀0).le
      linarith
    -- The exact accounting: the `γ`-coefficient of the difference is `s`, and what
    -- print discards -- its `ε²` term and its `3ε^{3/2}ρ₁` term -- is these two.
    have hident : (1 + s ^ 2 - g) * ρ₀ * (1 - ρ₀ - s)
        - ((1 - s ^ 2) ^ 2 - g) * (ρ₀ + s) * (1 - ρ₀)
        = s * g - (s * (1 - 2 * s ^ 2 - 3 * s * ρ₀ * (1 - ρ₀))
            + 3 * s ^ 3 * ρ₀ + s ^ 4 * ((ρ₀ + s) * (1 - ρ₀))) := by ring
    have hdrop₁ : 0 ≤ 3 * s ^ 3 * ρ₀ := by positivity
    have hdrop₂ : 0 ≤ s ^ 4 * ((ρ₀ + s) * (1 - ρ₀)) := by positivity
    have hpoly : s * (1 - 2 * s ^ 2 - 3 * s * ρ₀ * (1 - ρ₀)) < s * g := by linarith
    exact le_of_lt (lt_of_mul_lt_mul_left hpoly hs0)


/-! ## §3's derivation -/

/-- A bin's total score splits over the two classes. -/
public theorem sum_score_split (I : Instance F) (R : RiskAssignment F B) (t : Fin 2) :
    ∑ b, R.v b * assigned I R t b = positiveScore I R t + negativeScore I R t := by
  simp only [positiveScore, negativeScore, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [assigned_eq_add I R t b]; ring

/-- **Version of print's (7) reconstructed from the proof.** Under the adopted (A′) reading,
the total expected score handed to group `t` is within a factor `ε` of `μ t`,
which is what exact calibration makes it equal to. -/
public theorem sum_score_bounds (I : Instance F) (R : RiskAssignment F B) {ε : ℝ}
    (hA : ApproxCalibrated ε I R) (t : Fin 2) :
    WithinFactor ε (∑ b, R.v b * assigned I R t b) (I.μ t) := by
  constructor
  · rw [← sum_assignedPos I R t, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ ↦ (hA t b).1
  · rw [← sum_assignedPos I R t, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ ↦ (hA t b).2

/-- What the positive class leaves, written against the total actually handed out
rather than against `μ t`. Under exact calibration the two agree and this is
`negativeScore_eq`. -/
private theorem negativeScore_eq_sub (I : Instance F) (R : RiskAssignment F B) {t : Fin 2}
    (hμ : 0 < I.μ t) :
    negativeScore I R t
      = (∑ b, R.v b * assigned I R t b) - positiveAverage I R t * I.μ t := by
  have h : positiveAverage I R t * I.μ t = positiveScore I R t := by
    rw [positiveAverage]; field_simp
  rw [h, sum_score_split]; ring

/-- Print's chain from (B′) to (10), as an inequality between real numbers. The
two base-rate ratios are supplied by the caller as `mt / Dt` and `mu / Du`. -/
private theorem key_of_bounds {ε mt mu Dt Du nt nu Mt Mu gt gu : ℝ}
    (hε1 : ε < 1) (hmu : 0 < mu) (hDt : 0 < Dt) (hDu : 0 < Du)
    (hnt : nt = Mt - gt * mt) (hnu : nu = Mu - gu * mu)
    (hMt : Mt ≤ (1 + ε) * mt) (hMu : (1 - ε) * mu ≤ Mu)
    (hCtu : (1 - ε) * gu ≤ gt)
    (hBtu : (1 - ε) * (nu / Du) ≤ nt / Dt) :
    ((1 - ε) ^ 2 - gt) * (mu / Du) ≤ (1 + ε - gt) * (mt / Dt) := by
  have hone : (0:ℝ) ≤ 1 - ε := by linarith
  have h1 : ((1 - ε) ^ 2 - gt) * mu ≤ (1 - ε) * nu := by
    rw [hnu]
    nlinarith [mul_le_mul_of_nonneg_left hMu hone,
      mul_le_mul_of_nonneg_right hCtu hmu.le]
  have h2 : nt ≤ (1 + ε - gt) * mt := by rw [hnt]; nlinarith
  calc ((1 - ε) ^ 2 - gt) * (mu / Du) = (((1 - ε) ^ 2 - gt) * mu) / Du := by ring
    _ ≤ ((1 - ε) * nu) / Du := by gcongr
    _ = (1 - ε) * (nu / Du) := by ring
    _ ≤ nt / Dt := hBtu
    _ ≤ ((1 + ε - gt) * mt) / Dt := by gcongr
    _ = (1 + ε - gt) * (mt / Dt) := by ring

/-- `μ t / (N t - μ t)` is the base rate's odds, which is the form §3's algebra
needs. -/
private theorem mu_div_sub_eq (I : Instance F) {v : Fin 2}
    (hN : 0 < I.N v) (hD : 0 < I.N v - I.μ v) :
    I.μ v / (I.N v - I.μ v) = baseRate I v / (1 - baseRate I v) := by
  have hN' : I.N v ≠ 0 := ne_of_gt hN
  have hD' : I.N v - I.μ v ≠ 0 := ne_of_gt hD
  have hstep : 1 - baseRate I v = (I.N v - I.μ v) / I.N v := by
    rw [baseRate]; field_simp
  rw [hstep, baseRate, div_div_div_eq]
  field_simp

/-- **§3's core.** A group whose base rate falls short of the other by more than
`√ε` has its positive class averaging at least `1 - 2ε - (3/4)√ε`.

This is print's argument from (B′) down to `1 - 2ε - 3√ε ρ₁(1 - ρ₁) ≤ γ₁`,
together with `ρ(1 - ρ) ≤ 1/4`. The case print omits is inside `core_bound`. -/
public theorem average_lower_bound (I : Instance F) (R : RiskAssignment F B) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hμ : ∀ t, 0 < I.μ t) (hμN : ∀ t, I.μ t < I.N t)
    (hA : ApproxCalibrated ε I R) (hB : ApproxBalancedNegative ε I R)
    (hC : ApproxBalancedPositive ε I R)
    {t u : Fin 2} (htu : t ≠ u)
    (hgap : baseRate I t + Real.sqrt ε < baseRate I u) :
    1 - 2 * ε - 3 / 4 * Real.sqrt ε ≤ positiveAverage I R t := by
  have hs0 := Real.sqrt_nonneg ε
  have hs2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  have hN : ∀ v, 0 < I.N v := fun v ↦ lt_trans (hμ v) (hμN v)
  have hD : ∀ v, 0 < I.N v - I.μ v := fun v ↦ by have := hμN v; linarith
  have hρ0 : ∀ v, 0 < baseRate I v := fun v ↦ div_pos (hμ v) (hN v)
  have hρ1 : ∀ v, baseRate I v < 1 := fun v ↦ (div_lt_one (hN v)).2 (hμN v)
  have hBtu : (1 - ε) * (negativeScore I R u / (I.N u - I.μ u))
      ≤ negativeScore I R t / (I.N t - I.μ t) := (hB t u htu).1
  have key : ((1 - ε) ^ 2 - positiveAverage I R t)
        * (baseRate I u / (1 - baseRate I u))
      ≤ (1 + ε - positiveAverage I R t) * (baseRate I t / (1 - baseRate I t)) := by
    rw [← mu_div_sub_eq I (hN u) (hD u), ← mu_div_sub_eq I (hN t) (hD t)]
    exact key_of_bounds hε1 (hμ u) (hD t) (hD u)
      (negativeScore_eq_sub I R (hμ t)) (negativeScore_eq_sub I R (hμ u))
      (sum_score_bounds I R hA t).2 (sum_score_bounds I R hA u).1
      (hC t u htu).1 hBtu
  have core := core_bound hs0 (hρ0 t) (hρ1 t) (hρ1 u) hgap (by rw [hs2]; exact key)
  nlinarith [core, mul_nonneg hs0 (sq_nonneg (2 * baseRate I t - 1))]

/-- Both groups' positive classes average at least `1 - slack ε` once the base
rates are more than `√ε` apart. Print reaches the second group through (C′). -/
private theorem both_averages_large (I : Instance F) (R : RiskAssignment F B) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hμ : ∀ t, 0 < I.μ t) (hμN : ∀ t, I.μ t < I.N t)
    (hA : ApproxCalibrated ε I R) (hB : ApproxBalancedNegative ε I R)
    (hC : ApproxBalancedPositive ε I R)
    {t u : Fin 2} (htu : t ≠ u)
    (hgap : baseRate I t + Real.sqrt ε < baseRate I u) :
    1 - slack ε ≤ positiveAverage I R t ∧ 1 - slack ε ≤ positiveAverage I R u := by
  have hs0 := Real.sqrt_nonneg ε
  have hgt := average_lower_bound I R hε hε1 hμ hμN hA hB hC htu hgap
  have hgu0 : 0 ≤ positiveAverage I R u := positiveAverage_nonneg I R (hμ u)
  have hgu : (1 - ε) * positiveAverage I R t ≤ positiveAverage I R u := by
    have h := (hC t u htu).2
    nlinarith [mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ 1 - ε by linarith),
      mul_nonneg (sq_nonneg ε) hgu0]
  have hexp : Real.sqrt ε * (3 * Real.sqrt ε + 3 / 4)
      = 3 * Real.sqrt ε ^ 2 + 3 / 4 * Real.sqrt ε := by ring
  rw [Real.sq_sqrt hε] at hexp
  have hmax : Real.sqrt ε * (3 * Real.sqrt ε + 3 / 4) ≤ slack ε := by
    rw [slack]; gcongr; exact le_max_right _ _
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hgt (show (0:ℝ) ≤ 1 - ε by linarith),
    mul_nonneg hε hs0, sq_nonneg ε]

/-! ## Theorem 1.2 -/

/-- **Kleinberg–Mullainathan–Raghavan, Theorem 1.2.** An instance carrying a risk
assignment that meets (A′), (B′) and (C′) either has both positive classes
averaging at least `1 - slack ε`, or has base rates within `slack ε`.

The two numeric hypotheses are print's own, inherited from Theorem 1.1: it
divides by `μ t` in (C′) and by `N t - μ t` in (B′). Print states the theorem for
`ε > 0`; it is stated here for `ε ≥ 0`, which costs nothing and is what lets
`perfect_prediction_or_equal_base_rates_of_approx` recover Theorem 1.1 from it. -/
public theorem approx_perfect_prediction_or_equal_base_rates
    (I : Instance F) (R : RiskAssignment F B) {ε : ℝ} (hε : 0 ≤ ε)
    (hμ : ∀ t, 0 < I.μ t) (hμN : ∀ t, I.μ t < I.N t)
    (hA : ApproxCalibrated ε I R) (hB : ApproxBalancedNegative ε I R)
    (hC : ApproxBalancedPositive ε I R) :
    ApproxPerfectPrediction (slack ε) I R ∨ ApproxEqualBaseRates (slack ε) I := by
  have hs0 := Real.sqrt_nonneg ε
  have hN : ∀ v, 0 < I.N v := fun v ↦ lt_trans (hμ v) (hμN v)
  have hρ0 : ∀ v, 0 < baseRate I v := fun v ↦ div_pos (hμ v) (hN v)
  have hρ1 : ∀ v, baseRate I v < 1 := fun v ↦ (div_lt_one (hN v)).2 (hμN v)
  rcases le_or_gt 1 ε with hbig | hsmall
  · -- `ε ≥ 1` makes `slack ε ≥ 1`, and two base rates never differ by more than that.
    refine Or.inr ?_
    have h1 : (1:ℝ) ≤ Real.sqrt ε := by
      nlinarith [Real.sq_sqrt (le_trans zero_le_one hbig), hs0]
    have h2 : (1:ℝ) ≤ slack ε := by
      rw [slack]; nlinarith [le_max_left 1 (3 * Real.sqrt ε + 3 / 4)]
    rw [ApproxEqualBaseRates, abs_le]
    exact ⟨by linarith [hρ0 0, hρ1 1], by linarith [hρ0 1, hρ1 0]⟩
  rcases le_or_gt |baseRate I 0 - baseRate I 1| (slack ε) with hclose | hfar
  · exact Or.inr hclose
  refine Or.inl ?_
  have hfar' : Real.sqrt ε < |baseRate I 0 - baseRate I 1| :=
    lt_of_le_of_lt sqrt_le_slack hfar
  rcases lt_abs.1 hfar' with h | h
  · obtain ⟨h1, h0⟩ := both_averages_large I R hε hsmall hμ hμN hA hB hC
      (t := 1) (u := 0) (by decide) (by linarith)
    intro v; fin_cases v
    · exact h0
    · exact h1
  · obtain ⟨h0, h1⟩ := both_averages_large I R hε hsmall hμ hμN hA hB hC
      (t := 0) (u := 1) (by decide) (by linarith)
    intro v; fin_cases v
    · exact h0
    · exact h1

/-- **Theorem 1.2's existential form for the adopted predicates**: the existential
over a continuous `f` vanishing at `0`, witnessed by `slack`. The feature-vector
and bin types are universe-`0` here because they are bound under the `∃`; the
theorem above is the universe-polymorphic statement and is what every other
consumer should use. -/
public theorem exists_slack_function :
    ∃ f : ℝ → ℝ, Continuous f ∧ Filter.Tendsto f (nhds 0) (nhds 0) ∧
      ∀ (F B : Type) [Fintype F] [Fintype B] (I : Instance F) (R : RiskAssignment F B) (ε : ℝ),
        0 < ε → (∀ t, 0 < I.μ t) → (∀ t, I.μ t < I.N t) →
        ApproxCalibrated ε I R → ApproxBalancedNegative ε I R →
        ApproxBalancedPositive ε I R →
        ApproxPerfectPrediction (f ε) I R ∨ ApproxEqualBaseRates (f ε) I :=
  ⟨slack, continuous_slack, tendsto_slack_zero,
    fun _ _ _ _ I R _ hε hμ hμN hA hB hC ↦
      approx_perfect_prediction_or_equal_base_rates I R hε.le hμ hμN hA hB hC⟩

/-- **Theorem 1.1 recovered at `ε = 0` for the adopted predicates.** The exact
statement is proved independently in `AISafetyAtlas.Fairness.RiskAssignment`
from §2's own argument; this re-derives it through §3's forms reconstructed
from the proof. At `ε = 0`, those forms reduce to the exact conditions, and
`ApproxPerfectPrediction` at `δ = 0` gives print's first case under the exact
calibration hypothesis. This does not identify the PDF's literal (A′) display
with exact calibration for positive `ε`. -/
public theorem perfect_prediction_or_equal_base_rates_of_approx
    (I : Instance F) (R : RiskAssignment F B)
    (hμ : ∀ t, 0 < I.μ t) (hμN : ∀ t, I.μ t < I.N t)
    (hA : Calibrated I R) (hB : BalancedNegative I R) (hC : BalancedPositive I R) :
    PerfectPrediction I ∨ EqualBaseRates I := by
  have h := approx_perfect_prediction_or_equal_base_rates I R le_rfl hμ hμN
    ((approxCalibrated_zero_iff I R).2 hA)
    ((approxBalancedNegative_zero_iff I R).2 hB)
    ((approxBalancedPositive_zero_iff I R).2 hC)
  rw [slack_zero] at h
  rcases h with h | h
  · exact Or.inl (perfectPrediction_of_approx_zero I R hμ hA h)
  · exact Or.inr ((approxEqualBaseRates_zero_iff I).1 h)

end AISafetyAtlas.Fairness
