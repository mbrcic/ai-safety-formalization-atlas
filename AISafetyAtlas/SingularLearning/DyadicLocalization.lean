module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Dyadic localization: why a globally Gaussian-weighted integral computes a *local* pair

## What this module is

This is the **engine** of Lemma 8.6 of the MAIS issue #3 candidate, extracted as a standalone
analysis lemma about an abstract nonnegative homogeneous function. Lemma 8.6 is the step that
lets a Laplace integral taken over *all* of `ℝ^D`, weighted by a global Gaussian prior, compute
a quantity that is *local* at the origin: the learning coefficient of a zero set is a local
invariant, but the integral defining it is not localized by hand.

Nothing about reduced-rank regression appears here. The decomposition and estimate are proved
first, and then assembled in the final section into the two-sided comparison

    e^{-δ²} L_δ(T) ≤ L_G(T) ≤ (1 + S_δ) L_{2δ}(T),   S_δ = ∑_j 2^{jD} e^{-δ² 4^j} < ∞,

between the globally Gaussian-weighted `L_G` and the local `L_δ` over a ball. That is Lemma 8.6
with the scale left out: the candidate compares `L_G` directly with `H_{λ₀,m₀}`, which it can do
because it already has the exact volume asymptotics of Lemma 6.1(i) to feed the Abelian bridge.
Comparing two integrals instead defers the pair to `TauberianLog.lean`, and is what keeps the
volume-order table free of the exact-asymptotics frontier.

## The mechanism, and why non-compactness is not an obstruction

The zero set `{f = 0}` of a homogeneous `f` is a cone, hence never compact (unless trivial), and
the naive worry is that the integral picks up mass arbitrarily far out. Homogeneity turns that
non-compactness from an obstruction into the mechanism:

* `smul_dyadicShell_zero` — the dyadic shells `A_j = {δ 2^j ≤ ‖x‖ < δ 2^{j+1}}` are not merely
  small, they are **all the same set**, `A_j = 2^j · A_0`. A degree-`k` homogeneous `f`
  therefore transfers each shell integral to one over the *fixed* region `A_0 ⊆ B(0,2δ)`, at the
  price of rescaling the temperature `T ↦ T 2^{kj}` and picking up the Jacobian `2^{jD}`
  (`setIntegral_dyadicShell_rescale`, `setIntegral_dyadicShell_homogeneous_le`).
* `summable_pow_mul_exp_neg_four_pow` — the resulting series converges, because on `A_j` the
  Gaussian weight is at most `e^{-δ² 4^j}`, which decays *doubly* exponentially and so beats the
  polynomial volume growth `2^{jD}` of the shells. This is the arithmetic heart of the argument.

The consequences are `setIntegral_tail_le` (the tail is at most the sum of the shell bounds),
`setIntegral_tail_le_const` (an explicit constant depending only on `δ` and `D`), and
`tendsto_setIntegral_tail_atTop` (the tail vanishes as `δ → ∞`, uniformly over `[0,1]`-valued
weights) — the last being the usable form: outside a ball of large enough radius there is
nothing left, so the global integral *is* the local one up to an arbitrarily small error.

## Contents

1. `iUnion_dyadicShell`, `pairwise_disjoint_dyadicShell` — the shell decomposition of
   `{δ ≤ ‖x‖}`.
2. `measureReal_dyadicShell_le` — the shell volume bound, from `Measure.addHaar_ball_of_pos`.
3. `summable_pow_mul_exp_neg_four_pow` — doubly exponential decay beats geometric growth.
4. `setIntegral_dyadicShell_le`, `setIntegral_tail_le`, `setIntegral_tail_le_const`,
   `tendsto_setIntegral_tail_atTop` — the tail bound and its limit form.
5. `smul_dyadicShell_zero`, `setIntegral_dyadicShell_rescale`,
   `setIntegral_dyadicShell_homogeneous_le` — the homogeneity rescaling step.
6. `gaussian_ge_ball`, `gaussian_le_ball` — Lemma 8.6's two bounds.

`integrable_exp_neg_sq_norm` is a small gap-filler: the pinned Mathlib states Gaussian
integrability on an inner-product space only for the *complex* Gaussian
(`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`), and the real statement is its norm.

## A note on exponents

Every exponent in this file is a `ℕ`-power of a *real* base, and every index identity used is
subtraction-free: `(j+1) * D = j * D + D` (`add_mul`, `pow_add`), `(2^j)^k = 2^(j*k)`
(`pow_mul`), `(2^j)² = 4^j`. No `ℕ`-subtraction occurs anywhere, so no truncation can silently
collapse two shells or kill a dimension; the shell index `j` and the dimension `D` are never
decremented.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Metric Filter Real
open scoped ENNReal Pointwise Topology

variable {D : ℕ}

/-- The `j`-th dyadic shell of radius scale `δ`. -/
@[expose] public def dyadicShell (δ : ℝ) (j : ℕ) : Set (EuclideanSpace ℝ (Fin D)) :=
  {x | δ * 2 ^ j ≤ ‖x‖ ∧ ‖x‖ < δ * 2 ^ (j + 1)}

public theorem mem_dyadicShell {δ : ℝ} {j : ℕ} {x : EuclideanSpace ℝ (Fin D)} :
    x ∈ dyadicShell δ j ↔ δ * 2 ^ j ≤ ‖x‖ ∧ ‖x‖ < δ * 2 ^ (j + 1) := Iff.rfl

public theorem measurableSet_dyadicShell (δ : ℝ) (j : ℕ) :
    MeasurableSet (dyadicShell (D := D) δ j) := by
  exact (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

public theorem iUnion_dyadicShell {δ : ℝ} (hδ : 0 < δ) :
    (⋃ j : ℕ, dyadicShell (D := D) δ j) = {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖} := by
  ext x
  simp only [Set.mem_iUnion, mem_dyadicShell, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, -⟩
    exact le_trans (le_mul_of_one_le_right hδ.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))) hj
  · intro hx
    have hex : ∃ j : ℕ, ‖x‖ < δ * 2 ^ (j + 1) := by
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (‖x‖ / δ) (by norm_num : (1:ℝ) < 2)
      rw [div_lt_iff₀ hδ] at hj
      exact ⟨j, by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j]⟩
    classical
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simpa using hx
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have := Nat.find_min hex (m := k) (by omega)
      rw [hk]
      exact le_of_not_gt this

public theorem pairwise_disjoint_dyadicShell {δ : ℝ} (hδ : 0 ≤ δ) :
    Pairwise (Function.onFun Disjoint (dyadicShell (D := D) δ)) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (dyadicShell (D := D) δ i) (dyadicShell δ j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨-, hxi⟩ ⟨hxj, -⟩
    have hmono : δ * 2 ^ (i + 1) ≤ δ * 2 ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) hδ
    linarith
  intro i j hij
  rcases hij.lt_or_gt with h | h
  · exact key i j h
  · exact (key j i h).symm

/-! ## Shell volumes -/

/-- The volume of the unit ball of `EuclideanSpace ℝ (Fin D)`, as a real number. -/
@[expose] public noncomputable def unitBallVolume (D : ℕ) : ℝ :=
  volume.real (ball (0 : EuclideanSpace ℝ (Fin D)) 1)

public theorem unitBallVolume_nonneg (D : ℕ) : 0 ≤ unitBallVolume D :=
  measureReal_nonneg

public theorem dyadicShell_subset_ball (δ : ℝ) (j : ℕ) :
    dyadicShell (D := D) δ j ⊆ ball (0 : EuclideanSpace ℝ (Fin D)) (δ * 2 ^ (j + 1)) := by
  rintro x ⟨-, hx⟩
  exact mem_ball_zero_iff.mpr hx

/-- **Shell volume bound.** The `j`-th shell sits inside the ball of radius `δ 2^(j+1)`, whose
volume scales as the `D`-th power of the radius times the volume of the unit ball. The exponent
`D` is a `ℕ`-power of a *real* base, so no `ℕ`-subtraction occurs. -/
public theorem measureReal_dyadicShell_le {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    volume.real (dyadicShell (D := D) δ j) ≤ (δ * 2 ^ (j + 1)) ^ D * unitBallVolume D := by
  have hpos : (0 : ℝ) < δ * 2 ^ (j + 1) := by positivity
  have hsub := measureReal_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin D))))
    (dyadicShell_subset_ball δ j) measure_ball_lt_top.ne
  refine hsub.trans_eq ?_
  unfold Measure.real unitBallVolume Measure.real
  rw [Measure.addHaar_ball_of_pos _ _ hpos, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-! ## The summability that makes the decomposition work -/

/-- **Doubly exponential decay beats geometric growth.** For every `D : ℕ` and every `δ > 0` the
series `∑_j 2^{jD} e^{-δ² 4^j}` converges.

This is the arithmetic heart of the dyadic argument: the `j`-th shell has volume `O(2^{jD})`
while the Gaussian weight on it is at most `e^{-δ² 4^j}`, and the second beats the first by the
ratio test — the ratio of consecutive terms is `2^D e^{-3δ² 4^j} → 0`.

The exponent `j * D` is a `ℕ`-product used as the exponent of the real base `2`, and the
exponent `j` of `4` likewise; no `ℕ`-subtraction appears, and the arithmetic identity
`(j+1) * D = j * D + D` used below is subtraction-free. -/
public theorem summable_pow_mul_exp_neg_four_pow (D : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j : ℕ => (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) := by
  have hpos : ∀ j : ℕ, 0 < (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) := fun j => by
    positivity
  refine summable_of_ratio_test_tendsto_lt_one zero_lt_one
    (Eventually.of_forall fun j => (hpos j).ne') ?_
  have hratio : ∀ j : ℕ,
      ‖(2 : ℝ) ^ ((j + 1) * D) * Real.exp (-(δ ^ 2) * 4 ^ (j + 1))‖ /
          ‖(2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j)‖
        = 2 ^ D * Real.exp (-(3 * δ ^ 2) * 4 ^ j) := by
    intro j
    rw [Real.norm_of_nonneg (hpos (j + 1)).le, Real.norm_of_nonneg (hpos j).le]
    have hsplit : (2 : ℝ) ^ ((j + 1) * D) * Real.exp (-(δ ^ 2) * 4 ^ (j + 1))
        = 2 ^ D * Real.exp (-(3 * δ ^ 2) * 4 ^ j) *
          ((2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j)) := by
      have hexp : Real.exp (-(3 * δ ^ 2) * 4 ^ j) * Real.exp (-(δ ^ 2) * 4 ^ j)
          = Real.exp (-(δ ^ 2) * (4 ^ j * 4)) := by
        rw [← Real.exp_add]; ring_nf
      rw [add_mul, one_mul, pow_add, pow_succ (4 : ℝ) j, ← hexp]
      ring
    rw [hsplit, mul_div_assoc, div_self (hpos j).ne', mul_one]
  simp only [hratio]
  have h4 : Tendsto (fun j : ℕ => (4 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hb : Tendsto (fun j : ℕ => -(3 * δ ^ 2) * 4 ^ j) atTop atBot :=
    h4.const_mul_atTop_of_neg (by nlinarith)
  simpa using (Real.tendsto_exp_atBot.comp hb).const_mul ((2 : ℝ) ^ D)

/-! ## Integrability of the Gaussian weight -/

/-- The Gaussian `exp (-‖x‖²)` is integrable on `EuclideanSpace ℝ (Fin D)`. The pinned Mathlib
states the integrability only for the *complex* Gaussian
(`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`); the real statement is its norm. -/
public theorem integrable_exp_neg_sq_norm (D : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin D) => Real.exp (-‖x‖ ^ 2)) volume := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (1 : ℂ)) (V := EuclideanSpace ℝ (Fin D)) (by norm_num) 0 0).norm
  refine h.congr ?_
  filter_upwards with v
  simp [Complex.norm_exp, ← Complex.ofReal_pow]

/-- A measurable weight `g` with `0 ≤ g ≤ 1` does not destroy integrability of the Gaussian. -/
public theorem integrable_exp_neg_sq_norm_mul {g : EuclideanSpace ℝ (Fin D) → ℝ}
    (hgm : Measurable g) (hg : ∀ x, 0 ≤ g x) (hgb : ∀ x, g x ≤ 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin D) => Real.exp (-‖x‖ ^ 2) * g x) volume := by
  refine (integrable_exp_neg_sq_norm D).mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg x))]
  nlinarith [Real.exp_pos (-‖x‖ ^ 2), hg x, hgb x]

/-! ## The per-shell bound and the tail bound -/

/-- **The Gaussian weight on the `j`-th shell.** On `dyadicShell δ j` one has `‖x‖ ≥ δ 2^j`,
hence `exp (-‖x‖²) ≤ exp (-δ² 4^j)`, and the integral of a `[0,1]`-valued weight against it is
at most `exp (-δ² 4^j)` times the volume of the shell. -/
public theorem setIntegral_dyadicShell_le {δ : ℝ} (hδ : 0 < δ)
    {g : EuclideanSpace ℝ (Fin D) → ℝ} (hg : ∀ x, 0 ≤ g x) (hgb : ∀ x, g x ≤ 1) (j : ℕ) :
    ∫ x in dyadicShell δ j, Real.exp (-‖x‖ ^ 2) * g x
      ≤ Real.exp (-(δ ^ 2) * 4 ^ j) * volume.real (dyadicShell (D := D) δ j) := by
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine norm_setIntegral_le_of_norm_le_const
    (lt_of_le_of_lt (measure_mono (dyadicShell_subset_ball δ j)) measure_ball_lt_top) ?_
  rintro x ⟨hx, -⟩
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg x))]
  have hfour : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hx2 : δ ^ 2 * 4 ^ j ≤ ‖x‖ ^ 2 := by
    calc δ ^ 2 * 4 ^ j = (δ * 2 ^ j) ^ 2 := by rw [mul_pow, hfour]
      _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
  calc Real.exp (-‖x‖ ^ 2) * g x ≤ Real.exp (-‖x‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (hgb x) (Real.exp_pos _).le
    _ = Real.exp (-‖x‖ ^ 2) := mul_one _
    _ ≤ Real.exp (-(δ ^ 2) * 4 ^ j) := Real.exp_le_exp.mpr (by linarith)

/-- The shell bounds are summable: `exp (-δ² 4^j) · vol (shell j)` is dominated by
`(δ^D 2^D vol B₁) · 2^{jD} exp (-δ² 4^j)`, which is `summable_pow_mul_exp_neg_four_pow`. -/
public theorem summable_exp_mul_measureReal_dyadicShell {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j : ℕ =>
      Real.exp (-(δ ^ 2) * 4 ^ j) * volume.real (dyadicShell (D := D) δ j) := by
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (Real.exp_pos _).le measureReal_nonneg) (fun j => ?_)
    (((summable_pow_mul_exp_neg_four_pow D hδ).mul_left
      (δ ^ D * 2 ^ D * unitBallVolume D)))
  have hpow : ((2 : ℝ) ^ (j + 1)) ^ D = 2 ^ (j * D) * 2 ^ D := by
    rw [← pow_mul, add_mul, one_mul, pow_add]
  calc Real.exp (-(δ ^ 2) * 4 ^ j) * volume.real (dyadicShell (D := D) δ j)
      ≤ Real.exp (-(δ ^ 2) * 4 ^ j) * ((δ * 2 ^ (j + 1)) ^ D * unitBallVolume D) :=
        mul_le_mul_of_nonneg_left (measureReal_dyadicShell_le hδ j) (Real.exp_pos _).le
    _ = δ ^ D * 2 ^ D * unitBallVolume D * (2 ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j)) := by
        rw [mul_pow, hpow]; ring

/-- **The tail bound.** For a measurable weight `g` with `0 ≤ g ≤ 1`, the Gaussian integral over
the complement of the ball of radius `δ` is bounded by the sum of the shell bounds. -/
public theorem setIntegral_tail_le {δ : ℝ} (hδ : 0 < δ) {g : EuclideanSpace ℝ (Fin D) → ℝ}
    (hgm : Measurable g) (hg : ∀ x, 0 ≤ g x) (hgb : ∀ x, g x ≤ 1) :
    ∫ x in {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖}, Real.exp (-‖x‖ ^ 2) * g x
      ≤ ∑' j : ℕ, Real.exp (-(δ ^ 2) * 4 ^ j) * volume.real (dyadicShell (D := D) δ j) := by
  have hint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin D) => Real.exp (-‖x‖ ^ 2) * g x)
      (⋃ j : ℕ, dyadicShell δ j) volume :=
    (integrable_exp_neg_sq_norm_mul hgm hg hgb).integrableOn
  have hsum := hasSum_integral_iUnion (measurableSet_dyadicShell (D := D) δ)
    (pairwise_disjoint_dyadicShell hδ.le) hint
  rw [← iUnion_dyadicShell hδ, ← hsum.tsum_eq]
  exact Summable.tsum_le_tsum (fun j => setIntegral_dyadicShell_le hδ hg hgb j) hsum.summable
    (summable_exp_mul_measureReal_dyadicShell hδ)

/-- **The tail bound in explicit constant form.** The same integral is at most
`δ^D · 2^D · vol B₁ · ∑_j 2^{jD} e^{-δ² 4^j}`, a constant depending only on `δ` and `D`. -/
public theorem setIntegral_tail_le_const {δ : ℝ} (hδ : 0 < δ)
    {g : EuclideanSpace ℝ (Fin D) → ℝ} (hgm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hgb : ∀ x, g x ≤ 1) :
    ∫ x in {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖}, Real.exp (-‖x‖ ^ 2) * g x
      ≤ δ ^ D * 2 ^ D * unitBallVolume D *
        ∑' j : ℕ, (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) := by
  refine (setIntegral_tail_le hδ hgm hg hgb).trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_exp_mul_measureReal_dyadicShell hδ)
    ((summable_pow_mul_exp_neg_four_pow D hδ).mul_left _)
  have hpow : ((2 : ℝ) ^ (j + 1)) ^ D = 2 ^ (j * D) * 2 ^ D := by
    rw [← pow_mul, add_mul, one_mul, pow_add]
  calc Real.exp (-(δ ^ 2) * 4 ^ j) * volume.real (dyadicShell (D := D) δ j)
      ≤ Real.exp (-(δ ^ 2) * 4 ^ j) * ((δ * 2 ^ (j + 1)) ^ D * unitBallVolume D) :=
        mul_le_mul_of_nonneg_left (measureReal_dyadicShell_le hδ j) (Real.exp_pos _).le
    _ = δ ^ D * 2 ^ D * unitBallVolume D * (2 ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j)) := by
        rw [mul_pow, hpow]; ring

/-! ## The homogeneity rescaling: every shell is a rescaled copy of one fixed shell -/

/-- Every dyadic shell is the dilate of the zeroth one: `2^j · A₀ = A_j`. This is what makes the
decomposition useful — the shells are not merely small, they are *all the same set* up to a
dilation, so a scaling law for the integrand transfers the whole family to one fixed region. -/
public theorem smul_dyadicShell_zero {δ : ℝ} (j : ℕ) :
    ((2 : ℝ) ^ j) • dyadicShell (D := D) δ 0 = dyadicShell δ j := by
  have hR : (0 : ℝ) < 2 ^ j := by positivity
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  simp only [mem_dyadicShell, pow_zero, mul_one, zero_add, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_nonneg hR.le, inv_mul_eq_div, le_div_iff₀ hR, div_lt_iff₀ hR,
    pow_succ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **The homogeneity rescaling step.** If `f` is nonnegative and homogeneous of degree `k`,
the substitution `x = 2^j y` turns the integral of `exp (-T f)` over the `j`-th shell into
`2^{jD}` times the integral of `exp (-(T 2^{kj}) f)` over the *fixed* zeroth shell: the
temperature is rescaled and the Jacobian `2^{jD}` is the only trace left of `j`.

The two exponents are `ℕ`-products of a real base (`2 ^ (j * D)`, `2 ^ (k * j)`); the identity
`(2^j)^k = 2^(j*k)` is `pow_mul`, and no `ℕ`-subtraction occurs. -/
public theorem setIntegral_dyadicShell_rescale {δ : ℝ} {k : ℕ}
    {f : EuclideanSpace ℝ (Fin D) → ℝ} (hhom : ∀ t : ℝ, 0 ≤ t → ∀ x, f (t • x) = t ^ k * f x)
    (T : ℝ) (j : ℕ) :
    ∫ x in dyadicShell (D := D) δ j, Real.exp (-T * f x)
      = 2 ^ (j * D) * ∫ y in dyadicShell (D := D) δ 0, Real.exp (-(T * 2 ^ (k * j)) * f y) := by
  have hR : ((2 : ℝ) ^ j) ≠ 0 := by positivity
  have hkey := Measure.setIntegral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin D)))
    (fun x => Real.exp (-T * f x)) (R := (2 : ℝ) ^ j) (dyadicShell δ 0) hR
  rw [smul_dyadicShell_zero (δ := δ) j, finrank_euclideanSpace_fin, ← pow_mul] at hkey
  have hfun : ∀ y : EuclideanSpace ℝ (Fin D),
      Real.exp (-T * f (((2 : ℝ) ^ j) • y)) = Real.exp (-(T * 2 ^ (k * j)) * f y) := by
    intro y
    rw [hhom _ (by positivity) y, ← pow_mul, mul_comm k j]
    ring_nf
  simp only [hfun] at hkey
  rw [hkey, smul_eq_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (j * D))⁻¹),
    ← mul_assoc, mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ (j * D)) ≠ 0), one_mul]

/-- A measurable `[0,1]`-valued function is integrable on any set of finite volume. -/
public theorem integrableOn_of_mem_Icc {s : Set (EuclideanSpace ℝ (Fin D))} (hs : volume s ≠ ⊤)
    {h : EuclideanSpace ℝ (Fin D) → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (h1 : ∀ x, h x ≤ 1) : IntegrableOn h s volume :=
  Measure.integrableOn_of_bounded (M := 1) hs hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (h0 x)]; exact h1 x)

/-- **The candidate's upper bound on a single shell.** For `f` nonnegative, measurable and
homogeneous of degree `k`, and `T ≥ 0`,

    ∫_{A_j} exp (-T f x) exp (-‖x‖²) dx
      ≤ 2^{jD} · exp (-δ² 4^j) · ∫_{B(0,2δ)} exp (-(T 2^{kj}) f y) dy .

Three moves: the Gaussian factor is at most `exp (-δ² 4^j)` on the shell; the substitution
`x = 2^j y` (`setIntegral_dyadicShell_rescale`) contributes the Jacobian `2^{jD}` and rescales
the temperature to `T 2^{kj}`; and the zeroth shell sits inside `B(0,2δ)`, where the integrand
is still nonnegative. This is the inequality the candidate sums over `j`, and
`summable_pow_mul_exp_neg_four_pow` is what makes the sum converge. -/
public theorem setIntegral_dyadicShell_homogeneous_le {δ : ℝ} (hδ : 0 < δ) {k : ℕ}
    {f : EuclideanSpace ℝ (Fin D) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ x, f (t • x) = t ^ k * f x) {T : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    ∫ x in dyadicShell (D := D) δ j, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
      ≤ 2 ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) *
        ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ),
          Real.exp (-(T * 2 ^ (k * j)) * f y) := by
  -- Volumes of the two regions in play are finite.
  have hvolshell : ∀ i : ℕ, volume (dyadicShell (D := D) δ i) ≠ ⊤ := fun i =>
    (lt_of_le_of_lt (measure_mono (dyadicShell_subset_ball δ i)) measure_ball_lt_top).ne
  have hvolball : volume (ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  -- `exp (-S * f)` is `[0,1]`-valued for every `S ≥ 0`.
  have hbdd : ∀ S : ℝ, 0 ≤ S → ∀ x, Real.exp (-S * f x) ≤ 1 := fun S hS x =>
    Real.exp_le_one_iff.mpr (by nlinarith [hf x])
  have hTk : (0 : ℝ) ≤ T * 2 ^ (k * j) := by positivity
  -- Step 1: the Gaussian factor is at most `exp (-δ² 4^j)` on the `j`-th shell.
  have hstep1 : ∫ x in dyadicShell (D := D) δ j, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
      ≤ Real.exp (-(δ ^ 2) * 4 ^ j) * ∫ x in dyadicShell (D := D) δ j, Real.exp (-T * f x) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ?_ ?_ (measurableSet_dyadicShell δ j) ?_
    · exact integrableOn_of_mem_Icc (hvolshell j) (by fun_prop)
        (fun x => by positivity) (fun x => by
          have hsq : Real.exp (-‖x‖ ^ 2) ≤ 1 :=
            Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
          nlinarith [Real.exp_pos (-T * f x), Real.exp_pos (-‖x‖ ^ 2), hbdd T hT x])
    · exact (integrableOn_of_mem_Icc (hvolshell j) (by fun_prop) (fun x => (Real.exp_pos _).le)
        (hbdd T hT)).const_mul _
    · rintro x ⟨hx, -⟩
      have hfour : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have hx2 : δ ^ 2 * 4 ^ j ≤ ‖x‖ ^ 2 := by
        calc δ ^ 2 * 4 ^ j = (δ * 2 ^ j) ^ 2 := by rw [mul_pow, hfour]
          _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
      rw [mul_comm (Real.exp (-(δ ^ 2) * 4 ^ j))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
  -- Step 3: the zeroth shell sits inside `B (0, 2δ)`, where the integrand is nonnegative.
  have hstep3 : ∫ y in dyadicShell (D := D) δ 0, Real.exp (-(T * 2 ^ (k * j)) * f y)
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ),
          Real.exp (-(T * 2 ^ (k * j)) * f y) := by
    have hsub : dyadicShell (D := D) δ 0 ⊆ ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ) := by
      have h0 := dyadicShell_subset_ball (D := D) δ 0
      rwa [show δ * 2 ^ (0 + 1) = 2 * δ by ring] at h0
    exact setIntegral_mono_set
      (integrableOn_of_mem_Icc hvolball (by fun_prop) (fun x => (Real.exp_pos _).le)
        (hbdd _ hTk)) (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      (LE.le.eventuallyLE hsub)
  -- Step 2 glues the two through the rescaling identity.
  refine hstep1.trans ?_
  rw [setIntegral_dyadicShell_rescale (D := D) (δ := δ) hhom T j]
  calc Real.exp (-(δ ^ 2) * 4 ^ j) *
        (2 ^ (j * D) * ∫ y in dyadicShell (D := D) δ 0, Real.exp (-(T * 2 ^ (k * j)) * f y))
      = 2 ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) *
        ∫ y in dyadicShell (D := D) δ 0, Real.exp (-(T * 2 ^ (k * j)) * f y) := by ring
    _ ≤ 2 ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) *
        ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ),
          Real.exp (-(T * 2 ^ (k * j)) * f y) :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)

/-- **The usable form: the tail vanishes.** As `δ → ∞` the Gaussian mass outside the ball of
radius `δ` goes to zero, uniformly in the `[0,1]`-valued weight `g`. Together with
`setIntegral_tail_le_const` this is what lets a globally Gaussian-weighted integral be replaced
by its restriction to a fixed neighbourhood of the origin, up to an error one can make
arbitrarily small — the localization the candidate's Lemma 8.6 performs. -/
public theorem tendsto_setIntegral_tail_atTop {g : EuclideanSpace ℝ (Fin D) → ℝ}
    (hgm : Measurable g) (hg : ∀ x, 0 ≤ g x) (hgb : ∀ x, g x ≤ 1) :
    Tendsto (fun δ : ℝ => ∫ x in {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖},
      Real.exp (-‖x‖ ^ 2) * g x) atTop (𝓝 0) := by
  have hmeas : ∀ δ : ℝ, MeasurableSet {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖} :=
    fun δ => measurableSet_le measurable_const measurable_norm
  simp only [fun δ : ℝ => (integral_indicator (μ := (volume : Measure (EuclideanSpace ℝ (Fin D))))
    (f := fun x => Real.exp (-‖x‖ ^ 2) * g x) (hmeas δ)).symm]
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin D))))
    (bound := fun x : EuclideanSpace ℝ (Fin D) => Real.exp (-‖x‖ ^ 2))
    (F := fun δ : ℝ => Set.indicator {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖}
      fun x => Real.exp (-‖x‖ ^ 2) * g x)
    (f := fun _ : EuclideanSpace ℝ (Fin D) => (0 : ℝ)) (l := atTop)
    (Filter.Eventually.of_forall fun δ =>
      ((Measurable.indicator (by fun_prop) (hmeas δ)).aestronglyMeasurable))
    (Filter.Eventually.of_forall fun δ => Filter.Eventually.of_forall fun x => ?_)
    (integrable_exp_neg_sq_norm D) ?_
  · simpa using hlim
  · refine norm_indicator_le_norm_self _ x |>.trans ?_
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg x))]
    nlinarith [Real.exp_pos (-‖x‖ ^ 2), hg x, hgb x]
  · refine Filter.Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ‖x‖] with δ hδ
    rw [Set.indicator_of_notMem (by simpa using hδ.not_ge)]

/-! ## Worked examples -/

/-- The homogeneity hypothesis is satisfiable, so `setIntegral_dyadicShell_homogeneous_le` is not
vacuous: `f x = ‖x‖²` is nonnegative, measurable, and homogeneous of degree `2`. -/
example (D : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin D)) :
    ‖t • x‖ ^ 2 = t ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_pow]

/-- The shell bound instantiated at the degree-`2` homogeneous `f x = ‖x‖²`: the temperature is
rescaled by `2 ^ (2 * j)`, the Jacobian is `2 ^ (j * D)`, and the whole family of shells is
compared against the *fixed* ball `B (0, 2δ)`. -/
example {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 0 ≤ T) (D j : ℕ) :
    ∫ x in dyadicShell (D := D) δ j, Real.exp (-T * ‖x‖ ^ 2) * Real.exp (-‖x‖ ^ 2)
      ≤ 2 ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) *
        ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ),
          Real.exp (-(T * 2 ^ (2 * j)) * ‖y‖ ^ 2) :=
  setIntegral_dyadicShell_homogeneous_le hδ (by fun_prop) (fun x => by positivity)
    (fun t ht x => by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_pow]) hT j

/-- The tail bound at the constant weight `g = 1`: the plain Gaussian mass outside `B (0, δ)`
is at most `δ^D 2^D vol(B₁) ∑_j 2^{jD} e^{-δ² 4^j}`. -/
example {δ : ℝ} (hδ : 0 < δ) (D : ℕ) :
    ∫ x in {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖}, Real.exp (-‖x‖ ^ 2) * 1
      ≤ δ ^ D * 2 ^ D * unitBallVolume D *
        ∑' j : ℕ, (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) :=
  setIntegral_tail_le_const hδ measurable_const (fun _ => zero_le_one) (fun _ => le_rfl)

/-! ## Lemma 8.6: the Gaussian-weighted integral is the local one

The pieces above assemble into the two-sided statement the candidate's Lemma 8.6 makes. Write

    L_G(T) = ∫_{ℝ^D} e^{-T f(x)} e^{-‖x‖²} dx,    L_δ(T) = ∫_{B(0,δ)} e^{-T f(x)} dx .

Then `e^{-δ²} L_δ(T) ≤ L_G(T) ≤ (1 + S_δ) L_{2δ}(T)`, with `S_δ = ∑_j 2^{jD} e^{-δ² 4^j}` finite.
The lower bound is one line: on `B(0,δ)` the Gaussian factor is at least `e^{-δ²}`. The upper
bound is the dyadic sum, with the temperature rescaling absorbed by the observation that
`T 2^{kj} ≥ T` and `f ≥ 0`, so a hotter integral is a smaller one.

The candidate states Lemma 8.6 against `H_{λ₀,m₀}` directly, because it already has the exact
volume asymptotics of Lemma 6.1(i) to feed the Abelian bridge. This form is the same argument
without that input: it compares two integrals rather than an integral with a scale, so the pair
enters only later, through `TauberianLog.lean`. That is what keeps the volume-order table free of
the exact-asymptotics frontier.

The two radii `δ` and `2δ` do not match, and cannot be made to: the dyadic argument pays a factor
of two in the radius. Nothing downstream minds, because the pair is radius-independent — both
bounds hold at *every* small radius, so applying the upper bound at `δ` and the lower bound at
`δ/2` gives a two-sided statement at `δ`. -/

section GaussianLocalization

/-- Raising the temperature lowers the integral, for a nonnegative germ. Used to absorb the
rescaling `T ↦ T 2^{kj}` that the homogeneity step introduces. -/
public theorem setIntegral_exp_antitone {s : Set (EuclideanSpace ℝ (Fin D))}
    (hsm : MeasurableSet s) (hs : volume s ≠ ⊤) {f : EuclideanSpace ℝ (Fin D) → ℝ}
    (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {S T : ℝ} (hT : 0 ≤ T) (hST : T ≤ S) :
    ∫ y in s, Real.exp (-S * f y) ≤ ∫ y in s, Real.exp (-T * f y) := by
  have hbdd : ∀ R : ℝ, 0 ≤ R → ∀ x, Real.exp (-R * f x) ≤ 1 := fun R hR x =>
    Real.exp_le_one_iff.mpr (by nlinarith [hf x])
  refine setIntegral_mono_on
    (integrableOn_of_mem_Icc hs (by fun_prop) (fun _ => (Real.exp_pos _).le)
      (hbdd S (hT.trans hST)))
    (integrableOn_of_mem_Icc hs (by fun_prop) (fun _ => (Real.exp_pos _).le) (hbdd T hT))
    hsm ?_
  intro y _
  exact Real.exp_le_exp.mpr (by nlinarith [hf y])

/-- **Lemma 8.6, lower bound.** On `B(0,δ)` the Gaussian factor costs at most `e^{-δ²}`, so the
globally weighted integral dominates the local one. -/
public theorem gaussian_ge_ball {δ : ℝ} (hδ : 0 < δ)
    {f : EuclideanSpace ℝ (Fin D) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(δ ^ 2)) * ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) δ, Real.exp (-T * f y)
      ≤ ∫ x, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2) := by
  have hbdd : ∀ x, Real.exp (-T * f x) ≤ 1 := fun x =>
    Real.exp_le_one_iff.mpr (by nlinarith [hf x])
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin D) =>
      Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)) volume := by
    have h := integrable_exp_neg_sq_norm_mul (D := D) (g := fun x => Real.exp (-T * f x))
      (by fun_prop) (fun _ => (Real.exp_pos _).le) hbdd
    exact h.congr (Filter.Eventually.of_forall fun x => by ring)
  have hstep1 : Real.exp (-(δ ^ 2)) *
        ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) δ, Real.exp (-T * f y)
      ≤ ∫ x in ball (0 : EuclideanSpace ℝ (Fin D)) δ,
          Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on
      ((integrableOn_of_mem_Icc measure_ball_lt_top.ne (by fun_prop)
        (fun _ => (Real.exp_pos _).le) hbdd).const_mul _)
      hint.integrableOn measurableSet_ball ?_
    intro x hx
    have hxδ : ‖x‖ < δ := by simpa using hx
    have hgauss : Real.exp (-(δ ^ 2)) ≤ Real.exp (-‖x‖ ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [norm_nonneg x])
    calc Real.exp (-(δ ^ 2)) * Real.exp (-T * f x)
        ≤ Real.exp (-‖x‖ ^ 2) * Real.exp (-T * f x) :=
          mul_le_mul_of_nonneg_right hgauss (Real.exp_pos _).le
      _ = Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2) := by ring
  refine hstep1.trans ?_
  refine setIntegral_le_integral hint ?_
  filter_upwards with x
  positivity

/-- **Lemma 8.6, upper bound.** The dyadic sum: the global Gaussian integral is at most a
constant times the local integral at twice the radius. The constant `1 + S_δ` depends only on
`δ` and `D`, not on `T`, which is what makes the comparison an asymptotic one. -/
public theorem gaussian_le_ball {δ : ℝ} (hδ : 0 < δ) {k : ℕ}
    {f : EuclideanSpace ℝ (Fin D) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ x, f (t • x) = t ^ k * f x) {T : ℝ} (hT : 0 ≤ T) :
    ∫ x, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
      ≤ (1 + ∑' j : ℕ, (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j)) *
        ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ), Real.exp (-T * f y) := by
  have hbdd : ∀ R : ℝ, 0 ≤ R → ∀ x, Real.exp (-R * f x) ≤ 1 := fun R hR x =>
    Real.exp_le_one_iff.mpr (by nlinarith [hf x])
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin D) =>
      Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)) volume := by
    have h := integrable_exp_neg_sq_norm_mul (D := D) (g := fun x => Real.exp (-T * f x))
      (by fun_prop) (fun _ => (Real.exp_pos _).le) (hbdd T hT)
    exact h.congr (Filter.Eventually.of_forall fun x => by ring)
  have hballint : IntegrableOn (fun y : EuclideanSpace ℝ (Fin D) => Real.exp (-T * f y))
      (ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ)) volume :=
    integrableOn_of_mem_Icc measure_ball_lt_top.ne (by fun_prop)
      (fun _ => (Real.exp_pos _).le) (hbdd T hT)
  have hballnn : (0:ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ),
      Real.exp (-T * f y) :=
    setIntegral_nonneg measurableSet_ball fun _ _ => (Real.exp_pos _).le
  -- Split off the ball of radius `δ`.
  have hsplit : ∫ x, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
      = (∫ x in ball (0 : EuclideanSpace ℝ (Fin D)) δ,
          Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2))
        + ∫ x in {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖},
          Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2) := by
    have hcompl : {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖}
        = (ball (0 : EuclideanSpace ℝ (Fin D)) δ)ᶜ := by
      ext x
      simp
    rw [hcompl, ← integral_add_compl measurableSet_ball hint]
  -- The inner piece.
  have hinner : ∫ x in ball (0 : EuclideanSpace ℝ (Fin D)) δ,
        Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ), Real.exp (-T * f y) := by
    have h1 : ∫ x in ball (0 : EuclideanSpace ℝ (Fin D)) δ,
          Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
        ≤ ∫ x in ball (0 : EuclideanSpace ℝ (Fin D)) δ, Real.exp (-T * f x) := by
      refine setIntegral_mono_on hint.integrableOn
        (integrableOn_of_mem_Icc measure_ball_lt_top.ne (by fun_prop)
          (fun _ => (Real.exp_pos _).le) (hbdd T hT)) measurableSet_ball ?_
      intro x _
      have hgauss : Real.exp (-‖x‖ ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      nlinarith [Real.exp_pos (-T * f x)]
    refine h1.trans (setIntegral_mono_set hballint
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) ?_)
    exact (ball_subset_ball (by linarith)).eventuallyLE
  -- The tail, shell by shell.
  have hshell : ∀ j : ℕ, ∫ x in dyadicShell (D := D) δ j,
        Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
      ≤ (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) *
        ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ), Real.exp (-T * f y) := by
    intro j
    refine (setIntegral_dyadicShell_homogeneous_le hδ hfm hf hhom hT j).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine setIntegral_exp_antitone measurableSet_ball measure_ball_lt_top.ne hfm hf hT ?_
    have h2 : (1:ℝ) ≤ 2 ^ (k * j) := one_le_pow₀ (by norm_num)
    nlinarith
  have hsum := hasSum_integral_iUnion (measurableSet_dyadicShell (D := D) δ)
    (pairwise_disjoint_dyadicShell hδ.le) (hint.integrableOn)
  have htail : ∫ x in {x : EuclideanSpace ℝ (Fin D) | δ ≤ ‖x‖},
        Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)
      ≤ (∑' j : ℕ, (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j)) *
        ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ), Real.exp (-T * f y) := by
    rw [← iUnion_dyadicShell hδ, ← hsum.tsum_eq, ← tsum_mul_right]
    exact Summable.tsum_le_tsum hshell hsum.summable
      ((summable_pow_mul_exp_neg_four_pow D hδ).mul_right _)
  rw [hsplit, add_mul, one_mul]
  exact add_le_add hinner htail

end GaussianLocalization

end AISafetyAtlas.SingularLearning
