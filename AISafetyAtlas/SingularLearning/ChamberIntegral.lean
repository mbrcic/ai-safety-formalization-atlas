module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# The chamber integral of the candidate's Appendix A, end to end

This module carries the whole `I(T)`/`J(T)` chain of the MAIS issue #3 candidate's Section 8.6
and Appendix A, from the one-dimensional model integral to the two-sided order estimate:

* **Lemma A.2** — `chamberA2`, the one-dimensional two-sided bound
  `κ⁻¹ Θ(T;a,b) ≤ G(T;a,b) ≤ κ Θ(T;a,b)` with `Θ(T;a,b) = T^{-min(a,b)}(log T)^{1{a=b}}`,
  together with the three *localized* lower bounds `chamberA2_localSmall`,
  `chamberA2_localLarge`, `chamberA2_localLog` that Lemma A.5 consumes instead.
* **Lemma A.4** — `chamberA4_upper`, the Vandermonde majorization and the product upper bound
  `I(T) ≤ ∏_i κ(A_i,ρ) Θ(T;A_i,ρ)`, with `A_i = α + i`.
* **Lemma 8.15** — `chamberJFull_eq_factorial_mul_chamberI`, the `k!` symmetrization
  `J(T) = k! I(T)`.
* **Lemma A.5** — all five clauses. `chamberSeparated_of_mem_chamberOmega` and
  `chamberVandermonde_ge_prod` are clause (i); `chamberA5_vertex` and `chamberA5_lower` are
  clause (ii); `chamberA5_edge` is clause (iii), the sole source of a logarithm;
  `chamberA5_matching` is clause (iv); `chamberA5_matching_three` is clause (v), which trades
  print's threshold `T₀ = 16^{k+1}` for a smaller constant and so puts the lower bound on the
  same range `T ≥ 3` as the upper one.
* **Lemma A.3(iii)–(iv)** — `chamberMinExponent_eq_sum_min` and `chamberResonanceCount_le_one`,
  the identifications `E⋆ = ∑_i min(A_i,ρ)` and `N⋆ ∈ {1,2}` that join the two sides.
* **Corollary 8.16** — `chamberCor816`, the two-sided order of `J`.

## What is assumed

Nothing is assumed. Every statement above is proved from Mathlib; there is no axiom and no
`sorry` in this file, and no hypothesis of integrality anywhere. That last point is print's
own, made twice in Appendix A and again at Proposition 8.17: *"α is a half-integer here and ρ
need not be an integer, but neither the corollary nor anything it rests on assumes more than
`α > −1` and `ρ > 0`."* The formalization keeps that promise — `α` and `ρ` are arbitrary reals
subject only to `α > −1` and `ρ > 0` (or `ρ ≥ 0`, where that suffices).

## Two indexing conventions worth stating once

Print indexes coordinates `1 … k`; `Fin k` indexes them `0 … k-1`. So print's `A_i = α + i` is
`α + (i : ℕ) + 1` here, and print's box exponent `4^i` is `4^((i : ℕ) + 1)`. Print's `j - 1`
and `k - j` never appear: the Vandermonde exponent is `#(Finset.Iio j) = (j : ℕ)`
(`Fin.card_Iio`), and the count of large boxes is carried by the sum defining
`chamberVertexExponent` rather than by a subtraction. Print's `j*` is written `m + 1`
throughout the edge-sector material, for the same reason.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

/-- integrand -/
@[expose] public noncomputable def chamberIntegrand (T a b s : ℝ) : ℝ :=
  Real.exp (-s) * s ^ (a - 1) * (1 + T * s) ^ (-b)

/-- G -/
@[expose] public noncomputable def chamberG (T a b : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0:ℝ), chamberIntegrand T a b s

/-- Gamma_1 -/
@[expose] public noncomputable def gammaOne (a b : ℝ) : ℝ :=
  ∫ s in Set.Ioi (1:ℝ), Real.exp (-s) * s ^ (a - b - 1)

public theorem integrableOn_exp_neg_rpow {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s => Real.exp (-s) * s ^ (a - 1)) (Set.Ioi 0) := by
  simpa using Real.GammaIntegral_convergent (s := a) ha

public theorem chamberIntegrand_nonneg {T a b s : ℝ} (hT : 0 ≤ T) (hs : 0 < s) :
    0 ≤ chamberIntegrand T a b s := by
  have h1 : (0:ℝ) < 1 + T * s := by positivity
  unfold chamberIntegrand
  positivity

public theorem chamberIntegrand_le {T a b s : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) (hs : 0 < s) :
    chamberIntegrand T a b s ≤ Real.exp (-s) * s ^ (a - 1) := by
  have h1 : (1:ℝ) ≤ 1 + T * s := by nlinarith
  have h2 : (1 + T * s) ^ (-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  have h3 : (0:ℝ) ≤ Real.exp (-s) * s ^ (a - 1) := by positivity
  calc chamberIntegrand T a b s ≤ Real.exp (-s) * s ^ (a - 1) * 1 :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = Real.exp (-s) * s ^ (a - 1) := mul_one _

public theorem measurable_chamberIntegrand (T a b : ℝ) :
    Measurable (chamberIntegrand T a b) := by
  unfold chamberIntegrand
  fun_prop

public theorem integrableOn_chamberIntegrand {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    IntegrableOn (chamberIntegrand T a b) (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (integrableOn_exp_neg_rpow ha)
    (measurable_chamberIntegrand T a b).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : (0:ℝ) < s := hs
  rw [Real.norm_of_nonneg (chamberIntegrand_nonneg hT hs0)]
  exact chamberIntegrand_le hT hb hs0

/-! ### Elementary integrals of a real power on an interval -/

/-- `s ↦ s ^ r` is integrable on `Ioc u v` whenever `-1 < r`. -/
public theorem integrableOn_rpow_Ioc {u v r : ℝ} (h : -1 < r) :
    IntegrableOn (fun s : ℝ => s ^ r) (Set.Ioc u v) :=
  (intervalIntegral.intervalIntegrable_rpow' (a := u) (b := v) h).1

/-- `s ↦ s ^ r` is integrable on `Ioc u v` whenever `0 < u`; no constraint on `r`. -/
public theorem integrableOn_rpow_Ioc_of_pos {u v r : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntegrableOn (fun s : ℝ => s ^ r) (Set.Ioc u v) := by
  refine (intervalIntegral.intervalIntegrable_rpow (a := u) (b := v) (Or.inr ?_)).1
  rw [Set.uIcc_of_le huv]
  intro hmem
  exact absurd hmem.1 (by linarith)

/-- `∫_{(0,v]} s^{c-1} ds = v^c / c` for `0 < c`, `0 ≤ v`. -/
public theorem integral_rpow_Ioc_zero {v c : ℝ} (hc : 0 < c) (hv : 0 ≤ v) :
    ∫ s in Set.Ioc (0:ℝ) v, s ^ (c - 1) = v ^ c / c := by
  have hcc : c - 1 + 1 = c := by ring
  rw [← intervalIntegral.integral_of_le hv, integral_rpow (Or.inl (by linarith)), hcc,
    Real.zero_rpow hc.ne']
  ring

/-- `∫_{(u,v]} s^{c-1} ds = (v^c - u^c)/c` for `0 < u ≤ v` and `c ≠ 0`. -/
public theorem integral_rpow_Ioc_pos {u v c : ℝ} (hu : 0 < u) (huv : u ≤ v) (hc : c ≠ 0) :
    ∫ s in Set.Ioc u v, s ^ (c - 1) = (v ^ c - u ^ c) / c := by
  have hcc : c - 1 + 1 = c := by ring
  have hne : c - 1 ≠ -1 := by intro h; exact hc (by linarith)
  have hmem : (0:ℝ) ∉ Set.uIcc u v := by
    rw [Set.uIcc_of_le huv]
    intro hmem
    exact absurd hmem.1 (by linarith)
  rw [← intervalIntegral.integral_of_le huv, integral_rpow (Or.inr ⟨hne, hmem⟩), hcc]

/-- `∫_{(u,v]} s^{-1} ds = log (v/u)` for `0 < u ≤ v`: the `a = b` case of `J`. -/
public theorem integral_rpow_Ioc_log {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫ s in Set.Ioc u v, s ^ ((0:ℝ) - 1) = Real.log (v / u) := by
  have hv : (0:ℝ) < v := lt_of_lt_of_le hu huv
  rw [← intervalIntegral.integral_of_le huv, ← integral_inv_of_pos hu hv]
  refine intervalIntegral.integral_congr ?_
  intro s hs
  rw [Set.uIcc_of_le huv] at hs
  have : (0:ℝ) < s := lt_of_lt_of_le hu hs.1
  simp [Real.rpow_neg_one]

/-! ### The pointwise two-sided bounds on the factor `(1 + Ts)^{-b}` -/

/-- Small scales: for `T s ≤ 1` one has `1 ≤ 1 + Ts ≤ 2`, hence `2^{-b} ≤ (1+Ts)^{-b} ≤ 1`. -/
public theorem rpow_one_add_small {T b s : ℝ} (hT : 0 < T) (hs : 0 < s) (hb : 0 ≤ b)
    (h1 : T * s ≤ 1) :
    (2:ℝ) ^ (-b) ≤ (1 + T * s) ^ (-b) ∧ (1 + T * s) ^ (-b) ≤ 1 := by
  have hpos : (0:ℝ) < 1 + T * s := by positivity
  refine ⟨Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith), ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by linarith)

/-- Large scales: for `1 ≤ T s` one has `Ts ≤ 1 + Ts ≤ 2 Ts`, hence
`2^{-b} T^{-b} s^{-b} ≤ (1+Ts)^{-b} ≤ T^{-b} s^{-b}`. -/
public theorem rpow_one_add_large {T b s : ℝ} (hT : 0 < T) (hs : 0 < s) (hb : 0 ≤ b)
    (h1 : 1 ≤ T * s) :
    (2:ℝ) ^ (-b) * (T ^ (-b) * s ^ (-b)) ≤ (1 + T * s) ^ (-b) ∧
      (1 + T * s) ^ (-b) ≤ T ^ (-b) * s ^ (-b) := by
  have hTs : (0:ℝ) < T * s := by positivity
  have hsplit : (T * s) ^ (-b) = T ^ (-b) * s ^ (-b) := Real.mul_rpow hT.le hs.le
  have hupper : (1 + T * s) ^ (-b) ≤ T ^ (-b) * s ^ (-b) := by
    rw [← hsplit]
    exact Real.rpow_le_rpow_of_nonpos hTs (by linarith) (by linarith)
  refine ⟨?_, hupper⟩
  have h2 : (2 * (T * s)) ^ (-b) = 2 ^ (-b) * (T ^ (-b) * s ^ (-b)) := by
    rw [Real.mul_rpow (by norm_num) hTs.le, hsplit]
  rw [← h2]
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)

/-- `s^{a-1} · s^{-b} = s^{a-b-1}` for `s > 0`. -/
public theorem rpow_sub_one_mul {a b s : ℝ} (hs : 0 < s) :
    s ^ (a - 1) * s ^ (-b) = s ^ (a - b - 1) := by
  rw [← Real.rpow_add hs]
  ring_nf

/-- `(1/T)^a = T^{-a}` for `T > 0`. -/
public theorem one_div_rpow_eq {T a : ℝ} (hT : 0 < T) : (1 / T) ^ a = T ^ (-a) := by
  rw [Real.rpow_neg hT.le, one_div, Real.inv_rpow hT.le]

/-- `e^{-s} s^c` is integrable on `(1, ∞)` for **every** real `c`: the exponential beats any
power at infinity, and there is no singularity at the left endpoint. Dominate `s^c` by
`s^{max c 0}` on `s ≥ 1` and apply `Real.GammaIntegral_convergent` at `max c 0 + 1 > 0`. -/
public theorem integrableOn_exp_neg_rpow_Ioi_one (c : ℝ) :
    IntegrableOn (fun s => Real.exp (-s) * s ^ c) (Set.Ioi 1) := by
  have hd0 : (0:ℝ) ≤ max c 0 := le_max_right _ _
  have hdom : IntegrableOn (fun s => Real.exp (-s) * s ^ max c 0) (Set.Ioi 1) := by
    have h := Real.GammaIntegral_convergent (s := max c 0 + 1) (by linarith)
    simp only [add_sub_cancel_right] at h
    exact h.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  refine MeasureTheory.Integrable.mono' hdom (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : (1:ℝ) < s := hs
  have hnn : (0:ℝ) ≤ Real.exp (-s) * s ^ c := by positivity
  rw [Real.norm_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hs1.le (le_max_left _ _)) (Real.exp_pos _).le

/-- `Γ₁(a,b) = ∫₁^∞ e^{-s} s^{a-b-1} ds` is finite and strictly positive; both halves of
Lemma A.2 use it, the lower half through the constant `2^b/Γ₁`. -/
public theorem gammaOne_pos (a b : ℝ) : 0 < gammaOne a b := by
  set c : ℝ := a - b - 1 with hc
  have hint : IntegrableOn (fun s => Real.exp (-s) * s ^ c) (Set.Ioi 1) :=
    integrableOn_exp_neg_rpow_Ioi_one c
  have hsub : (∫ s in Set.Ioc (1:ℝ) 2, Real.exp (-s) * s ^ c) ≤ gammaOne a b := by
    refine setIntegral_mono_set hint ?_ Set.Ioc_subset_Ioi_self.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs1 : (1:ℝ) < s := hs
    positivity
  have hlow : Real.exp (-2) * 2 ^ min c 0 ≤ ∫ s in Set.Ioc (1:ℝ) 2, Real.exp (-s) * s ^ c := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.exp (-2) * 2 ^ min c 0) (Set.Ioc (1:ℝ) 2) := by
      exact MeasureTheory.integrableOn_const (by simp)
    have hmono : (∫ _ in Set.Ioc (1:ℝ) 2, Real.exp (-2) * 2 ^ min c 0)
        ≤ ∫ s in Set.Ioc (1:ℝ) 2, Real.exp (-s) * s ^ c := by
      refine setIntegral_mono_on hconst (hint.mono_set Set.Ioc_subset_Ioi_self)
        measurableSet_Ioc ?_
      intro s hs
      have hs1 : (1:ℝ) < s := hs.1
      have hs2 : s ≤ 2 := hs.2
      have he : Real.exp (-2) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
      have hp : (2:ℝ) ^ min c 0 ≤ s ^ c := by
        rcases le_or_gt 0 c with hc0 | hc0
        · rw [min_eq_right hc0, Real.rpow_zero]
          exact Real.one_le_rpow hs1.le hc0
        · rw [min_eq_left hc0.le]
          exact Real.rpow_le_rpow_of_nonpos (by linarith) hs2 hc0.le
      have h2 : (0:ℝ) < (2:ℝ) ^ min c 0 := Real.rpow_pos_of_pos (by norm_num) _
      exact mul_le_mul he hp h2.le (Real.exp_pos _).le
    refine le_trans (le_of_eq ?_) hmono
    rw [MeasureTheory.setIntegral_const]
    norm_num [Real.volume_real_Ioc]
  have hpos : (0:ℝ) < Real.exp (-2) * 2 ^ min c 0 := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) (min c 0)
    positivity
  linarith

/-! ### The three pieces `(0, 1/T]`, `(1/T, 1]`, `(1, ∞)` -/

/-- Crude majorant, valid on all of `(0, ∞)`: `e^{-s} ≤ 1` and `(1+Ts)^{-b} ≤ 1`. -/
public theorem chamberIntegrand_le_rpow {T a b s : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) (hs : 0 < s) :
    chamberIntegrand T a b s ≤ s ^ (a - 1) := by
  refine (chamberIntegrand_le hT hb hs).trans ?_
  have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : (0:ℝ) ≤ s ^ (a - 1) := Real.rpow_nonneg hs.le _
  nlinarith

/-- Small scales `0 < s ≤ 1/T ≤ 1`: `e^{-1} 2^{-b} s^{a-1} ≤ F(s)`. -/
public theorem chamberIntegrand_ge_small {T a b s : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hs : 0 < s)
    (hs1 : s ≤ 1 / T) (hT1 : 1 ≤ T) :
    Real.exp (-1) * 2 ^ (-b) * s ^ (a - 1) ≤ chamberIntegrand T a b s := by
  have hTs : T * s ≤ 1 := by
    rw [← le_div_iff₀' hT]
    simpa [one_div] using hs1
  have hsle1 : s ≤ 1 := le_trans hs1 (by rw [div_le_one hT]; linarith)
  have e1 : Real.exp (-1) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
  have e2 : (2:ℝ) ^ (-b) ≤ (1 + T * s) ^ (-b) := (rpow_one_add_small hT hs hb hTs).1
  have hsp : (0:ℝ) ≤ s ^ (a - 1) := Real.rpow_nonneg hs.le _
  have h2pos : (0:ℝ) < (2:ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  have hb1 : (0:ℝ) ≤ Real.exp (-s) * s ^ (a - 1) := by positivity
  unfold chamberIntegrand
  calc Real.exp (-1) * 2 ^ (-b) * s ^ (a - 1)
      = Real.exp (-1) * s ^ (a - 1) * 2 ^ (-b) := by ring
    _ ≤ Real.exp (-s) * s ^ (a - 1) * (1 + T * s) ^ (-b) :=
        mul_le_mul (mul_le_mul_of_nonneg_right e1 hsp) e2 h2pos.le hb1

/-- **(O.1) upper.** `G₀ ≤ T^{-a}/a`. -/
public theorem chamberG0_le {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ s in Set.Ioc (0:ℝ) (1 / T), chamberIntegrand T a b s) ≤ T ^ (-a) / a := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have hint : IntegrableOn (chamberIntegrand T a b) (Set.Ioc (0:ℝ) (1 / T)) :=
    (integrableOn_chamberIntegrand (T := T) (a := a) (b := b) hT0.le ha hb).mono_set
      Set.Ioc_subset_Ioi_self
  have hmono : (∫ s in Set.Ioc (0:ℝ) (1 / T), chamberIntegrand T a b s)
      ≤ ∫ s in Set.Ioc (0:ℝ) (1 / T), s ^ (a - 1) := by
    refine setIntegral_mono_on hint (integrableOn_rpow_Ioc (by linarith)) measurableSet_Ioc ?_
    intro s hs
    exact chamberIntegrand_le_rpow hT0.le hb hs.1
  rwa [integral_rpow_Ioc_zero ha hTinv.le, one_div_rpow_eq hT0] at hmono

/-- **(O.1) lower.** `e^{-1} 2^{-b} T^{-a}/a ≤ G₀`. -/
public theorem chamberG0_ge {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    Real.exp (-1) * 2 ^ (-b) * (T ^ (-a) / a)
      ≤ ∫ s in Set.Ioc (0:ℝ) (1 / T), chamberIntegrand T a b s := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have hint : IntegrableOn (chamberIntegrand T a b) (Set.Ioc (0:ℝ) (1 / T)) :=
    (integrableOn_chamberIntegrand (T := T) (a := a) (b := b) hT0.le ha hb).mono_set
      Set.Ioc_subset_Ioi_self
  have hmono : (∫ s in Set.Ioc (0:ℝ) (1 / T), Real.exp (-1) * 2 ^ (-b) * s ^ (a - 1))
      ≤ ∫ s in Set.Ioc (0:ℝ) (1 / T), chamberIntegrand T a b s := by
    refine setIntegral_mono_on
      ((integrableOn_rpow_Ioc (u := (0:ℝ)) (v := 1 / T) (by linarith)).const_mul _)
      hint measurableSet_Ioc ?_
    intro s hs
    exact chamberIntegrand_ge_small hT0 hb hs.1 hs.2 (by linarith)
  rwa [MeasureTheory.integral_const_mul, integral_rpow_Ioc_zero ha hTinv.le,
    one_div_rpow_eq hT0] at hmono

/-- Middle and far scales `T s ≥ 1`, upper half: `F(s) ≤ T^{-b} s^{a-b-1}` after `e^{-s} ≤ 1`. -/
public theorem chamberIntegrand_le_large {T a b s : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hs : 0 < s)
    (hTs : 1 ≤ T * s) :
    chamberIntegrand T a b s ≤ Real.exp (-s) * (T ^ (-b) * s ^ (a - b - 1)) := by
  have h2 : (1 + T * s) ^ (-b) ≤ T ^ (-b) * s ^ (-b) := (rpow_one_add_large hT hs hb hTs).2
  have hsp : (0:ℝ) ≤ s ^ (a - 1) := Real.rpow_nonneg hs.le _
  have hnn : (0:ℝ) ≤ (1 + T * s) ^ (-b) := Real.rpow_nonneg (by positivity) _
  have he : (0:ℝ) < Real.exp (-s) := Real.exp_pos _
  calc chamberIntegrand T a b s = Real.exp (-s) * s ^ (a - 1) * (1 + T * s) ^ (-b) := rfl
    _ ≤ Real.exp (-s) * s ^ (a - 1) * (T ^ (-b) * s ^ (-b)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp (-s) * (T ^ (-b) * (s ^ (a - 1) * s ^ (-b))) := by ring
    _ = Real.exp (-s) * (T ^ (-b) * s ^ (a - b - 1)) := by rw [rpow_sub_one_mul hs]

/-- Middle and far scales `T s ≥ 1`, lower half: `2^{-b} T^{-b} e^{-s} s^{a-b-1} ≤ F(s)`. -/
public theorem chamberIntegrand_ge_large {T a b s : ℝ} (hT : 0 < T) (hb : 0 ≤ b) (hs : 0 < s)
    (hTs : 1 ≤ T * s) :
    2 ^ (-b) * (Real.exp (-s) * (T ^ (-b) * s ^ (a - b - 1))) ≤ chamberIntegrand T a b s := by
  have h2 : (2:ℝ) ^ (-b) * (T ^ (-b) * s ^ (-b)) ≤ (1 + T * s) ^ (-b) :=
    (rpow_one_add_large hT hs hb hTs).1
  have hsp : (0:ℝ) ≤ s ^ (a - 1) := Real.rpow_nonneg hs.le _
  calc 2 ^ (-b) * (Real.exp (-s) * (T ^ (-b) * s ^ (a - b - 1)))
      = Real.exp (-s) * s ^ (a - 1) * (2 ^ (-b) * (T ^ (-b) * s ^ (-b))) := by
        rw [show a - b - 1 = (a - 1) + (-b) by ring, Real.rpow_add hs]; ring
    _ ≤ Real.exp (-s) * s ^ (a - 1) * (1 + T * s) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = chamberIntegrand T a b s := rfl

/-- `J = ∫_{1/T}^1 s^{a-b-1} ds`: the middle piece stripped of its `T^{-b}`. -/
@[expose] public noncomputable def chamberJ (T a b : ℝ) : ℝ :=
  ∫ s in Set.Ioc (1 / T) (1:ℝ), s ^ (a - b - 1)

/-- **(O.2).** `e^{-1} 2^{-b} T^{-b} J ≤ G₁ ≤ T^{-b} J`. -/
public theorem chamberG1_bounds {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    Real.exp (-1) * 2 ^ (-b) * T ^ (-b) * chamberJ T a b
        ≤ ∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s ∧
      (∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s) ≤ T ^ (-b) * chamberJ T a b := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have hTinv1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; linarith
  have hint : IntegrableOn (chamberIntegrand T a b) (Set.Ioc (1 / T) (1:ℝ)) :=
    ((integrableOn_chamberIntegrand (T := T) (a := a) (b := b) hT0.le ha hb).mono_set
      (Set.Ioi_subset_Ioi hTinv.le)).mono_set Set.Ioc_subset_Ioi_self
  have hpow : IntegrableOn (fun s : ℝ => s ^ (a - b - 1)) (Set.Ioc (1 / T) (1:ℝ)) :=
    integrableOn_rpow_Ioc_of_pos hTinv hTinv1
  have hTs : ∀ s ∈ Set.Ioc (1 / T) (1:ℝ), (0 < s ∧ 1 ≤ T * s) := by
    intro s hs
    have hs0 : (0:ℝ) < s := lt_trans hTinv hs.1
    refine ⟨hs0, ?_⟩
    have h1 : (1:ℝ) < s * T := (div_lt_iff₀ hT0).mp hs.1
    rw [mul_comm]; linarith
  constructor
  · have hmono : (∫ s in Set.Ioc (1 / T) (1:ℝ),
        Real.exp (-1) * 2 ^ (-b) * T ^ (-b) * s ^ (a - b - 1))
        ≤ ∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s := by
      refine setIntegral_mono_on (hpow.const_mul _) hint measurableSet_Ioc ?_
      intro s hs
      obtain ⟨hs0, hs1⟩ := hTs s hs
      refine le_trans ?_ (chamberIntegrand_ge_large hT0 hb hs0 hs1)
      have he : Real.exp (-1) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith [hs.2])
      have hrest : (0:ℝ) ≤ 2 ^ (-b) * (T ^ (-b) * s ^ (a - b - 1)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right he hrest]
    rwa [MeasureTheory.integral_const_mul, ← chamberJ] at hmono
  · have hmono : (∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s)
        ≤ ∫ s in Set.Ioc (1 / T) (1:ℝ), T ^ (-b) * s ^ (a - b - 1) := by
      refine setIntegral_mono_on hint (hpow.const_mul _) measurableSet_Ioc ?_
      intro s hs
      obtain ⟨hs0, hs1⟩ := hTs s hs
      refine (chamberIntegrand_le_large hT0 hb hs0 hs1).trans ?_
      have he : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have hrest : (0:ℝ) ≤ T ^ (-b) * s ^ (a - b - 1) := by positivity
      nlinarith
    rwa [MeasureTheory.integral_const_mul, ← chamberJ] at hmono

/-! ### The far region `(1, ∞)` -/

/-- **(O.3).** On `(1, ∞)` we have `Ts > T ≥ 3 > 1`, so the two-sided comparison
`2^{-b}(Ts)^{-b} ≤ (1+Ts)^{-b} ≤ (Ts)^{-b}` applies pointwise and integrates against
`Γ₁(a,b) = ∫₁^∞ e^{-s} s^{a-b-1} ds`:
`2^{-b} T^{-b} Γ₁ ≤ G₂ ≤ T^{-b} Γ₁`. -/
public theorem chamberG2_bounds {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    2 ^ (-b) * T ^ (-b) * gammaOne a b ≤ ∫ s in Set.Ioi (1:ℝ), chamberIntegrand T a b s ∧
      (∫ s in Set.Ioi (1:ℝ), chamberIntegrand T a b s) ≤ T ^ (-b) * gammaOne a b := by
  have hT0 : (0:ℝ) < T := by linarith
  have hint : IntegrableOn (chamberIntegrand T a b) (Set.Ioi (1:ℝ)) :=
    (integrableOn_chamberIntegrand (T := T) (a := a) (b := b) hT0.le ha hb).mono_set
      (Set.Ioi_subset_Ioi (by norm_num))
  have hTs : ∀ s ∈ Set.Ioi (1:ℝ), (0 < s ∧ 1 ≤ T * s) := by
    intro s hs
    have hs1 : (1:ℝ) < s := hs
    exact ⟨by linarith, by nlinarith⟩
  constructor
  · have hlow : IntegrableOn
        (fun s : ℝ => 2 ^ (-b) * T ^ (-b) * (Real.exp (-s) * s ^ (a - b - 1))) (Set.Ioi (1:ℝ)) :=
      (integrableOn_exp_neg_rpow_Ioi_one (a - b - 1)).const_mul _
    have hmono : (∫ s in Set.Ioi (1:ℝ),
        2 ^ (-b) * T ^ (-b) * (Real.exp (-s) * s ^ (a - b - 1)))
        ≤ ∫ s in Set.Ioi (1:ℝ), chamberIntegrand T a b s := by
      refine setIntegral_mono_on hlow hint measurableSet_Ioi ?_
      intro s hs
      obtain ⟨hs0, hs1⟩ := hTs s hs
      refine le_trans (le_of_eq ?_) (chamberIntegrand_ge_large hT0 hb hs0 hs1)
      ring
    rwa [MeasureTheory.integral_const_mul, ← gammaOne] at hmono
  · have hup : IntegrableOn
        (fun s : ℝ => T ^ (-b) * (Real.exp (-s) * s ^ (a - b - 1))) (Set.Ioi (1:ℝ)) :=
      (integrableOn_exp_neg_rpow_Ioi_one (a - b - 1)).const_mul _
    have hmono : (∫ s in Set.Ioi (1:ℝ), chamberIntegrand T a b s)
        ≤ ∫ s in Set.Ioi (1:ℝ), T ^ (-b) * (Real.exp (-s) * s ^ (a - b - 1)) := by
      refine setIntegral_mono_on hint hup measurableSet_Ioi ?_
      intro s hs
      obtain ⟨hs0, hs1⟩ := hTs s hs
      refine (chamberIntegrand_le_large hT0 hb hs0 hs1).trans (le_of_eq ?_)
      ring
    rwa [MeasureTheory.integral_const_mul, ← gammaOne] at hmono

/-! ### Evaluating `J` in the three regimes -/

/-- `J = (1 - T^{b-a})/(a-b)` whenever `a ≠ b`; no integrality is used, only `a - b ≠ 0`. -/
public theorem chamberJ_of_ne {T a b : ℝ} (hT : 3 ≤ T) (hab : a ≠ b) :
    chamberJ T a b = (1 - T ^ (b - a)) / (a - b) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have hTinv1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; linarith
  rw [chamberJ, integral_rpow_Ioc_pos hTinv hTinv1 (sub_ne_zero.mpr hab), Real.one_rpow,
    one_div_rpow_eq hT0, neg_sub]

/-- `J = log T` when `a = b`. **This is the source of the logarithm** in `Θ`, and hence the
only reason the multiplicity `N⋆` can exceed `1`. -/
public theorem chamberJ_of_eq {T a b : ℝ} (hT : 3 ≤ T) (hab : a = b) :
    chamberJ T a b = Real.log T := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have hTinv1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; linarith
  have hexp : a - b - 1 = (0:ℝ) - 1 := by rw [hab]; ring
  rw [chamberJ, hexp, integral_rpow_Ioc_log hTinv hTinv1, one_div_one_div]

/-- `a < b`: `0 < J ≤ T^{b-a}/(b-a)`. -/
public theorem chamberJ_le_of_lt {T a b : ℝ} (hT : 3 ≤ T) (hab : a < b) :
    chamberJ T a b ≤ T ^ (b - a) / (b - a) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hpow : (0:ℝ) < T ^ (b - a) := Real.rpow_pos_of_pos hT0 _
  have h : (1 - T ^ (b - a)) / (a - b) = (T ^ (b - a) - 1) / (b - a) := by
    rw [show (1:ℝ) - T ^ (b - a) = -(T ^ (b - a) - 1) by ring,
      show a - b = -(b - a) by ring, neg_div_neg_eq]
  rw [chamberJ_of_ne hT hab.ne, h]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `b < a`: `J ≤ 1/(a-b)`. -/
public theorem chamberJ_le_of_gt {T a b : ℝ} (hT : 3 ≤ T) (hab : b < a) :
    chamberJ T a b ≤ 1 / (a - b) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hpow : (0:ℝ) < T ^ (b - a) := Real.rpow_pos_of_pos hT0 _
  rw [chamberJ_of_ne hT hab.ne']
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-! ### Splitting `G` into its three regions -/

/-- `∫_{(0,∞)} = ∫_{(0,1/T]} + ∫_{(1/T,1]} + ∫_{(1,∞)}`. -/
public theorem chamberG_split {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    chamberG T a b = (∫ s in Set.Ioc (0:ℝ) (1 / T), chamberIntegrand T a b s)
      + (∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s)
      + ∫ s in Set.Ioi (1:ℝ), chamberIntegrand T a b s := by
  have hT0 : (0:ℝ) < T := by linarith
  have hTinv : (0:ℝ) < 1 / T := by positivity
  have hTinv1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; linarith
  have hall : IntegrableOn (chamberIntegrand T a b) (Set.Ioi (0:ℝ)) :=
    integrableOn_chamberIntegrand hT0.le ha hb
  have h1 : Set.Ioc (0:ℝ) (1 / T) ∪ Set.Ioc (1 / T) 1 = Set.Ioc (0:ℝ) 1 :=
    Set.Ioc_union_Ioc_eq_Ioc hTinv.le hTinv1
  have h2 : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hd2 : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ hx'
    exact absurd (hx' : (1:ℝ) < x) (not_lt.2 hx)
  have hd1 : Disjoint (Set.Ioc (0:ℝ) (1 / T)) (Set.Ioc (1 / T) 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ ⟨hx', -⟩
    exact absurd hx' (not_lt.2 hx)
  have hA : IntegrableOn (chamberIntegrand T a b) (Set.Ioc (0:ℝ) 1) :=
    hall.mono_set Set.Ioc_subset_Ioi_self
  have hB : IntegrableOn (chamberIntegrand T a b) (Set.Ioi (1:ℝ)) :=
    hall.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hA1 : IntegrableOn (chamberIntegrand T a b) (Set.Ioc (0:ℝ) (1 / T)) :=
    hall.mono_set Set.Ioc_subset_Ioi_self
  have hA2 : IntegrableOn (chamberIntegrand T a b) (Set.Ioc (1 / T) (1:ℝ)) :=
    hall.mono_set (fun x hx => lt_trans hTinv hx.1)
  rw [chamberG, ← h2, setIntegral_union hd2 measurableSet_Ioi hA hB, ← h1,
    setIntegral_union hd1 measurableSet_Ioc hA1 hA2]

/-! ### Lemma A.2 -/

/-- `1 ≤ log T` for `T ≥ 3`, because `e < 3`. Used to absorb `1/a + 1 + Γ₁` against `log T`
in the critical case `a = b`. -/
public theorem one_le_log_of_three_le {T : ℝ} (hT : 3 ≤ T) : 1 ≤ Real.log T := by
  have hT0 : (0:ℝ) < T := by linarith
  rw [Real.le_log_iff_exp_le hT0]
  linarith [Real.exp_one_lt_d9]

/-- `Θ(T;a,b) = T^{-min(a,b)} (log T)^{1{a=b}}`. -/
@[expose] public noncomputable def chamberTheta (T a b : ℝ) : ℝ :=
  T ^ (-min a b) * (if a = b then Real.log T else 1)

/-- The constant of Lemma A.2:
`κ = max{ 1/a + 1/|a-b| + Γ₁, 1/a + 1 + Γ₁, e·2^b·a, 2^b/Γ₁, e·2^b }`,
the term `1/|a-b|` being present only when `a ≠ b`. -/
@[expose] public noncomputable def kappaA2 (a b : ℝ) : ℝ :=
  max (max (1 / a + (if a = b then 0 else 1 / |a - b|) + gammaOne a b)
        (1 / a + 1 + gammaOne a b))
    (max (max (Real.exp 1 * 2 ^ b * a) (2 ^ b / gammaOne a b)) (Real.exp 1 * 2 ^ b))

/-- `1/a + 1/|a-b| + Γ₁ ≤ κ` (the `a ≠ b` upper constant). -/
public theorem kappaA2_ge_upper_ne (a b : ℝ) :
    1 / a + (if a = b then 0 else 1 / |a - b|) + gammaOne a b ≤ kappaA2 a b :=
  le_max_of_le_left (le_max_left _ _)

/-- `1/a + 1 + Γ₁ ≤ κ` (the `a = b` upper constant). -/
public theorem kappaA2_ge_upper_eq (a b : ℝ) : 1 / a + 1 + gammaOne a b ≤ kappaA2 a b :=
  le_max_of_le_left (le_max_right _ _)

/-- `e·2^b·a ≤ κ` (the `a < b` lower constant, coming from `G₀`). -/
public theorem kappaA2_ge_lower_small (a b : ℝ) : Real.exp 1 * 2 ^ b * a ≤ kappaA2 a b :=
  le_max_of_le_right (le_max_of_le_left (le_max_left _ _))

/-- `2^b/Γ₁ ≤ κ` (the `a > b` lower constant, coming from `G₂`). -/
public theorem kappaA2_ge_lower_far (a b : ℝ) : 2 ^ b / gammaOne a b ≤ kappaA2 a b :=
  le_max_of_le_right (le_max_of_le_left (le_max_right _ _))

/-- `e·2^b ≤ κ` (the `a = b` lower constant, coming from `G₁`). -/
public theorem kappaA2_ge_lower_mid (a b : ℝ) : Real.exp 1 * 2 ^ b ≤ kappaA2 a b :=
  le_max_of_le_right (le_max_right _ _)

/-- `0 < κ`. -/
public theorem kappaA2_pos (a b : ℝ) : 0 < kappaA2 a b := by
  have h : (0:ℝ) < Real.exp 1 * 2 ^ b := by
    have : (0:ℝ) < (2:ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  exact lt_of_lt_of_le h (kappaA2_ge_lower_mid a b)

/-- **Lemma A.2 (the one-dimensional model integral).** For real `a > 0`, real `b ≥ 0` and
`T ≥ 3`,
`κ⁻¹ Θ(T;a,b) ≤ G(T;a,b) ≤ κ Θ(T;a,b)`, with `Θ(T;a,b) = T^{-min(a,b)}(log T)^{1{a=b}}`
and `κ = max{1/a + 1/|a-b| + Γ₁, 1/a + 1 + Γ₁, e 2^b a, 2^b/Γ₁, e 2^b}`.
Nothing here is integral: `a` and `b` range over the reals. -/
public theorem chamberA2 {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    (kappaA2 a b)⁻¹ * chamberTheta T a b ≤ chamberG T a b ∧
      chamberG T a b ≤ kappaA2 a b * chamberTheta T a b := by
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hlog : (1:ℝ) ≤ Real.log T := one_le_log_of_three_le hT
  have hGam : 0 < gammaOne a b := gammaOne_pos a b
  have hE : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hP : (0:ℝ) < (2:ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) _
  have hTa : (0:ℝ) < T ^ (-a) := Real.rpow_pos_of_pos hT0 _
  have hTb : (0:ℝ) < T ^ (-b) := Real.rpow_pos_of_pos hT0 _
  have hexpneg : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h2neg : (2:ℝ) ^ (-b) = ((2:ℝ) ^ b)⁻¹ := Real.rpow_neg (by norm_num) b
  have hane : a ≠ 0 := ha.ne'
  have hsplit := chamberG_split hT ha hb
  obtain ⟨hg1l, hg1u⟩ := chamberG1_bounds hT ha hb
  obtain ⟨hg2l, hg2u⟩ := chamberG2_bounds hT ha hb
  have hg0u := chamberG0_le hT ha hb
  have hg0l := chamberG0_ge hT ha hb
  have hn0 : (0:ℝ) ≤ ∫ s in Set.Ioc (0:ℝ) (1 / T), chamberIntegrand T a b s :=
    setIntegral_nonneg measurableSet_Ioc fun _ hs => chamberIntegrand_nonneg hT0.le hs.1
  have hn1 : (0:ℝ) ≤ ∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s :=
    setIntegral_nonneg measurableSet_Ioc fun _ hs =>
      chamberIntegrand_nonneg hT0.le (lt_trans (by positivity) hs.1)
  have hn2 : (0:ℝ) ≤ ∫ s in Set.Ioi (1:ℝ), chamberIntegrand T a b s :=
    setIntegral_nonneg measurableSet_Ioi fun _ hs =>
      chamberIntegrand_nonneg hT0.le (lt_trans one_pos hs)
  rcases lt_trichotomy a b with hab | hab | hab
  · -- `a < b`: `Θ = T^{-a}`, the small region dominates.
    have hba : (0:ℝ) < b - a := by linarith
    have hbane : b - a ≠ 0 := hba.ne'
    have hth : chamberTheta T a b = T ^ (-a) := by
      rw [chamberTheta, min_eq_left hab.le, if_neg hab.ne, mul_one]
    have hmul : T ^ (-b) * T ^ (b - a) = T ^ (-a) := by
      rw [← Real.rpow_add hT0, show -b + (b - a) = -a by ring]
    have hle : T ^ (-b) ≤ T ^ (-a) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    rw [hth, hsplit]
    constructor
    · have hstep : (kappaA2 a b)⁻¹ ≤ (Real.exp 1 * 2 ^ b * a)⁻¹ :=
        inv_anti₀ (by positivity) (kappaA2_ge_lower_small a b)
      have h1 : (kappaA2 a b)⁻¹ * T ^ (-a) ≤ (Real.exp 1 * 2 ^ b * a)⁻¹ * T ^ (-a) :=
        mul_le_mul_of_nonneg_right hstep hTa.le
      have h2 : (Real.exp 1 * 2 ^ b * a)⁻¹ * T ^ (-a)
          = Real.exp (-1) * 2 ^ (-b) * (T ^ (-a) / a) := by
        rw [hexpneg, h2neg]; field_simp
      linarith
    · have hu1 : T ^ (-b) * chamberJ T a b ≤ T ^ (-a) / (b - a) := by
        calc T ^ (-b) * chamberJ T a b ≤ T ^ (-b) * (T ^ (b - a) / (b - a)) :=
              mul_le_mul_of_nonneg_left (chamberJ_le_of_lt hT hab) hTb.le
          _ = T ^ (-a) / (b - a) := by rw [← mul_div_assoc, hmul]
      have hu2 : T ^ (-b) * gammaOne a b ≤ T ^ (-a) * gammaOne a b :=
        mul_le_mul_of_nonneg_right hle hGam.le
      have hc1 : 1 / a + 1 / (b - a) + gammaOne a b ≤ kappaA2 a b := by
        have h := kappaA2_ge_upper_ne a b
        rwa [if_neg hab.ne, abs_sub_comm, abs_of_pos hba] at h
      have hfin : (1 / a + 1 / (b - a) + gammaOne a b) * T ^ (-a) ≤ kappaA2 a b * T ^ (-a) :=
        mul_le_mul_of_nonneg_right hc1 hTa.le
      have hexpand : (1 / a + 1 / (b - a) + gammaOne a b) * T ^ (-a)
          = T ^ (-a) / a + T ^ (-a) / (b - a) + T ^ (-a) * gammaOne a b := by
        field_simp
      linarith
  · -- `a = b`: `Θ = T^{-a} log T`; the middle region contributes the logarithm.
    subst hab
    have hth : chamberTheta T a a = T ^ (-a) * Real.log T := by
      rw [chamberTheta, min_self, if_pos rfl]
    have hJ : chamberJ T a a = Real.log T := chamberJ_of_eq hT rfl
    rw [hJ] at hg1l hg1u
    have hkey : T ^ (-a) ≤ T ^ (-a) * Real.log T := le_mul_of_one_le_right hTa.le hlog
    rw [hth, hsplit]
    constructor
    · have hstep : (kappaA2 a a)⁻¹ ≤ (Real.exp 1 * 2 ^ a)⁻¹ :=
        inv_anti₀ (by positivity) (kappaA2_ge_lower_mid a a)
      have h1 : (kappaA2 a a)⁻¹ * (T ^ (-a) * Real.log T)
          ≤ (Real.exp 1 * 2 ^ a)⁻¹ * (T ^ (-a) * Real.log T) :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
      have h2 : (Real.exp 1 * 2 ^ a)⁻¹ * (T ^ (-a) * Real.log T)
          = Real.exp (-1) * 2 ^ (-a) * T ^ (-a) * Real.log T := by
        rw [hexpneg, h2neg]; field_simp
      linarith
    · have hu0 : T ^ (-a) / a ≤ T ^ (-a) * Real.log T / a :=
        div_le_div_of_nonneg_right hkey ha.le
      have hu2 : T ^ (-a) * gammaOne a a ≤ T ^ (-a) * Real.log T * gammaOne a a :=
        mul_le_mul_of_nonneg_right hkey hGam.le
      have hc1 : 1 / a + 1 + gammaOne a a ≤ kappaA2 a a := kappaA2_ge_upper_eq a a
      have hfin : (1 / a + 1 + gammaOne a a) * (T ^ (-a) * Real.log T)
          ≤ kappaA2 a a * (T ^ (-a) * Real.log T) :=
        mul_le_mul_of_nonneg_right hc1 (by positivity)
      have hexpand : (1 / a + 1 + gammaOne a a) * (T ^ (-a) * Real.log T)
          = T ^ (-a) * Real.log T / a + T ^ (-a) * Real.log T
            + T ^ (-a) * Real.log T * gammaOne a a := by
        field_simp
      linarith
  · -- `b < a`: `Θ = T^{-b}`, the far region dominates.
    have hab' : (0:ℝ) < a - b := by linarith
    have habne : a - b ≠ 0 := hab'.ne'
    have hth : chamberTheta T a b = T ^ (-b) := by
      rw [chamberTheta, min_eq_right hab.le, if_neg hab.ne', mul_one]
    have hle : T ^ (-a) ≤ T ^ (-b) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    rw [hth, hsplit]
    constructor
    · have hstep : (kappaA2 a b)⁻¹ ≤ ((2:ℝ) ^ b / gammaOne a b)⁻¹ :=
        inv_anti₀ (by positivity) (kappaA2_ge_lower_far a b)
      have h1 : (kappaA2 a b)⁻¹ * T ^ (-b) ≤ ((2:ℝ) ^ b / gammaOne a b)⁻¹ * T ^ (-b) :=
        mul_le_mul_of_nonneg_right hstep hTb.le
      have h2 : ((2:ℝ) ^ b / gammaOne a b)⁻¹ * T ^ (-b)
          = 2 ^ (-b) * T ^ (-b) * gammaOne a b := by
        rw [h2neg]; field_simp
      linarith
    · have hu0 : T ^ (-a) / a ≤ T ^ (-b) / a := div_le_div_of_nonneg_right hle ha.le
      have hu1 : T ^ (-b) * chamberJ T a b ≤ T ^ (-b) / (a - b) := by
        calc T ^ (-b) * chamberJ T a b ≤ T ^ (-b) * (1 / (a - b)) :=
              mul_le_mul_of_nonneg_left (chamberJ_le_of_gt hT hab) hTb.le
          _ = T ^ (-b) / (a - b) := by rw [mul_one_div]
      have hc1 : 1 / a + 1 / (a - b) + gammaOne a b ≤ kappaA2 a b := by
        have h := kappaA2_ge_upper_ne a b
        rwa [if_neg hab.ne', abs_of_pos hab'] at h
      have hfin : (1 / a + 1 / (a - b) + gammaOne a b) * T ^ (-b) ≤ kappaA2 a b * T ^ (-b) :=
        mul_le_mul_of_nonneg_right hc1 hTb.le
      have hexpand : (1 / a + 1 / (a - b) + gammaOne a b) * T ^ (-b)
          = T ^ (-b) / a + T ^ (-b) / (a - b) + T ^ (-b) * gammaOne a b := by
        field_simp
      linarith

/-! ### Appendix A.4: the Vandermonde majorization and the product upper bound

The paper indexes the coordinates of the chamber by `1 ≤ i ≤ k`; we index them by `Fin k`, so
the paper's `s_j` is our `s j` with `j : Fin k` and the paper's `j - 1` is our `(j : ℕ)`.
No natural subtraction occurs anywhere below. -/

/-- The ordered chamber `Δ = {s ∈ ℝ^k : 0 < s₁ ≤ s₂ ≤ ⋯ ≤ s_k}` of (8.17). -/
@[expose] public def chamberDelta (k : ℕ) : Set (Fin k → ℝ) :=
  {s | (∀ i, 0 < s i) ∧ Monotone s}

public theorem mem_chamberDelta {k : ℕ} {s : Fin k → ℝ} :
    s ∈ chamberDelta k ↔ (∀ i, 0 < s i) ∧ Monotone s := Iff.rfl

/-- `Δ ⊆ (0, ∞)^k`. -/
public theorem chamberDelta_subset_pi (k : ℕ) :
    chamberDelta k ⊆ Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ) := by
  intro s hs i _
  exact (mem_chamberDelta.mp hs).1 i

public theorem measurableSet_chamberDelta (k : ℕ) : MeasurableSet (chamberDelta k) := by
  classical
  have h : chamberDelta k =
      (⋂ i : Fin k, {s : Fin k → ℝ | 0 < s i}) ∩
        ⋂ i : Fin k, ⋂ j : Fin k, {s : Fin k → ℝ | i ≤ j → s i ≤ s j} := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, mem_chamberDelta]
    exact ⟨fun h => ⟨h.1, fun i j hij => h.2 hij⟩, fun h => ⟨h.1, fun _ _ hij => h.2 _ _ hij⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · exact measurableSet_lt measurable_const (measurable_pi_apply i)
  · by_cases hij : i ≤ j
    · have hset : {s : Fin k → ℝ | i ≤ j → s i ≤ s j} = {s : Fin k → ℝ | s i ≤ s j} := by
        simp [hij]
      rw [hset]
      exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
    · simp [hij]

/-- The Vandermonde factor `∏_{1 ≤ i < j ≤ k} (s_j - s_i)` of (8.18), written as the iterated
product `∏_j ∏_{i < j} (s_j - s_i)` over `Fin k`. -/
@[expose] public noncomputable def chamberVandermonde {k : ℕ} (s : Fin k → ℝ) : ℝ :=
  ∏ j : Fin k, ∏ i ∈ Finset.Iio j, (s j - s i)

/-- **A.4, Step 1 (U.2), lower half.** `0 ≤ ∏_{i<j} (s_j - s_i)` on `Δ`. -/
public theorem chamberVandermonde_nonneg {k : ℕ} {s : Fin k → ℝ} (hs : s ∈ chamberDelta k) :
    0 ≤ chamberVandermonde s :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ hi =>
    sub_nonneg.2 ((mem_chamberDelta.mp hs).2 (Finset.mem_Iio.mp hi).le)

/-- **A.4, Step 1 (U.2), upper half.** For `s ∈ Δ` and `i < j` one has `0 ≤ s_j - s_i ≤ s_j`,
so `∏_{i<j} (s_j - s_i) ≤ ∏_j s_j^{j-1}`, "each factor `s_j` being counted once for each of the
`j - 1` indices `i < j`". In the `Fin k` indexing the count is `#(Finset.Iio j) = (j : ℕ)`, a
natural number exponent, and the paper's `j - 1` never has to be formed. -/
public theorem chamberVandermonde_le_prod {k : ℕ} {s : Fin k → ℝ} (hs : s ∈ chamberDelta k) :
    chamberVandermonde s ≤ ∏ j : Fin k, s j ^ (j : ℕ) := by
  refine Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ hi =>
    sub_nonneg.2 ((mem_chamberDelta.mp hs).2 (Finset.mem_Iio.mp hi).le)) fun j _ => ?_
  calc ∏ i ∈ Finset.Iio j, (s j - s i) ≤ ∏ _i ∈ Finset.Iio j, s j :=
        Finset.prod_le_prod
          (fun _ hi => sub_nonneg.2 ((mem_chamberDelta.mp hs).2 (Finset.mem_Iio.mp hi).le))
          (fun i _ => by linarith [(mem_chamberDelta.mp hs).1 i])
    _ = s j ^ (j : ℕ) := by rw [Finset.prod_const, Fin.card_Iio]

/-! ### A.4 Steps 1-3: the product upper bound

`A_i = α + i` of Lemma A.4 is `α + (i : ℕ) + 1` in the `Fin k` indexing, and the majorant
`g_i(s) = e^{-s} s^{A_i - 1}(1 + Ts)^{-ρ}` is `chamberIntegrand T (α + i + 1) ρ`. -/

/-- `F_T` of (8.18):
`F_T(s) = e^{-∑ s_i} ∏_i s_i^α ∏_{i<j}(s_j - s_i) ∏_i (1 + T s_i)^{-ρ}`. -/
@[expose] public noncomputable def chamberFT (k : ℕ) (T α ρ : ℝ) (s : Fin k → ℝ) : ℝ :=
  Real.exp (-∑ i, s i) * (∏ i, s i ^ α) * chamberVandermonde s * ∏ i, (1 + T * s i) ^ (-ρ)

/-- `I(T) = ∫_Δ F_T(s) ds` of (8.18). -/
@[expose] public noncomputable def chamberI (k : ℕ) (T α ρ : ℝ) : ℝ :=
  ∫ s in chamberDelta k, chamberFT k T α ρ s

/-- `0 < A_i = α + i` whenever `α > -1`; this is the only place `α > -1` is used, and it is
used exactly as the paper uses it (`A_i ≥ α + 1 > 0`). -/
public theorem chamberIndex_pos {k : ℕ} {α : ℝ} (hα : -1 < α) (i : Fin k) :
    0 < α + (i : ℕ) + 1 := by
  have : (0:ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

public theorem measurable_chamberFT (k : ℕ) (T α ρ : ℝ) : Measurable (chamberFT k T α ρ) := by
  unfold chamberFT chamberVandermonde
  fun_prop

public theorem chamberFT_nonneg {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) {s : Fin k → ℝ}
    (hs : s ∈ chamberDelta k) : 0 ≤ chamberFT k T α ρ s := by
  have hpos : ∀ i : Fin k, 0 < s i := (mem_chamberDelta.mp hs).1
  have h1 : (0:ℝ) ≤ ∏ i : Fin k, s i ^ α :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpos i).le _
  have h2 : (0:ℝ) ≤ ∏ i : Fin k, (1 + T * s i) ^ (-ρ) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by nlinarith [hpos i]) _
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le h1)
    (chamberVandermonde_nonneg hs)) h2

/-- **A.4, Step 1 (U.3).** Pointwise on `Δ`,
`0 ≤ F_T(s) ≤ ∏_i [e^{-s_i} s_i^α s_i^{i-1} (1 + T s_i)^{-ρ}] = ∏_i g_i(s_i)`.
The only inequality used is the Vandermonde majorization (U.2); every other factor of `F_T`
is already a product over the coordinates. -/
public theorem chamberFT_le_prod {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) {s : Fin k → ℝ}
    (hs : s ∈ chamberDelta k) :
    chamberFT k T α ρ s ≤ ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i) := by
  have hpos : ∀ i : Fin k, 0 < s i := (mem_chamberDelta.mp hs).1
  have hexp : Real.exp (-∑ i, s i) = ∏ i : Fin k, Real.exp (-s i) := by
    rw [← Real.exp_sum]
    congr 1
    simp
  have hterm : ∀ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i)
      = Real.exp (-s i) * (s i ^ α * s i ^ (i : ℕ)) * (1 + T * s i) ^ (-ρ) := by
    intro i
    have h1 : s i ^ (α + ((i : ℕ) : ℝ) + 1 - 1) = s i ^ α * s i ^ ((i : ℕ) : ℝ) := by
      rw [show α + ((i : ℕ) : ℝ) + 1 - 1 = α + ((i : ℕ) : ℝ) by ring, Real.rpow_add (hpos i)]
    simp only [chamberIntegrand]
    rw [h1, Real.rpow_natCast]
  have hprod : (∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i))
      = (∏ i : Fin k, Real.exp (-s i))
        * ((∏ i : Fin k, s i ^ α) * ∏ i : Fin k, s i ^ (i : ℕ))
        * ∏ i : Fin k, (1 + T * s i) ^ (-ρ) := by
    simp only [hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hP : (0:ℝ) ≤ ∏ i : Fin k, Real.exp (-s i) :=
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hQ : (0:ℝ) ≤ ∏ i : Fin k, s i ^ α :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpos i).le _
  have hR : (0:ℝ) ≤ ∏ i : Fin k, (1 + T * s i) ^ (-ρ) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by nlinarith [hpos i]) _
  rw [chamberFT, hexp, hprod]
  refine mul_le_mul_of_nonneg_right ?_ hR
  calc (∏ i : Fin k, Real.exp (-s i)) * (∏ i : Fin k, s i ^ α) * chamberVandermonde s
      ≤ (∏ i : Fin k, Real.exp (-s i)) * (∏ i : Fin k, s i ^ α)
          * ∏ j : Fin k, s j ^ (j : ℕ) :=
        mul_le_mul_of_nonneg_left (chamberVandermonde_le_prod hs) (mul_nonneg hP hQ)
    _ = _ := by ring

/-- The majorant `s ↦ ∏_i g_i(s_i)` is integrable on `(0, ∞)^k`: each `g_i` is integrable on
`(0, ∞)` by the one-dimensional theory, and a product of one-variable integrable functions is
integrable for the product measure. -/
public theorem integrableOn_prod_chamberIntegrand {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T)
    (hα : -1 < α) (hρ : 0 ≤ ρ) :
    IntegrableOn (fun s : Fin k → ℝ => ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i))
      (Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ)) := by
  have hg : ∀ i : Fin k, Integrable (chamberIntegrand T (α + (i : ℕ) + 1) ρ)
      (volume.restrict (Set.Ioi (0:ℝ))) := fun i =>
    integrableOn_chamberIntegrand hT (chamberIndex_pos hα i) hρ
  rw [IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod hg

/-- `F_T` is integrable on `Δ`, dominated by the majorant of (U.3). -/
public theorem integrableOn_chamberFT {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) (hα : -1 < α)
    (hρ : 0 ≤ ρ) : IntegrableOn (chamberFT k T α ρ) (chamberDelta k) := by
  refine MeasureTheory.Integrable.mono'
    ((integrableOn_prod_chamberIntegrand hT hα hρ).mono_set (chamberDelta_subset_pi k))
    (measurable_chamberFT k T α ρ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_chamberDelta k)] with s hs
  rw [Real.norm_of_nonneg (chamberFT_nonneg hT hs)]
  exact chamberFT_le_prod hT hs

/-- **A.4, Step 2 (U.4).** `Δ ⊆ (0,∞)^k` and the majorant of (U.3) is nonnegative and
integrable there, so
`I(T) ≤ ∫_{(0,∞)^k} ∏_i g_i(s_i) ds = ∏_i G(T; A_i, ρ)`.
In particular `I(T) < ∞` (`integrableOn_chamberFT`). -/
public theorem chamberI_le_prod_chamberG {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) (hα : -1 < α)
    (hρ : 0 ≤ ρ) :
    chamberI k T α ρ ≤ ∏ i : Fin k, chamberG T (α + (i : ℕ) + 1) ρ := by
  have hmaj := integrableOn_prod_chamberIntegrand (k := k) hT hα hρ
  calc chamberI k T α ρ
      ≤ ∫ s in chamberDelta k, ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i) := by
        refine setIntegral_mono_on (integrableOn_chamberFT hT hα hρ)
          (hmaj.mono_set (chamberDelta_subset_pi k)) (measurableSet_chamberDelta k) ?_
        intro s hs
        exact chamberFT_le_prod hT hs
    _ ≤ ∫ s in Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ),
          ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i) := by
        refine setIntegral_mono_set hmaj ?_ (chamberDelta_subset_pi k).eventuallyLE
        filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)]
          with s hs
        exact Finset.prod_nonneg fun i _ => chamberIntegrand_nonneg hT (hs i (Set.mem_univ i))
    _ = ∏ i : Fin k, chamberG T (α + (i : ℕ) + 1) ρ := by
        rw [volume_pi, Measure.restrict_pi_pi, MeasureTheory.integral_fintype_prod_eq_prod]
        rfl

/-- `0 ≤ G(T; a, b)`. -/
public theorem chamberG_nonneg {T a b : ℝ} (hT : 0 ≤ T) : 0 ≤ chamberG T a b :=
  setIntegral_nonneg measurableSet_Ioi fun _ hs => chamberIntegrand_nonneg hT hs

/-- **A.4, Step 3.** Lemma A.2 applies to every factor, since `A_i = α + i > 0` and `ρ ≥ 0`:
`∏_i G_i(T) ≤ ∏_i κ(A_i, ρ) Θ(T; A_i, ρ)`. -/
public theorem prod_chamberG_le {k : ℕ} {T α ρ : ℝ} (hT : 3 ≤ T) (hα : -1 < α) (hρ : 0 ≤ ρ) :
    (∏ i : Fin k, chamberG T (α + (i : ℕ) + 1) ρ)
      ≤ ∏ i : Fin k, kappaA2 (α + (i : ℕ) + 1) ρ * chamberTheta T (α + (i : ℕ) + 1) ρ :=
  Finset.prod_le_prod (fun _ _ => chamberG_nonneg (by linarith))
    fun i _ => (chamberA2 hT (chamberIndex_pos hα i) hρ).2

/-- **Lemma A.4, (U.1), in the factored form.** For `k ≥ 1` an integer, `α > -1` and `ρ ≥ 0`
real and `T ≥ 3`,
`I(T) ≤ ∏_i G(T; A_i, ρ) ≤ ∏_i κ(A_i, ρ) Θ(T; A_i, ρ)`, `A_i = α + i`.
The paper's `C₊ T^{-E⋆}(log T)^{N⋆-1}` is this product after Lemma A.3 evaluates
`∑_i min(A_i, ρ)` and `#{i : A_i = ρ}`; that evaluation is `chamberA4_upper_eval` below, via
`prod_chamberTheta` and `chamberMinExponent_eq_sum_min`. The further identification of this
exponent with the O70 rank-table cost is
`AISafetyAtlas.Conjectures.MAIS.chamberExponentNum_eq_residualCost` together with
`residualMinCost_eq_argmin` and `residualMultiplicity_le_two` of `Conjectures/MAIS/O70.lean`,
and is not repeated here. -/
public theorem chamberA4_upper {k : ℕ} {T α ρ : ℝ} (hT : 3 ≤ T) (hα : -1 < α) (hρ : 0 ≤ ρ) :
    chamberI k T α ρ
      ≤ ∏ i : Fin k, kappaA2 (α + (i : ℕ) + 1) ρ * chamberTheta T (α + (i : ℕ) + 1) ρ :=
  le_trans (chamberI_le_prod_chamberG (by linarith) hα hρ) (prod_chamberG_le hT hα hρ)

/-! ### Lemma 8.15: the `k!` symmetrization

`Φ_T` of Definition 8.12 differs from `F_T` of (8.18) only in carrying `|s_i - s_j|` where
`F_T` carries the signed `s_j - s_i`; the two agree on the ordered chamber. The chamber is a
fundamental domain for the action of `S_k` on `(0, ∞)^k` by permutation of coordinates, the
diagonal is Lebesgue null, and each permutation preserves Lebesgue measure, so
`J(T) = k! · I(T)`. -/

/-- The open chamber `{s : 0 < s₁ < s₂ < ⋯ < s_k}`. -/
@[expose] public def chamberDeltaStrict (k : ℕ) : Set (Fin k → ℝ) :=
  {s | (∀ i, 0 < s i) ∧ StrictMono s}

public theorem mem_chamberDeltaStrict {k : ℕ} {s : Fin k → ℝ} :
    s ∈ chamberDeltaStrict k ↔ (∀ i, 0 < s i) ∧ StrictMono s := Iff.rfl

/-- `Δ_σ = {s ∈ (0,∞)^k : s_{σ(1)} < ⋯ < s_{σ(k)}}`, the image of the open chamber under `σ`. -/
@[expose] public def chamberDeltaPerm (k : ℕ) (σ : Equiv.Perm (Fin k)) : Set (Fin k → ℝ) :=
  (fun s : Fin k → ℝ => s ∘ σ) ⁻¹' chamberDeltaStrict k

public theorem mem_chamberDeltaPerm {k : ℕ} {σ : Equiv.Perm (Fin k)} {s : Fin k → ℝ} :
    s ∈ chamberDeltaPerm k σ ↔ (∀ i, 0 < s i) ∧ StrictMono (s ∘ σ) := by
  constructor
  · rintro ⟨hpos, hmono⟩
    exact ⟨fun i => by simpa using hpos (σ.symm i), hmono⟩
  · rintro ⟨hpos, hmono⟩
    exact ⟨fun i => hpos (σ i), hmono⟩

public theorem chamberDeltaPerm_one (k : ℕ) :
    chamberDeltaPerm k 1 = chamberDeltaStrict k := by
  ext s
  simp [mem_chamberDeltaPerm, mem_chamberDeltaStrict]

public theorem chamberDeltaStrict_subset (k : ℕ) : chamberDeltaStrict k ⊆ chamberDelta k :=
  fun _ hs => ⟨hs.1, hs.2.monotone⟩

public theorem chamberDeltaPerm_subset_pi (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    chamberDeltaPerm k σ ⊆ Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ) :=
  fun _ hs i _ => (mem_chamberDeltaPerm.mp hs).1 i

public theorem measurableSet_chamberDeltaStrict (k : ℕ) :
    MeasurableSet (chamberDeltaStrict k) := by
  classical
  have h : chamberDeltaStrict k =
      (⋂ i : Fin k, {s : Fin k → ℝ | 0 < s i}) ∩
        ⋂ i : Fin k, ⋂ j : Fin k, {s : Fin k → ℝ | i < j → s i < s j} := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, mem_chamberDeltaStrict]
    exact ⟨fun h => ⟨h.1, fun i j hij => h.2 hij⟩, fun h => ⟨h.1, fun _ _ hij => h.2 _ _ hij⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · exact measurableSet_lt measurable_const (measurable_pi_apply i)
  · by_cases hij : i < j
    · have hset : {s : Fin k → ℝ | i < j → s i < s j} = {s : Fin k → ℝ | s i < s j} := by
        simp [hij]
      rw [hset]
      exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    · simp [hij]

public theorem measurableSet_chamberDeltaPerm (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    MeasurableSet (chamberDeltaPerm k σ) :=
  (measurableSet_chamberDeltaStrict k).preimage (measurable_pi_lambda _ fun i =>
    measurable_pi_apply (σ i))

/-- The diagonal `Ξ = {s ∈ ℝ^k : s_i = s_j for some i ≠ j}`. -/
@[expose] public def chamberDiag (k : ℕ) : Set (Fin k → ℝ) :=
  ⋃ i : Fin k, ⋃ j : Fin k, ⋃ _ : i ≠ j, {s : Fin k → ℝ | s i = s j}

/-- Each hyperplane `{s_i = s_j}`, `i ≠ j`, is a proper linear subspace of `ℝ^k`, hence null
for the Haar measure `volume`. -/
public theorem volume_hyperplane_eq_zero {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    (volume : Measure (Fin k → ℝ)) {s | s i = s j} = 0 := by
  classical
  set f : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i
      - LinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j with hf
  have hset : {s : Fin k → ℝ | s i = s j} = (LinearMap.ker f : Set (Fin k → ℝ)) := by
    ext s
    simp [hf, LinearMap.mem_ker, sub_eq_zero]
  have hne : LinearMap.ker f ≠ ⊤ := by
    intro h
    have hm : (Pi.single i (1:ℝ)) ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simp [hf, LinearMap.mem_ker, Ne.symm hij] at hm
  rw [hset]
  exact Measure.addHaar_submodule _ _ hne

/-- **The diagonal is null.** "`Ξ` is a finite union of intersections of `(0,∞)^k` with
hyperplanes, hence Lebesgue null." -/
public theorem volume_chamberDiag (k : ℕ) : (volume : Measure (Fin k → ℝ)) (chamberDiag k) = 0 := by
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  exact volume_hyperplane_eq_zero hij

/-- The `|s_j - s_i|` form of the Vandermonde factor, as it appears in Definition 8.12. -/
@[expose] public noncomputable def chamberAbsVandermonde {k : ℕ} (s : Fin k → ℝ) : ℝ :=
  ∏ j : Fin k, ∏ i ∈ Finset.Iio j, |s j - s i|

public theorem chamberAbsVandermonde_eq_abs {k : ℕ} (s : Fin k → ℝ) :
    chamberAbsVandermonde s = |chamberVandermonde s| := by
  rw [chamberAbsVandermonde, chamberVandermonde, Finset.abs_prod]
  exact Finset.prod_congr rfl fun j _ => (Finset.abs_prod _ _).symm

/-- The signed Vandermonde factor is the Vandermonde determinant of Mathlib. -/
public theorem chamberVandermonde_eq_det {k : ℕ} (s : Fin k → ℝ) :
    chamberVandermonde s = (Matrix.vandermonde s).det := by
  rw [Matrix.det_vandermonde, chamberVandermonde]
  refine (Finset.prod_comm' ?_).symm
  intro i j
  simp [Finset.mem_Ioi, Finset.mem_Iio]

/-- `∏_{i<j} |s_i - s_j|` "is a product over the unordered pairs `{i, j}` of a quantity that
depends only on the unordered pair, while `σ` merely permutes those pairs": permuting the
coordinates permutes the rows of the Vandermonde matrix, which changes its determinant only
by the sign of `σ`. -/
public theorem chamberAbsVandermonde_comp {k : ℕ} (s : Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    chamberAbsVandermonde (s ∘ σ) = chamberAbsVandermonde s := by
  rw [chamberAbsVandermonde_eq_abs, chamberAbsVandermonde_eq_abs, chamberVandermonde_eq_det,
    chamberVandermonde_eq_det]
  have h : Matrix.vandermonde (s ∘ σ) = (Matrix.vandermonde s).submatrix (⇑σ) id := by
    ext i j
    simp [Matrix.vandermonde]
  have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [h, Matrix.det_permute, abs_mul, hsign, one_mul]

/-- `Φ_T` of Definition 8.12:
`Φ_T(s) = ∏_i s_i^α ∏_{i<j}|s_i - s_j| e^{-∑ s_i} ∏_i (1 + T s_i)^{-ρ}`. -/
@[expose] public noncomputable def chamberPhiT (k : ℕ) (T α ρ : ℝ) (s : Fin k → ℝ) : ℝ :=
  Real.exp (-∑ i, s i) * (∏ i, s i ^ α) * chamberAbsVandermonde s * ∏ i, (1 + T * s i) ^ (-ρ)

/-- `J(T) = ∫_{(0,∞)^k} Φ_T(s) ds` of Definition 8.12. -/
@[expose] public noncomputable def chamberJFull (k : ℕ) (T α ρ : ℝ) : ℝ :=
  ∫ s in Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ), chamberPhiT k T α ρ s

/-- **Lemma 8.15, symmetry.** `Φ_T(σ s) = Φ_T(s)` for every `σ ∈ S_k`. -/
public theorem chamberPhiT_comp_perm {k : ℕ} (T α ρ : ℝ) (s : Fin k → ℝ)
    (σ : Equiv.Perm (Fin k)) : chamberPhiT k T α ρ (s ∘ σ) = chamberPhiT k T α ρ s := by
  have h1 : ∑ i, (s ∘ σ) i = ∑ i, s i := by
    simpa [Function.comp_apply] using Equiv.sum_comp σ s
  have h2 : (∏ i, (s ∘ σ) i ^ α) = ∏ i, s i ^ α := by
    simpa [Function.comp_apply] using Equiv.prod_comp σ fun x => s x ^ α
  have h3 : (∏ i, (1 + T * (s ∘ σ) i) ^ (-ρ)) = ∏ i, (1 + T * s i) ^ (-ρ) := by
    simpa [Function.comp_apply] using Equiv.prod_comp σ fun x => (1 + T * s x) ^ (-ρ)
  rw [chamberPhiT, chamberPhiT, h1, h2, h3, chamberAbsVandermonde_comp]

/-- **Lemma 8.15, agreement on the chamber.** "If `s ∈ Δ` and `i < j` then `s_i ≤ s_j`, so
`|s_i - s_j| = s_j - s_i` and every other factor is literally the same." -/
public theorem chamberPhiT_eq_chamberFT {k : ℕ} (T α ρ : ℝ) {s : Fin k → ℝ}
    (hs : s ∈ chamberDelta k) : chamberPhiT k T α ρ s = chamberFT k T α ρ s := by
  have h : chamberAbsVandermonde s = chamberVandermonde s := by
    simp only [chamberAbsVandermonde, chamberVandermonde]
    exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i hi =>
      abs_of_nonneg (sub_nonneg.2 ((mem_chamberDelta.mp hs).2 (Finset.mem_Iio.mp hi).le))
  rw [chamberPhiT, chamberFT, h]

public theorem measurable_chamberPhiT (k : ℕ) (T α ρ : ℝ) : Measurable (chamberPhiT k T α ρ) := by
  unfold chamberPhiT chamberAbsVandermonde
  fun_prop

/-- The coordinate permutation `s ↦ s ∘ σ` is the measurable equivalence
`MeasurableEquiv.piCongrLeft` at `σ⁻¹`. -/
public theorem coe_piCongrLeft_perm (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) σ.symm)
      = fun s : Fin k → ℝ => s ∘ σ := by
  funext t i
  rw [MeasurableEquiv.coe_piCongrLeft]
  simpa using Equiv.piCongrLeft_apply_apply (fun _ : Fin k => ℝ) σ.symm t (σ i)

/-- "Each permutation is measure-preserving with `|det| = 1`." -/
public theorem measurePreserving_comp_perm (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    MeasurePreserving (fun s : Fin k → ℝ => s ∘ σ) volume volume := by
  rw [← coe_piCongrLeft_perm k σ]
  exact MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin k => ℝ) σ.symm

public theorem measurableEmbedding_comp_perm (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    MeasurableEmbedding (fun s : Fin k → ℝ => s ∘ σ) := by
  rw [← coe_piCongrLeft_perm k σ]
  exact (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) σ.symm).measurableEmbedding

public theorem injective_of_mem_chamberDeltaPerm {k : ℕ} {σ : Equiv.Perm (Fin k)}
    {s : Fin k → ℝ} (hs : s ∈ chamberDeltaPerm k σ) : Function.Injective s := by
  have h : Function.Injective (s ∘ σ) := (mem_chamberDeltaPerm.mp hs).2.injective
  intro a b hab
  have hab' : (s ∘ σ) (σ.symm a) = (s ∘ σ) (σ.symm b) := by simpa using hab
  simpa using h hab'

public theorem notMem_chamberDiag_of_injective {k : ℕ} {s : Fin k → ℝ}
    (hinj : Function.Injective s) : s ∉ chamberDiag k := by
  intro hmem
  simp only [chamberDiag, Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
  obtain ⟨i, j, hij, h⟩ := hmem
  exact hij (hinj h)

public theorem injective_of_notMem_chamberDiag {k : ℕ} {s : Fin k → ℝ}
    (hs : s ∉ chamberDiag k) : Function.Injective s := by
  intro a b hab
  by_contra hne
  refine hs ?_
  simp only [chamberDiag, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨a, b, hne, hab⟩

/-- **Lemma 8.15, the chamber is a fundamental domain.** "A point `s ∉ Ξ` has pairwise distinct
coordinates, so exactly one `σ` sorts them increasingly; thus the `Δ_σ` are pairwise disjoint and
their union is `(0,∞)^k \ Ξ`." This is the existence half. -/
public theorem iUnion_chamberDeltaPerm (k : ℕ) :
    (⋃ σ : Equiv.Perm (Fin k), chamberDeltaPerm k σ)
      = (Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ)) \ chamberDiag k := by
  ext s
  constructor
  · intro hs
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hs
    exact ⟨fun i _ => (mem_chamberDeltaPerm.mp hσ).1 i,
      notMem_chamberDiag_of_injective (injective_of_mem_chamberDeltaPerm hσ)⟩
  · rintro ⟨hpi, hdiag⟩
    have hpos : ∀ i, 0 < s i := fun i => hpi i (Set.mem_univ i)
    have hinj : Function.Injective s := injective_of_notMem_chamberDiag hdiag
    refine Set.mem_iUnion.mpr ⟨Tuple.sort s, mem_chamberDeltaPerm.mpr ⟨hpos, ?_⟩⟩
    exact (Tuple.monotone_sort s).strictMono_of_injective (hinj.comp (Tuple.sort s).injective)

/-- The uniqueness half: distinct permutations give disjoint chambers. -/
public theorem pairwise_disjoint_chamberDeltaPerm (k : ℕ) :
    Pairwise (Function.onFun Disjoint (chamberDeltaPerm k)) := by
  intro σ τ hστ
  rw [Function.onFun, Set.disjoint_left]
  intro s hσ hτ
  have hinj : Function.Injective s := injective_of_mem_chamberDeltaPerm hσ
  have heq : s ∘ σ = s ∘ τ :=
    Tuple.unique_monotone (mem_chamberDeltaPerm.mp hσ).2.monotone
      (mem_chamberDeltaPerm.mp hτ).2.monotone
  exact hστ (Equiv.ext fun i => hinj (congrFun heq i))

/-- `(0,∞)^k` and `⋃_σ Δ_σ` differ by the null set `Ξ`. -/
public theorem pi_ae_eq_iUnion_chamberDeltaPerm (k : ℕ) :
    (Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ))
      =ᵐ[volume] ⋃ σ : Equiv.Perm (Fin k), chamberDeltaPerm k σ := by
  rw [MeasureTheory.ae_eq_set, iUnion_chamberDeltaPerm]
  refine ⟨?_, ?_⟩
  · rw [Set.sdiff_sdiff_right_self]
    exact measure_mono_null Set.inter_subset_right (volume_chamberDiag k)
  · rw [Set.sdiff_eq_empty.mpr Set.sdiff_subset, measure_empty]

/-- The closed and the open chamber differ by the null set `Ξ`. -/
public theorem chamberDelta_ae_eq_strict (k : ℕ) :
    chamberDelta k =ᵐ[volume] chamberDeltaStrict k := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨measure_mono_null ?_ (volume_chamberDiag k), ?_⟩
  · rintro s ⟨hs, hns⟩
    by_contra hdiag
    exact hns ⟨(mem_chamberDelta.mp hs).1,
      (mem_chamberDelta.mp hs).2.strictMono_of_injective (injective_of_notMem_chamberDiag hdiag)⟩
  · rw [Set.sdiff_eq_empty.mpr (chamberDeltaStrict_subset k), measure_empty]

public theorem integrableOn_chamberPhiT_strict {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) (hα : -1 < α)
    (hρ : 0 ≤ ρ) : IntegrableOn (chamberPhiT k T α ρ) (chamberDeltaStrict k) :=
  ((integrableOn_chamberFT hT hα hρ).mono_set (chamberDeltaStrict_subset k)).congr_fun
    (fun _s hs => (chamberPhiT_eq_chamberFT T α ρ (chamberDeltaStrict_subset k hs)).symm)
    (measurableSet_chamberDeltaStrict k)

public theorem integrableOn_chamberPhiT_perm {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) (hα : -1 < α)
    (hρ : 0 ≤ ρ) (σ : Equiv.Perm (Fin k)) :
    IntegrableOn (chamberPhiT k T α ρ) (chamberDeltaPerm k σ) := by
  have hcomp : chamberPhiT k T α ρ ∘ (fun s : Fin k → ℝ => s ∘ σ) = chamberPhiT k T α ρ :=
    funext fun s => chamberPhiT_comp_perm T α ρ s σ
  have h := (measurePreserving_comp_perm k σ).integrableOn_comp_preimage
    (measurableEmbedding_comp_perm k σ) (f := chamberPhiT k T α ρ) (s := chamberDeltaStrict k)
  rw [hcomp] at h
  exact h.mpr (integrableOn_chamberPhiT_strict hT hα hρ)

/-- Each permuted chamber carries the same integral, because `Φ_T` is symmetric and the
permutation preserves Lebesgue measure. -/
public theorem setIntegral_chamberPhiT_perm {k : ℕ} (T α ρ : ℝ) (σ : Equiv.Perm (Fin k)) :
    (∫ s in chamberDeltaPerm k σ, chamberPhiT k T α ρ s)
      = ∫ s in chamberDeltaStrict k, chamberPhiT k T α ρ s := by
  have h := (measurePreserving_comp_perm k σ).setIntegral_preimage_emb
    (measurableEmbedding_comp_perm k σ) (chamberPhiT k T α ρ) (chamberDeltaStrict k)
  rw [← h]
  exact setIntegral_congr_fun (measurableSet_chamberDeltaPerm k σ)
    fun x _ => (chamberPhiT_comp_perm T α ρ x σ).symm

/-- **Lemma 8.15 (Symmetrization).** For `k ≥ 1` an integer, `α > -1` and `ρ ≥ 0` real and
`T ≥ 0`: `Φ_T` is invariant under permutations of the coordinates of `s`, it agrees with `F_T`
on `Δ`, and `J(T) = k! · I(T)`, both sides being finite. -/
public theorem chamberJFull_eq_factorial_mul_chamberI {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T)
    (hα : -1 < α) (hρ : 0 ≤ ρ) :
    chamberJFull k T α ρ = (Nat.factorial k : ℝ) * chamberI k T α ρ := by
  have hunion : IntegrableOn (chamberPhiT k T α ρ)
      (⋃ σ : Equiv.Perm (Fin k), chamberDeltaPerm k σ) :=
    integrableOn_finite_iUnion.mpr fun σ => integrableOn_chamberPhiT_perm hT hα hρ σ
  have hIstrict : (∫ s in chamberDeltaStrict k, chamberPhiT k T α ρ s) = chamberI k T α ρ := by
    rw [chamberI,
      ← setIntegral_congr_set (f := chamberPhiT k T α ρ) (chamberDelta_ae_eq_strict k)]
    exact setIntegral_congr_fun (measurableSet_chamberDelta k)
      fun s hs => chamberPhiT_eq_chamberFT T α ρ hs
  calc chamberJFull k T α ρ
      = ∫ s in ⋃ σ : Equiv.Perm (Fin k), chamberDeltaPerm k σ, chamberPhiT k T α ρ s := by
        rw [chamberJFull, setIntegral_congr_set (pi_ae_eq_iUnion_chamberDeltaPerm k)]
    _ = ∑' σ : Equiv.Perm (Fin k), ∫ s in chamberDeltaPerm k σ, chamberPhiT k T α ρ s :=
        integral_iUnion (measurableSet_chamberDeltaPerm k)
          (pairwise_disjoint_chamberDeltaPerm k) hunion
    _ = ∑ _σ : Equiv.Perm (Fin k), ∫ s in chamberDeltaStrict k, chamberPhiT k T α ρ s := by
        rw [tsum_fintype]
        exact Finset.sum_congr rfl fun σ _ => setIntegral_chamberPhiT_perm T α ρ σ
    _ = (Nat.factorial k : ℝ) * chamberI k T α ρ := by
        rw [Finset.sum_const, hIstrict, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]

/-! ### Lemma A.2, the localized lower bounds (i), (ii), (iii)

Lemma A.5 feeds not on the two-sided bound of Lemma A.2 but on its three *localized* clauses.
For any constant `c ≥ 1`:

* **(i)** if `T ≥ 2c` then `∫_{c/T}^{2c/T} e^{-s} s^{a-1} (1+Ts)^{-b} ds ≥ η₁ T^{-a}`, where
  `η₁ = e^{-1}(1+2c)^{-b} c^a min(1, 2^{a-1}) > 0`;
* **(ii)** `∫_c^{2c} e^{-s} s^{a-1} (1+Ts)^{-b} ds ≥ η₂ T^{-b}`, where
  `η₂ = e^{-2c} c^a min(1, 2^{a-1}) (4c)^{-b} > 0`;
* **(iii)** if `a = b` and `T ≥ c²` then
  `∫_{c/T}^1 e^{-s} s^{a-1} (1+Ts)^{-b} ds ≥ ½ e^{-1} 2^{-b} T^{-b} log T`.

All constants depend only on `(a, b, c)` and not on `T`. -/

/-- Pointwise lower bound on `[u, v]`, `0 < u ≤ v`: `e^{-s} ≥ e^{-v}`, `(1+Ts)^{-b} ≥ (1+Tv)^{-b}`
and `s^{a-1} ≥ min(u^{a-1}, v^{a-1})`, the power being monotone in one direction, so that its
minimum over the interval sits at an endpoint. -/
public theorem chamberIntegrand_ge_endpoints {T a b u v s : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b)
    (hu : 0 < u) (hus : u ≤ s) (hsv : s ≤ v) :
    Real.exp (-v) * min (u ^ (a - 1)) (v ^ (a - 1)) * (1 + T * v) ^ (-b)
      ≤ chamberIntegrand T a b s := by
  have hs : (0:ℝ) < s := lt_of_lt_of_le hu hus
  have hv : (0:ℝ) < v := lt_of_lt_of_le hs hsv
  have he : Real.exp (-v) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
  have hp : min (u ^ (a - 1)) (v ^ (a - 1)) ≤ s ^ (a - 1) := by
    rcases le_or_gt 0 (a - 1) with h | h
    · exact le_trans (min_le_left _ _) (Real.rpow_le_rpow hu.le hus h)
    · exact le_trans (min_le_right _ _) (Real.rpow_le_rpow_of_nonpos hs hsv h.le)
  have hq : (1 + T * v) ^ (-b) ≤ (1 + T * s) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith) (by linarith)
  have hmin0 : (0:ℝ) ≤ min (u ^ (a - 1)) (v ^ (a - 1)) :=
    le_min (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _)
  have hq0 : (0:ℝ) ≤ (1 + T * v) ^ (-b) := Real.rpow_nonneg (by nlinarith) _
  calc Real.exp (-v) * min (u ^ (a - 1)) (v ^ (a - 1)) * (1 + T * v) ^ (-b)
      ≤ Real.exp (-s) * s ^ (a - 1) * (1 + T * s) ^ (-b) :=
        mul_le_mul (mul_le_mul he hp hmin0 (Real.exp_pos _).le) hq hq0 (by positivity)
    _ = chamberIntegrand T a b s := rfl

/-- The mass of `G` carried by `(u, v]`, `0 < u ≤ v`: the pointwise bound of
`chamberIntegrand_ge_endpoints` integrated against the length `v - u` of the interval. -/
public theorem chamberIntegral_Ioc_ge {T a b u v : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 ≤ b)
    (hu : 0 < u) (huv : u ≤ v) :
    (v - u) * (Real.exp (-v) * min (u ^ (a - 1)) (v ^ (a - 1)) * (1 + T * v) ^ (-b))
      ≤ ∫ s in Set.Ioc u v, chamberIntegrand T a b s := by
  have hint : IntegrableOn (chamberIntegrand T a b) (Set.Ioc u v) :=
    (integrableOn_chamberIntegrand hT ha hb).mono_set fun x hx => lt_trans hu hx.1
  have hconst : IntegrableOn
      (fun _ : ℝ => Real.exp (-v) * min (u ^ (a - 1)) (v ^ (a - 1)) * (1 + T * v) ^ (-b))
      (Set.Ioc u v) := integrableOn_const (by simp)
  have hmono : (∫ _ in Set.Ioc u v,
      Real.exp (-v) * min (u ^ (a - 1)) (v ^ (a - 1)) * (1 + T * v) ^ (-b))
      ≤ ∫ s in Set.Ioc u v, chamberIntegrand T a b s :=
    setIntegral_mono_on hconst hint measurableSet_Ioc fun s hs =>
      chamberIntegrand_ge_endpoints hT hb hu hs.1.le hs.2
  rwa [setIntegral_const, Real.volume_real_Ioc, max_eq_left (by linarith), smul_eq_mul] at hmono

/-- `min(u^{a-1}, (2u)^{a-1}) = u^{a-1} min(1, 2^{a-1})`: the shape in which the constants
`η₁`, `η₂` of Lemma A.2 are written. -/
public theorem min_rpow_two_mul {a u : ℝ} (hu : 0 < u) :
    min (u ^ (a - 1)) ((2 * u) ^ (a - 1)) = u ^ (a - 1) * min 1 (2 ^ (a - 1)) := by
  have h2 : ((2:ℝ) * u) ^ (a - 1) = 2 ^ (a - 1) * u ^ (a - 1) :=
    Real.mul_rpow (by norm_num) hu.le
  have h3 : u ^ (a - 1) * min 1 ((2:ℝ) ^ (a - 1))
      = min (u ^ (a - 1) * 1) (u ^ (a - 1) * 2 ^ (a - 1)) :=
    mul_min_of_nonneg _ _ (Real.rpow_nonneg hu.le _)
  rw [h2, h3, mul_one, mul_comm (u ^ (a - 1)) ((2:ℝ) ^ (a - 1))]

/-- `0 < min(1, 2^{a-1})`. -/
public theorem min_one_rpow_pos (a : ℝ) : 0 < min 1 ((2:ℝ) ^ (a - 1)) :=
  lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _)

/-- `η₁(a,b,c) = e^{-1}(1+2c)^{-b} c^a min(1, 2^{a-1})`, the constant of Lemma A.2(i). -/
@[expose] public noncomputable def etaOne (a b c : ℝ) : ℝ :=
  Real.exp (-1) * (1 + 2 * c) ^ (-b) * (c ^ a * min 1 (2 ^ (a - 1)))

public theorem etaOne_pos {a b c : ℝ} (hc : 0 < c) : 0 < etaOne a b c :=
  mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by linarith) _))
    (mul_pos (Real.rpow_pos_of_pos hc _) (min_one_rpow_pos a))

/-- **Lemma A.2(i).** For `c ≥ 1` and `T ≥ 2c`,
`∫_{(c/T, 2c/T]} e^{-s} s^{a-1} (1+Ts)^{-b} ds ≥ η₁(a,b,c) T^{-a}`. -/
public theorem chamberA2_localSmall {T a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 1 ≤ c)
    (hT : 2 * c ≤ T) :
    etaOne a b c * T ^ (-a) ≤ ∫ s in Set.Ioc (c / T) (2 * (c / T)), chamberIntegrand T a b s := by
  have hc0 : (0:ℝ) < c := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hTne : T ≠ 0 := hT0.ne'
  have hu : (0:ℝ) < c / T := by positivity
  have hv1 : 2 * (c / T) ≤ 1 := by
    rw [show 2 * (c / T) = 2 * c / T by ring, div_le_one hT0]; linarith
  have key := chamberIntegral_Ioc_ge (T := T) (a := a) (b := b) (u := c / T) (v := 2 * (c / T))
    hT0.le ha hb hu (by linarith)
  have hTv : 1 + T * (2 * (c / T)) = 1 + 2 * c := by field_simp
  have hmin : min ((c / T) ^ (a - 1)) ((2 * (c / T)) ^ (a - 1))
      = (c / T) ^ (a - 1) * min 1 (2 ^ (a - 1)) := min_rpow_two_mul hu
  have hpow : c / T * (c / T) ^ (a - 1) = c ^ a * T ^ (-a) := by
    have h1 : (c / T) ^ (1:ℝ) * (c / T) ^ (a - 1) = (c / T) ^ a := by
      rw [← Real.rpow_add hu]; ring_nf
    rw [Real.rpow_one] at h1
    rw [h1, Real.div_rpow hc0.le hT0.le, Real.rpow_neg hT0.le, div_eq_mul_inv]
  have hrw : (2 * (c / T) - c / T) * (Real.exp (-(2 * (c / T)))
      * min ((c / T) ^ (a - 1)) ((2 * (c / T)) ^ (a - 1)) * (1 + T * (2 * (c / T))) ^ (-b))
      = Real.exp (-(2 * (c / T))) * ((1 + 2 * c) ^ (-b) * (c ^ a * min 1 (2 ^ (a - 1)))
        * T ^ (-a)) := by
    rw [hmin, hTv]
    calc (2 * (c / T) - c / T) * (Real.exp (-(2 * (c / T)))
          * ((c / T) ^ (a - 1) * min 1 (2 ^ (a - 1))) * (1 + 2 * c) ^ (-b))
        = Real.exp (-(2 * (c / T))) * (1 + 2 * c) ^ (-b) * min 1 (2 ^ (a - 1))
            * (c / T * (c / T) ^ (a - 1)) := by ring
      _ = Real.exp (-(2 * (c / T))) * (1 + 2 * c) ^ (-b) * min 1 (2 ^ (a - 1))
            * (c ^ a * T ^ (-a)) := by rw [hpow]
      _ = _ := by ring
  rw [hrw] at key
  have heq : etaOne a b c * T ^ (-a)
      = Real.exp (-1) * ((1 + 2 * c) ^ (-b) * (c ^ a * min 1 (2 ^ (a - 1))) * T ^ (-a)) := by
    unfold etaOne; ring
  rw [heq]
  refine le_trans ?_ key
  have hexp : Real.exp (-1) ≤ Real.exp (-(2 * (c / T))) := Real.exp_le_exp.2 (by linarith)
  have h1 : (0:ℝ) < (1 + 2 * c) ^ (-b) := Real.rpow_pos_of_pos (by linarith) _
  have h2 : (0:ℝ) < c ^ a := Real.rpow_pos_of_pos hc0 _
  have h3 := min_one_rpow_pos a
  have h4 : (0:ℝ) < T ^ (-a) := Real.rpow_pos_of_pos hT0 _
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- `η₂(a,b,c) = e^{-2c} c^a min(1, 2^{a-1}) (4c)^{-b}`, the constant of Lemma A.2(ii). -/
@[expose] public noncomputable def etaTwo (a b c : ℝ) : ℝ :=
  Real.exp (-(2 * c)) * (c ^ a * min 1 (2 ^ (a - 1))) * (4 * c) ^ (-b)

public theorem etaTwo_pos {a b c : ℝ} (hc : 0 < c) : 0 < etaTwo a b c :=
  mul_pos (mul_pos (Real.exp_pos _) (mul_pos (Real.rpow_pos_of_pos hc _) (min_one_rpow_pos a)))
    (Real.rpow_pos_of_pos (by linarith) _)

/-- **Lemma A.2(ii).** For `c ≥ 1` and `T ≥ 3`,
`∫_{(c, 2c]} e^{-s} s^{a-1} (1+Ts)^{-b} ds ≥ η₂(a,b,c) T^{-b}`. -/
public theorem chamberA2_localLarge {T a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 1 ≤ c)
    (hT : 3 ≤ T) :
    etaTwo a b c * T ^ (-b) ≤ ∫ s in Set.Ioc c (2 * c), chamberIntegrand T a b s := by
  have hc0 : (0:ℝ) < c := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have key := chamberIntegral_Ioc_ge (T := T) (a := a) (b := b) (u := c) (v := 2 * c)
    hT0.le ha hb hc0 (by linarith)
  have hmin : min (c ^ (a - 1)) ((2 * c) ^ (a - 1)) = c ^ (a - 1) * min 1 (2 ^ (a - 1)) :=
    min_rpow_two_mul hc0
  have hcpow : c * c ^ (a - 1) = c ^ a := by
    have h1 : c ^ (1:ℝ) * c ^ (a - 1) = c ^ a := by rw [← Real.rpow_add hc0]; ring_nf
    rwa [Real.rpow_one] at h1
  have hbase : (4 * c * T) ^ (-b) ≤ (1 + T * (2 * c)) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith) (by linarith)
  have hsplit : (4 * c * T) ^ (-b) = (4 * c) ^ (-b) * T ^ (-b) :=
    Real.mul_rpow (by linarith) hT0.le
  have hrw : (2 * c - c) * (Real.exp (-(2 * c)) * min (c ^ (a - 1)) ((2 * c) ^ (a - 1))
      * (1 + T * (2 * c)) ^ (-b))
      = Real.exp (-(2 * c)) * (c ^ a * min 1 (2 ^ (a - 1))) * (1 + T * (2 * c)) ^ (-b) := by
    rw [hmin]
    calc (2 * c - c) * (Real.exp (-(2 * c)) * (c ^ (a - 1) * min 1 (2 ^ (a - 1)))
          * (1 + T * (2 * c)) ^ (-b))
        = Real.exp (-(2 * c)) * min 1 (2 ^ (a - 1)) * (1 + T * (2 * c)) ^ (-b)
            * (c * c ^ (a - 1)) := by ring
      _ = Real.exp (-(2 * c)) * min 1 (2 ^ (a - 1)) * (1 + T * (2 * c)) ^ (-b) * c ^ a := by
          rw [hcpow]
      _ = _ := by ring
  rw [hrw] at key
  refine le_trans ?_ key
  have h2 : (0:ℝ) < c ^ a := Real.rpow_pos_of_pos hc0 _
  have h3 := min_one_rpow_pos a
  have hnn : (0:ℝ) ≤ Real.exp (-(2 * c)) * (c ^ a * min 1 (2 ^ (a - 1))) := by positivity
  calc etaTwo a b c * T ^ (-b)
      = Real.exp (-(2 * c)) * (c ^ a * min 1 (2 ^ (a - 1))) * ((4 * c) ^ (-b) * T ^ (-b)) := by
        unfold etaTwo; ring
    _ = Real.exp (-(2 * c)) * (c ^ a * min 1 (2 ^ (a - 1))) * (4 * c * T) ^ (-b) := by
        rw [hsplit]
    _ ≤ Real.exp (-(2 * c)) * (c ^ a * min 1 (2 ^ (a - 1))) * (1 + T * (2 * c)) ^ (-b) :=
        mul_le_mul_of_nonneg_left hbase hnn

/-- **Lemma A.2(iii).** In the resonant case `a = b`, for `c ≥ 1`, `T ≥ 3` and `T ≥ c²`,
`∫_{(c/T, 1]} e^{-s} s^{a-1} (1+Ts)^{-b} ds ≥ ½ e^{-1} 2^{-b} T^{-b} log T`.
This is the only clause that produces a logarithm, and hence the only source of the factor
`(log T)^{N⋆-1}` in the matching lower bound. -/
public theorem chamberA2_localLog {T a b c : ℝ} (ha : 0 < a) (hab : a = b) (hc : 1 ≤ c)
    (hT : 3 ≤ T) (hTc : c ^ 2 ≤ T) :
    1 / 2 * (Real.exp (-1) * 2 ^ (-b) * T ^ (-b)) * Real.log T
      ≤ ∫ s in Set.Ioc (c / T) 1, chamberIntegrand T a b s := by
  have hb : (0:ℝ) ≤ b := by rw [← hab]; exact ha.le
  have hc0 : (0:ℝ) < c := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hu : (0:ℝ) < c / T := by positivity
  have hu1 : c / T ≤ 1 := by rw [div_le_one hT0]; nlinarith
  have hint : IntegrableOn (chamberIntegrand T a b) (Set.Ioc (c / T) 1) :=
    (integrableOn_chamberIntegrand hT0.le ha hb).mono_set fun x hx => lt_trans hu hx.1
  have hlow : IntegrableOn
      (fun s : ℝ => 2 ^ (-b) * Real.exp (-1) * T ^ (-b) * s ^ ((0:ℝ) - 1)) (Set.Ioc (c / T) 1) :=
    (integrableOn_rpow_Ioc_of_pos hu hu1).const_mul _
  have hmono : (∫ s in Set.Ioc (c / T) 1,
      2 ^ (-b) * Real.exp (-1) * T ^ (-b) * s ^ ((0:ℝ) - 1))
      ≤ ∫ s in Set.Ioc (c / T) 1, chamberIntegrand T a b s := by
    refine setIntegral_mono_on hlow hint measurableSet_Ioc ?_
    intro s hs
    have hs0 : (0:ℝ) < s := lt_trans hu hs.1
    have hTs : 1 ≤ T * s := by
      have h := (div_lt_iff₀ hT0).mp hs.1
      nlinarith
    have hbig := chamberIntegrand_ge_large (a := a) hT0 hb hs0 hTs
    have habs : a - b - 1 = (0:ℝ) - 1 := by rw [hab]; ring
    rw [habs] at hbig
    refine le_trans ?_ hbig
    have hexp : Real.exp (-1) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith [hs.2])
    have hrest : (0:ℝ) ≤ T ^ (-b) * s ^ ((0:ℝ) - 1) := by positivity
    have h2 : (0:ℝ) < (2:ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [mul_le_mul_of_nonneg_right hexp hrest]
  rw [MeasureTheory.integral_const_mul, integral_rpow_Ioc_log hu hu1] at hmono
  refine le_trans ?_ hmono
  have hlogeq : Real.log (1 / (c / T)) = Real.log T - Real.log c := by
    rw [one_div_div, Real.log_div hT0.ne' hc0.ne']
  have hlogc : 2 * Real.log c ≤ Real.log T := by
    have h := Real.log_le_log (by positivity) hTc
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hK : (0:ℝ) < Real.exp (-1) * 2 ^ (-b) * T ^ (-b) := by
    have h2 : (0:ℝ) < (2:ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0:ℝ) < T ^ (-b) := Real.rpow_pos_of_pos hT0 _
    positivity
  rw [hlogeq]
  nlinarith [mul_nonneg hK.le
    (show (0:ℝ) ≤ Real.log T - Real.log c - Real.log T / 2 by linarith)]

/-! ### Lemma A.5, step (i): strong separation and the Vandermonde lower bound

Print's clause (i) does two things: it places the explicit boxes inside `Δ`, and it converts
the strong separation `s_i ≤ ½ s_j` for `i < j` into a *lower* bound on the Vandermonde factor,

    ∏_{i<j} (s_j - s_i) ≥ 2^{-k(k-1)/2} ∏_j s_j^{j-1}.

Both facts depend only on the separation, not on the boxes, so they are proved for an
arbitrary separated point and the boxes are checked against them afterwards. The exponent is
again `#(Finset.Iio j) = (j : ℕ)`, so print's `j - 1` is never formed; and print's constant
`2^{-k(k-1)/2}` appears as `(1/2)^(∑ j, (j : ℕ))`, whose exponent is pinned to `k(k-1)/2` by
`sum_fin_val_mul_two` without any division in `ℕ`. -/

/-- Print's "strong sense" separation of clause (i): positive coordinates, and
`s_i ≤ ½ s_j` — written `2 s_i ≤ s_j` — for every `i < j`. -/
@[expose] public def chamberSeparated {k : ℕ} (s : Fin k → ℝ) : Prop :=
  (∀ i, 0 < s i) ∧ ∀ i j : Fin k, i < j → 2 * s i ≤ s j

/-- A separated point lies in the ordered chamber: separation is strictly stronger than the
monotonicity `Δ` asks for, since `2 s_i ≤ s_j` and `s_i > 0` give `s_i < s_j`. -/
public theorem chamberSeparated.mem_chamberDelta {k : ℕ} {s : Fin k → ℝ}
    (hs : chamberSeparated s) : s ∈ chamberDelta k := by
  refine ⟨hs.1, ?_⟩
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · have := hs.2 i j hlt
    linarith [hs.1 i]

/-- `∑_{j : Fin k} (j : ℕ) = k(k-1)/2`, stated as `(∑ j, (j : ℕ)) * 2 = k * (k - 1)` so that
no division or truncated subtraction is formed: at `k = 0` both sides are `0`. -/
public theorem sum_fin_val_mul_two (k : ℕ) : (∑ j : Fin k, (j : ℕ)) * 2 = k * (k - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) k]
  exact Finset.sum_range_id_mul_two k

/-- **Lemma A.5(i), the Vandermonde lower bound.** On a separated point,
`s_j - s_i ≥ ½ s_j` for `i < j`, so the product over the `k(k-1)/2` pairs is at least
`∏_j (s_j / 2)^{j-1}`. Stated in the factored form `∏_j (s_j / 2)^(j : ℕ)`, which is print's
`2^{-k(k-1)/2} ∏_j s_j^{j-1}` after `Finset.prod_div_distrib`. -/
public theorem chamberVandermonde_ge_prod {k : ℕ} {s : Fin k → ℝ} (hs : chamberSeparated s) :
    (∏ j : Fin k, (s j / 2) ^ (j : ℕ)) ≤ chamberVandermonde s := by
  refine Finset.prod_le_prod (fun j _ => pow_nonneg (by linarith [hs.1 j]) _) ?_
  intro j _
  calc (s j / 2) ^ (j : ℕ) = ∏ _i ∈ Finset.Iio j, (s j / 2) := by
        rw [Finset.prod_const, Fin.card_Iio]
    _ ≤ ∏ i ∈ Finset.Iio j, (s j - s i) :=
        Finset.prod_le_prod (fun _ _ => by linarith [hs.1 j])
          (fun i hi => by linarith [hs.2 i j (Finset.mem_Iio.mp hi)])

/-- Print's constant `2^{-k(k-1)/2}` of clause (i), as a positive real. -/
@[expose] public noncomputable def chamberSepConst (k : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ (∑ j : Fin k, (j : ℕ))

public theorem chamberSepConst_pos (k : ℕ) : 0 < chamberSepConst k := by
  unfold chamberSepConst; positivity

/-- The separated form of print's clause (i): the Vandermonde factor is at least
`2^{-k(k-1)/2} ∏_j s_j^{j-1}`, print's own display. -/
public theorem chamberVandermonde_ge_const_mul {k : ℕ} {s : Fin k → ℝ}
    (hs : chamberSeparated s) :
    chamberSepConst k * (∏ j : Fin k, s j ^ (j : ℕ)) ≤ chamberVandermonde s := by
  refine le_trans (le_of_eq ?_) (chamberVandermonde_ge_prod hs)
  rw [chamberSepConst, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [div_pow, div_eq_mul_inv, ← inv_pow]
  ring

/-- **Lemma A.5(ii), the pointwise half.** On a separated point,
`F_T(s) ≥ 2^{-k(k-1)/2} ∏_i g_i(s_i)` — print's display, and the exact mirror of A.4's
`chamberFT_le_prod`, with the Vandermonde inequality reversed and nothing else changed. -/
public theorem chamberFT_ge_prod {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) {s : Fin k → ℝ}
    (hs : chamberSeparated s) :
    chamberSepConst k * ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i)
      ≤ chamberFT k T α ρ s := by
  have hpos : ∀ i : Fin k, 0 < s i := hs.1
  have hexp : Real.exp (-∑ i, s i) = ∏ i : Fin k, Real.exp (-s i) := by
    rw [← Real.exp_sum]
    congr 1
    simp
  have hterm : ∀ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i)
      = Real.exp (-s i) * (s i ^ α * s i ^ (i : ℕ)) * (1 + T * s i) ^ (-ρ) := by
    intro i
    have h1 : s i ^ (α + ((i : ℕ) : ℝ) + 1 - 1) = s i ^ α * s i ^ ((i : ℕ) : ℝ) := by
      rw [show α + ((i : ℕ) : ℝ) + 1 - 1 = α + ((i : ℕ) : ℝ) by ring, Real.rpow_add (hpos i)]
    simp only [chamberIntegrand]
    rw [h1, Real.rpow_natCast]
  have hprod : (∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i))
      = (∏ i : Fin k, Real.exp (-s i))
        * ((∏ i : Fin k, s i ^ α) * ∏ i : Fin k, s i ^ (i : ℕ))
        * ∏ i : Fin k, (1 + T * s i) ^ (-ρ) := by
    simp only [hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hP : (0:ℝ) ≤ ∏ i : Fin k, Real.exp (-s i) :=
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hQ : (0:ℝ) ≤ ∏ i : Fin k, s i ^ α :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpos i).le _
  have hR : (0:ℝ) ≤ ∏ i : Fin k, (1 + T * s i) ^ (-ρ) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by nlinarith [hpos i]) _
  have key : chamberSepConst k * ((∏ i : Fin k, Real.exp (-s i))
        * ((∏ i : Fin k, s i ^ α) * ∏ i : Fin k, s i ^ (i : ℕ)))
      ≤ (∏ i : Fin k, Real.exp (-s i)) * (∏ i : Fin k, s i ^ α) * chamberVandermonde s := by
    calc chamberSepConst k * ((∏ i : Fin k, Real.exp (-s i))
            * ((∏ i : Fin k, s i ^ α) * ∏ i : Fin k, s i ^ (i : ℕ)))
        = (∏ i : Fin k, Real.exp (-s i)) * (∏ i : Fin k, s i ^ α)
            * (chamberSepConst k * ∏ i : Fin k, s i ^ (i : ℕ)) := by ring
      _ ≤ (∏ i : Fin k, Real.exp (-s i)) * (∏ i : Fin k, s i ^ α) * chamberVandermonde s :=
          mul_le_mul_of_nonneg_left (chamberVandermonde_ge_const_mul hs) (mul_nonneg hP hQ)
  rw [chamberFT, hexp, hprod]
  calc chamberSepConst k * ((∏ i : Fin k, Real.exp (-s i))
          * ((∏ i : Fin k, s i ^ α) * ∏ i : Fin k, s i ^ (i : ℕ))
          * ∏ i : Fin k, (1 + T * s i) ^ (-ρ))
      = chamberSepConst k * ((∏ i : Fin k, Real.exp (-s i))
          * ((∏ i : Fin k, s i ^ α) * ∏ i : Fin k, s i ^ (i : ℕ)))
          * ∏ i : Fin k, (1 + T * s i) ^ (-ρ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right key hR


/-! ### Lemma A.5, the explicit sectors and the matching lower bound

Print's boxes, in the `Fin k` indexing where coordinate `i` carries print's index `i + 1`:

    Ω_j = ∏_{i+1 ≤ j} ( 4^{i+1}/T , 2·4^{i+1}/T ]  ×  ∏_{i+1 > j} ( 4^{i+1} , 2·4^{i+1} ]

Print writes closed boxes; half-open ones are used here because the endpoints carry no
measure and a *lower* bound on a subset is still a lower bound, while `Set.Ioc` is the shape
`chamberA2_localSmall` and `chamberA2_localLarge` already deliver. The two interval shapes are
exactly those two lemmas' domains — `Ioc (c/T) (2·(c/T))` and `Ioc c (2c)` with `c = 4^{i+1}` —
so no reshaping is needed at the point of use.

Print states its clauses for `T ≥ T₀ = 16^{k+1}`. What the proof actually consumes is
`3 ≤ T` and `2·4^k ≤ T`, and those are the hypotheses carried below; `chamberT0_le` records
that print's threshold implies them, so the print-facing corollary is available without
weakening anything. -/

/-- The `i`-th factor of print's vertex sector `Ω_j`: the small box `(4^{i+1}/T, 2·4^{i+1}/T]`
when print's index `i + 1` is at most `j`, and the large box `(4^{i+1}, 2·4^{i+1}]` otherwise. -/
@[expose] public noncomputable def chamberBox (T : ℝ) (j : ℕ) {k : ℕ} (i : Fin k) : Set ℝ :=
  if (i : ℕ) + 1 ≤ j then
    Set.Ioc ((4:ℝ) ^ ((i : ℕ) + 1) / T) (2 * ((4:ℝ) ^ ((i : ℕ) + 1) / T))
  else Set.Ioc ((4:ℝ) ^ ((i : ℕ) + 1)) (2 * (4:ℝ) ^ ((i : ℕ) + 1))

/-- Print's vertex sector `Ω_j`, a product of intervals. -/
@[expose] public noncomputable def chamberOmega (k : ℕ) (T : ℝ) (j : ℕ) : Set (Fin k → ℝ) :=
  Set.univ.pi fun i : Fin k => chamberBox T j i

public theorem measurableSet_chamberBox (T : ℝ) (j : ℕ) {k : ℕ} (i : Fin k) :
    MeasurableSet (chamberBox T j i) := by
  unfold chamberBox
  split <;> exact measurableSet_Ioc

public theorem measurableSet_chamberOmega (k : ℕ) (T : ℝ) (j : ℕ) :
    MeasurableSet (chamberOmega k T j) :=
  MeasurableSet.univ_pi fun i => measurableSet_chamberBox T j i

/-- Print's threshold `T₀ = 16^{k+1}` dominates the two bounds the proof consumes. -/
public theorem chamberT0_le (k : ℕ) : 3 ≤ (16:ℝ) ^ (k + 1) ∧ 2 * (4:ℝ) ^ k ≤ (16:ℝ) ^ (k + 1) := by
  have h4 : (1:ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have h16 : (16:ℝ) ^ (k + 1) = 16 * 16 ^ k := by rw [pow_succ]; ring
  have hle : (4:ℝ) ^ k ≤ 16 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  constructor
  · rw [h16]; nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 16 by norm_num) (n := k)]
  · rw [h16]; nlinarith

/-- **Lemma A.5(i), the separation of the vertex sector.** On `Ω_j` the coordinates are
pairwise separated in print's strong sense `s_i ≤ ½ s_{i'}` for `i < i'`. Print's three cases
are the three cases below: both indices small, both large, and the crossing pair — the last
being the only one that uses `4^k ≤ T`, exactly as print says. -/
public theorem chamberSeparated_of_mem_chamberOmega {k : ℕ} {T : ℝ} {j : ℕ}
    (hT : 2 * (4:ℝ) ^ k ≤ T) {s : Fin k → ℝ} (hs : s ∈ chamberOmega k T j) :
    chamberSeparated s := by
  have h4k : (1:ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hT0 : (0:ℝ) < T := by nlinarith
  have hmem : ∀ i : Fin k, s i ∈ chamberBox T j i := fun i => hs i (Set.mem_univ i)
  have hpow : ∀ i : Fin k, (0:ℝ) < 4 ^ ((i : ℕ) + 1) := fun i => by positivity
  have hpowle : ∀ i : Fin k, (4:ℝ) ^ ((i : ℕ) + 1) ≤ 4 ^ k := fun i =>
    pow_le_pow_right₀ (by norm_num) i.isLt
  refine ⟨fun i => ?_, fun i i' hii' => ?_⟩
  · have h := hmem i
    unfold chamberBox at h
    split at h
    · exact lt_trans (by positivity) h.1
    · exact lt_trans (hpow i) h.1
  · have hlt : (i : ℕ) + 1 < (i' : ℕ) + 1 := by
      simpa using Fin.lt_def.mp hii'
    have hstep : (4:ℝ) ^ ((i' : ℕ) + 1) ≥ 4 * 4 ^ ((i : ℕ) + 1) := by
      calc (4:ℝ) * 4 ^ ((i : ℕ) + 1) = 4 ^ ((i : ℕ) + 2) := by rw [pow_succ]; ring
        _ ≤ 4 ^ ((i' : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hi := hmem i
    have hi' := hmem i'
    unfold chamberBox at hi hi'
    split at hi
    · rename_i hsmall
      split at hi'
      · -- both small: the step from `4^{i+1}` to `4^{i'+1}` beats the factor `2`
        have h1 : s i ≤ 2 * ((4:ℝ) ^ ((i : ℕ) + 1) / T) := hi.2
        have h2 : (4:ℝ) ^ ((i' : ℕ) + 1) / T < s i' := hi'.1
        have hkey : (4:ℝ) * 4 ^ ((i : ℕ) + 1) / T ≤ 4 ^ ((i' : ℕ) + 1) / T := by gcongr
        have h3 : 2 * (2 * ((4:ℝ) ^ ((i : ℕ) + 1) / T)) = 4 * 4 ^ ((i : ℕ) + 1) / T := by ring
        linarith
      · -- the crossing pair: this is where `4^k ≤ T` is used
        have h1 : s i ≤ 2 * ((4:ℝ) ^ ((i : ℕ) + 1) / T) := hi.2
        have h2 : (4:ℝ) ^ ((i' : ℕ) + 1) < s i' := hi'.1
        have h3 : (4:ℝ) ≤ 4 ^ ((i' : ℕ) + 1) := by
          calc (4:ℝ) = 4 ^ 1 := by norm_num
            _ ≤ 4 ^ ((i' : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h4 : (4:ℝ) ^ ((i : ℕ) + 1) / T ≤ 1 := by
          rw [div_le_one hT0]
          nlinarith [hpowle i]
        nlinarith
    · rename_i hlarge
      have hnot : ¬ ((i' : ℕ) + 1 ≤ j) := by omega
      rw [if_neg hnot] at hi'
      have h1 : s i ≤ 2 * (4:ℝ) ^ ((i : ℕ) + 1) := hi.2
      have h2 : (4:ℝ) ^ ((i' : ℕ) + 1) < s i' := hi'.1
      nlinarith

/-- `Ω_j ⊆ Δ`, the first half of print's clause (i). -/
public theorem chamberOmega_subset_chamberDelta {k : ℕ} {T : ℝ} {j : ℕ}
    (hT : 2 * (4:ℝ) ^ k ≤ T) : chamberOmega k T j ⊆ chamberDelta k :=
  fun _ hs => (chamberSeparated_of_mem_chamberOmega hT hs).mem_chamberDelta

public theorem chamberOmega_subset_pi {k : ℕ} {T : ℝ} {j : ℕ} (hT : 2 * (4:ℝ) ^ k ≤ T) :
    chamberOmega k T j ⊆ Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ) :=
  fun _ hs i _ => (chamberSeparated_of_mem_chamberOmega hT hs).1 i

/-- Tonelli on a box: the integral of a product of one-variable functions over a product of
sets is the product of the one-variable integrals. Print's "since `Ω_j` is a product of
intervals, Tonelli gives". -/
public theorem setIntegral_univ_pi_prod {k : ℕ} (B : Fin k → Set ℝ) (f : Fin k → ℝ → ℝ) :
    (∫ s in Set.univ.pi B, ∏ i, f i (s i)) = ∏ i, ∫ s in B i, f i s := by
  have h : (volume : Measure (Fin k → ℝ)).restrict (Set.univ.pi B)
      = Measure.pi fun i => (volume : Measure ℝ).restrict (B i) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  rw [h, MeasureTheory.integral_fintype_prod_eq_prod]


/-! ### Lemma A.5(ii): the vertex-sector lower bound

Print's exponent `∑_{i ≤ j} A_i + (k - j)ρ` is the sum, over all `k` coordinates, of `A_i` on
the small boxes and `ρ` on the large ones. Written that way it needs no `k - j`: the count of
large boxes is carried by the sum itself. -/

/-- Print's exponent `E(v^{(j)}) = ∑_{i ≤ j} A_i + (k - j)ρ` at the `j`-th vertex, as one sum
over `Fin k` with no truncated subtraction. -/
@[expose] public noncomputable def chamberVertexExponent (k : ℕ) (α ρ : ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin k, if (i : ℕ) + 1 ≤ j then α + (i : ℕ) + 1 else ρ

/-- Print's `κ₃ = 2^{-k(k-1)/2} ∏_i min(η₁(A_i, ρ, 4^i), η₂(A_i, ρ, 4^i))`. -/
@[expose] public noncomputable def chamberKappa3 (k : ℕ) (α ρ : ℝ) : ℝ :=
  chamberSepConst k * ∏ i : Fin k,
    min (etaOne (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
      (etaTwo (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))

public theorem chamberKappa3_pos {k : ℕ} {α ρ : ℝ} : 0 < chamberKappa3 k α ρ := by
  refine mul_pos (chamberSepConst_pos k) (Finset.prod_pos fun i _ => ?_)
  have hc : (0:ℝ) < 4 ^ ((i : ℕ) + 1) := by positivity
  exact lt_min (etaOne_pos hc) (etaTwo_pos hc)

/-- **Lemma A.5(ii), one factor.** On the `i`-th box the one-dimensional integral of `g_i` is
bounded below by `min(η₁, η₂)` times `T^{-A_i}` on a small box and `T^{-ρ}` on a large one:
`chamberA2_localSmall` with `c = 4^{i+1}` in the first case (legitimate because
`2·4^{i+1} ≤ 2·4^k ≤ T`), `chamberA2_localLarge` with the same `c` in the second. -/
public theorem chamberBox_integral_ge {k : ℕ} {T α ρ : ℝ} {j : ℕ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hT3 : 3 ≤ T) (hTk : 2 * (4:ℝ) ^ k ≤ T) (i : Fin k) :
    min (etaOne (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
        (etaTwo (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
      * T ^ (-(if (i : ℕ) + 1 ≤ j then α + (i : ℕ) + 1 else ρ))
      ≤ ∫ s in chamberBox T j i, chamberIntegrand T (α + (i : ℕ) + 1) ρ s := by
  have hT0 : (0:ℝ) < T := by linarith
  have hA : (0:ℝ) < α + (i : ℕ) + 1 := chamberIndex_pos hα i
  have hc1 : (1:ℝ) ≤ 4 ^ ((i : ℕ) + 1) := one_le_pow₀ (by norm_num)
  have hck : (4:ℝ) ^ ((i : ℕ) + 1) ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) i.isLt
  have hc0 : (0:ℝ) < 4 ^ ((i : ℕ) + 1) := by positivity
  unfold chamberBox
  by_cases hj : (i : ℕ) + 1 ≤ j
  · rw [if_pos hj, if_pos hj]
    have hbase := chamberA2_localSmall (T := T) (a := α + (i : ℕ) + 1) (b := ρ)
      (c := (4:ℝ) ^ ((i : ℕ) + 1)) hA hρ hc1 (by linarith)
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ?_) hbase
    exact (Real.rpow_pos_of_pos hT0 _).le
  · rw [if_neg hj, if_neg hj]
    have hbase := chamberA2_localLarge (T := T) (a := α + (i : ℕ) + 1) (b := ρ)
      (c := (4:ℝ) ^ ((i : ℕ) + 1)) hA hρ hc1 hT3
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) ?_) hbase
    exact (Real.rpow_pos_of_pos hT0 _).le

/-- **Lemma A.5(ii).** `∫_{Ω_j} F_T ≥ κ₃ T^{-E(v^{(j)})}` for every `0 ≤ j ≤ k`, with `κ₃`
depending only on `(k, α, ρ)`.

The proof is print's, in print's order: the pointwise bound of clause (i)
(`chamberFT_ge_prod`), Tonelli on the box (`setIntegral_univ_pi_prod`), and then Lemma A.2's
localized clauses factor by factor (`chamberBox_integral_ge`). Print's threshold `T₀` is
replaced by the two inequalities the argument consumes; `chamberT0_le` recovers print's form. -/
public theorem chamberA5_vertex {k : ℕ} {T α ρ : ℝ} {j : ℕ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hT3 : 3 ≤ T) (hTk : 2 * (4:ℝ) ^ k ≤ T) :
    chamberKappa3 k α ρ * T ^ (-chamberVertexExponent k α ρ j)
      ≤ ∫ s in chamberOmega k T j, chamberFT k T α ρ s := by
  have hT0 : (0:ℝ) < T := by linarith
  have hFT : IntegrableOn (chamberFT k T α ρ) (chamberOmega k T j) :=
    (integrableOn_chamberFT (by linarith) hα hρ).mono_set
      (chamberOmega_subset_chamberDelta hTk)
  have hmaj : IntegrableOn
      (fun s : Fin k → ℝ =>
        chamberSepConst k * ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i))
      (chamberOmega k T j) :=
    ((integrableOn_prod_chamberIntegrand (by linarith) hα hρ).mono_set
      (chamberOmega_subset_pi hTk)).const_mul _
  have hstep1 : (∫ s in chamberOmega k T j,
      chamberSepConst k * ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i))
      ≤ ∫ s in chamberOmega k T j, chamberFT k T α ρ s :=
    setIntegral_mono_on hmaj hFT (measurableSet_chamberOmega k T j) fun s hs =>
      chamberFT_ge_prod (by linarith) (chamberSeparated_of_mem_chamberOmega hTk hs)
  -- `κ₃ T^{-E}` regrouped as `2^{-k(k-1)/2} ∏_i (min(η₁,η₂) T^{-e_i})`
  have hmid : chamberKappa3 k α ρ * T ^ (-chamberVertexExponent k α ρ j)
      = chamberSepConst k * ∏ i : Fin k,
          (min (etaOne (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
              (etaTwo (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
            * T ^ (-(if (i : ℕ) + 1 ≤ j then α + (i : ℕ) + 1 else ρ))) := by
    rw [chamberKappa3, chamberVertexExponent, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos hT0, Finset.sum_neg_distrib]
    ring
  have hprod : chamberSepConst k * ∏ i : Fin k,
        (min (etaOne (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
            (etaTwo (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
          * T ^ (-(if (i : ℕ) + 1 ≤ j then α + (i : ℕ) + 1 else ρ)))
      ≤ ∫ s in chamberOmega k T j,
          chamberSepConst k * ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i) := by
    rw [MeasureTheory.integral_const_mul, chamberOmega, setIntegral_univ_pi_prod]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_)
      (chamberSepConst_pos k).le
    · exact mul_nonneg (le_min (etaOne_pos (by positivity)).le (etaTwo_pos (by positivity)).le)
        (Real.rpow_pos_of_pos hT0 _).le
    · exact chamberBox_integral_ge hα hρ hT3 hTk i
  rw [hmid]
  exact le_trans hprod hstep1


/-! ### Lemma A.5(ii), the conclusion `I(T) ≥ κ₃ T^{-E⋆}`

Print's `E⋆` is `min_{0 ≤ j ≤ k} E_j`, and clause (ii) concludes by "taking `j = j₋`", the
minimizing index supplied by Lemma A.3(iv). Here the minimizing index comes from
`Finset.exists_mem_eq_inf'` rather than from A.3: the direction of the argument only needs
*some* minimizer, and which vertex it is is A.3's business, not A.5's. -/

/-- Print's `E⋆ = min_{0 ≤ j ≤ k} E_j`, the minimum of the vertex exponents. -/
@[expose] public noncomputable def chamberMinExponent (k : ℕ) (α ρ : ℝ) : ℝ :=
  (Finset.range (k + 1)).inf' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero k))
    (chamberVertexExponent k α ρ)

/-- `E⋆` is attained: print's `j₋`. -/
public theorem exists_chamberMinExponent (k : ℕ) (α ρ : ℝ) :
    ∃ j ∈ Finset.range (k + 1), chamberMinExponent k α ρ = chamberVertexExponent k α ρ j :=
  Finset.exists_mem_eq_inf' _ _

/-- A vertex sector contributes at most the whole chamber integral: `Ω_j ⊆ Δ` and `F_T ≥ 0`. -/
public theorem setIntegral_chamberOmega_le_chamberI {k : ℕ} {T α ρ : ℝ} {j : ℕ}
    (hα : -1 < α) (hρ : 0 ≤ ρ) (hT : 2 * (4:ℝ) ^ k ≤ T) (hT0 : 0 ≤ T) :
    (∫ s in chamberOmega k T j, chamberFT k T α ρ s) ≤ chamberI k T α ρ := by
  refine MeasureTheory.setIntegral_mono_set (integrableOn_chamberFT hT0 hα hρ) ?_
    (Filter.Eventually.of_forall (chamberOmega_subset_chamberDelta hT))
  filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_chamberDelta k)] with s hs
  exact chamberFT_nonneg hT0 hs

/-- **Lemma A.5(ii), as print states it.** `I(T) ≥ κ₃ T^{-E⋆}`, with `κ₃ > 0` depending only on
`(k, α, ρ)`. This is the matching lower bound for the exponent; the logarithmic factor of a
resonant vertex is clause (iii). -/
public theorem chamberA5_lower {k : ℕ} {T α ρ : ℝ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hT3 : 3 ≤ T) (hTk : 2 * (4:ℝ) ^ k ≤ T) :
    chamberKappa3 k α ρ * T ^ (-chamberMinExponent k α ρ) ≤ chamberI k T α ρ := by
  obtain ⟨j, -, hj⟩ := exists_chamberMinExponent k α ρ
  rw [hj]
  exact le_trans (chamberA5_vertex hα hρ hT3 hTk)
    (setIntegral_chamberOmega_le_chamberI hα hρ hTk (by linarith))

/-- Print's own form of clause (ii), at print's threshold `T₀ = 16^{k+1}`. -/
public theorem chamberA5_lower_of_T0 {k : ℕ} {T α ρ : ℝ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hT : (16:ℝ) ^ (k + 1) ≤ T) :
    chamberKappa3 k α ρ * T ^ (-chamberMinExponent k α ρ) ≤ chamberI k T α ρ := by
  obtain ⟨h3, hk⟩ := chamberT0_le k
  exact chamberA5_lower hα hρ (le_trans h3 hT) (le_trans hk hT)


/-! ### Lemma A.5(iii): the edge sector and the logarithm

When `j₀ = 1` — equivalently `N⋆ = 2` — print replaces the `j*`-th box of `Ω_{j₋}` by the long
interval `(4^{j*}/T, 1]`, where `j* = j₋ + 1` is the index with `a_{j*} = 0`, i.e. `A_{j*} = ρ`.
That resonance is exactly the hypothesis `chamberA2_localLog` needs, and its conclusion is the
only place in the whole development where a `log T` is produced. Print: *"this is precisely the
resonance that makes the scale of `s_{j*}` undetermined."*

Print's `j₋` is written `m` below, so that print's `j*` is `m + 1` and no subtraction of
natural numbers is formed anywhere. The resonance hypothesis is `α + m + 1 = ρ`, which is
`A_{j*} = ρ` in the `Fin k` indexing. -/

/-- The `i`-th factor of print's edge sector `Ω_{edge}`, with print's `j*` equal to `m + 1`: the
small box below `j*`, the long box `(4^{j*}/T, 1]` at `j*`, the large box above. -/
@[expose] public noncomputable def chamberEdgeBox (T : ℝ) (m : ℕ) {k : ℕ} (i : Fin k) : Set ℝ :=
  if (i : ℕ) + 1 ≤ m then
    Set.Ioc ((4:ℝ) ^ ((i : ℕ) + 1) / T) (2 * ((4:ℝ) ^ ((i : ℕ) + 1) / T))
  else if (i : ℕ) = m then Set.Ioc ((4:ℝ) ^ ((i : ℕ) + 1) / T) 1
  else Set.Ioc ((4:ℝ) ^ ((i : ℕ) + 1)) (2 * (4:ℝ) ^ ((i : ℕ) + 1))

/-- Print's edge sector `Ω_{edge}`. -/
@[expose] public noncomputable def chamberOmegaEdge (k : ℕ) (T : ℝ) (m : ℕ) :
    Set (Fin k → ℝ) :=
  Set.univ.pi fun i : Fin k => chamberEdgeBox T m i

public theorem measurableSet_chamberEdgeBox (T : ℝ) (m : ℕ) {k : ℕ} (i : Fin k) :
    MeasurableSet (chamberEdgeBox T m i) := by
  unfold chamberEdgeBox
  split
  · exact measurableSet_Ioc
  · split <;> exact measurableSet_Ioc

public theorem measurableSet_chamberOmegaEdge (k : ℕ) (T : ℝ) (m : ℕ) :
    MeasurableSet (chamberOmegaEdge k T m) :=
  MeasurableSet.univ_pi fun i => measurableSet_chamberEdgeBox T m i

/-- The lower endpoint of the `i`-th edge box: `4^{i+1}/T` at and below `j*`, `4^{i+1}` above.
The long box and the small boxes share their lower endpoint, which is why print's first two
separation cases are one computation. -/
@[expose] public noncomputable def chamberEdgeLower (T : ℝ) (m : ℕ) {k : ℕ} (i : Fin k) : ℝ :=
  if (i : ℕ) ≤ m then (4:ℝ) ^ ((i : ℕ) + 1) / T else (4:ℝ) ^ ((i : ℕ) + 1)

/-- The upper endpoint of the `i`-th edge box. -/
@[expose] public noncomputable def chamberEdgeUpper (T : ℝ) (m : ℕ) {k : ℕ} (i : Fin k) : ℝ :=
  if (i : ℕ) + 1 ≤ m then 2 * ((4:ℝ) ^ ((i : ℕ) + 1) / T)
  else if (i : ℕ) = m then 1 else 2 * (4:ℝ) ^ ((i : ℕ) + 1)

public theorem chamberEdgeLower_lt_of_mem {T : ℝ} {m k : ℕ} {i : Fin k} {x : ℝ}
    (hx : x ∈ chamberEdgeBox T m i) : chamberEdgeLower T m i < x := by
  unfold chamberEdgeBox at hx
  unfold chamberEdgeLower
  split at hx
  · rename_i h
    rw [if_pos (by omega)]
    exact hx.1
  · split at hx
    · rename_i h
      rw [if_pos (by omega)]
      exact hx.1
    · rename_i h1 h2
      rw [if_neg (by omega)]
      exact hx.1

public theorem le_chamberEdgeUpper_of_mem {T : ℝ} {m k : ℕ} {i : Fin k} {x : ℝ}
    (hx : x ∈ chamberEdgeBox T m i) : x ≤ chamberEdgeUpper T m i := by
  unfold chamberEdgeBox at hx
  unfold chamberEdgeUpper
  split at hx
  · rename_i h
    rw [if_pos h]
    exact hx.2
  · rename_i h
    rw [if_neg h]
    split at hx
    · rename_i h2
      rw [if_pos h2]
      exact hx.2
    · rename_i h2
      rw [if_neg h2]
      exact hx.2

/-- **Lemma A.5(i) for the edge sector.** Print's four cases: pairs below `j*` (identical to
the vertex computation, because the long box shares its lower endpoint with a small box), the
crossing pair below-to-above, the pair `(j*, j')` with `j' > j*` — where `s_{j*} ≤ 1` and
`s_{j'} > 4`, print's `s_{j*} ≤ s_{j'}/4` — and pairs above `j*`. -/
public theorem chamberEdge_two_mul_upper_le_lower {T : ℝ} {m k : ℕ}
    (hTk : 2 * (4:ℝ) ^ k ≤ T) {i i' : Fin k} (hii' : i < i') :
    2 * chamberEdgeUpper T m i ≤ chamberEdgeLower T m i' := by
  have h4k : (1:ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hT0 : (0:ℝ) < T := by nlinarith
  have hlt : (i : ℕ) < (i' : ℕ) := Fin.lt_def.mp hii'
  have hpowle : (4:ℝ) ^ ((i : ℕ) + 1) ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) i.isLt
  have hstep : (4:ℝ) * 4 ^ ((i : ℕ) + 1) ≤ 4 ^ ((i' : ℕ) + 1) := by
    calc (4:ℝ) * 4 ^ ((i : ℕ) + 1) = 4 ^ ((i : ℕ) + 2) := by rw [pow_succ]; ring
      _ ≤ 4 ^ ((i' : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfour : (4:ℝ) ≤ 4 ^ ((i' : ℕ) + 1) := by
    calc (4:ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ ((i' : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold chamberEdgeUpper chamberEdgeLower
  by_cases hi : (i : ℕ) + 1 ≤ m
  · rw [if_pos hi]
    by_cases hi' : (i' : ℕ) ≤ m
    · -- both at or below `j*`: the shared lower endpoint makes this print's first case
      rw [if_pos hi']
      have hkey : (4:ℝ) * 4 ^ ((i : ℕ) + 1) / T ≤ 4 ^ ((i' : ℕ) + 1) / T := by gcongr
      have h3 : 2 * (2 * ((4:ℝ) ^ ((i : ℕ) + 1) / T)) = 4 * 4 ^ ((i : ℕ) + 1) / T := by ring
      linarith
    · -- the crossing pair: this is where `4^k ≤ T` is used
      rw [if_neg hi']
      have h4 : (4:ℝ) ^ ((i : ℕ) + 1) / T ≤ 1 := by
        rw [div_le_one hT0]; nlinarith
      nlinarith
  · rw [if_neg hi]
    by_cases hj : (i : ℕ) = m
    · -- `(j*, j')`: `s_{j*} ≤ 1` against `s_{j'} > 4`
      rw [if_pos hj, if_neg (by omega)]
      linarith
    · -- both above `j*`
      rw [if_neg hj, if_neg (by omega)]
      linarith

/-- The edge sector is separated, hence contained in `Δ`. -/
public theorem chamberSeparated_of_mem_chamberOmegaEdge {k : ℕ} {T : ℝ} {m : ℕ}
    (hTk : 2 * (4:ℝ) ^ k ≤ T) {s : Fin k → ℝ} (hs : s ∈ chamberOmegaEdge k T m) :
    chamberSeparated s := by
  have h4k : (1:ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hT0 : (0:ℝ) < T := by nlinarith
  have hmem : ∀ i : Fin k, s i ∈ chamberEdgeBox T m i := fun i => hs i (Set.mem_univ i)
  have hlow : ∀ i : Fin k, chamberEdgeLower T m i < s i := fun i =>
    chamberEdgeLower_lt_of_mem (hmem i)
  have hlow0 : ∀ i : Fin k, (0:ℝ) < chamberEdgeLower T m i := by
    intro i
    unfold chamberEdgeLower
    split <;> positivity
  refine ⟨fun i => lt_trans (hlow0 i) (hlow i), fun i i' hii' => ?_⟩
  have h1 := le_chamberEdgeUpper_of_mem (hmem i)
  have h2 := chamberEdge_two_mul_upper_le_lower (m := m) hTk hii'
  have h3 := hlow i'
  linarith

public theorem chamberOmegaEdge_subset_chamberDelta {k : ℕ} {T : ℝ} {m : ℕ}
    (hTk : 2 * (4:ℝ) ^ k ≤ T) : chamberOmegaEdge k T m ⊆ chamberDelta k :=
  fun _ hs => (chamberSeparated_of_mem_chamberOmegaEdge hTk hs).mem_chamberDelta

public theorem chamberOmegaEdge_subset_pi {k : ℕ} {T : ℝ} {m : ℕ}
    (hTk : 2 * (4:ℝ) ^ k ≤ T) :
    chamberOmegaEdge k T m ⊆ Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ) :=
  fun _ hs i _ => (chamberSeparated_of_mem_chamberOmegaEdge hTk hs).1 i


/-- The constant attached to the `i`-th edge box: print's `min(η₁, η₂)` away from `j*`, and the
constant `½ e^{-1} 2^{-ρ}` of `chamberA2_localLog` at `j*`. -/
@[expose] public noncomputable def chamberEdgeConst (α ρ : ℝ) (m : ℕ) {k : ℕ} (i : Fin k) : ℝ :=
  if (i : ℕ) = m then 1 / 2 * (Real.exp (-1) * 2 ^ (-ρ))
  else min (etaOne (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))
    (etaTwo (α + (i : ℕ) + 1) ρ ((4:ℝ) ^ ((i : ℕ) + 1)))

/-- The `T`-dependent weight of the `i`-th edge box: `T^{-A_i}` on a small box, `T^{-ρ}` on a
large one, and `T^{-ρ} log T` on the long box at `j*` — the single logarithm. -/
@[expose] public noncomputable def chamberEdgeWeight (T α ρ : ℝ) (m : ℕ) {k : ℕ} (i : Fin k) :
    ℝ :=
  if (i : ℕ) = m then T ^ (-ρ) * Real.log T
  else T ^ (-(if (i : ℕ) + 1 ≤ m then α + (i : ℕ) + 1 else ρ))

public theorem chamberEdgeConst_pos {α ρ : ℝ} {m k : ℕ} (i : Fin k) :
    0 < chamberEdgeConst α ρ m i := by
  unfold chamberEdgeConst
  split
  · have h2 : (0:ℝ) < (2:ℝ) ^ (-ρ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  · have hc : (0:ℝ) < 4 ^ ((i : ℕ) + 1) := by positivity
    exact lt_min (etaOne_pos hc) (etaTwo_pos hc)

/-- Print's `κ₄`, the edge-sector constant. -/
@[expose] public noncomputable def chamberKappa4 (k : ℕ) (α ρ : ℝ) (m : ℕ) : ℝ :=
  chamberSepConst k * ∏ i : Fin k, chamberEdgeConst α ρ m i

public theorem chamberKappa4_pos {k : ℕ} {α ρ : ℝ} {m : ℕ} : 0 < chamberKappa4 k α ρ m :=
  mul_pos (chamberSepConst_pos k) (Finset.prod_pos fun i _ => chamberEdgeConst_pos i)

/-- The edge weights multiply to `T^{-E_{j₋}} log T`: exactly one factor carries the
logarithm, and the remaining exponents sum to print's `E(v^{(j*-1)}) = E(v^{(j₋)})`. This is
where print's "the exponent equals `E(v^{(j*-1)}) = E⋆`" is discharged, and the reason the
edge sector produces the same power of `T` as the vertex `j₋` and one extra `log T`. -/
public theorem prod_chamberEdgeWeight {k : ℕ} {T α ρ : ℝ} {m : ℕ} (hT0 : 0 < T) (hm : m < k) :
    (∏ i : Fin k, chamberEdgeWeight T α ρ m i)
      = T ^ (-chamberVertexExponent k α ρ m) * Real.log T := by
  classical
  have hmem : (⟨m, hm⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
  have hval : ((⟨m, hm⟩ : Fin k) : ℕ) = m := rfl
  rw [← Finset.mul_prod_erase _ _ hmem, chamberVertexExponent,
    ← Finset.add_sum_erase _ _ hmem]
  have hw0 : chamberEdgeWeight T α ρ m (⟨m, hm⟩ : Fin k) = T ^ (-ρ) * Real.log T := by
    rw [chamberEdgeWeight, if_pos hval]
  have hif0 : (if ((⟨m, hm⟩ : Fin k) : ℕ) + 1 ≤ m then α + ((⟨m, hm⟩ : Fin k) : ℕ) + 1 else ρ)
      = ρ := by
    rw [hval, if_neg (by omega)]
  have hrest : (∏ i ∈ (Finset.univ : Finset (Fin k)).erase ⟨m, hm⟩,
      chamberEdgeWeight T α ρ m i)
      = T ^ (-∑ i ∈ (Finset.univ : Finset (Fin k)).erase ⟨m, hm⟩,
          (if (i : ℕ) + 1 ≤ m then α + (i : ℕ) + 1 else ρ)) := by
    rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hT0]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : (i : ℕ) ≠ m := by
      intro h
      exact (Finset.ne_of_mem_erase hi) (Fin.ext (by simpa [hval] using h))
    rw [chamberEdgeWeight, if_neg hne]
  rw [hw0, hrest, hif0, neg_add, Real.rpow_add hT0]
  ring

/-- **Lemma A.5(iii), one factor.** Away from `j*` the two localized clauses of Lemma A.2 apply
as in clause (ii); at `j*` the resonance `A_{j*} = ρ` puts `chamberA2_localLog` in force, and
its threshold `c² ≤ T` is `16^{m+1} ≤ 16^k ≤ T`. -/
public theorem chamberEdgeBox_integral_ge {k : ℕ} {T α ρ : ℝ} {m : ℕ} (hα : -1 < α)
    (hρ : 0 ≤ ρ) (hres : α + (m : ℝ) + 1 = ρ) (hT3 : 3 ≤ T) (hTk : 2 * (4:ℝ) ^ k ≤ T)
    (hT16 : (16:ℝ) ^ k ≤ T) (i : Fin k) :
    chamberEdgeConst α ρ m i * chamberEdgeWeight T α ρ m i
      ≤ ∫ s in chamberEdgeBox T m i, chamberIntegrand T (α + (i : ℕ) + 1) ρ s := by
  have hT0 : (0:ℝ) < T := by linarith
  have hA : (0:ℝ) < α + (i : ℕ) + 1 := chamberIndex_pos hα i
  have hc1 : (1:ℝ) ≤ 4 ^ ((i : ℕ) + 1) := one_le_pow₀ (by norm_num)
  have hck : (4:ℝ) ^ ((i : ℕ) + 1) ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) i.isLt
  unfold chamberEdgeConst chamberEdgeWeight chamberEdgeBox
  by_cases hj : (i : ℕ) = m
  · -- the long box at `j*`: `chamberA2_localLog`
    rw [if_pos hj, if_pos hj, if_neg (by omega), if_pos hj]
    have hab : α + (i : ℕ) + 1 = ρ := by rw [hj]; exact hres
    have hsq : ((4:ℝ) ^ ((i : ℕ) + 1)) ^ 2 ≤ T := by
      have h1 : ((4:ℝ) ^ ((i : ℕ) + 1)) ^ 2 = 16 ^ ((i : ℕ) + 1) := by
        rw [← pow_mul, show ((i : ℕ) + 1) * 2 = 2 * ((i : ℕ) + 1) by ring, pow_mul]
        norm_num
      have h2 : (16:ℝ) ^ ((i : ℕ) + 1) ≤ 16 ^ k := pow_le_pow_right₀ (by norm_num) i.isLt
      rw [h1]; linarith
    have hbase := chamberA2_localLog (T := T) (a := α + (i : ℕ) + 1) (b := ρ)
      (c := (4:ℝ) ^ ((i : ℕ) + 1)) hA hab hc1 hT3 hsq
    refine le_trans (le_of_eq ?_) hbase
    ring
  · rw [if_neg hj, if_neg hj]
    by_cases hs : (i : ℕ) + 1 ≤ m
    · rw [if_pos hs, if_pos hs]
      have hbase := chamberA2_localSmall (T := T) (a := α + (i : ℕ) + 1) (b := ρ)
        (c := (4:ℝ) ^ ((i : ℕ) + 1)) hA hρ hc1 (by linarith)
      refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ?_) hbase
      exact (Real.rpow_pos_of_pos hT0 _).le
    · rw [if_neg hs, if_neg hs, if_neg hj]
      have hbase := chamberA2_localLarge (T := T) (a := α + (i : ℕ) + 1) (b := ρ)
        (c := (4:ℝ) ^ ((i : ℕ) + 1)) hA hρ hc1 hT3
      refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) ?_) hbase
      exact (Real.rpow_pos_of_pos hT0 _).le

/-- **Lemma A.5(iii).** In the resonant case `A_{j*} = ρ`,
`∫_{Ω_{edge}} F_T ≥ κ₄ T^{-E_{j₋}} log T` with `κ₄ > 0` depending only on `(k, α, ρ)`. -/
public theorem chamberA5_edge {k : ℕ} {T α ρ : ℝ} {m : ℕ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hres : α + (m : ℝ) + 1 = ρ) (hm : m < k) (hT3 : 3 ≤ T) (hTk : 2 * (4:ℝ) ^ k ≤ T)
    (hT16 : (16:ℝ) ^ k ≤ T) :
    chamberKappa4 k α ρ m * (T ^ (-chamberVertexExponent k α ρ m) * Real.log T)
      ≤ ∫ s in chamberOmegaEdge k T m, chamberFT k T α ρ s := by
  have hT0 : (0:ℝ) < T := by linarith
  have hFT : IntegrableOn (chamberFT k T α ρ) (chamberOmegaEdge k T m) :=
    (integrableOn_chamberFT (by linarith) hα hρ).mono_set
      (chamberOmegaEdge_subset_chamberDelta hTk)
  have hmaj : IntegrableOn
      (fun s : Fin k → ℝ =>
        chamberSepConst k * ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i))
      (chamberOmegaEdge k T m) :=
    ((integrableOn_prod_chamberIntegrand (by linarith) hα hρ).mono_set
      (chamberOmegaEdge_subset_pi hTk)).const_mul _
  have hstep1 : (∫ s in chamberOmegaEdge k T m,
      chamberSepConst k * ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i))
      ≤ ∫ s in chamberOmegaEdge k T m, chamberFT k T α ρ s :=
    setIntegral_mono_on hmaj hFT (measurableSet_chamberOmegaEdge k T m) fun s hs =>
      chamberFT_ge_prod (by linarith) (chamberSeparated_of_mem_chamberOmegaEdge hTk hs)
  have hmid : chamberKappa4 k α ρ m * (T ^ (-chamberVertexExponent k α ρ m) * Real.log T)
      = chamberSepConst k * ∏ i : Fin k,
          (chamberEdgeConst α ρ m i * chamberEdgeWeight T α ρ m i) := by
    rw [chamberKappa4, Finset.prod_mul_distrib, prod_chamberEdgeWeight hT0 hm]
    ring
  have hprod : chamberSepConst k * ∏ i : Fin k,
        (chamberEdgeConst α ρ m i * chamberEdgeWeight T α ρ m i)
      ≤ ∫ s in chamberOmegaEdge k T m,
          chamberSepConst k * ∏ i : Fin k, chamberIntegrand T (α + (i : ℕ) + 1) ρ (s i) := by
    rw [MeasureTheory.integral_const_mul, chamberOmegaEdge, setIntegral_univ_pi_prod]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_)
      (chamberSepConst_pos k).le
    · refine mul_nonneg (chamberEdgeConst_pos i).le ?_
      unfold chamberEdgeWeight
      split
      · exact mul_nonneg (Real.rpow_pos_of_pos hT0 _).le
          (by linarith [one_le_log_of_three_le hT3])
      · exact (Real.rpow_pos_of_pos hT0 _).le
    · exact chamberEdgeBox_integral_ge hα hρ hres hT3 hTk hT16 i
  rw [hmid]
  exact le_trans hprod hstep1


/-! ### Lemma A.5(iv): the two clauses combined

Print reads the resonance `a_{j*} = 0` off Lemma A.3(iv). It is available here directly,
because the increment of the vertex exponent is computable: `E_{j+1} − E_j = A_{j+1} − ρ`, so
`j` and `j+1` are both minimizers exactly when `A_{j+1} = ρ`. This is print's Proposition 8.18
increment, and it is what lets clause (iii) be invoked without importing A.3. -/

/-- **The increment of the vertex exponent**, print's `E_{s+1} − E_s = a_{s+1} = α + s + 1 − ρ`.
The two sums differ in exactly one term, the one at the coordinate `i` with `i = j`, which
moves from the `ρ` branch to the `A_i` branch. -/
public theorem chamberVertexExponent_succ {k : ℕ} (α ρ : ℝ) {j : ℕ} (hj : j < k) :
    chamberVertexExponent k α ρ (j + 1)
      = chamberVertexExponent k α ρ j + ((α + (j : ℝ) + 1) - ρ) := by
  classical
  have hmem : (⟨j, hj⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
  have hval : ((⟨j, hj⟩ : Fin k) : ℕ) = j := rfl
  rw [chamberVertexExponent, chamberVertexExponent,
    ← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have hA : (if ((⟨j, hj⟩ : Fin k) : ℕ) + 1 ≤ j + 1 then α + ((⟨j, hj⟩ : Fin k) : ℕ) + 1 else ρ)
      = α + (j : ℝ) + 1 := by rw [hval, if_pos (by omega)]
  have hB : (if ((⟨j, hj⟩ : Fin k) : ℕ) + 1 ≤ j then α + ((⟨j, hj⟩ : Fin k) : ℕ) + 1 else ρ)
      = ρ := by rw [hval, if_neg (by omega)]
  have hrest : (∑ i ∈ (Finset.univ : Finset (Fin k)).erase ⟨j, hj⟩,
        if (i : ℕ) + 1 ≤ j + 1 then α + (i : ℕ) + 1 else ρ)
      = ∑ i ∈ (Finset.univ : Finset (Fin k)).erase ⟨j, hj⟩,
        if (i : ℕ) + 1 ≤ j then α + (i : ℕ) + 1 else ρ := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : (i : ℕ) ≠ j := by
      intro h
      exact (Finset.ne_of_mem_erase hi) (Fin.ext (by simpa [hval] using h))
    by_cases hlt : (i : ℕ) < j
    · rw [if_pos (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]
  rw [hA, hB, hrest]
  ring

/-- **Print's resonance, derived.** If the vertices `j` and `j+1` carry the same exponent — the
case `j₀ = 1`, `N⋆ = 2` of print — then `A_{j+1} = ρ`, which is print's `a_{j*} = 0`. -/
public theorem resonance_of_chamberVertexExponent_eq {k : ℕ} {α ρ : ℝ} {j : ℕ} (hj : j < k)
    (h : chamberVertexExponent k α ρ (j + 1) = chamberVertexExponent k α ρ j) :
    α + (j : ℝ) + 1 = ρ := by
  have := chamberVertexExponent_succ α ρ hj
  rw [h] at this
  linarith

/-- The edge sector contributes at most the whole chamber integral. -/
public theorem setIntegral_chamberOmegaEdge_le_chamberI {k : ℕ} {T α ρ : ℝ} {m : ℕ}
    (hα : -1 < α) (hρ : 0 ≤ ρ) (hT : 2 * (4:ℝ) ^ k ≤ T) (hT0 : 0 ≤ T) :
    (∫ s in chamberOmegaEdge k T m, chamberFT k T α ρ s) ≤ chamberI k T α ρ := by
  refine MeasureTheory.setIntegral_mono_set (integrableOn_chamberFT hT0 hα hρ) ?_
    (Filter.Eventually.of_forall (chamberOmegaEdge_subset_chamberDelta hT))
  filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_chamberDelta k)] with s hs
  exact chamberFT_nonneg hT0 hs

/-- **Lemma A.5(iv), the resonant case `N⋆ = 2`.** If two adjacent vertices `m` and `m+1`
attain `E⋆`, then `I(T) ≥ κ₄ T^{-E⋆} log T`. The hypothesis is stated as the equality of the
two vertex exponents — print's `j₀ = 1` — and the resonance A.2(iii) needs is derived from it. -/
public theorem chamberA5_lower_log {k : ℕ} {T α ρ : ℝ} {m : ℕ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hm : m < k) (hmin : chamberVertexExponent k α ρ m = chamberMinExponent k α ρ)
    (hadj : chamberVertexExponent k α ρ (m + 1) = chamberVertexExponent k α ρ m)
    (hT3 : 3 ≤ T) (hTk : 2 * (4:ℝ) ^ k ≤ T) (hT16 : (16:ℝ) ^ k ≤ T) :
    chamberKappa4 k α ρ m * (T ^ (-chamberMinExponent k α ρ) * Real.log T)
      ≤ chamberI k T α ρ := by
  have hres := resonance_of_chamberVertexExponent_eq hm hadj
  rw [← hmin]
  exact le_trans (chamberA5_edge hα hρ hres hm hT3 hTk hT16)
    (setIntegral_chamberOmegaEdge_le_chamberI hα hρ hTk (by linarith))

/-- **Lemma A.5(iv), print's statement.** `I(T) ≥ C₋ T^{-E⋆} (log T)^{N⋆-1}` with
`C₋ = min(κ₃, κ₄) > 0`, in the two cases print distinguishes: `N⋆ = 1`, where the power of the
logarithm is `0` and clause (ii) is the whole content, and `N⋆ = 2`, where two adjacent
vertices attain `E⋆` and clause (iii) supplies the single logarithm. The multiplicity is
carried as the exponent `n` of `(log T)^n`, so the statement covers both at once. -/
public theorem chamberA5_matching {k : ℕ} {T α ρ : ℝ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hT3 : 3 ≤ T) (hTk : 2 * (4:ℝ) ^ k ≤ T) (hT16 : (16:ℝ) ^ k ≤ T)
    (n : ℕ) (m : ℕ)
    (hcase : n = 0 ∨ (n = 1 ∧ m < k ∧
      chamberVertexExponent k α ρ m = chamberMinExponent k α ρ ∧
      chamberVertexExponent k α ρ (m + 1) = chamberVertexExponent k α ρ m)) :
    ∃ C : ℝ, 0 < C ∧
      C * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n) ≤ chamberI k T α ρ := by
  rcases hcase with rfl | ⟨rfl, hm, hmin, hadj⟩
  · refine ⟨chamberKappa3 k α ρ, chamberKappa3_pos, ?_⟩
    simpa using chamberA5_lower hα hρ hT3 hTk
  · refine ⟨chamberKappa4 k α ρ m, chamberKappa4_pos, ?_⟩
    simpa using chamberA5_lower_log hα hρ hm hmin hadj hT3 hTk hT16


/-! ### Lemma A.5(v): the threshold is immaterial

Print's two observations. First, `T ↦ I(T)` is nonincreasing on `[3, ∞)`, because every factor
`(1 + T s_i)^{-ρ}` is nonincreasing in `T` pointwise on `Δ` and integration preserves the
inequality. Second, `E⋆ > 0`, being a sum of `k ≥ 1` positive numbers. Together they push the
bound of clause (iv) down from `T₀` to `3`, changing only the constant — which is what makes
the matching lower bound comparable with `chamberA4_upper`, itself stated at `T ≥ 3`. -/

/-- `F_T` is pointwise nonincreasing in `T` on `Δ`: only the factors `(1 + T s_i)^{-ρ}` see
`T`, and each is nonincreasing because `s_i > 0` and `-ρ ≤ 0`. -/
public theorem chamberFT_antitone_T {k : ℕ} {T T' α ρ : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T')
    (hρ : 0 ≤ ρ) {s : Fin k → ℝ} (hs : s ∈ chamberDelta k) :
    chamberFT k T' α ρ s ≤ chamberFT k T α ρ s := by
  have hpos : ∀ i : Fin k, 0 < s i := (mem_chamberDelta.mp hs).1
  have hfac : ∀ i : Fin k, (1 + T' * s i) ^ (-ρ) ≤ (1 + T * s i) ^ (-ρ) := fun i =>
    Real.rpow_le_rpow_of_nonpos (by nlinarith [hpos i]) (by nlinarith [hpos i]) (by linarith)
  have hlead : (0:ℝ) ≤ Real.exp (-∑ i, s i) * (∏ i, s i ^ α) * chamberVandermonde s := by
    refine mul_nonneg (mul_nonneg (Real.exp_pos _).le ?_) (chamberVandermonde_nonneg hs)
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpos i).le _
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => ?_) fun i _ => hfac i) hlead
  exact Real.rpow_nonneg (by nlinarith [hpos i]) _

/-- **Lemma A.5(v), first observation.** `T ↦ I(T)` is nonincreasing on `[0, ∞)`. -/
public theorem chamberI_antitone_T {k : ℕ} {T T' α ρ : ℝ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (hTT' : T ≤ T') : chamberI k T' α ρ ≤ chamberI k T α ρ := by
  refine setIntegral_mono_on (integrableOn_chamberFT (by linarith) hα hρ)
    (integrableOn_chamberFT hT hα hρ) (measurableSet_chamberDelta k) fun s hs => ?_
  exact chamberFT_antitone_T hT hTT' hρ hs

/-- **Lemma A.5(v), second observation.** `E⋆ > 0`: print's "the sum of the `k ≥ 1` strictly
positive numbers `min(α + i, ρ)`", here directly because every summand of every `E_j` is
either some `A_i > 0` or `ρ > 0`. -/
public theorem chamberMinExponent_pos {k : ℕ} {α ρ : ℝ} (hα : -1 < α) (hρ : 0 < ρ)
    (hk : 0 < k) : 0 < chamberMinExponent k α ρ := by
  have hpos : ∀ j ∈ Finset.range (k + 1), 0 < chamberVertexExponent k α ρ j := by
    intro j _
    refine Finset.sum_pos (fun i _ => ?_) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    by_cases h : (i : ℕ) + 1 ≤ j
    · rw [if_pos h]; exact chamberIndex_pos hα i
    · rw [if_neg h]; exact hρ
  obtain ⟨j, hj, hje⟩ := exists_chamberMinExponent k α ρ
  rw [hje]
  exact hpos j hj

/-- **Lemma A.5(iv) with print's threshold, uniformly in `T`.** The constant is independent of
`T`, which is what clause (v) needs in order to trade the threshold for a smaller constant. -/
public theorem chamberA5_matching_of_T0 {k : ℕ} {α ρ : ℝ} (hα : -1 < α) (hρ : 0 ≤ ρ)
    (n m : ℕ)
    (hcase : n = 0 ∨ (n = 1 ∧ m < k ∧
      chamberVertexExponent k α ρ m = chamberMinExponent k α ρ ∧
      chamberVertexExponent k α ρ (m + 1) = chamberVertexExponent k α ρ m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, (16:ℝ) ^ (k + 1) ≤ T →
      C * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n) ≤ chamberI k T α ρ := by
  have h16 : (16:ℝ) ^ k ≤ 16 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨h3, hk4⟩ := chamberT0_le k
  rcases hcase with rfl | ⟨rfl, hm, hmin, hadj⟩
  · refine ⟨chamberKappa3 k α ρ, chamberKappa3_pos, fun T hT => ?_⟩
    simpa using chamberA5_lower hα hρ (le_trans h3 hT) (le_trans hk4 hT)
  · refine ⟨chamberKappa4 k α ρ m, chamberKappa4_pos, fun T hT => ?_⟩
    simpa using chamberA5_lower_log hα hρ hm hmin hadj (le_trans h3 hT) (le_trans hk4 hT)
      (le_trans h16 hT)

/-- **Lemma A.5(v).** The matching lower bound holds on the whole range `T ≥ 3`, with a
constant depending only on `(k, α, ρ)`. Print's `C₋' = C₋ (3/T₀)^{E⋆}`; here the constant is
produced rather than named, since only its positivity and its independence of `T` are used
downstream.

Print's two ranges are the two branches below. Above `T₀` the bound of clause (iv) is used as
it stands. Below `T₀`, `I(T) ≥ I(T₀)` by the first observation, while
`T^{-E⋆}(log T)^n ≤ 3^{-E⋆}(log T₀)^n` by the second — this is the only place `E⋆ > 0` is
needed, and it is needed exactly where print needs it. -/
public theorem chamberA5_matching_three {k : ℕ} {α ρ : ℝ} (hα : -1 < α) (hρ : 0 < ρ)
    (hk : 0 < k) (n m : ℕ)
    (hcase : n = 0 ∨ (n = 1 ∧ m < k ∧
      chamberVertexExponent k α ρ m = chamberMinExponent k α ρ ∧
      chamberVertexExponent k α ρ (m + 1) = chamberVertexExponent k α ρ m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
      C * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n) ≤ chamberI k T α ρ := by
  obtain ⟨C, hC, hbound⟩ := chamberA5_matching_of_T0 hα hρ.le n m hcase
  obtain ⟨h3T0, -⟩ := chamberT0_le k
  set T₀ : ℝ := (16:ℝ) ^ (k + 1) with hT₀def
  have hT₀3 : 3 ≤ T₀ := h3T0
  have hT₀0 : (0:ℝ) < T₀ := by linarith
  have hE : 0 < chamberMinExponent k α ρ := chamberMinExponent_pos hα hρ hk
  have hlogT₀ : 0 ≤ Real.log T₀ := Real.log_nonneg (by linarith)
  -- print's `(3 / T₀)^{E⋆}`
  have hratio : (0:ℝ) < (3 / T₀) ^ chamberMinExponent k α ρ :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C * (3 / T₀) ^ chamberMinExponent k α ρ, mul_pos hC hratio, fun T hT => ?_⟩
  by_cases hcase' : T₀ ≤ T
  · -- above the threshold: clause (iv), weakened by `(3/T₀)^{E⋆} ≤ 1`
    have hle1 : (3 / T₀) ^ chamberMinExponent k α ρ ≤ 1 := by
      refine Real.rpow_le_one (by positivity) ?_ hE.le
      rw [div_le_one hT₀0]; linarith
    have hw : (0:ℝ) ≤ T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n := by
      have h1 : (0:ℝ) < T ^ (-chamberMinExponent k α ρ) :=
        Real.rpow_pos_of_pos (by linarith) _
      have h2 : (0:ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
      positivity
    calc C * (3 / T₀) ^ chamberMinExponent k α ρ
          * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n)
        ≤ C * 1 * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle1 hC.le) hw
      _ = C * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n) := by ring
      _ ≤ chamberI k T α ρ := hbound T hcase'
  · -- below the threshold: monotonicity of `I`, and the scale is dominated at `T = 3`
    have hTle : T ≤ T₀ := (not_le.mp hcase').le
    have hImono : chamberI k T₀ α ρ ≤ chamberI k T α ρ :=
      chamberI_antitone_T hα hρ.le (by linarith) hTle
    have hbase := hbound T₀ (le_refl _)
    -- `T^{-E⋆} (log T)^n ≤ 3^{-E⋆} (log T₀)^n`
    have hpow : T ^ (-chamberMinExponent k α ρ) ≤ (3:ℝ) ^ (-chamberMinExponent k α ρ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hT (by linarith)
    have hlog : Real.log T ^ n ≤ Real.log T₀ ^ n :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hTle) n
    have hscale : T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n
        ≤ (3:ℝ) ^ (-chamberMinExponent k α ρ) * Real.log T₀ ^ n := by
      refine mul_le_mul hpow hlog (pow_nonneg (Real.log_nonneg (by linarith)) n) ?_
      exact (Real.rpow_pos_of_pos (by norm_num) _).le
    -- `(3/T₀)^{E⋆} · 3^{-E⋆} = T₀^{-E⋆}`
    have hid : (3 / T₀) ^ chamberMinExponent k α ρ * (3:ℝ) ^ (-chamberMinExponent k α ρ)
        = T₀ ^ (-chamberMinExponent k α ρ) := by
      rw [Real.div_rpow (by norm_num) hT₀0.le, Real.rpow_neg (by norm_num),
        Real.rpow_neg hT₀0.le, div_mul_eq_mul_div, mul_inv_cancel₀
          (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _).ne',
        one_div, ← Real.rpow_neg hT₀0.le]
    calc C * (3 / T₀) ^ chamberMinExponent k α ρ
          * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ n)
        ≤ C * (3 / T₀) ^ chamberMinExponent k α ρ
            * ((3:ℝ) ^ (-chamberMinExponent k α ρ) * Real.log T₀ ^ n) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = C * (T₀ ^ (-chamberMinExponent k α ρ) * Real.log T₀ ^ n) := by
          rw [← hid]; ring
      _ ≤ chamberI k T₀ α ρ := hbase
      _ ≤ chamberI k T α ρ := hImono


/-! ### Lemma A.3(iii)–(iv): `E⋆ = ∑_i min(A_i, ρ)` and `N⋆ ∈ {1, 2}`

The upper bound `chamberA4_upper` produces the exponent `∑_i min(A_i, ρ)` and the logarithmic
power `#{i : A_i = ρ}`, because that is what `chamberTheta` contributes factor by factor. The
lower bound of Lemma A.5 produces `E⋆ = minⱼ E_j`. Corollary 8.16 needs them to be the same
two numbers, which is print's Lemma A.3(iii)–(iv).

Neither identification needs convexity. `E_j ≥ ∑_i min(A_i, ρ)` term by term for every `j`,
and the vertex `j = #{i : A_i ≤ ρ}` attains it, because `A_i = α + i + 1` is increasing in `i`
and so `{i : A_i ≤ ρ}` is exactly an initial segment. That `A_i` is increasing is also why at
most one `i` can have `A_i = ρ`, which is print's `N⋆ ∈ {1, 2}`. -/

/-- Print's `#{i ≤ k : α + i = ρ}`, so that print's `N⋆` is this plus one. -/
@[expose] public noncomputable def chamberResonanceCount (k : ℕ) (α ρ : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin k => α + (i : ℕ) + 1 = ρ).card

/-- **Print's `N⋆ ∈ {1, 2}`.** `A_i = α + i + 1` is injective in `i`, so at most one coordinate
resonates. Print derives this from strict convexity (Proposition 8.18); it is immediate from
the increment being exactly `1`. -/
public theorem chamberResonanceCount_le_one (k : ℕ) (α ρ : ℝ) :
    chamberResonanceCount k α ρ ≤ 1 := by
  classical
  rw [chamberResonanceCount, Finset.card_le_one]
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith [hi, hj]
  exact Fin.ext (Nat.cast_injective this)

/-- The initial-segment property: for a coordinate of `Fin k`, being below the count of
resonance-or-below indices is the same as being resonance-or-below. This is the only place the
monotonicity of `i ↦ A_i` is used. -/
public theorem lt_card_filter_iff {k : ℕ} {α ρ : ℝ} (i : Fin k) :
    (i : ℕ) < (Finset.univ.filter fun i : Fin k => α + (i : ℕ) + 1 ≤ ρ).card
      ↔ α + (i : ℕ) + 1 ≤ ρ := by
  classical
  set S : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => α + (i : ℕ) + 1 ≤ ρ) with hS
  have hmemS : ∀ x : Fin k, x ∈ S ↔ α + (x : ℕ) + 1 ≤ ρ := by
    intro x
    simp [hS]
  constructor
  · intro hlt
    by_contra hcon
    -- every element of `S` sits strictly below `i`, so `S.card ≤ i`
    have hsub : S ⊆ Finset.Iio i := by
      intro x hx
      have hxle := (hmemS x).mp hx
      refine Finset.mem_Iio.2 (Fin.lt_def.2 ?_)
      by_contra hnl
      have hij : (i : ℕ) ≤ (x : ℕ) := by omega
      have : α + (i : ℕ) + 1 ≤ α + (x : ℕ) + 1 := by
        have : ((i : ℕ) : ℝ) ≤ ((x : ℕ) : ℝ) := (Nat.cast_le (α := ℝ)).2 hij
        linarith
      exact hcon (le_trans this hxle)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hle
    -- every index at or below `i` lies in `S`, so `S.card ≥ i + 1`
    have hsub : Finset.Iic i ⊆ S := by
      intro x hx
      have hxi : (x : ℕ) ≤ (i : ℕ) := Fin.le_def.1 (Finset.mem_Iic.1 hx)
      refine (hmemS x).mpr (le_trans ?_ hle)
      have : ((x : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := (Nat.cast_le (α := ℝ)).2 hxi
      linarith
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

/-- **Lemma A.3(iii).** `E⋆ = ∑_i min(A_i, ρ)`: the minimum over the `k + 1` vertices of the
order polytope equals the coordinatewise minimum, attained at the vertex
`j = #{i : A_i ≤ ρ}`. -/
public theorem chamberMinExponent_eq_sum_min (k : ℕ) (α ρ : ℝ) :
    chamberMinExponent k α ρ = ∑ i : Fin k, min (α + (i : ℕ) + 1) ρ := by
  classical
  set N : ℕ := (Finset.univ.filter fun i : Fin k => α + (i : ℕ) + 1 ≤ ρ).card with hN
  have hattain : chamberVertexExponent k α ρ N = ∑ i : Fin k, min (α + (i : ℕ) + 1) ρ := by
    rw [chamberVertexExponent]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : α + (i : ℕ) + 1 ≤ ρ
    · rw [if_pos (by have := (lt_card_filter_iff (α := α) (ρ := ρ) i).mpr hi; omega),
        min_eq_left hi]
    · rw [if_neg (by
        have hnl : ¬ ((i : ℕ) < N) := fun h =>
          hi ((lt_card_filter_iff (α := α) (ρ := ρ) i).mp h)
        omega), min_eq_right (by linarith)]
  have hNmem : N ∈ Finset.range (k + 1) := by
    have : N ≤ k := le_trans (Finset.card_le_card (Finset.subset_univ _))
      (by simp [Finset.card_univ])
    exact Finset.mem_range.2 (by omega)
  refine le_antisymm ?_ ?_
  · rw [← hattain, chamberMinExponent]
    exact Finset.inf'_le _ hNmem
  · rw [chamberMinExponent]
    refine Finset.le_inf' _ _ fun j _ => ?_
    rw [chamberVertexExponent]
    refine Finset.sum_le_sum fun i _ => ?_
    split
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- **Lemma A.3(iv), the resonant vertex.** If `A_m = ρ` then the vertex `m` attains `E⋆`, and
so — by `chamberVertexExponent_succ` — does `m + 1`: print's pair of adjacent minimizers. -/
public theorem chamberVertexExponent_eq_min_of_resonance {k : ℕ} {α ρ : ℝ} {m : ℕ}
    (hres : α + (m : ℝ) + 1 = ρ) :
    chamberVertexExponent k α ρ m = chamberMinExponent k α ρ := by
  rw [chamberMinExponent_eq_sum_min, chamberVertexExponent]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) + 1 ≤ m
  · rw [if_pos hi, min_eq_left]
    have : ((i : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).2 (show (i : ℕ) + 1 ≤ m from hi)
      push_cast at h
      linarith
    linarith
  · rw [if_neg hi, min_eq_right]
    have : (m : ℝ) ≤ ((i : ℕ) : ℝ) := (Nat.cast_le (α := ℝ)).2 (by omega)
    linarith


/-! ### Corollary 8.16: the order of `J`

> **Corollary 8.16 (Order of `J`).** Let `k ≥ 1` be an integer and let `α > −1` and `ρ > 0` be
> real. With `J` as in Definition 8.12 and `E⋆`, `N⋆` as in (8.13)–(8.14), there are constants
> `0 < c ≤ C < ∞`, depending only on `(k, α, ρ)`, such that
>
>     c T^{-E⋆}(log T)^{N⋆-1} ≤ J(T) ≤ C T^{-E⋆}(log T)^{N⋆-1}    for all T ≥ 3.

The upper half is `chamberA4_upper` with `∏_i Θ` evaluated; the lower half is Lemma A.5(v);
the two exponents are identified by `chamberMinExponent_eq_sum_min`, and `N⋆ − 1` is
`chamberResonanceCount`, which `chamberResonanceCount_le_one` pins to `{0, 1}` — print's
`N⋆ ∈ {1, 2}`. Both constants are `k!` times the ones for `I`, by Lemma 8.15.

Print's remark at the point of use (Proposition 8.17) is worth recording: *"α is a half-integer
here and ρ need not be an integer, but neither the corollary nor anything it rests on assumes
more than `α > −1` and `ρ > 0`."* Nothing below assumes any integrality of `α` or `ρ`. -/

/-- `∏_i Θ(T; A_i, ρ) = T^{-∑_i min(A_i,ρ)} (log T)^{#{i : A_i = ρ}}`: the upper bound's shape,
read off from `chamberTheta` factor by factor. -/
public theorem prod_chamberTheta {k : ℕ} {T α ρ : ℝ} (hT0 : 0 < T) :
    (∏ i : Fin k, chamberTheta T (α + (i : ℕ) + 1) ρ)
      = T ^ (-∑ i : Fin k, min (α + (i : ℕ) + 1) ρ)
        * Real.log T ^ chamberResonanceCount k α ρ := by
  classical
  simp only [chamberTheta]
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← Real.rpow_sum_of_pos hT0, ← Finset.sum_neg_distrib]
  · rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      chamberResonanceCount]

/-- The upper constant of Corollary 8.16 for `I`, print's `C₊ = ∏_i κ(A_i, ρ)`. -/
@[expose] public noncomputable def chamberCPlus (k : ℕ) (α ρ : ℝ) : ℝ :=
  ∏ i : Fin k, kappaA2 (α + (i : ℕ) + 1) ρ

public theorem chamberCPlus_pos (k : ℕ) (α ρ : ℝ) : 0 < chamberCPlus k α ρ :=
  Finset.prod_pos fun _i _ => kappaA2_pos _ _

/-- **The upper half of Corollary 8.16, for `I`.** -/
public theorem chamberA4_upper_eval {k : ℕ} {T α ρ : ℝ} (hT : 3 ≤ T) (hα : -1 < α)
    (hρ : 0 ≤ ρ) :
    chamberI k T α ρ
      ≤ chamberCPlus k α ρ
        * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ chamberResonanceCount k α ρ) := by
  have hT0 : (0:ℝ) < T := by linarith
  refine le_trans (chamberA4_upper hT hα hρ) (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, prod_chamberTheta hT0, chamberMinExponent_eq_sum_min,
    chamberCPlus]

/-- If a coordinate resonates, that coordinate's index is a minimizing vertex and so is the
next one: print's `j₋` and `j* = j₋ + 1`. -/
public theorem exists_resonant_vertex {k : ℕ} {α ρ : ℝ}
    (hn : chamberResonanceCount k α ρ = 1) :
    ∃ m : ℕ, m < k ∧ chamberVertexExponent k α ρ m = chamberMinExponent k α ρ ∧
      chamberVertexExponent k α ρ (m + 1) = chamberVertexExponent k α ρ m := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hn
  have hmem : i ∈ Finset.univ.filter fun i : Fin k => α + (i : ℕ) + 1 = ρ := by
    rw [hi]; exact Finset.mem_singleton_self i
  have hres : α + ((i : ℕ) : ℝ) + 1 = ρ := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  refine ⟨(i : ℕ), i.isLt, chamberVertexExponent_eq_min_of_resonance hres, ?_⟩
  rw [chamberVertexExponent_succ α ρ i.isLt, hres]
  ring

/-- **Corollary 8.16.** Two-sided, on print's full range `T ≥ 3`, with both constants depending
only on `(k, α, ρ)`. `chamberResonanceCount` is print's `N⋆ − 1`. -/
public theorem chamberCor816 {k : ℕ} {α ρ : ℝ} (hα : -1 < α) (hρ : 0 < ρ) (hk : 0 < k) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ T : ℝ, 3 ≤ T →
      c * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ chamberResonanceCount k α ρ)
          ≤ chamberJFull k T α ρ ∧
        chamberJFull k T α ρ
          ≤ C * (T ^ (-chamberMinExponent k α ρ)
            * Real.log T ^ chamberResonanceCount k α ρ) := by
  -- the lower constant, from Lemma A.5(v) in whichever of print's two cases applies
  have hcase : chamberResonanceCount k α ρ = 0 ∨
      (chamberResonanceCount k α ρ = 1 ∧ ∃ m : ℕ, m < k ∧
        chamberVertexExponent k α ρ m = chamberMinExponent k α ρ ∧
        chamberVertexExponent k α ρ (m + 1) = chamberVertexExponent k α ρ m) := by
    rcases Nat.lt_or_ge (chamberResonanceCount k α ρ) 1 with h | h
    · exact Or.inl (by omega)
    · have h1 : chamberResonanceCount k α ρ = 1 :=
        le_antisymm (chamberResonanceCount_le_one k α ρ) h
      exact Or.inr ⟨h1, exists_resonant_vertex h1⟩
  obtain ⟨Cm, hCm, hlow⟩ :
      ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
        C * (T ^ (-chamberMinExponent k α ρ)
          * Real.log T ^ chamberResonanceCount k α ρ) ≤ chamberI k T α ρ := by
    rcases hcase with h0 | ⟨h1, m, hm, hmin, hadj⟩
    · rw [h0]
      exact chamberA5_matching_three hα hρ hk 0 0 (Or.inl rfl)
    · rw [h1]
      exact chamberA5_matching_three hα hρ hk 1 m (Or.inr ⟨rfl, hm, hmin, hadj⟩)
  have hfac : (0:ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  refine ⟨(Nat.factorial k : ℝ) * Cm, (Nat.factorial k : ℝ) * chamberCPlus k α ρ,
    mul_pos hfac hCm, ?_, fun T hT => ?_⟩
  · -- `c ≤ C`, since the two-sided bounds at `T = 3` force it
    refine mul_le_mul_of_nonneg_left ?_ hfac.le
    have h3 : (3:ℝ) ≤ 3 := le_refl 3
    have hlo := hlow 3 h3
    have hhi := chamberA4_upper_eval (k := k) (T := 3) (α := α) (ρ := ρ) h3 hα hρ.le
    have hw : (0:ℝ) < (3:ℝ) ^ (-chamberMinExponent k α ρ)
        * Real.log 3 ^ chamberResonanceCount k α ρ := by
      have h1 : (0:ℝ) < (3:ℝ) ^ (-chamberMinExponent k α ρ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h2 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      positivity
    exact le_of_mul_le_mul_right (by linarith) hw
  · have hJ : chamberJFull k T α ρ = (Nat.factorial k : ℝ) * chamberI k T α ρ :=
      chamberJFull_eq_factorial_mul_chamberI (by linarith) hα hρ.le
    rw [hJ]
    refine ⟨?_, ?_⟩
    · rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hlow T hT) hfac.le
    · rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (chamberA4_upper_eval hT hα hρ.le) hfac.le


/-! ## The multiplicity: `N⋆ = #{i : A_i = ρ} + 1`

`chamberResonanceCount` counts the coordinates whose exponent ties with `ρ`, and print's `N⋆` is
the number of vertices attaining `E⋆`. That the two differ by one is print's Proposition 8.18
read at the minimum, and it needs no convexity beyond the increment being exactly `1`:

* two minimizers cannot be more than one apart. If `s < s'` both attain `E⋆` then
  `a_{s+1} = E_{s+1} − E_s ≥ 0` and `a_{s'} = E_{s'} − E_{s'−1} ≤ 0`, while `a` is increasing and
  `s + 1 ≤ s'`; so both vanish, and `a` increasing by exactly one forces `s + 1 = s'`.
* if there are two, the increment between them vanishes, which is the resonance
  `α + s + 1 = ρ`; and conversely a resonance produces two, by
  `chamberVertexExponent_eq_min_of_resonance` and `chamberVertexExponent_succ`.

So the minimizer set is a single vertex or an adjacent pair, and it is a pair exactly when a
coordinate resonates. -/

section Multiplicity

open scoped Classical

/-- Print's minimizing vertices: the `s ∈ {0, …, k}` attaining `E⋆`. Its cardinality is
print's `N⋆`. -/
@[expose] public noncomputable def chamberMinimizers (k : ℕ) (α ρ : ℝ) : Finset ℕ :=
  (Finset.range (k + 1)).filter
    fun s => chamberVertexExponent k α ρ s = chamberMinExponent k α ρ

public theorem mem_chamberMinimizers {k : ℕ} {α ρ : ℝ} {s : ℕ} :
    s ∈ chamberMinimizers k α ρ ↔
      s ≤ k ∧ chamberVertexExponent k α ρ s = chamberMinExponent k α ρ := by
  rw [chamberMinimizers, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

public theorem chamberMinimizers_nonempty (k : ℕ) (α ρ : ℝ) :
    (chamberMinimizers k α ρ).Nonempty := by
  obtain ⟨j, hj, hval⟩ := exists_chamberMinExponent k α ρ
  exact ⟨j, mem_chamberMinimizers.2
    ⟨Nat.lt_succ_iff.1 (Finset.mem_range.1 hj), hval.symm⟩⟩

/-- Every vertex exponent is at least the minimum. -/
public theorem chamberMinExponent_le {k : ℕ} (α ρ : ℝ) {s : ℕ} (hs : s ≤ k) :
    chamberMinExponent k α ρ ≤ chamberVertexExponent k α ρ s :=
  Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hs))

/-- **Two minimizers are adjacent.** -/
public theorem chamberMinimizers_adjacent {k : ℕ} {α ρ : ℝ} {s s' : ℕ}
    (hs : s ∈ chamberMinimizers k α ρ) (hs' : s' ∈ chamberMinimizers k α ρ) (hlt : s < s') :
    s' = s + 1 := by
  obtain ⟨hsk, hsv⟩ := mem_chamberMinimizers.1 hs
  obtain ⟨hs'k, hs'v⟩ := mem_chamberMinimizers.1 hs'
  by_contra hne
  have h2 : s + 2 ≤ s' := by omega
  -- the increment out of `s` is nonnegative
  have hsk1 : s < k := by omega
  have hstep := chamberVertexExponent_succ (k := k) α ρ hsk1
  have hge : chamberMinExponent k α ρ ≤ chamberVertexExponent k α ρ (s + 1) :=
    chamberMinExponent_le α ρ (by omega)
  have ha1 : (0:ℝ) ≤ α + (s : ℝ) + 1 - ρ := by
    rw [hsv] at hstep
    linarith [hstep, hge]
  -- the increment into `s'` is nonpositive
  have hpred : s' - 1 < k := by omega
  have hs'eq : s' - 1 + 1 = s' := by omega
  have hstep' := chamberVertexExponent_succ (k := k) α ρ hpred
  rw [hs'eq, hs'v] at hstep'
  have hge' : chamberMinExponent k α ρ ≤ chamberVertexExponent k α ρ (s' - 1) :=
    chamberMinExponent_le α ρ (by omega)
  have ha2 : α + ((s' - 1 : ℕ) : ℝ) + 1 - ρ ≤ 0 := by linarith [hstep', hge']
  -- but the increments increase, and `s + 1 ≤ s' - 1`
  have hmono : (s : ℝ) ≤ ((s' - 1 : ℕ) : ℝ) := by
    have : s ≤ s' - 1 := by omega
    exact_mod_cast this
  have hlt' : (s : ℝ) < ((s' - 1 : ℕ) : ℝ) := by
    have : s < s' - 1 := by omega
    exact_mod_cast this
  linarith

/-- **A pair of minimizers is a resonance.** -/
public theorem resonance_of_two_minimizers {k : ℕ} {α ρ : ℝ} {s : ℕ}
    (hs : s ∈ chamberMinimizers k α ρ) (hs1 : s + 1 ∈ chamberMinimizers k α ρ) :
    α + (s : ℝ) + 1 = ρ := by
  obtain ⟨hsk, hsv⟩ := mem_chamberMinimizers.1 hs
  obtain ⟨hs1k, hs1v⟩ := mem_chamberMinimizers.1 hs1
  have hsk1 : s < k := by omega
  have hstep := chamberVertexExponent_succ (k := k) α ρ hsk1
  rw [hsv, hs1v] at hstep
  linarith

/-- **`N⋆ = #{i : A_i = ρ} + 1`.** The minimizer set is a single vertex, or an adjacent pair
exactly when one coordinate resonates. -/
public theorem chamberMinimizers_card (k : ℕ) (α ρ : ℝ) :
    (chamberMinimizers k α ρ).card = chamberResonanceCount k α ρ + 1 := by
  classical
  obtain ⟨s₀, hs₀⟩ := chamberMinimizers_nonempty k α ρ
  -- every minimizer is `s₀'` or `s₀' + 1` for the least one
  set s₁ := (chamberMinimizers k α ρ).min' ⟨s₀, hs₀⟩ with hs₁
  have hs₁mem : s₁ ∈ chamberMinimizers k α ρ := Finset.min'_mem _ _
  have hsub : chamberMinimizers k α ρ ⊆ {s₁, s₁ + 1} := by
    intro s hs
    have hle : s₁ ≤ s := Finset.min'_le _ _ hs
    rcases eq_or_lt_of_le hle with h | h
    · simp [← h]
    · have := chamberMinimizers_adjacent hs₁mem hs h
      simp [this]
  have hcard2 : (chamberMinimizers k α ρ).card ≤ 2 := by
    refine le_trans (Finset.card_le_card hsub) ?_
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  rcases Nat.lt_or_ge (chamberResonanceCount k α ρ) 1 with hres | hres
  · -- no resonance: the minimizer is unique
    have hres0 : chamberResonanceCount k α ρ = 0 := by omega
    rw [hres0]
    refine le_antisymm ?_ (Finset.card_pos.2 ⟨s₀, hs₀⟩)
    by_contra hlt
    have h2 : 2 ≤ (chamberMinimizers k α ρ).card := by omega
    have hpair : s₁ + 1 ∈ chamberMinimizers k α ρ := by
      by_contra hnot
      have : chamberMinimizers k α ρ ⊆ {s₁} := by
        intro s hs
        rcases Finset.mem_insert.1 (hsub hs) with h | h
        · simpa using h
        · exfalso
          apply hnot
          have hseq : s = s₁ + 1 := by simpa using h
          rwa [hseq] at hs
      have := Finset.card_le_card this
      simp at this
      omega
    have hr := resonance_of_two_minimizers hs₁mem hpair
    have hs₁k : s₁ < k := by
      obtain ⟨hk, -⟩ := mem_chamberMinimizers.1 hpair
      omega
    have : (⟨s₁, hs₁k⟩ : Fin k) ∈
        (Finset.univ.filter fun i : Fin k => α + (i : ℕ) + 1 = ρ) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hr
    have := Finset.card_pos.2 ⟨_, this⟩
    rw [← chamberResonanceCount] at this
    omega
  · -- a resonance: exactly two minimizers
    have hres1 : chamberResonanceCount k α ρ = 1 :=
      le_antisymm (chamberResonanceCount_le_one k α ρ) hres
    rw [hres1]
    obtain ⟨m, hmk, hmin, hadj⟩ := exists_resonant_vertex hres1
    have hm : m ∈ chamberMinimizers k α ρ :=
      mem_chamberMinimizers.2 ⟨by omega, hmin⟩
    have hm1 : m + 1 ∈ chamberMinimizers k α ρ :=
      mem_chamberMinimizers.2 ⟨by omega, by rw [hadj, hmin]⟩
    have hpair : ({m, m + 1} : Finset ℕ) ⊆ chamberMinimizers k α ρ := by
      intro s hs
      rcases Finset.mem_insert.1 hs with h | h
      · exact h ▸ hm
      · exact (by simpa using h) ▸ hm1
    have hge : 2 ≤ (chamberMinimizers k α ρ).card := by
      refine le_trans ?_ (Finset.card_le_card hpair)
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    omega

end Multiplicity

end AISafetyAtlas.SingularLearning
