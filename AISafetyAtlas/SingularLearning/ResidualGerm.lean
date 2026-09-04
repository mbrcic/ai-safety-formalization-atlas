module

public import AISafetyAtlas.SingularLearning.Coordinates
public import AISafetyAtlas.SingularLearning.MatrixNormBridge
public import AISafetyAtlas.SingularLearning.DyadicLocalization
public import AISafetyAtlas.SingularLearning.LayerCake
public import AISafetyAtlas.SingularLearning.TauberianLog

/-!
# The residual germ `‖Y X‖²_F`, in Euclidean coordinates

Section 8 of the MAIS issue #3 candidate determines the local pair of

    f(Y, X) = ‖Y X‖²_F   on   ℝ^{p×h} × ℝ^{h×n} ≅ ℝ^D,   D = ph + hn ,

at the origin. This module puts that germ into the coordinates the atlas's local-pair relations
are stated in, and proves the three structural facts the analysis chain consumes. It proves
nothing asymptotic.

## The three facts

* **Nonnegativity.** `residualGerm_nonneg`. Needed by the layer cake, which represents
  `e^{-Tf}` as an integral over `[f(w), ∞)` and so wants `f ≥ 0`, and by `Lemma 8.6`'s
  temperature-rescaling step, where a hotter integral of a nonnegative germ is a smaller one.
* **Continuity**, hence measurability. `continuous_residualGerm`. Needed by both.
* **Degree-four homogeneity.** `residualGerm_smul`: `f(t·w) = t⁴ f(w)`. This is the whole of
  what Lemma 8.6 uses from the germ — print's Lemma 7.1 homogeneity clause, and the reason the
  dyadic shells are all the same set up to dilation. `(tY)(tX) = t²(YX)`, and the Frobenius
  square of a scalar multiple picks up the square of the scalar.

## Why the germ is defined through `matrixPairEquiv`

`HasLocalVolumeOrder` and `HasExactLocalPair` are relations on `EuclideanSpace ℝ (Fin D)`,
because the pinned Mathlib puts no `MeasureSpace` on `Matrix`. `matrixPairEquiv` of
`Coordinates.lean` is the atlas's packing of a matrix pair into those coordinates, and it is the
one `O70.lean` states `rrrLossCoords` through — so the residual germ and the O70 statement live
in the same coordinates and no later comparison between two packings is needed.

Two properties of that packing matter, and both are proved rather than assumed:
`measurePreserving_matrixPairEquiv` says it is a coordinate reindexing, so no Jacobian is
silently discarded; and `norm_sq_matrixPairEquiv` below says it is an isometry, so the Euclidean
ball the local pair is measured in is the ball of `‖X‖²_F + ‖Y‖²_F`, the norm print uses.

The index order follows `matrixPairEquiv`: the pair is `(X, Y)` with `X : h × n` first, so the
ambient dimension reads `hn + ph`. Print writes `(Y, X)` and `D = ph + hn`; the two are the same
space and the same `D`.

## What is not here

The asymptotics. `hasLocalVolumeOrder_residualGerm` — the theorem that the local pair is
`(E⋆, N⋆)` — needs
Proposition 8.9, the `O70-EIGEN-LAW` frontier, Corollary 8.16, Lemma 8.6 and the Tauberian
transfer, and is assembled elsewhere.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Matrix

/-! ## The Frobenius square under scaling -/

/-- `‖tA‖²_F = t² ‖A‖²_F`. -/
public theorem frobeniusSq_smul {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ℝ)
    (A : Matrix ι κ ℝ) : frobeniusSq (t • A) = t ^ 2 * frobeniusSq A := by
  simp only [frobeniusSq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- `(tY)(tX) = t²(YX)`: the product of two scaled matrices scales quadratically. -/
public theorem smul_mul_smul_eq {ι κ ν : Type*} [Fintype κ] (t : ℝ) (Y : Matrix ι κ ℝ)
    (X : Matrix κ ν ℝ) : (t • Y) * (t • X) = (t ^ 2) • (Y * X) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

/-! ## The packing is an isometry -/

/-- **`matrixPairEquiv` is an isometry**: the Euclidean norm of the packed pair is the sum of the
two Frobenius squares. Together with `measurePreserving_matrixPairEquiv` this says the packing
changes neither the measure nor the metric, so a local pair computed in Euclidean coordinates is
the local pair print speaks about. -/
public theorem norm_sq_matrixPairEquiv (M N H : ℕ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    ‖matrixPairEquiv M N H (A, B)‖ ^ 2 = frobeniusSq A + frobeniusSq B := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hre : ∑ k : Fin (H * N + M * H), matrixPairEquiv M N H (A, B) k ^ 2
      = ∑ s : (Fin H × Fin N) ⊕ (Fin M × Fin H),
          matrixPairEquiv M N H (A, B) (matrixPairIndex M N H s) ^ 2 :=
    (Fintype.sum_equiv (matrixPairIndex M N H) _ _ fun _ => rfl).symm
  rw [hre, Fintype.sum_sum_type]
  have hA : ∑ q : Fin H × Fin N,
      matrixPairEquiv M N H (A, B) (matrixPairIndex M N H (Sum.inl q)) ^ 2
      = frobeniusSq A := by
    rw [frobeniusSq, ← Finset.sum_product']
    exact Finset.sum_congr rfl fun q _ => by
      rw [matrixPairEquiv_apply_inl]
  have hB : ∑ q : Fin M × Fin H,
      matrixPairEquiv M N H (A, B) (matrixPairIndex M N H (Sum.inr q)) ^ 2
      = frobeniusSq B := by
    rw [frobeniusSq, ← Finset.sum_product']
    exact Finset.sum_congr rfl fun q _ => by
      rw [matrixPairEquiv_apply_inr]
  rw [hA, hB]

/-! ## The germ -/

variable {p n h : ℕ}

/-- The `X` block of a point of `ℝ^{hn + ph}`, print's second factor. -/
@[expose] public noncomputable def residualX (p n h : ℕ)
    (w : EuclideanSpace ℝ (Fin (h * n + p * h))) : Matrix (Fin h) (Fin n) ℝ :=
  ((matrixPairEquiv p n h).symm w).1

/-- The `Y` block, print's first factor. -/
@[expose] public noncomputable def residualY (p n h : ℕ)
    (w : EuclideanSpace ℝ (Fin (h * n + p * h))) : Matrix (Fin p) (Fin h) ℝ :=
  ((matrixPairEquiv p n h).symm w).2

/-- **Print's `f(Y, X) = ‖Y X‖²_F`**, on `ℝ^D` with `D = hn + ph`. -/
@[expose] public noncomputable def residualGerm (p n h : ℕ)
    (w : EuclideanSpace ℝ (Fin (h * n + p * h))) : ℝ :=
  frobeniusSq (residualY p n h w * residualX p n h w)

public theorem residualGerm_nonneg (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    0 ≤ residualGerm p n h w :=
  frobeniusSq_nonneg _

/-- The Euclidean norm of a point is the norm print measures the germ's ball in. -/
public theorem norm_sq_residual (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    ‖w‖ ^ 2 = frobeniusSq (residualX p n h w) + frobeniusSq (residualY p n h w) := by
  have hpair : matrixPairEquiv p n h (residualX p n h w, residualY p n h w) = w := by
    rw [residualX, residualY, Prod.mk.eta, LinearEquiv.apply_symm_apply]
  calc ‖w‖ ^ 2
      = ‖matrixPairEquiv p n h (residualX p n h w, residualY p n h w)‖ ^ 2 := by rw [hpair]
    _ = frobeniusSq (residualX p n h w) + frobeniusSq (residualY p n h w) :=
        norm_sq_matrixPairEquiv p n h _ _

public theorem continuous_residualX : Continuous (residualX p n h) :=
  continuous_fst.comp (matrixPairEquiv p n h).symm.toContinuousLinearEquiv.continuous

public theorem continuous_residualY : Continuous (residualY p n h) :=
  continuous_snd.comp (matrixPairEquiv p n h).symm.toContinuousLinearEquiv.continuous

/-- **The germ is continuous**, hence measurable — the hypothesis the layer cake and the dyadic
localisation both take. -/
public theorem continuous_residualGerm : Continuous (residualGerm p n h) :=
  continuous_frobeniusSq.comp (continuous_residualY.matrix_mul continuous_residualX)

public theorem measurable_residualGerm : Measurable (residualGerm p n h) :=
  continuous_residualGerm.measurable

/-- **Degree-four homogeneity**, print's Lemma 7.1 clause: `f(t·w) = t⁴ f(w)`.

This is the only property of the germ that Lemma 8.6's dyadic argument uses. `(tY)(tX)` is
`t²(YX)`, and the Frobenius square of a scalar multiple picks up the square of the scalar. -/
public theorem residualGerm_smul (t : ℝ) (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    residualGerm p n h (t • w) = t ^ 4 * residualGerm p n h w := by
  have hX : residualX p n h (t • w) = t • residualX p n h w := by
    rw [residualX, residualX, map_smul, Prod.smul_fst]
  have hY : residualY p n h (t • w) = t • residualY p n h w := by
    rw [residualY, residualY, map_smul, Prod.smul_snd]
  rw [residualGerm, residualGerm, hX, hY, smul_mul_smul_eq, frobeniusSq_smul]
  ring

/-- The homogeneity clause in the shape `setIntegral_dyadicShell_homogeneous_le` and
`gaussian_le_ball` consume it: degree `k = 4`, for nonnegative scalars. -/
public theorem residualGerm_hom (t : ℝ) (_ht : 0 ≤ t)
    (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    residualGerm p n h (t • w) = t ^ 4 * residualGerm p n h w :=
  residualGerm_smul t w

/-! ## The analytic engine, packaged

Everything the candidate's §8 does between the Laplace transform and the local pair, in one
statement: a nonnegative, measurable, homogeneous germ whose **globally Gaussian-weighted**
Laplace transform is two-sidedly `≍ H_{λ,m}(T)` has local volume order `(λ, m)` at the origin.

Three modules meet here.

* `gaussian_ge_ball` and `gaussian_le_ball` (Lemma 8.6) trade the global weight for the local
  one, at the price of a factor two in the radius. Applying the upper bound at `δ` and the
  lower bound at `δ/2` gives a two-sided estimate at the single radius `δ`.
* `integral_exp_neg_mul_eq_laplaceAverage` (the layer cake) turns that estimate on an integral
  into one on `laplaceAverage` of the sublevel volume.
* `volume_comparable_of_laplace_log` (the log-carrying Tauberian transfer) turns it into
  two-sided `volumeScale` bounds on the sublevel volume itself — exponent and multiplicity both.

Nothing here is specific to `‖YX‖²_F`; the germ enters only through nonnegativity,
measurability and homogeneity. -/

section Engine

open Metric

variable {D : ℕ}

/-- The sublevel volume is monotone in the level. -/
public theorem sublevelVolume_mono_level (f : EuclideanSpace ℝ (Fin D) → ℝ)
    (w : EuclideanSpace ℝ (Fin D)) (δ : ℝ) : Monotone (sublevelVolume f w δ) := by
  intro a b hab
  refine ENNReal.toReal_mono (sublevelVolume_ne_top f w δ b) (measure_mono ?_)
  rintro x ⟨hx, hfx⟩
  exact ⟨hx, hfx.trans hab⟩

/-- The sublevel volume is bounded by the volume of the ball it is taken in. -/
public theorem sublevelVolume_le_ball (f : EuclideanSpace ℝ (Fin D) → ℝ)
    (w : EuclideanSpace ℝ (Fin D)) (δ s : ℝ) :
    sublevelVolume f w δ s ≤ (volume (Metric.ball w δ)).toReal :=
  ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono fun _ hx => hx.1)

/-- **From a Gaussian-weighted Laplace estimate to the local pair.**

If `f` is nonnegative, measurable, homogeneous of some degree `k`, and

    c · H_{λ,m}(T) ≤ ∫ e^{-T f(x)} e^{-‖x‖²} dx ≤ C · H_{λ,m}(T)   for `T ≥ 3`,

then `f` has local volume order `(λ, m)` at the origin. -/
public theorem hasLocalVolumeOrder_of_gaussianLaplace {k : ℕ}
    {f : EuclideanSpace ℝ (Fin D) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ x, f (t • x) = t ^ k * f x)
    {lam : ℝ} {m : ℕ} (hlam : 0 < lam) (hm : 1 ≤ m) {c C : ℝ} (hc : 0 < c)
    (hlo : ∀ T : ℝ, 3 ≤ T →
      c * laplaceScale lam m T ≤ ∫ x, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2))
    (hup : ∀ T : ℝ, 3 ≤ T →
      (∫ x, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2)) ≤ C * laplaceScale lam m T) :
    HasLocalVolumeOrder f 0 lam m := by
  refine Or.inr ⟨hlam, hm, 1, one_pos, ?_⟩
  rintro δ ⟨hδ0, -⟩
  have hδ2 : (0:ℝ) < δ / 2 := by linarith
  set S := ∑' j : ℕ, (2 : ℝ) ^ (j * D) * Real.exp (-((δ / 2) ^ 2) * 4 ^ j) with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun j => by positivity
  have hden : (0:ℝ) < 1 + S := by linarith
  -- Both Lemma 8.6 bounds, at the single radius `δ`.
  have hball : ∀ T : ℝ, 0 ≤ T →
      Real.exp (-(δ ^ 2)) * (∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) δ,
            Real.exp (-T * f y))
          ≤ ∫ x, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2) ∧
        (∫ x, Real.exp (-T * f x) * Real.exp (-‖x‖ ^ 2))
          ≤ (1 + S) * ∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) δ,
              Real.exp (-T * f y) := by
    intro T hT
    refine ⟨gaussian_ge_ball hδ0 hfm hf hT, ?_⟩
    have h := gaussian_le_ball (δ := δ / 2) hδ2 hfm hf hhom hT
    rwa [show 2 * (δ / 2) = δ by ring, ← hS] at h
  -- Transport to `laplaceAverage`.
  have hcake : ∀ T : ℝ, 0 < T →
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin D)) δ, Real.exp (-T * f y))
        = laplaceAverage (sublevelVolume f 0 δ) T := fun T hT =>
    integral_exp_neg_mul_eq_laplaceAverage f 0 δ hT hf hfm
  have hVmono : Monotone (sublevelVolume f 0 δ) := sublevelVolume_mono_level f 0 δ
  have hVnn : ∀ s > (0:ℝ), 0 ≤ sublevelVolume f 0 δ s := fun _ _ => ENNReal.toReal_nonneg
  have hVmax : ∀ s, sublevelVolume f 0 δ s
      ≤ (volume (ball (0 : EuclideanSpace ℝ (Fin D)) δ)).toReal :=
    fun s => sublevelVolume_le_ball f 0 δ s
  -- The two-sided estimate on the Laplace average.
  have hlapLo : ∀ T ≥ (3:ℝ), (c / (1 + S)) * laplaceScale lam m T
      ≤ laplaceAverage (sublevelVolume f 0 δ) T := by
    intro T hT
    have hT0 : (0:ℝ) < T := by linarith
    rw [← hcake T hT0]
    have h1 := hlo T hT
    have h2 := (hball T hT0.le).2
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  have hlapUp : ∀ T ≥ (3:ℝ), laplaceAverage (sublevelVolume f 0 δ) T
      ≤ (Real.exp (δ ^ 2) * C) * laplaceScale lam m T := by
    intro T hT
    have hT0 : (0:ℝ) < T := by linarith
    rw [← hcake T hT0]
    have h1 := (hball T hT0.le).1
    have h2 := hup T hT
    have h3 := h1.trans h2
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (δ ^ 2)).le
    have hexp : Real.exp (δ ^ 2) * Real.exp (-(δ ^ 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [← mul_assoc, hexp, one_mul] at h4
    linarith
  obtain ⟨c₁, hc₁, ε₀, hε₀, hmain⟩ :=
    volume_comparable_of_laplace_log hVmono hVnn hlam hVmax
      (by positivity : (0:ℝ) < c / (1 + S)) (by norm_num : (0:ℝ) < 3) hlapLo hlapUp
  refine ⟨c₁, max c₁ (Real.exp 1 * (Real.exp (δ ^ 2) * C)), hc₁, le_max_left _ _, ?_⟩
  have hmem : Set.Ioo (0:ℝ) (min ε₀ (Real.exp (-1)))
      ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (lt_min hε₀ (Real.exp_pos _))
  filter_upwards [hmem] with ε hε
  obtain ⟨hε0, hεlt⟩ := hε
  have hεε₀ : ε ≤ ε₀ := le_of_lt (lt_of_lt_of_le hεlt (min_le_left _ _))
  have hεe : ε ≤ Real.exp (-1) := le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))
  obtain ⟨hgo, hup'⟩ := hmain ε ⟨hε0, hεε₀⟩
  have hvs : (0:ℝ) ≤ volumeScale lam m ε := by
    rw [volumeScale]
    have hlogε : (0:ℝ) ≤ Real.log (1 / ε) := by
      rw [Real.log_div one_ne_zero hε0.ne', Real.log_one, zero_sub, neg_nonneg]
      have hlt : Real.log ε ≤ Real.log (Real.exp (-1)) := Real.log_le_log hε0 hεe
      rw [Real.log_exp] at hlt
      linarith
    positivity
  refine ⟨hgo, hup'.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) hvs

end Engine

end AISafetyAtlas.SingularLearning
