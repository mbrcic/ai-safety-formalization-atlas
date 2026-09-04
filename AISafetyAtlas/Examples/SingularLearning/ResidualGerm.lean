module

public import AISafetyAtlas.SingularLearning.ResidualGerm

/-!
# Worked models: the residual germ and the analytic engine

`residualGerm p n h` is print's `f(Y, X) = ‖Y X‖²_F` in the coordinates the local-pair relations
are stated in, and `hasLocalVolumeOrder_of_gaussianLaplace` is everything §8 of the candidate
does between a Laplace estimate and the local pair, in one step.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory Metric

/-! ### The germ -/

/-- **Degree-four homogeneity**, the one property of the germ the dyadic argument uses. -/
example (p h n : ℕ) (t : ℝ) (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    residualGerm p n h (t • w) = t ^ 4 * residualGerm p n h w :=
  residualGerm_smul t w

/-- At the scalar stratum `(p, h, n) = (1, 1, 1)` the germ is `(Y X)²`, and scaling `w` by `t`
scales it by `t⁴`. -/
example (t : ℝ) (w : EuclideanSpace ℝ (Fin (1 * 1 + 1 * 1))) :
    residualGerm 1 1 1 (t • w) = t ^ 4 * residualGerm 1 1 1 w :=
  residualGerm_smul t w

/-- The germ is nonnegative, which is what the layer cake needs. -/
example (p h n : ℕ) (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    0 ≤ residualGerm p n h w :=
  residualGerm_nonneg w

/-- **The packing is an isometry**: the Euclidean ball the local pair is measured in is the ball
of `‖Y‖²_F + ‖X‖²_F`, which is the norm print uses. No Jacobian is discarded. -/
example (p h n : ℕ) (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    ‖w‖ ^ 2 = frobeniusSq (residualX p n h w) + frobeniusSq (residualY p n h w) :=
  norm_sq_residual w

/-- **A degenerate stratum**: `h = 0` makes `Y X` a matrix with no inner index, hence zero, so
the germ vanishes identically. This is print's Lemma 8.3. -/
example (p n : ℕ) (w : EuclideanSpace ℝ (Fin (0 * n + p * 0))) : residualGerm p n 0 w = 0 := by
  rw [residualGerm, frobeniusSq]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [Matrix.mul_apply]

/-! ### The sublevel volume -/

example {D : ℕ} (f : EuclideanSpace ℝ (Fin D) → ℝ) (w : EuclideanSpace ℝ (Fin D)) (δ : ℝ) :
    Monotone (sublevelVolume f w δ) :=
  sublevelVolume_mono_level f w δ

example {D : ℕ} (f : EuclideanSpace ℝ (Fin D) → ℝ) (w : EuclideanSpace ℝ (Fin D)) (δ s : ℝ) :
    sublevelVolume f w δ s ≤ (volume (ball w δ)).toReal :=
  sublevelVolume_le_ball f w δ s

/-! ### The engine

The three modules that meet in `hasLocalVolumeOrder_of_gaussianLaplace` — Lemma 8.6, the layer
cake and the log-carrying Tauberian transfer — are each restated here at the germ, so a change
to any of them shows up as a broken example rather than as a broken assembly. -/

/-- **The engine**, at the residual germ: a two-sided Gaussian-weighted Laplace estimate gives
the local volume order at the origin. Degree four is `residualGerm_hom`. -/
example {p h n : ℕ} {lam : ℝ} {m : ℕ} (hlam : 0 < lam) (hm : 1 ≤ m) {c C : ℝ} (hc : 0 < c)
    (hlo : ∀ T : ℝ, 3 ≤ T →
      c * laplaceScale lam m T
        ≤ ∫ x : EuclideanSpace ℝ (Fin (h * n + p * h)),
            Real.exp (-T * residualGerm p n h x) * Real.exp (-‖x‖ ^ 2))
    (hup : ∀ T : ℝ, 3 ≤ T →
      (∫ x : EuclideanSpace ℝ (Fin (h * n + p * h)),
          Real.exp (-T * residualGerm p n h x) * Real.exp (-‖x‖ ^ 2))
        ≤ C * laplaceScale lam m T) :
    HasLocalVolumeOrder (residualGerm p n h) 0 lam m :=
  hasLocalVolumeOrder_of_gaussianLaplace (k := 4) measurable_residualGerm
    (fun _ => residualGerm_nonneg _) residualGerm_hom hlam hm hc hlo hup

/-- **Lemma 8.6's two bounds**, at the residual germ. The radii differ by a factor of two, which
the engine absorbs by applying the upper bound at `δ` and the lower at `δ/2`. -/
example {p h n : ℕ} {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(δ ^ 2)) * ∫ y in ball (0 : EuclideanSpace ℝ (Fin (h * n + p * h))) δ,
        Real.exp (-T * residualGerm p n h y)
      ≤ ∫ x : EuclideanSpace ℝ (Fin (h * n + p * h)),
          Real.exp (-T * residualGerm p n h x) * Real.exp (-‖x‖ ^ 2) :=
  gaussian_ge_ball hδ measurable_residualGerm (fun _ => residualGerm_nonneg _) hT

/-- **The layer cake**, at the residual germ. -/
example {p h n : ℕ} (δ : ℝ) {T : ℝ} (hT : 0 < T) :
    ∫ x in ball (0 : EuclideanSpace ℝ (Fin (h * n + p * h))) δ,
        Real.exp (-T * residualGerm p n h x)
      = laplaceAverage (sublevelVolume (residualGerm p n h) 0 δ) T :=
  integral_exp_neg_mul_eq_laplaceAverage _ 0 δ hT (fun _ => residualGerm_nonneg _)
    measurable_residualGerm

end AISafetyAtlas.Examples.SingularLearning
