module

public import AISafetyAtlas.SingularLearning.DyadicLocalization

/-!
# Worked models for the dyadic localization engine

This is the engine of the MAIS issue #3 candidate's **Lemma 8.6** — the step that
makes a *globally* Gaussian-weighted integral compute a *local* pair.

The candidate supplies this argument itself, and this is its content: decompose
the complement
of a ball into dyadic shells `A_j = {δ2^j ≤ ‖x‖ < δ2^(j+1)}`, rescale each by
`x = 2^j y` using homogeneity of the germ, and observe that the doubly
exponential Gaussian decay `exp(-δ²4^j)` beats the polynomial volume growth
`2^(jD)`.

**The non-compactness of the zero set is the mechanism, not an obstruction.**
Homogeneity makes every shell a rescaled copy of a fixed ball, so the global
integral is controlled by the origin's own local pair rather than by any other
zero of the cone.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **The summability that makes the whole argument work.** Doubly exponential
decay beats geometric growth, for every dimension and every positive radius. -/
example (D : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j : ℕ => (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j) :=
  summable_pow_mul_exp_neg_four_pow D hδ

/-- The shells cover the complement of the ball, and are pairwise disjoint. -/
example {D : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    Pairwise (Function.onFun Disjoint (dyadicShell (D := D) δ)) :=
  pairwise_disjoint_dyadicShell hδ


/-! ### Lemma 8.6: the Gaussian-weighted integral is the local one

The two bounds, at the germ they are applied to. `‖Y X‖²_F` is homogeneous of degree four, which
is what the rescaling step consumes; here the same statements are exercised on the degree-two
germ `‖x‖²`, where both sides are elementary and the shape of the conclusion is visible. -/

/-- **The lower bound**, on the quadratic germ: the Gaussian weight costs at most `e^{-δ²}` on
the ball of radius `δ`. -/
example {D : ℕ} {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(δ ^ 2)) * ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin D)) δ,
        Real.exp (-T * ‖y‖ ^ 2)
      ≤ ∫ x : EuclideanSpace ℝ (Fin D), Real.exp (-T * ‖x‖ ^ 2) * Real.exp (-‖x‖ ^ 2) :=
  gaussian_ge_ball hδ (by fun_prop) (fun _ => by positivity) hT

/-- **The upper bound**, on the same germ, with the degree-two homogeneity supplied explicitly.
The constant is `1 + ∑_j 2^{jD} e^{-δ² 4^j}` and does not depend on `T`, which is what makes the
comparison usable as `T → ∞`. -/
example {D : ℕ} {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ x : EuclideanSpace ℝ (Fin D), Real.exp (-T * ‖x‖ ^ 2) * Real.exp (-‖x‖ ^ 2)
      ≤ (1 + ∑' j : ℕ, (2 : ℝ) ^ (j * D) * Real.exp (-(δ ^ 2) * 4 ^ j)) *
        ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin D)) (2 * δ), Real.exp (-T * ‖y‖ ^ 2) :=
  gaussian_le_ball (k := 2) hδ (by fun_prop) (fun _ => by positivity)
    (fun t ht x => by
      rw [norm_smul, Real.norm_of_nonneg ht, mul_pow]) hT

/-- **Raising the temperature lowers the integral**, which is how the rescaling `T ↦ T 2^{kj}`
introduced by homogeneity is absorbed. -/
example {D : ℕ} {S T : ℝ} (hT : 0 ≤ T) (hST : T ≤ S) (δ : ℝ) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin D)) δ, Real.exp (-S * ‖y‖ ^ 2)
      ≤ ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin D)) δ, Real.exp (-T * ‖y‖ ^ 2) :=
  setIntegral_exp_antitone measurableSet_ball MeasureTheory.measure_ball_lt_top.ne
    (by fun_prop) (fun _ => by positivity) hT hST

end AISafetyAtlas.Examples.SingularLearning
