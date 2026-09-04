module

public import AISafetyAtlas.SingularLearning.ChartGerm

/-!
# Worked models: the chart germ in Euclidean coordinates

Three checks: the germ really is print's `comparisonGerm` at an explicit point, the gauge block
really is ignored, and the pair assembles from the two block pairs.  The residual pair is a
hypothesis throughout, exactly as in the library module — nothing here depends on the Wishart
frontier.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **The germ is print's comparison function.** Restated at the smallest shape that has all
four blocks. -/
example (u : EuclideanSpace ℝ (Fin 1)) (Y₀ : Matrix (Fin 1) (Fin 1) ℝ)
    (S_Z : Matrix (Fin 1) (Fin 1) ℝ) (v : EuclideanSpace ℝ (Fin 1)) :
    chartGerm 1 1 1 1 1 (euclideanProdEquiv (1 + (1 * 1 + 1 * 1)) 1
        (euclideanProdEquiv 1 (1 * 1 + 1 * 1) (u, matrixPairEquiv 1 1 1 (S_Z, Y₀)), v))
      = ‖u‖ ^ 2 + frobeniusSq (Y₀ * S_Z) :=
  chartGerm_eq_comparisonGerm 1 1 1 1 1 u Y₀ S_Z v

/-- **The gauge block is ignored.** Two points differing only in `v` have the same germ value. -/
example (q p h n g : ℕ) (x : EuclideanSpace ℝ (Fin (q + (h * n + p * h))))
    (v v' : EuclideanSpace ℝ (Fin g)) :
    chartGerm q p h n g (euclideanProdEquiv (q + (h * n + p * h)) g (x, v))
      = chartGerm q p h n g (euclideanProdEquiv (q + (h * n + p * h)) g (x, v')) := by
  rw [chartGerm_apply, chartGerm_apply]

/-- **The germ is nonnegative**, so the layer-cake and product-rule interfaces accept it. -/
example (q p h n g : ℕ) (z : EuclideanSpace ℝ (Fin (q + (h * n + p * h) + g))) :
    0 ≤ chartGerm q p h n g z :=
  chartGerm_nonneg q p h n g z

/-- **The pair assembles.** Given any residual pair, the chart germ's exponent is the residual
exponent plus `q/2` and its multiplicity is the residual multiplicity. -/
example (q p h n g : ℕ) (hq : 0 < q) (lamR : ℝ) (mR : ℕ) (hlamR : 0 < lamR)
    (hres : HasLocalVolumeOrder (residualGerm p n h) 0 lamR mR) :
    HasLocalVolumeOrder (chartGerm q p h n g) 0 ((q : ℝ) / 2 + lamR) mR :=
  hasLocalVolumeOrder_chartGerm hq hlamR hres

/-- **The gauge block does not change the pair.** The same hypothesis gives the same pair at
`g = 0` and at any `g`, which is print's Lemma 6.4(ii) read on this germ. -/
example (q p h n : ℕ) (hq : 0 < q) (lamR : ℝ) (mR : ℕ) (hlamR : 0 < lamR)
    (hres : HasLocalVolumeOrder (residualGerm p n h) 0 lamR mR) :
    HasLocalVolumeOrder (chartGerm q p h n 0) 0 ((q : ℝ) / 2 + lamR) mR ∧
      HasLocalVolumeOrder (chartGerm q p h n 7) 0 ((q : ℝ) / 2 + lamR) mR :=
  ⟨hasLocalVolumeOrder_chartGerm hq hlamR hres, hasLocalVolumeOrder_chartGerm hq hlamR hres⟩

/-- **The degenerate `u` block.** With `q = 0` the whole pair is the residual pair. -/
example (p h n g : ℕ) (lamR : ℝ) (mR : ℕ)
    (hres : HasLocalVolumeOrder (residualGerm p n h) 0 lamR mR) :
    HasLocalVolumeOrder (chartGerm 0 p h n g) 0 lamR mR :=
  hasLocalVolumeOrder_chartGerm_zero_q hres

/-- **The degenerate residual block.** With `h = 0` the residual germ vanishes identically and
the pair is the transverse pair, with multiplicity one. -/
example (q p n g : ℕ) (hq : 0 < q) :
    HasLocalVolumeOrder (chartGerm q p 0 n g) 0 ((q : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_chartGerm_residual_zero hq (Or.inr (Or.inr rfl))

/-- The residual germ really does vanish there, so the previous example is not vacuous. -/
example (p n : ℕ) (w : EuclideanSpace ℝ (Fin (0 * n + p * 0))) : residualGerm p n 0 w = 0 :=
  residualGerm_eq_zero (Or.inr (Or.inr rfl)) w

/-- **One statement for every `q`.** -/
example (q p h n g : ℕ) (lamR : ℝ) (mR : ℕ) (hlamR : 0 < lamR)
    (hres : HasLocalVolumeOrder (residualGerm p n h) 0 lamR mR) :
    HasLocalVolumeOrder (chartGerm q p h n g) 0 ((q : ℝ) / 2 + lamR) mR :=
  hasLocalVolumeOrder_chartGerm_any hlamR hres

end AISafetyAtlas.Examples.SingularLearning
