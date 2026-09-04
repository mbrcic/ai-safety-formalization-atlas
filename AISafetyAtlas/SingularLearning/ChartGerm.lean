module

public import AISafetyAtlas.SingularLearning.CoordTransfer
public import AISafetyAtlas.SingularLearning.PairTransfer
public import AISafetyAtlas.SingularLearning.ResidualGerm
public import AISafetyAtlas.SingularLearning.EliminationChart

/-!
# The chart-space germ, in Euclidean coordinates, and its pair

Theorem 5.1 compares `2K` with `comparisonGerm u Y₀ S_Z = ‖u‖² + ‖Y₀ S_Z‖²_F` on
`ChartSpace q p h n g`, a product of a Euclidean space, two matrix spaces and a second
Euclidean space.  The local pair is stated on `EuclideanSpace ℝ (Fin d)` alone, and the two
germs whose pairs are known — `quadraticGerm` (`PairTransfer.lean`) and `residualGerm`
(`ResidualGerm.lean`) — live there.  This module writes the comparison germ in those
coordinates and reads off its pair.

## The coordinate order

`residualGerm p n h` is packed through `matrixPairEquiv p n h`, whose argument order is
`(S_Z, Y₀)` — the `X` block first, then the `Y` block, because that is the order
`ResidualGerm.lean` fixed and `ResidualLaplace.lean`'s Gaussian integral consumes.  The chart's
own order is `(u, Y₀, S_Z, v)`.  `chartGerm_eq_comparisonGerm` is where the two meet, and it is
the only place the swap happens.

The gauge block `v` is last, which is what `hasLocalVolumeOrder_freeCoords` expects, and the
`u` block is first, which is what `hasLocalVolumeOrder_add` expects of the multiplicity-one
factor.  Nothing else fixes the order.

## What is assumed

The residual pair is a *hypothesis* here, not an import: proving it needs
`hasLocalVolumeOrder_residualGerm_table`, which lives above this module in the dependency
order and carries the Wishart frontier.  Keeping it a hypothesis makes this module frontier-free
and reusable at any residual pair.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

/-! ## The germ -/

/-- The comparison germ on the `u`-and-residual block, in Euclidean coordinates. -/
@[expose] public noncomputable def chartInnerGerm (q p h n : ℕ)
    (x : EuclideanSpace ℝ (Fin (q + (h * n + p * h)))) : ℝ :=
  quadraticGerm q ((euclideanProdEquiv q (h * n + p * h)).symm x).1
    + residualGerm p n h ((euclideanProdEquiv q (h * n + p * h)).symm x).2

/-- The comparison germ on the whole chart space, in Euclidean coordinates: the gauge block is
appended last and ignored. -/
@[expose] public noncomputable def chartGerm (q p h n g : ℕ)
    (z : EuclideanSpace ℝ (Fin (q + (h * n + p * h) + g))) : ℝ :=
  chartInnerGerm q p h n ((euclideanProdEquiv (q + (h * n + p * h)) g).symm z).1

public theorem chartInnerGerm_apply (q p h n : ℕ) (x : EuclideanSpace ℝ (Fin q))
    (y : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    chartInnerGerm q p h n (euclideanProdEquiv q (h * n + p * h) (x, y))
      = quadraticGerm q x + residualGerm p n h y := by
  rw [chartInnerGerm, (euclideanProdEquiv q (h * n + p * h)).symm_apply_apply]

public theorem chartGerm_apply (q p h n g : ℕ)
    (x : EuclideanSpace ℝ (Fin (q + (h * n + p * h)))) (v : EuclideanSpace ℝ (Fin g)) :
    chartGerm q p h n g (euclideanProdEquiv (q + (h * n + p * h)) g (x, v))
      = chartInnerGerm q p h n x := by
  rw [chartGerm, (euclideanProdEquiv (q + (h * n + p * h)) g).symm_apply_apply]

public theorem chartGerm_nonneg (q p h n g : ℕ)
    (z : EuclideanSpace ℝ (Fin (q + (h * n + p * h) + g))) : 0 ≤ chartGerm q p h n g z :=
  add_nonneg (quadraticGerm_nonneg _) (residualGerm_nonneg _)

/-! ## The bridge to `comparisonGerm` -/

/-- **The chart germ is print's comparison germ.** The `X`/`Y` swap between the chart's order
`(u, Y₀, S_Z, v)` and `matrixPairEquiv`'s order `(S_Z, Y₀)` happens here and nowhere else. -/
public theorem chartGerm_eq_comparisonGerm (q p h n g : ℕ) (u : EuclideanSpace ℝ (Fin q))
    (Y₀ : Matrix (Fin p) (Fin h) ℝ) (S_Z : Matrix (Fin h) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin g)) :
    chartGerm q p h n g (euclideanProdEquiv (q + (h * n + p * h)) g
        (euclideanProdEquiv q (h * n + p * h) (u, matrixPairEquiv p n h (S_Z, Y₀)), v))
      = comparisonGerm u Y₀ S_Z := by
  rw [chartGerm_apply, chartInnerGerm_apply, comparisonGerm, quadraticGerm_eq_norm_sq,
    residualGerm, residualX, residualY, LinearEquiv.symm_apply_apply]

/-! ## The pair -/

/-- **The pair of the chart germ.** The `u` block contributes `q/2` with multiplicity one, the
residual block contributes its own pair, and the gauge block contributes nothing — print's
steps 5, 6 and 4 in that order.

`0 < q` and `0 < lamR` are the hypotheses `hasLocalVolumeOrder_add` needs: its degenerate
branch is reserved for a germ vanishing on a whole neighbourhood, which neither block is at a
positive exponent. -/
public theorem hasLocalVolumeOrder_chartGerm {q p h n g : ℕ} (hq : 0 < q)
    {lamR : ℝ} {mR : ℕ} (hlamR : 0 < lamR)
    (hres : HasLocalVolumeOrder (residualGerm p n h) 0 lamR mR) :
    HasLocalVolumeOrder (chartGerm q p h n g) 0 ((q : ℝ) / 2 + lamR) mR := by
  have hinner : HasLocalVolumeOrder (chartInnerGerm q p h n)
      (euclideanProdEquiv q (h * n + p * h) (0, 0)) ((q : ℝ) / 2 + lamR) mR :=
    hasLocalVolumeOrder_add (chartInnerGerm_apply q p h n) quadraticGerm_nonneg
      (residualGerm_nonneg (p := p) (n := n) (h := h)) (by positivity) hlamR
      (hasLocalVolumeOrder_quadraticGerm hq) hres
  rw [euclideanProdEquiv_zero] at hinner
  have hfull : HasLocalVolumeOrder (chartGerm q p h n g)
      (euclideanProdEquiv (q + (h * n + p * h)) g (0, 0)) ((q : ℝ) / 2 + lamR) mR :=
    hasLocalVolumeOrder_freeCoords (chartGerm_apply q p h n g) hinner
  rwa [euclideanProdEquiv_zero] at hfull

/-! ## The degenerate strata

Two blocks of the chart can be empty at a legitimate stratum, and in each case the product rule
is the wrong combinator: it reserves the zero exponent for a germ vanishing on a whole
neighbourhood, which is exactly what an empty block produces. The right combinator is free
coordinates, on the left for an empty `u` block and on the right for an empty residual block.
-/

/-- With no `u` block the inner germ is the residual germ read off the second factor. -/
public theorem chartInnerGerm_apply_zero (p h n : ℕ) (x : EuclideanSpace ℝ (Fin 0))
    (y : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    chartInnerGerm 0 p h n (euclideanProdEquiv 0 (h * n + p * h) (x, y))
      = residualGerm p n h y := by
  rw [chartInnerGerm_apply]
  simp [quadraticGerm]

/-- **An empty transverse block.** With `q = 0` the whole pair is the residual pair.

The stratum this corresponds to is `a = b = 0` — the truth matrix and both factors vanish — but
only once `M` and `N` are positive: `elimQ M N a b = a(M − b) + bN` also vanishes at, say,
`N = 0`. The identification is made at the point of use, not here; this statement quantifies over
a bare `q`. -/
public theorem hasLocalVolumeOrder_chartGerm_zero_q {p h n g : ℕ} {lamR : ℝ} {mR : ℕ}
    (hres : HasLocalVolumeOrder (residualGerm p n h) 0 lamR mR) :
    HasLocalVolumeOrder (chartGerm 0 p h n g) 0 lamR mR := by
  have hinner : HasLocalVolumeOrder (chartInnerGerm 0 p h n)
      (euclideanProdEquiv 0 (h * n + p * h) (0, 0)) lamR mR :=
    hasLocalVolumeOrder_freeCoords_left (chartInnerGerm_apply_zero p h n) hres
  rw [euclideanProdEquiv_zero] at hinner
  have hfull := hasLocalVolumeOrder_freeCoords (v := (0 : EuclideanSpace ℝ (Fin g)))
    (chartGerm_apply 0 p h n g) hinner
  rwa [euclideanProdEquiv_zero] at hfull

/-- **The pair of the chart germ, at every `q`.** -/
public theorem hasLocalVolumeOrder_chartGerm_any {q p h n g : ℕ} {lamR : ℝ} {mR : ℕ}
    (hlamR : 0 < lamR) (hres : HasLocalVolumeOrder (residualGerm p n h) 0 lamR mR) :
    HasLocalVolumeOrder (chartGerm q p h n g) 0 ((q : ℝ) / 2 + lamR) mR := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simpa using hasLocalVolumeOrder_chartGerm_zero_q hres
  · exact hasLocalVolumeOrder_chartGerm hq hlamR hres

/-- The residual germ vanishes identically when any of its three shape parameters does: with
`h = 0` the product is a sum over an empty index, and with `p = 0` or `n = 0` the product has no
entries at all. -/
public theorem residualGerm_eq_zero {p h n : ℕ} (hdeg : p = 0 ∨ n = 0 ∨ h = 0)
    (w : EuclideanSpace ℝ (Fin (h * n + p * h))) : residualGerm p n h w = 0 := by
  rw [residualGerm, frobeniusSq]
  rcases hdeg with rfl | rfl | rfl
  · simp
  · simp
  · simp [Matrix.mul_apply]

/-- **An empty residual block** — the strata `b = M`, `a = N` and `a + b = H + r`, which is what
`p = 0`, `n = 0` and `h = 0` come to. The pair is the transverse pair `(q/2, 1)`.

`0 < q` is needed by the route, not by the conclusion: at `q = 0` the germ vanishes identically
and the neutral branch of `HasLocalVolumeOrder` gives the same answer. -/
public theorem hasLocalVolumeOrder_chartGerm_residual_zero {q p h n g : ℕ} (hq : 0 < q)
    (hdeg : p = 0 ∨ n = 0 ∨ h = 0) :
    HasLocalVolumeOrder (chartGerm q p h n g) 0 ((q : ℝ) / 2) 1 := by
  have happ : ∀ (x : EuclideanSpace ℝ (Fin q)) (y : EuclideanSpace ℝ (Fin (h * n + p * h))),
      chartInnerGerm q p h n (euclideanProdEquiv q (h * n + p * h) (x, y)) = quadraticGerm q x := by
    intro x y
    rw [chartInnerGerm_apply, residualGerm_eq_zero hdeg, add_zero]
  have hinner : HasLocalVolumeOrder (chartInnerGerm q p h n)
      (euclideanProdEquiv q (h * n + p * h) (0, 0)) ((q : ℝ) / 2) 1 :=
    hasLocalVolumeOrder_freeCoords happ (hasLocalVolumeOrder_quadraticGerm hq)
  rw [euclideanProdEquiv_zero] at hinner
  have hfull := hasLocalVolumeOrder_freeCoords (v := (0 : EuclideanSpace ℝ (Fin g)))
    (chartGerm_apply q p h n g) hinner
  rwa [euclideanProdEquiv_zero] at hfull

end AISafetyAtlas.SingularLearning
