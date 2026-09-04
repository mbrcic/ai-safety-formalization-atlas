module

public import AISafetyAtlas.SingularLearning.ChartGerm
public import AISafetyAtlas.SingularLearning.ChartTransport

/-!
# The chart space in Euclidean coordinates, as one continuous linear equivalence

`ChartGerm.lean` reads print's comparison germ in Euclidean coordinates, but only as a *function
identity*: it says what the germ is at a point written in split coordinates, which is all the
pair combinators need. Transporting the pair *through* the chart needs more. Print's Lemma
6.4(i) is stated for an analytic diffeomorphism between open sets of one Euclidean space, and
`Ψ` runs between `ParamSpace M N H` and `ChartSpace q p h n g` — products of matrix spaces.
Conjugating `Ψ` into Euclidean coordinates needs the two coordinate maps to be analytic, hence
continuous and linear, not merely bijective.

Both halves already exist. `matrixPairEquiv` (`Coordinates.lean`) is a `≃ₗ[ℝ]` and
`euclSplitEquiv` (`ChartTransport.lean`) is a `≃L[ℝ]`; the only new content is that
`euclSplitEquiv`'s inverse **is** `PairTransfer.lean`'s split map, on the nose
(`coe_euclSplitEquiv_symm`, by `rfl`), so the linear packaging and the measure-preserving one
are the same function and no compatibility lemma has to be carried around.

## Why the rearrangement is `rfl`-linear

The chart lists `(u, Y₀, S_Z, v)` and the residual packing wants `(S_Z, Y₀)`. The reshuffle is a
permutation of the components of a nested product, so `map_add'` and `map_smul'` hold by `rfl`.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory

/-- **The two splittings agree.** `ChartTransport.lean` built its block splitting as a
continuous linear equivalence and `PairTransfer.lean` built the same reindexing as a measurable
equivalence; they are the same function. -/
public theorem coe_euclSplitEquiv_symm (n k : ℕ) :
    ⇑(euclSplitEquiv n k).symm = ⇑(euclideanProdEquiv n k) := rfl

/-- The reshuffle from the chart's own order `(u, Y₀, S_Z, v)` to the order the Euclidean
packing wants, `((u, (S_Z, Y₀)), v)`. A permutation of components, so linear by `rfl`. -/
@[expose] public def chartRearrange (q p h n g : ℕ) :
    ChartSpace q p h n g ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin q) × (Matrix (Fin h) (Fin n) ℝ × Matrix (Fin p) (Fin h) ℝ))
        × EuclideanSpace ℝ (Fin g) where
  toFun z := ((z.1, (z.2.2.1, z.2.1)), z.2.2.2)
  invFun z := (z.1.1, z.1.2.2, z.1.2.1, z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The chart space in Euclidean coordinates.** -/
@[expose] public noncomputable def chartCoords (q p h n g : ℕ) :
    ChartSpace q p h n g ≃L[ℝ] EuclideanSpace ℝ (Fin (q + (h * n + p * h) + g)) :=
  ((chartRearrange q p h n g).toContinuousLinearEquiv.trans
      ((((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin q))).prodCongr
            (matrixPairEquiv p n h).toContinuousLinearEquiv).trans
          (euclSplitEquiv q (h * n + p * h)).symm).prodCongr
        (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin g))))).trans
    (euclSplitEquiv (q + (h * n + p * h)) g).symm

public theorem chartCoords_apply (q p h n g : ℕ) (u : EuclideanSpace ℝ (Fin q))
    (Y₀ : Matrix (Fin p) (Fin h) ℝ) (S_Z : Matrix (Fin h) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin g)) :
    chartCoords q p h n g (u, Y₀, S_Z, v)
      = euclideanProdEquiv (q + (h * n + p * h)) g
          (euclideanProdEquiv q (h * n + p * h) (u, matrixPairEquiv p n h (S_Z, Y₀)), v) := rfl

/-- **The germ in chart coordinates is print's comparison germ.** This is
`chartGerm_eq_comparisonGerm` with the coordinate map named. -/
public theorem chartGerm_chartCoords (q p h n g : ℕ) (z : ChartSpace q p h n g) :
    chartGerm q p h n g (chartCoords q p h n g z) = comparisonGerm z.1 z.2.1 z.2.2.1 := by
  obtain ⟨u, Y₀, S_Z, v⟩ := z
  rw [chartCoords_apply, chartGerm_eq_comparisonGerm]

/-- The parameter space in Euclidean coordinates, as a continuous linear equivalence. -/
@[expose] public noncomputable def paramCoords (M N H : ℕ) :
    ParamSpace M N H ≃L[ℝ] EuclideanSpace ℝ (Fin (H * N + M * H)) :=
  (matrixPairEquiv M N H).toContinuousLinearEquiv

@[simp] public theorem coe_paramCoords (M N H : ℕ) :
    ⇑(paramCoords M N H) = ⇑(matrixPairEquiv M N H) := rfl

/-- A continuous linear equivalence is analytic on every set. Stated once so that the two
coordinate maps and their inverses discharge their share of Lemma 6.4(i)'s hypotheses without
an estimate. -/
public theorem analyticOnNhd_continuousLinearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (s : Set E) :
    AnalyticOnNhd ℝ e s :=
  fun x _ => e.toContinuousLinearMap.analyticAt x

end AISafetyAtlas.SingularLearning
