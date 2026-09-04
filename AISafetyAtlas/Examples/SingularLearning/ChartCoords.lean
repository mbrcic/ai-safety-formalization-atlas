module

public import AISafetyAtlas.SingularLearning.ChartCoords

/-!
# Worked models: the chart coordinate map

The map is the one `ChartGerm.lean` already computes the germ against, it agrees with the
splitting `ChartTransport.lean` built for a different purpose, and it is linear — so the origin
of the chart space is the origin of its coordinates, which is the base point every pair in this
development is stated at.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **The two splittings are the same function**, so the measure-preserving packaging and the
linear one never have to be reconciled. -/
example (n k : ℕ) : ⇑(euclSplitEquiv n k).symm = ⇑(euclideanProdEquiv n k) :=
  coe_euclSplitEquiv_symm n k

/-- **The germ in chart coordinates.** -/
example (q p h n g : ℕ) (u : EuclideanSpace ℝ (Fin q)) (Y₀ : Matrix (Fin p) (Fin h) ℝ)
    (S_Z : Matrix (Fin h) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin g)) :
    chartGerm q p h n g (chartCoords q p h n g (u, Y₀, S_Z, v)) = ‖u‖ ^ 2 + frobeniusSq (Y₀ * S_Z) :=
  chartGerm_chartCoords q p h n g (u, Y₀, S_Z, v)

/-- **The base point is the origin.** Theorem 5.1 sends `(A*, B*)` to `0` in the chart space, and
the coordinate map is linear, so the transported pair is stated at `0`. -/
example (q p h n g : ℕ) : chartCoords q p h n g 0 = 0 := map_zero _

/-- **The parameter coordinate map is the atlas's own.** -/
example (M N H : ℕ) (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    paramCoords M N H (A, B) = matrixPairCoords A B := rfl

end AISafetyAtlas.Examples.SingularLearning
