module

public import AISafetyAtlas.SingularLearning.Coordinates

/-!
# Worked models for the parameter-space transport

The local-pair relations are stated on `EuclideanSpace ℝ (Fin d)` because the
pinned Mathlib gives `Matrix` **no `MeasureSpace` instance at all**. The
reduced-rank parameter is a pair of matrices, so a local-pair claim about
reduced-rank regression cannot be stated until the parameter space is
transported.

The transport is a coordinate **reindexing**, deliberately: a reshape that was
not measure-preserving would contribute a Jacobian factor to every volume
asymptotic downstream, and it would do so silently. So
`measurePreserving_matrixPairEquiv` is proved, not assumed.

`AISafetyAtlas/SingularLearning/Coordinates.lean` introduces a **scoped**
`MeasureSpace (Matrix m n α)` instance, defined as `inferInstanceAs` of the
`MeasureSpace (m → n → α)` instance — the product measure on the entries, and
definitionally nothing else. It is scoped rather than global so it cannot leak,
and it is the first instance the atlas declares on a Mathlib type.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The parameter space of reduced-rank regression, in Euclidean coordinates,
as a linear equivalence — linearity matters downstream because the loss is a
polynomial in the coordinates. -/
noncomputable example (M N H : ℕ) :
    (Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (H * N + M * H)) :=
  matrixPairEquiv M N H

/-- **No Jacobian.** The transport carries Lebesgue measure to Lebesgue measure,
so the volume asymptotics the local-pair relations speak about are the ones on
the matrix-pair space. -/
example (M N H : ℕ) : MeasureTheory.MeasurePreserving (matrixPairEquiv M N H) :=
  measurePreserving_matrixPairEquiv M N H

/-- The inverse transport too. -/
example (M N H : ℕ) :
    MeasureTheory.MeasurePreserving (matrixPairEquiv M N H).symm :=
  measurePreserving_matrixPairEquiv_symm M N H

/-- The point of the fiber a local-pair claim is anchored at. -/
noncomputable example {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    EuclideanSpace ℝ (Fin (H * N + M * H)) :=
  matrixPairCoords A B

end AISafetyAtlas.Examples.SingularLearning
