module

public import AISafetyAtlas.Conjectures.MAIS.O77Chart
public import AISafetyAtlas.Examples.Conjectures.MAIS.O77

/-!
# The O77 chart at a worked rung point

`O77Chart.lean` produces a chart, a criticality statement and a block matrix at
an arbitrary saddle rung point of an arbitrary certified frame.  Each of those
is a conditional statement, and a conditional statement about an empty class of
points is a valid theorem about nothing.  This file discharges every hypothesis
at the two-by-two frame `wideFrame` already witnessed in
`AISafetyAtlas.Examples.Conjectures.MAIS`, at its rank-zero rung `A = B = 0` and
its single discarded mode.

The frame has `M = N = H = 2` and one singular value, so the variation block has
dimension `2H = 4` inside a parameter space of dimension `H M + N H = 8`, and the
complement the chart produces is honestly four-dimensional rather than empty.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.SingularLearning

/-- The rank-zero rung of the wide frame, restated here so the chart theorems
can consume it. -/
public theorem isRungPoint_wideFrame (s : ℝ) (hs : 0 < s) :
    IsO77SaddleRungPoint (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨by norm_num, by simp [O77SpectralFrame.truncation], by simp, by simp⟩

/-- **The chart exists at the wide frame's variation block.**  Non-vacuity for
`exists_o77_chart`: the block subspace of a frame that actually has a mode, in a
parameter space that actually has a complement. -/
public theorem exists_chart_wideFrame (s : ℝ) (hs : 0 < s) :
    ∃ (d : ℕ) (_ : 2 * 2 + d = 2 * 2 + 2 * 2)
      (Xi : (EuclideanSpace ℝ (Fin (2 * 2)) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (2 * 2 + 2 * 2))),
      (∀ z : EuclideanSpace ℝ (Fin (2 * 2)), Xi (z, 0) ∈ o77BlockSubspace (wideFrame s hs) 0) ∧
      (∀ v ∈ o77BlockSubspace (wideFrame s hs) 0, ∃ z, Xi (z, 0) = v) :=
  exists_o77_chart (wideFrame s hs) 0

/-- **The rung point is critical for the loss in coordinates.** -/
public theorem fderiv_loss_wideFrame (s : ℝ) (hs : 0 < s) :
    fderiv ℝ (o77LossCoords 2 2 2 (wideFrame s hs).target)
        (matrixPairCoords (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ))
      = 0 :=
  fderiv_o77LossCoords_eq_zero (isRungPoint_wideFrame s hs)

/-- **The whole package, at one point of one frame**: a chart whose first block is
print's variation block, criticality in that chart, and the block Hessian as a
symmetric nonsingular matrix taking both signs. -/
public theorem exists_block_matrix_wideFrame (s : ℝ) (hs : 0 < s) :
    ∃ (d : ℕ) (Xi : (EuclideanSpace ℝ (Fin (2 * 2)) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (2 * 2 + 2 * 2)))
      (K : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℝ),
      K.IsSymm ∧ K.det ≠ 0 ∧
      (∃ z, 0 < matrixQuadForm K z) ∧ (∃ z, matrixQuadForm K z < 0) ∧
      fderiv ℝ (fun p => o77LossCoords 2 2 2 (wideFrame s hs).target
          (matrixPairCoords (0 : Matrix (Fin 2) (Fin 2) ℝ)
            (0 : Matrix (Fin 2) (Fin 2) ℝ) + Xi p)) 0 = 0 ∧
      ∀ x y, blockW (EuclideanSpace ℝ (Fin (2 * 2))) (EuclideanSpace ℝ (Fin d))
          (fderiv ℝ (fderiv ℝ (fun p => o77LossCoords 2 2 2 (wideFrame s hs).target
            (matrixPairCoords (0 : Matrix (Fin 2) (Fin 2) ℝ)
              (0 : Matrix (Fin 2) (Fin 2) ℝ) + Xi p))) 0) x y
        = matrixQuadPolar K x y := by
  obtain ⟨d, _, Xi, hmem, honto⟩ := exists_o77_chart (wideFrame s hs) 0
  obtain ⟨K, hsymm, hdet, hpos, hneg, hQ⟩ :=
    exists_o77_block_matrix (isRungPoint_wideFrame s hs) (by norm_num) 0 (Nat.zero_le _)
      Xi hmem honto
  exact ⟨d, Xi, K, hsymm, hdet, hpos, hneg,
    fderiv_o77_chart_eq_zero (isRungPoint_wideFrame s hs) Xi, hQ⟩


/-- **Pair `(1,1)` at a rung that is not the rank-zero one.**

Every other witness in this tree sits at `k = 0`, where both factors vanish and
print's spectral step is true because the truncation's Gram is `0`. Here the
product is the top-one truncation, both Gram blocks are nonzero
(`rank2_gram_blocks_ne_zero`), and `s_1² = b²` is excluded from a spectrum that
actually contains something (`rank2_truncation_gram_ne_zero`). So this is the
first witness on which `o77AllSaddlesHavePairOne_holds` runs its whole argument
rather than a degenerate shadow of it. -/
public theorem pair_rank2 (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    HasO77TwoSidedPairAt (rank2Frame a b hb hab).target
      (matrixPairCoords (rank2A a) rank2B) 1 1 :=
  o77AllSaddlesHavePairOne_holds 2 2 3 2 (by norm_num)
    (rank2Frame a b hb hab) 1 (rank2A a) rank2B (rungPoint_rank2 a b hb hab)

end AISafetyAtlas.Examples.Conjectures.MAIS
