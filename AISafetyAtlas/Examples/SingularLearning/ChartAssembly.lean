module

public import AISafetyAtlas.SingularLearning.ChartAssembly

/-!
# Worked models: the elimination chart at a general stratum

The base-point calculation of `ChartAssembly.lean`, exercised at the strata that used to be
done by hand and at the boundaries the feasibility hypotheses permit.

`(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)` is the smallest stratum on which all six of print's
index types are nonempty; `EliminationChart.lean` computes its base point entry by entry, and
the first example below recovers the same facts from the general theorem instead. The
remaining examples check the degenerate corners: `r = a = b = 0`, a full-rank square stratum,
and the case `a = b = r` in which the transverse block `W_{b−r}` is empty and the reordering is
the identity.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-! ### The witness stratum, from the general theorem -/

/-- **`A* = (I_a 0 ; 0 0)` at the witness stratum**, obtained from the general theorem rather
than by evaluating `canonicalA` entry by entry. Compare
`canonicalA_reordered_block_structure`, which is the same fact computed by hand. -/
example :
    (canonicalA 3 4 2 2 1).submatrix
        (elimHiddenIdxNF (H := 4) (r := 1) (a := 2) (b := 2)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        (elimInputIdx (N := 3) (a := 2) (r := 1) (by norm_num) (by norm_num))
      = Matrix.fromBlocks 1 0 0 0 :=
  canonicalA_reindex _ _ _ _ _

/-- **`B* = (J | D* | 0)` at the witness stratum.** -/
example :
    (canonicalB 3 4 2 1).submatrix
        (elimOutputIdx (M := 3) (b := 2) (r := 1) (by norm_num) (by norm_num))
        (elimHiddenIdxNF (H := 4) (r := 1) (a := 2) (b := 2)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      = Matrix.fromCols (elimCI (elimJ (Fin 1) (Fin 1) (Fin 1)) (Fin 1))
          (Matrix.fromCols (elimDstar (Fin 1) (Fin 1) (Fin 1)) 0) :=
  canonicalB_reindex _ _ _ _ _

/-- **The witness stratum's base point is in print's neighborhood.** This is what the
by-hand calculations of `EliminationChart.lean` were converging on; it now holds at every
feasible stratum, and the witness is a special case rather than a dependency. -/
example :
    elimBasePoint 1 2 2 3 3 4 ∈
      ElimChartNbhd (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1)
        (elimJ (Fin 1) (Fin 1) (Fin 1)) :=
  elimBasePoint_mem_ElimChartNbhd

/-- The base point really is the canonical representative. -/
example :
    elimParamEquivNF (H := 4) (r := 1) (a := 2) (b := 2) (N := 3) (M := 3)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (elimBasePoint 1 2 2 3 3 4)
      = (canonicalA 3 4 2 2 1, canonicalB 3 4 2 1) :=
  elimParamEquivNF_elimBasePoint _ _ _ _ _ _

/-! ### Boundaries -/

/-- **The degenerate stratum `r = a = b = 0`**, the one `isEliminationChart_zero` handles.
Every print index type is empty except the residual blocks. -/
example :
    elimBasePoint 0 0 0 5 4 3 ∈
      ElimChartNbhd (Fin 0) (Fin 0) (Fin 0) (Fin 3) (Fin 4) (Fin 5)
        (elimJ (Fin 0) (Fin 0) (Fin 5)) :=
  elimBasePoint_mem_ElimChartNbhd

/-- **A full-rank square stratum**, `M = N = H = a = b = r = 2`: the residual blocks
`W_h`, `ℝ^p` and `ℝ^n` are all empty and the chart is pure gauge. -/
example :
    elimBasePoint 2 2 2 2 2 2 ∈
      ElimChartNbhd (Fin 2) (Fin 0) (Fin 0) (Fin 0) (Fin 0) (Fin 0)
        (elimJ (Fin 2) (Fin 0) (Fin 0)) :=
  elimBasePoint_mem_ElimChartNbhd

/-- **`a = b = r`: the transverse block `W_{b−r}` is empty**, so `elimReorder` is the identity
and the ordering clash does not arise. The theorem is stated uniformly and does not need to
know that. -/
example :
    elimBasePoint 2 2 2 4 5 3 ∈
      ElimChartNbhd (Fin 2) (Fin 0) (Fin 0) (Fin 1) (Fin 3) (Fin 2)
        (elimJ (Fin 2) (Fin 0) (Fin 2)) :=
  elimBasePoint_mem_ElimChartNbhd

/-- **`r = 0` with `a, b > 0`**: nothing is shared between the image of `A` and the part of the
hidden space `B` is injective on, so `J` is empty and `P(D*) = (I_b ; 0)` is carried entirely
by `D*`. -/
example :
    elimPblock (elimJ (Fin 0) (Fin 2) (Fin 1)) (elimDstar (Fin 0) (Fin 2) (Fin 1))
      = Matrix.fromRows 1 0 :=
  elimPblock_elimJ_elimDstar

/-! ### `P(D*) = (I_b ; 0)` is print's display, not a normalisation -/

/-- The two consequences the chart consumes: the second denominator is a unit, and print's
`R(D*) = I_M` holds because `P_{bot}` vanishes. -/
example : elimPtop (elimJ (Fin 1) (Fin 1) (Fin 1)) (elimDstar (Fin 1) (Fin 1) (Fin 1)) = 1 :=
  elimPtop_elimJ_elimDstar

example : elimPbot (elimJ (Fin 1) (Fin 1) (Fin 1)) (elimDstar (Fin 1) (Fin 1) (Fin 1)) = 0 :=
  elimPbot_elimJ_elimDstar


/-! ### Step 6 and Step 7 at the chart's own coordinates -/

/-- **`2K` vanishes at the base point.** `B*A* = C` exactly, so the canonical representative is
a zero of the loss and not merely a point of the chart. -/
example :
    frobeniusSq ((elimBasePoint 1 2 2 3 3 4).2 * (elimBasePoint 1 2 2 3 3 4).1
        - elimCmat (elimJ (Fin 1) (Fin (2 - 1)) (Fin (elimP 3 2))) (Fin (2 - 1))
          (Fin (elimN 3 2))) = 0 := by
  rw [elimBasePoint_product, sub_self, frobeniusSq_zero]

/-- **The four comparison coordinates vanish at the base point**, so print's normalization by
`A₁₁ − I_a` and `D − D*` leaves `comparisonGerm` alone. -/
example :
    (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) (elimBasePoint 1 2 2 3 3 4).1
        (elimBasePoint 1 2 2 3 3 4).2).U = 0
      ∧ (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) (elimBasePoint 1 2 2 3 3 4).1
        (elimBasePoint 1 2 2 3 3 4).2).Tp = 0
      ∧ (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) (elimBasePoint 1 2 2 3 3 4).1
        (elimBasePoint 1 2 2 3 3 4).2).Y0 = 0
      ∧ (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) (elimBasePoint 1 2 2 3 3 4).1
        (elimBasePoint 1 2 2 3 3 4).2).SZ = 0 :=
  elimPsi_elimBasePoint_comparison

/-- **Print's two constants, at the witness stratum.** Step 7's conclusion on
`ElimChartNbhd`, with `1/12` and `6` and nothing else. -/
example (w : PairSpace (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1))
    (hw : w ∈ ElimChartNbhd (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1)
      (elimJ (Fin 1) (Fin 1) (Fin 1))) :
    1 / 12 * (frobeniusSq (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).U
          + frobeniusSq (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).Tp
          + frobeniusSq ((elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).Y0
              * (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).SZ))
        ≤ frobeniusSq (w.2 * w.1 - elimCmat (elimJ (Fin 1) (Fin 1) (Fin 1)) (Fin 1) (Fin 1)) :=
  (elim_comparison_on_nbhd _ hw).1

/-- **The comparison is two-sided**, which is what the local-volume-order argument consumes:
a one-sided bound would not determine the germ. -/
example (w : PairSpace (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1))
    (hw : w ∈ ElimChartNbhd (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1)
      (elimJ (Fin 1) (Fin 1) (Fin 1))) :
    frobeniusSq (w.2 * w.1 - elimCmat (elimJ (Fin 1) (Fin 1) (Fin 1)) (Fin 1) (Fin 1))
        ≤ 6 * (frobeniusSq (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).U
          + frobeniusSq (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).Tp
          + frobeniusSq ((elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).Y0
              * (elimPsi (elimJ (Fin 1) (Fin 1) (Fin 1)) w.1 w.2).SZ)) :=
  (elim_comparison_on_nbhd _ hw).2

/-- **The truth matrix really is `partialIdMatrix`** read through the index equivalences, so
Step 6's `C` and `IsEliminationChart`'s `C` are the same matrix. -/
example :
    (partialIdMatrix 3 3 1).submatrix
        (elimOutputIdx (M := 3) (b := 2) (r := 1) (by norm_num) (by norm_num))
        (elimInputIdx (N := 3) (a := 2) (r := 1) (by norm_num) (by norm_num))
      = elimCmat (elimJ (Fin 1) (Fin 1) (Fin 1)) (Fin 1) (Fin 1) :=
  partialIdMatrix_reindex _ _ _ _


/-! ### Theorem 5.1 itself

`isEliminationChart_of_feasible` is the general theorem; these are the strata the earlier
by-hand calculations covered, obtained from it. The boundaries are the same ones the base-point
examples above check, so a regression in either shows up in both. -/

/-- **The witness stratum `(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)`.** -/
example : IsEliminationChart 3 3 4 1 2 2 :=
  isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **The degenerate stratum**, previously the only inhabitant. `isEliminationChart_zero`
proves it directly with the identity chart; the general theorem covers it too. -/
example : IsEliminationChart 5 4 3 0 0 0 :=
  isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **A full-rank square stratum**, where the residual blocks are all empty. -/
example : IsEliminationChart 2 2 2 2 2 2 :=
  isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **`a = b = r`**: the transverse block `W_{b−r}` is empty and the hidden reordering is the
identity. -/
example : IsEliminationChart 4 5 3 2 2 2 :=
  isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **`r = 0` with `a, b > 0`**: the image of `A` and the part of the hidden space `B` is
injective on share nothing, so `J` is empty. -/
example : IsEliminationChart 4 4 4 0 2 2 :=
  isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **Maximal hidden width**, `H` far larger than `a + b`: the residual hidden block `W_h`
carries almost everything. -/
example : IsEliminationChart 3 3 9 1 2 2 :=
  isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- **Transposed shapes.** `(M, N, a, b) = (5, 3, 1, 2)` against `(3, 5, 2, 1)`: both are
feasible and both get a chart, with the residual shapes exchanged. -/
example : IsEliminationChart 5 3 4 1 1 2 ∧ IsEliminationChart 3 5 4 1 2 1 :=
  ⟨isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    isEliminationChart_of_feasible (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)⟩

end AISafetyAtlas.Examples.SingularLearning
