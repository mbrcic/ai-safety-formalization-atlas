module

public import AISafetyAtlas.SingularLearning.ChartAnalytic

/-!
# Theorem 5.1, assembled: the elimination chart at a general stratum

`EliminationChart.lean` proves Steps 1–7 over `Sum` index types with the chart's constants `J`
and `D*` held as parameters, and `ChartAnalytic.lean` proves that the resulting map is an
analytic bijection between open sets. What neither does is *point* the construction at the
canonical representative of a stratum: `IsEliminationChart` fixes its base point to
`OrbitNormalForm`'s `(canonicalA, canonicalB)`, and the two modules never look at it.

This module closes that gap for **every feasible stratum**, not just the fixed witness the
earlier commits computed.

## The ordering clash, resolved

`EliminationChart.lean` records that the canonical representative is *not* in the chart's
domain under the obvious index equivalence: print orders the hidden coordinates
`(W_r ⊕ W_{a−r}) ⊕ (W_{b−r} ⊕ W_h)`, so that `A₁₁* = I_a`, while `OrbitNormalForm` puts
`W_{b−r}` first, so that `canonicalB` reads simplest. Under print's ordering `canonicalA`'s
`a × a` block is strictly below the diagonal, hence singular.

`elimHiddenIdxNF` is print's hidden index composed with `elimReorderEquiv`, the permutation
between the two orderings. With it:

* `canonicalA_reindex` — `A*` is `(I_a 0 ; 0 0)`, which is print's `A₁₁* = I_a` together with
  `A₁₂* = A₂₁* = A₂₂* = 0`;
* `canonicalB_reindex` — `B*` is `(J | D* | 0)`, print's description of the canonical `B`;
* `elimBasePoint_mem_ElimChartNbhd` — the base point is in print's `N₀` and in the
  determinant locus, with both determinants equal to `1` and all three Frobenius conditions
  reading `0 < ¼`.

None of this touches `OrbitNormalForm`. The reordering is composed into the parameter
equivalence (`elimParamEquivNF`), which is still a continuous linear equivalence, so
`chart_transport` applies to it verbatim.

## What the constants are

Print carries `J` and `D*` as fixed matrices of the stratum. They are named here rather than in
`EliminationChart.lean` because their *values* are `OrbitNormalForm`'s business: `elimJ` is the
inclusion of `W_r` into the first `r` outputs, `elimDstar` the block of `B*` over `W_{b−r}`,
which lands on the outputs `[r, b)`. Their one joint property is print's Step 3 display
`P(D*) = (I_b ; 0)`, proved here at every stratum as `elimPblock_elimJ_elimDstar`.

## Theorem 5.1

`isEliminationChart_of_feasible` is the general inhabitant of `IsEliminationChart`. Its
hypotheses are exactly the feasibility conditions that make print's five `ℕ` subtractions
exact — `r ≤ a`, `r ≤ b`, `a + b ≤ H + r`, `a ≤ N`, `b ≤ M`. `a ≤ H` is not among them: it
follows from the third and second, and stating it would leave an unused hypothesis.

The assembly is: restrict the chart to `ElimChartNbhd` (`bijOn_elimPsiProd_nbhd`); normalize at
the base point, which does not move the germ because the four comparison coordinates already
vanish there (`comparisonGerm_transported`); transport along `elimParamEquivNF` and
`elimCoordEquiv`, neither of which moves either side of the comparison
(`comparisonGerm_elimCoordEquiv`, `two_mul_rrrLoss_elimParamEquivNF`); and read off Step 7
(`elim_comparison_on_nbhd`).

## Index conventions

Every `ℕ` subtraction in this file appears only as a *type index* (`Fin (b − r)`, `elimH`,
`elimN`, `elimP`) or inside an `omega` call with the feasibility hypotheses in scope. The four
`elimHiddenIdxNF` index lemmas (`elimHiddenIdxNF_inl_inl` and its three siblings) are the only
place the truncation is reasoned about directly, and
each is discharged by the four branches of `elimReorder`.
-/

namespace AISafetyAtlas.SingularLearning

open scoped Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-! ## The three index equivalences, evaluated -/

section IndexValues

variable {M N H r a b : ℕ}

public theorem elimHiddenIdx_inl_inl (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (k : Fin r) :
    ((elimHiddenIdx haH hra hrb hab (Sum.inl (Sum.inl k)) : Fin H) : ℕ) = (k : ℕ) := by
  simp [elimHiddenIdx, elimHiddenEquiv, finSplit, finSumFinEquiv]

public theorem elimHiddenIdx_inl_inr (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (s : Fin (a - r)) :
    ((elimHiddenIdx haH hra hrb hab (Sum.inl (Sum.inr s)) : Fin H) : ℕ) = r + (s : ℕ) := by
  simp [elimHiddenIdx, elimHiddenEquiv, finSplit, finSumFinEquiv]

public theorem elimHiddenIdx_inr_inl (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (t : Fin (b - r)) :
    ((elimHiddenIdx haH hra hrb hab (Sum.inr (Sum.inl t)) : Fin H) : ℕ) = a + (t : ℕ) := by
  simp [elimHiddenIdx, elimHiddenEquiv, finSplit, finSumFinEquiv]

public theorem elimHiddenIdx_inr_inr (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (z : Fin (elimH H r a b)) :
    ((elimHiddenIdx haH hra hrb hab (Sum.inr (Sum.inr z)) : Fin H) : ℕ)
      = a + (b - r) + (z : ℕ) := by
  simp [elimHiddenIdx, elimHiddenEquiv, finSplit, finSumFinEquiv]
  omega

public theorem elimInputIdx_inl_inl (haN : a ≤ N) (hra : r ≤ a) (k : Fin r) :
    ((elimInputIdx haN hra (Sum.inl (Sum.inl k)) : Fin N) : ℕ) = (k : ℕ) := by
  simp [elimInputIdx, elimInputEquiv, finSplit, finSumFinEquiv]

public theorem elimInputIdx_inl_inr (haN : a ≤ N) (hra : r ≤ a) (s : Fin (a - r)) :
    ((elimInputIdx haN hra (Sum.inl (Sum.inr s)) : Fin N) : ℕ) = r + (s : ℕ) := by
  simp [elimInputIdx, elimInputEquiv, finSplit, finSumFinEquiv]

public theorem elimInputIdx_inr (haN : a ≤ N) (hra : r ≤ a) (m : Fin (elimN N a)) :
    ((elimInputIdx haN hra (Sum.inr m) : Fin N) : ℕ) = a + (m : ℕ) := by
  simp [elimInputIdx, elimInputEquiv, finSplit, finSumFinEquiv]

public theorem elimOutputIdx_inl_inl (hbM : b ≤ M) (hrb : r ≤ b) (k : Fin r) :
    ((elimOutputIdx hbM hrb (Sum.inl (Sum.inl k)) : Fin M) : ℕ) = (k : ℕ) := by
  simp [elimOutputIdx, elimOutputEquiv, finSplit, finSumFinEquiv]

public theorem elimOutputIdx_inl_inr (hbM : b ≤ M) (hrb : r ≤ b) (t : Fin (b - r)) :
    ((elimOutputIdx hbM hrb (Sum.inl (Sum.inr t)) : Fin M) : ℕ) = r + (t : ℕ) := by
  simp [elimOutputIdx, elimOutputEquiv, finSplit, finSumFinEquiv]

public theorem elimOutputIdx_inr (hbM : b ≤ M) (hrb : r ≤ b) (u : Fin (elimP M b)) :
    ((elimOutputIdx hbM hrb (Sum.inr u) : Fin M) : ℕ) = b + (u : ℕ) := by
  simp [elimOutputIdx, elimOutputEquiv, finSplit, finSumFinEquiv]

end IndexValues


/-! ## The hidden index in print's ordering

`elimHiddenIdx` reads print's hidden decomposition into `Fin H` in print's own order, in which
the `a` coordinates `A` lands on come first. `OrbitNormalForm`'s canonical pair uses the other
order, `W_{b−r}` first. `elimReorderEquiv` is the permutation between them, and composing it
here is what puts `A₁₁* = I_a` back where print says it is — without touching
`OrbitNormalForm`. -/

section HiddenNF

variable {M N H r a b : ℕ}

/-- **Print's hidden index, in `OrbitNormalForm`'s ordering.** -/
@[expose] public def elimHiddenIdxNF (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) :
    ((Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b))) ≃ Fin H :=
  (elimHiddenIdx haH hra hrb hab).trans
    (elimReorderEquiv hra hrb (show a + (b - r) ≤ H by omega))

public theorem elimHiddenIdxNF_val (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (x : (Fin r ⊕ Fin (a - r)) ⊕ (Fin (b - r) ⊕ Fin (elimH H r a b))) :
    ((elimHiddenIdxNF haH hra hrb hab x : Fin H) : ℕ)
      = elimReorder a b r ((elimHiddenIdx haH hra hrb hab x : Fin H) : ℕ) := rfl

/-- Print's `W_r` sits at `OrbitNormalForm`'s `[b−r, b)`. -/
public theorem elimHiddenIdxNF_inl_inl (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (k : Fin r) :
    ((elimHiddenIdxNF haH hra hrb hab (Sum.inl (Sum.inl k)) : Fin H) : ℕ) = (b - r) + (k : ℕ) := by
  rw [elimHiddenIdxNF_val, elimHiddenIdx_inl_inl]
  have := k.isLt
  unfold elimReorder
  split_ifs
  omega

/-- Print's `W_{a−r}` sits at `[b, b + (a−r))`. -/
public theorem elimHiddenIdxNF_inl_inr (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (s : Fin (a - r)) :
    ((elimHiddenIdxNF haH hra hrb hab (Sum.inl (Sum.inr s)) : Fin H) : ℕ) = b + (s : ℕ) := by
  rw [elimHiddenIdxNF_val, elimHiddenIdx_inl_inr]
  have := s.isLt
  unfold elimReorder
  split_ifs <;> omega

/-- Print's `W_{b−r}` sits first, at `[0, b−r)`. -/
public theorem elimHiddenIdxNF_inr_inl (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (t : Fin (b - r)) :
    ((elimHiddenIdxNF haH hra hrb hab (Sum.inr (Sum.inl t)) : Fin H) : ℕ) = (t : ℕ) := by
  rw [elimHiddenIdxNF_val, elimHiddenIdx_inr_inl]
  have := t.isLt
  unfold elimReorder
  split_ifs <;> omega

/-- `W_h` is last in both orderings. -/
public theorem elimHiddenIdxNF_inr_inr (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (z : Fin (elimH H r a b)) :
    ((elimHiddenIdxNF haH hra hrb hab (Sum.inr (Sum.inr z)) : Fin H) : ℕ)
      = a + (b - r) + (z : ℕ) := by
  rw [elimHiddenIdxNF_val, elimHiddenIdx_inr_inr]
  unfold elimReorder
  split_ifs <;> omega

end HiddenNF


/-! ## The canonical pair, in print's coordinates

Print's `J` is the inclusion of `W_r` into the first `r` outputs, and its `D*` is the block of
`B` over `W_{b−r}`. Both are constants of the chart, not coordinates; they are named here so
that the base-point calculation has something to be an equation between. -/

section Constants

variable {ρ τ π : Type*} [DecidableEq ρ] [DecidableEq τ]

/-- Print's `J ∈ ℝ^{M×r}`: the inclusion of `W_r` into the first `r` output coordinates. -/
@[expose] public def elimJ (ρ τ π : Type*) [DecidableEq ρ] :
    Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ :=
  Matrix.fromRows (Matrix.fromRows (1 : Matrix ρ ρ ℝ) (0 : Matrix τ ρ ℝ)) (0 : Matrix π ρ ℝ)

/-- Print's `D* ∈ ℝ^{M×(b−r)}`: the block of `B*` over `W_{b−r}`, which lands on the output
coordinates `[r, b)`. -/
@[expose] public def elimDstar (ρ τ π : Type*) [DecidableEq τ] :
    Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ :=
  Matrix.fromRows (Matrix.fromRows (0 : Matrix ρ τ ℝ) (1 : Matrix τ τ ℝ)) (0 : Matrix π τ ℝ)

/-- **Print's `P(D*) = (I_b ; 0)`**, at every stratum. `(J | D*)` is the identity on the first
`b` output coordinates and empty below, because `J` fills the `r` block and `D*` the `b − r`
block, in that order. -/
public theorem elimPblock_elimJ_elimDstar :
    elimPblock (elimJ ρ τ π) (elimDstar ρ τ π)
      = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0 := by
  ext i j
  rcases i with (i | i) | i <;> rcases j with j | j <;>
    simp [elimPblock, elimJ, elimDstar, Matrix.one_apply, Sum.inl_injective.eq_iff,
      Sum.inr_injective.eq_iff]

/-- `P_{top}(D*) = I_b`, so the chart's second denominator is a unit at the base point. -/
public theorem elimPtop_elimJ_elimDstar :
    elimPtop (elimJ ρ τ π) (elimDstar ρ τ π) = 1 :=
  elimPtop_eq_one_of_pblock elimPblock_elimJ_elimDstar

/-- `P_{bot}(D*) = 0`. -/
public theorem elimPbot_elimJ_elimDstar :
    elimPbot (elimJ ρ τ π) (elimDstar ρ τ π) = 0 :=
  elimPbot_eq_zero_of_pblock elimPblock_elimJ_elimDstar

end Constants


/-! ## The canonical pair at the base point

`canonicalA` and `canonicalB` are column-selection matrices, so each is `1` at one entry per
column and `0` elsewhere. Reading them through the three index equivalences turns each into a
block matrix, and the blocks are exactly print's base-point values: `A₁₁* = I_a`, `A₁₂* = 0`,
`A₂₁* = 0`, `A₂₂* = 0` for `A`, and `B* = (J | D* | 0)` for `B`. -/

section BasePointValue

variable {M N H r a b : ℕ}

/-- `canonicalA` in the form its base-point calculation uses: the entry is `1` exactly when the
column is one of the first `a` and the row is its image. -/
public theorem canonicalA_apply_iff (i : Fin H) (j : Fin N) :
    canonicalA N H a b r i j = if (j : ℕ) < a ∧ (i : ℕ) = (j : ℕ) + (b - r) then 1 else 0 := by
  show (if (i : ℕ) = (if (j : ℕ) < a then (j : ℕ) + (b - r) else H) then (1:ℝ) else 0) = _
  by_cases hj : (j : ℕ) < a
  · rw [if_pos hj]
    by_cases hi : (i : ℕ) = (j : ℕ) + (b - r)
    · rw [if_pos hi, if_pos ⟨hj, hi⟩]
    · rw [if_neg hi, if_neg (fun h => hi h.2)]
  · rw [if_neg hj, if_neg (show (i : ℕ) ≠ H by have := i.isLt; omega),
      if_neg (fun h => hj h.1)]

/-- `canonicalB` in the same form: the two nonzero column ranges, written out. -/
public theorem canonicalB_apply_iff (i : Fin M) (q : Fin H) :
    canonicalB M H b r i q =
      if ((q : ℕ) < b - r ∧ (i : ℕ) = (q : ℕ) + r)
          ∨ (b - r ≤ (q : ℕ) ∧ (q : ℕ) < b ∧ (i : ℕ) = (q : ℕ) - (b - r)) then 1 else 0 := by
  show (if (i : ℕ) = (if (q : ℕ) < b - r then (q : ℕ) + r
    else if (q : ℕ) < b then (q : ℕ) - (b - r) else M) then (1:ℝ) else 0) = _
  by_cases h1 : (q : ℕ) < b - r
  · rw [if_pos h1]
    by_cases hi : (i : ℕ) = (q : ℕ) + r
    · rw [if_pos hi, if_pos (Or.inl ⟨h1, hi⟩)]
    · refine (if_neg hi).trans (if_neg ?_).symm
      rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
  · rw [if_neg h1]
    by_cases h2 : (q : ℕ) < b
    · rw [if_pos h2]
      by_cases hi : (i : ℕ) = (q : ℕ) - (b - r)
      · rw [if_pos hi, if_pos (Or.inr ⟨by omega, h2, hi⟩)]
      · refine (if_neg hi).trans (if_neg ?_).symm
        rintro (⟨h, -⟩ | ⟨-, -, h⟩) <;> omega
    · rw [if_neg h2]
      refine (if_neg (show (i : ℕ) ≠ M by have := i.isLt; omega)).trans (if_neg ?_).symm
      rintro (⟨h, -⟩ | ⟨-, h, -⟩) <;> omega

/-- **`A*` in print's coordinates: `(I_a 0 ; 0 0)`.** This is print's `A₁₁* = I_a` together
with the vanishing of the other three blocks, at every feasible stratum — the general form of
the fixed-stratum calculations `canonicalA_reordered_block_structure`. -/
public theorem canonicalA_reindex (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) :
    (canonicalA N H a b r).submatrix (elimHiddenIdxNF haH hra hrb hab)
        (elimInputIdx haN hra)
      = Matrix.fromBlocks (1 : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) ℝ) 0 0 0 := by
  ext x y
  rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | y <;>
    (try have hx := x.isLt) <;> (try have hy := y.isLt) <;>
    simp only [Matrix.submatrix_apply, canonicalA_apply_iff,
      elimHiddenIdxNF_inl_inl, elimHiddenIdxNF_inl_inr, elimHiddenIdxNF_inr_inl,
      elimHiddenIdxNF_inr_inr, elimInputIdx_inl_inl, elimInputIdx_inl_inr, elimInputIdx_inr,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Fin.ext_iff] <;>
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **`B*` in print's coordinates: `(J | D* | 0)`.** `B*` is injective on `W_r`, carries
`W_{b−r}` onto the outputs `[r, b)`, and kills `W_{a−r} ⊕ W_h` — which is exactly the
statement that its three column blocks are `J`, `D*` and `0`. -/
public theorem canonicalB_reindex (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (hbM : b ≤ M) :
    (canonicalB M H b r).submatrix (elimOutputIdx hbM hrb) (elimHiddenIdxNF haH hra hrb hab)
      = Matrix.fromCols (elimCI (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (Fin (a - r)))
          (Matrix.fromCols (elimDstar (Fin r) (Fin (b - r)) (Fin (elimP M b)))
            (0 : Matrix ((Fin r ⊕ Fin (b - r)) ⊕ Fin (elimP M b))
              (Fin (elimH H r a b)) ℝ)) := by
  ext x y
  rcases x with (x | x) | x <;> rcases y with (y | y) | (y | y) <;>
    (try have hx := x.isLt) <;> (try have hy := y.isLt) <;>
    simp only [Matrix.submatrix_apply, canonicalB_apply_iff,
      elimOutputIdx_inl_inl, elimOutputIdx_inl_inr, elimOutputIdx_inr,
      elimHiddenIdxNF_inl_inl, elimHiddenIdxNF_inl_inr, elimHiddenIdxNF_inr_inl,
      elimHiddenIdxNF_inr_inr, elimCI, elimJ, elimDstar,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.zero_apply, Matrix.one_apply, Fin.ext_iff] <;>
    split_ifs <;> first | rfl | (exfalso; omega)

end BasePointValue


/-! ## The parameter equivalence in print's ordering, and the base point

`elimParamEquiv` reads the `Sum`-indexed pair into `ParamSpace M N H` in print's hidden order.
Composing the hidden index with `elimReorderEquiv` — that is, using `elimHiddenIdxNF` in its
place — is what makes the canonical representative land in the chart's domain. Nothing else
changes: it is still a continuous linear equivalence, so `chart_transport` applies verbatim. -/

section ParamNF

variable {M N H r a b : ℕ}

/-- Print's parameter-space equivalence, with the hidden coordinates in `OrbitNormalForm`'s
order. -/
@[expose] public noncomputable def elimParamEquivNF (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M) :
    PairSpace (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b)) (Fin (elimN N a))
        (Fin (elimP M b)) ≃L[ℝ] ParamSpace M N H :=
  (matrixReindexEquiv (elimHiddenIdxNF haH hra hrb hab) (elimInputIdx haN hra)).prodCongr
    (matrixReindexEquiv (elimOutputIdx hbM hrb) (elimHiddenIdxNF haH hra hrb hab))

/-- **The base point, in print's coordinates.** `(A₁₁* , A₁₂* , A₂₁* , A₂₂*) = (I_a, 0, 0, 0)`
and `B* = (J | D* | 0)`. -/
@[expose] public noncomputable def elimBasePoint (r a b M N H : ℕ) :
    PairSpace (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b)) (Fin (elimN N a))
      (Fin (elimP M b)) :=
  (Matrix.fromBlocks (1 : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) ℝ) 0 0 0,
    Matrix.fromCols (elimCI (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (Fin (a - r)))
      (Matrix.fromCols (elimDstar (Fin r) (Fin (b - r)) (Fin (elimP M b)))
        (0 : Matrix ((Fin r ⊕ Fin (b - r)) ⊕ Fin (elimP M b))
          (Fin (elimH H r a b)) ℝ)))

/-- **The base point is the canonical representative.** Under the parameter equivalence in
print's ordering, `elimBasePoint` is `(A*, B*)` — so the chart, built over the `Sum` index
types, really is a chart at the point `IsEliminationChart` names. -/
public theorem elimParamEquivNF_elimBasePoint (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M) :
    elimParamEquivNF haH hra hrb hab haN hbM (elimBasePoint r a b M N H)
      = (canonicalA N H a b r, canonicalB M H b r) := by
  have hA : (Matrix.reindexLinearEquiv ℝ ℝ (elimHiddenIdxNF haH hra hrb hab)
      (elimInputIdx haN hra))
      (Matrix.fromBlocks (1 : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) ℝ) 0 0 0)
      = canonicalA N H a b r := by
    rw [← canonicalA_reindex haH hra hrb hab haN]
    ext i j
    simp [Matrix.coe_reindexLinearEquiv]
  have hB : (Matrix.reindexLinearEquiv ℝ ℝ (elimOutputIdx hbM hrb)
      (elimHiddenIdxNF haH hra hrb hab)) (elimBasePoint r a b M N H).2
      = canonicalB M H b r := by
    rw [show (elimBasePoint r a b M N H).2 = _ from
      (canonicalB_reindex haH hra hrb hab hbM).symm]
    ext i j
    simp [Matrix.coe_reindexLinearEquiv]
  exact Prod.ext hA hB

end ParamNF


/-! ## The base point lies in print's neighborhood

Print says `A₁₁* = I_a`, `X` vanishes at the base and `P(D*) = (I_b ; 0)`. Each of those is now
a computation at `elimBasePoint`, and together they are exactly membership in
`ElimChartNbhd`: the two determinants are `1`, and all three Frobenius conditions read `0 < ¼`.

The gauge is trivial at the base point — `A₂₁* = 0` makes `L(A*)⁻¹ = I` — which is why `D` read
off `B̄*` is `D*` on the nose. -/

section BaseMembership

variable {M N H r a b : ℕ}

@[simp] public theorem elimBasePoint_toBlocks₁₁ :
    (elimBasePoint r a b M N H).1.toBlocks₁₁ = 1 := Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

@[simp] public theorem elimBasePoint_toBlocks₁₂ :
    (elimBasePoint r a b M N H).1.toBlocks₁₂ = 0 := Matrix.toBlocks_fromBlocks₁₂ _ _ _ _

@[simp] public theorem elimBasePoint_toBlocks₂₁ :
    (elimBasePoint r a b M N H).1.toBlocks₂₁ = 0 := Matrix.toBlocks_fromBlocks₂₁ _ _ _ _

/-- **The gauge is trivial at the base point.** `A₂₁* = 0` and `A₁₁* = I`, so
`L(A*)⁻¹ = (A₁₁ 0 ; A₂₁ I) = I` and `B̄* = B*`. -/
public theorem elimLinv_elimBasePoint :
    elimLinv (elimBasePoint r a b M N H).1.toBlocks₁₁ (elimBasePoint r a b M N H).1.toBlocks₂₁
      = 1 := by
  rw [elimBasePoint_toBlocks₁₁, elimBasePoint_toBlocks₂₁, elimLinv, Matrix.fromBlocks_one]

/-- `B̄* = B*`. -/
public theorem elimBbarOf_elimBasePoint :
    elimBbarOf (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2
      = (elimBasePoint r a b M N H).2 := by
  rw [elimBbarOf, elimLinv_elimBasePoint, Matrix.mul_one]

/-- **`D` at the base point is print's `D*`.** -/
public theorem elimDOf_elimBasePoint :
    elimDOf (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2
      = elimDstar (Fin r) (Fin (b - r)) (Fin (elimP M b)) := by
  rw [elimDOf, elimBbarOf_elimBasePoint]
  show ((Matrix.fromCols _ (Matrix.fromCols _ _)).toCols₂).toCols₁ = _
  rw [Matrix.toCols₂_fromCols, Matrix.toCols₁_fromCols]

/-- `Y = 0` at the base point: `B*` kills `W_{a−r} ⊕ W_h`. -/
public theorem elimYOf_elimBasePoint :
    elimYOf (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2 = 0 := by
  rw [elimYOf, elimBbarOf_elimBasePoint]
  show ((Matrix.fromCols _ (Matrix.fromCols _ _)).toCols₂).toCols₂ = _
  rw [Matrix.toCols₂_fromCols, Matrix.toCols₂_fromCols]

/-- `B_I = C_I` at the base point, so print's `U` vanishes there. -/
public theorem elimBasePoint_toCols₁ :
    (elimBbarOf (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2).toCols₁
      = elimCI (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (Fin (a - r)) := by
  rw [elimBbarOf_elimBasePoint]
  show (Matrix.fromCols _ (Matrix.fromCols _ _)).toCols₁ = _
  rw [Matrix.toCols₁_fromCols]

/-- **`X = 0` at the base point**, since `A₁₂* = 0`. -/
public theorem elimX_elimBasePoint :
    elimX (elimBasePoint r a b M N H).1.toBlocks₁₁ (elimBasePoint r a b M N H).1.toBlocks₁₂
      = 0 := by
  rw [elimBasePoint_toBlocks₁₂, elimX, Matrix.mul_zero]

/-- **The base point lies in print's `N₀` and in the determinant locus** — that is, in
`ElimChartNbhd`. Both determinants are `1` and all three Frobenius conditions are `0 < ¼`. -/
public theorem elimBasePoint_mem_ElimChartNbhd :
    elimBasePoint r a b M N H ∈
      ElimChartNbhd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
        (Fin (elimN N a)) (Fin (elimP M b))
        (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) := by
  have hD := elimDOf_elimBasePoint (r := r) (a := a) (b := b) (M := M) (N := N) (H := H)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [elimBasePoint_toBlocks₁₁, Matrix.det_one]
    exact isUnit_one
  · rw [hD, elimPtop_elimJ_elimDstar, Matrix.det_one]
    exact isUnit_one
  · rw [elimX_elimBasePoint, frobeniusSq_zero]
    norm_num
  · rw [hD, elimPtop_elimJ_elimDstar, sub_self, frobeniusSq_zero]
    norm_num
  · rw [hD, elimPbot_elimJ_elimDstar, frobeniusSq_zero]
    norm_num

/-- **The truth matrix, in print's coordinates.** `C = (C_I | 0) = ((J | 0) | 0)` is
`partialIdMatrix M N r` read through the output and input equivalences: both are the identity
on the first `r` coordinates and zero elsewhere. -/
public theorem partialIdMatrix_reindex (hra : r ≤ a) (hrb : r ≤ b) (haN : a ≤ N)
    (hbM : b ≤ M) :
    (partialIdMatrix M N r).submatrix (elimOutputIdx hbM hrb) (elimInputIdx haN hra)
      = elimCmat (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (Fin (a - r))
          (Fin (elimN N a)) := by
  ext x y
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    (try have hx := x.isLt) <;> (try have hy := y.isLt) <;>
    simp only [Matrix.submatrix_apply, partialIdMatrix,
      elimOutputIdx_inl_inl, elimOutputIdx_inl_inr, elimOutputIdx_inr,
      elimInputIdx_inl_inl, elimInputIdx_inl_inr, elimInputIdx_inr,
      elimCmat, elimCI, elimJ, Matrix.of_apply,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.zero_apply, Matrix.one_apply, Fin.ext_iff] <;>
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **`B*A* = C` exactly**, in print's coordinates: the base point is a zero of the loss, which
is what makes `Ψ(A*, B*) = 0` a statement about a minimum rather than about an arbitrary
point. -/
public theorem elimBasePoint_product :
    (elimBasePoint r a b M N H).2 * (elimBasePoint r a b M N H).1
      = elimCmat (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (Fin (a - r))
          (Fin (elimN N a)) := by
  show Matrix.fromCols _ (Matrix.fromCols _ _) * Matrix.fromBlocks 1 0 0 0 = _
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero,
    Matrix.mul_zero, add_zero, add_zero, elimCmat]


private theorem toRows₁_zero {ι κ ν : Type*} :
    Matrix.toRows₁ (0 : Matrix (ι ⊕ κ) ν ℝ) = 0 := rfl

private theorem toRows₂_zero {ι κ ν : Type*} :
    Matrix.toRows₂ (0 : Matrix (ι ⊕ κ) ν ℝ) = 0 := rfl

private theorem fromRows_zero_zero {ι κ ν : Type*} :
    Matrix.fromRows (0 : Matrix ι ν ℝ) (0 : Matrix κ ν ℝ) = 0 := by
  ext (i | i) j <;> rfl

/-! ### `Ψ` at the base point

Print normalizes by `A₁₁ − I_a` and `D − D*`, which says that at the base point those two
gauge coordinates are `I_a` and `D*` and everything else vanishes. That is what is proved
here, and it is what makes the normalization harmless: the four comparison coordinates
`U`, `T′`, `Y₀`, `S_Z` are already `0`, so subtracting `Ψ(A*, B*)` does not move
`comparisonGerm`. -/

/-- The Schur complement vanishes at the base point: `A₂₂* = 0` and `A₂₁* = 0`. -/
public theorem elimSchur_elimBasePoint :
    elimSchur (elimBasePoint r a b M N H).1.toBlocks₁₁ (elimBasePoint r a b M N H).1.toBlocks₁₂
      (elimBasePoint r a b M N H).1.toBlocks₂₁ (elimBasePoint r a b M N H).1.toBlocks₂₂ = 0 := by
  rw [elimSchur, elimBasePoint_toBlocks₁₂, elimBasePoint_toBlocks₂₁,
    show (elimBasePoint r a b M N H).1.toBlocks₂₂ = 0 from Matrix.toBlocks_fromBlocks₂₂ _ _ _ _,
    Matrix.mul_zero, sub_zero]

/-- `R(D*)Y* = 0`, since `B*` kills `W_{a−r} ⊕ W_h`. -/
public theorem elimRYOf_elimBasePoint :
    elimRYOf (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
      (elimBasePoint r a b M N H).2 = 0 := by
  rw [elimRYOf, elimYOf_elimBasePoint, Matrix.mul_zero]

/-- **`U`, `T′`, `Y₀` and `S_Z` all vanish at the base point.** These are the four coordinates
`comparisonGerm` reads, so print's normalization leaves the germ alone. -/
public theorem elimPsi_elimBasePoint_comparison :
    (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).U = 0
      ∧ (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).Tp = 0
      ∧ (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).Y0 = 0
      ∧ (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).SZ = 0 := by
  have hRY := elimRYOf_elimBasePoint (r := r) (a := a) (b := b) (M := M) (N := N) (H := H)
  have hS := elimSchur_elimBasePoint (r := r) (a := a) (b := b) (M := M) (N := N) (H := H)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [elimPsi_U, elimBasePoint_toCols₁, sub_self]
  · rw [elimPsi_Tp, hRY, hS, elimX_elimBasePoint, elimShear, elimT,
      toRows₁_zero, toRows₂_zero, toRows₁_zero, Matrix.mul_zero, add_zero,
      fromRows_zero_zero]
  · rw [elimPsi_Y0, hRY, toRows₂_zero]
  · rw [elimPsi_SZ, hS, toRows₂_zero]

/-- The remaining five coordinates at the base point: `A₁₁* = I_a` and `D* `, the two print
normalizes away, and `A₂₁* = X_P* = Y₁* = 0`. -/
public theorem elimPsi_elimBasePoint_gauge :
    (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).A11 = 1
      ∧ (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).A21 = 0
      ∧ (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).XP = 0
      ∧ (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).D = elimDstar (Fin r) (Fin (b - r)) (Fin (elimP M b))
      ∧ (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (elimBasePoint r a b M N H).1
        (elimBasePoint r a b M N H).2).Y1 = 0 :=
  ⟨elimBasePoint_toBlocks₁₁, elimBasePoint_toBlocks₂₁,
    by rw [elimPsi_XP, elimX_elimBasePoint, toRows₂_zero],
    by rw [elimPsi_D, elimDOf_elimBasePoint],
    by rw [elimPsi_Y1, elimRYOf_elimBasePoint, toRows₁_zero]⟩

end BaseMembership


/-! ## Step 6 and Step 7, at the chart's own coordinates

`elim_step6` is stated in the nine block variables of Step 5, held as independent arguments.
`elimPsi` produces exactly those nine blocks from a parameter pair, so instantiating Step 6 at
`Ψ(A, B)` is a matter of recognising each argument. That is what `elim_step6_at_psi` does, and
its left-hand side is `2K` for the *original* pair `(A, B)`, not for the gauged one — the gauge
cancels by `elimGauge_preserves_product'`.

Step 7 is then applied on `ElimChartNbhd`, where all three of print's operator-norm hypotheses
hold. The constants `1/12` and `6` come out of `elimination_comparability` and nowhere else. -/

section Step6AtPsi

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
variable [DecidableEq π]

/-- `frobeniusSq` is the squared Frobenius norm at arbitrary index types.
`frobeniusSq_eq_norm_sq` states this for `Fin`-indexed matrices; Step 7 is applied over `Sum`
index types, where the same proof works unchanged. -/
public theorem frobeniusSq_eq_norm_sq' {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) : frobeniusSq X = ‖X‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num [frobeniusSq]

omit [Fintype ν] [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq ν]
  [DecidableEq π] in
/-- Print's `B̄`, recovered from its three column blocks. -/
public theorem elimBbar_of_elimBbarOf (w : PairSpace ρ σ τ η ν π) :
    elimBbar (elimBbarOf w.1 w.2).toCols₁ (elimDOf w.1 w.2) (elimYOf w.1 w.2)
      = elimBbarOf w.1 w.2 := by
  rw [elimBbar, elimDOf, elimYOf, Matrix.fromCols_toCols, Matrix.fromCols_toCols]

omit [Fintype π] [DecidableEq ν] [DecidableEq π] in
/-- Print's `Ā = L(A)A = (I_a X ; 0 S)`, in the shape `elimAbar` names. -/
public theorem elimAbar_of_gauge (w : PairSpace ρ σ τ η ν π)
    (hA : IsUnit (w.1.toBlocks₁₁).det) :
    elimL w.1.toBlocks₁₁ w.1.toBlocks₂₁ * w.1
      = elimAbar (Matrix.fromRows (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂).toRows₁
            (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂).toRows₂)
          (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₁
          (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₂ := by
  rw [Matrix.fromRows_toRows, elimAbar, Matrix.fromRows_toRows,
    ← elimL_mul_self w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂ hA, Matrix.fromBlocks_toBlocks]

omit [DecidableEq ν] in
/-- **Step 6, instantiated at `Ψ`.** `2K = ‖U‖² + ‖UX + R(D)⁻¹(T′ ; Y₀S_Z)‖²`, with every
block on the right the corresponding coordinate of `Ψ(A, B)`. -/
public theorem elim_step6_at_psi (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) (w : PairSpace ρ σ τ η ν π)
    (hA : IsUnit (w.1.toBlocks₁₁).det)
    (hP : IsUnit (elimPtop J (elimDOf w.1 w.2)).det) :
    frobeniusSq (w.2 * w.1 - elimCmat J σ ν)
      = frobeniusSq (elimPsi J w.1 w.2).U
        + frobeniusSq ((elimPsi J w.1 w.2).U * elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂
            + elimRinv (elimPtop J (elimDOf w.1 w.2)) (elimPbot J (elimDOf w.1 w.2))
              * Matrix.fromRows (elimPsi J w.1 w.2).Tp
                  ((elimPsi J w.1 w.2).Y0 * (elimPsi J w.1 w.2).SZ)) := by
  have hY : elimR (elimPtop J (elimDOf w.1 w.2)) (elimPbot J (elimDOf w.1 w.2))
      * elimYOf w.1 w.2
      = Matrix.fromRows (elimRYOf J w.1 w.2).toRows₁ (elimRYOf J w.1 w.2).toRows₂ := by
    rw [Matrix.fromRows_toRows, elimRYOf]
  have hkey := elim_step6 J (elimBbarOf w.1 w.2).toCols₁ (elimDOf w.1 w.2) (elimYOf w.1 w.2)
    (elimRYOf J w.1 w.2).toRows₁ (elimRYOf J w.1 w.2).toRows₂
    (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂).toRows₁
    (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂).toRows₂
    (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₁
    (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₂ hP hY
  rw [elimBbar_of_elimBbarOf w, ← elimAbar_of_gauge w hA, elimBbarOf,
    elimGauge_preserves_product' w.1.toBlocks₂₁ w.1 w.2 hA, Matrix.fromRows_toRows] at hkey
  rw [hkey]
  simp only [elimPsi_U, elimPsi_Tp, elimPsi_Y0, elimPsi_SZ, elimBbarOf, elimShear]

/-- **Step 7, on print's neighborhood.** The two-sided comparison of `2K` with
`NF = ‖U‖² + ‖T′‖² + ‖Y₀S_Z‖²`, with print's constants `1/12` and `6`.

Every input is discharged on `ElimChartNbhd`: `‖X‖₂ ≤ ½` and Lemma 5.2 give
`‖UX‖² ≤ ¼‖U‖²`; Lemma 5.4's two bounds on `R` and `R⁻¹` give
`‖V‖²/6 ≤ ‖R⁻¹V‖² ≤ 3‖V‖²`, the lower one because `R(R⁻¹V) = V`. -/
public theorem elim_comparison_on_nbhd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w : PairSpace ρ σ τ η ν π} (hw : w ∈ ElimChartNbhd ρ σ τ η ν π J) :
    1 / 12 * (frobeniusSq (elimPsi J w.1 w.2).U + frobeniusSq (elimPsi J w.1 w.2).Tp
          + frobeniusSq ((elimPsi J w.1 w.2).Y0 * (elimPsi J w.1 w.2).SZ))
        ≤ frobeniusSq (w.2 * w.1 - elimCmat J σ ν)
      ∧ frobeniusSq (w.2 * w.1 - elimCmat J σ ν)
        ≤ 6 * (frobeniusSq (elimPsi J w.1 w.2).U + frobeniusSq (elimPsi J w.1 w.2).Tp
            + frobeniusSq ((elimPsi J w.1 w.2).Y0 * (elimPsi J w.1 w.2).SZ)) := by
  obtain ⟨hR6, hR3⟩ := elim_opNormSqBounds_on_nbhd J hw
  set U := (elimPsi J w.1 w.2).U with hU
  set X := elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂ with hX
  set Rin := elimRinv (elimPtop J (elimDOf w.1 w.2)) (elimPbot J (elimDOf w.1 w.2)) with hRin
  set V := Matrix.fromRows (elimPsi J w.1 w.2).Tp
    ((elimPsi J w.1 w.2).Y0 * (elimPsi J w.1 w.2).SZ) with hV
  have hVsplit : frobeniusSq V = frobeniusSq (elimPsi J w.1 w.2).Tp
      + frobeniusSq ((elimPsi J w.1 w.2).Y0 * (elimPsi J w.1 w.2).SZ) := frobeniusSq_elimV _ _
  have hUn : (0 : ℝ) ≤ frobeniusSq U := frobeniusSq_nonneg _
  have hVn : (0 : ℝ) ≤ frobeniusSq V := frobeniusSq_nonneg _
  -- Lemma 5.2 with `‖X‖₂ ≤ ½`, on the right.
  have hPb : frobeniusSq (U * X) ≤ frobeniusSq U / 4 := by
    have hXt : IsOpNormSqBound Xᵀ (1 / 4) :=
      isOpNormSqBound_of_frobeniusSq_le (by rw [frobeniusSq_transpose]; exact hw.2.1.le)
    have := frobeniusSq_mul_le_right hXt U
    linarith
  -- Lemma 5.4's upper bound on `R⁻¹`.
  have hQhi : frobeniusSq (Rin * V) ≤ 3 * frobeniusSq V := frobeniusSq_mul_le hR3 V
  -- Lemma 5.4's lower bound, through `R(R⁻¹V) = V`.
  have hQlo : frobeniusSq V / 6 ≤ frobeniusSq (Rin * V) := by
    have hRR : elimR (elimPtop J (elimDOf w.1 w.2)) (elimPbot J (elimDOf w.1 w.2)) * (Rin * V)
        = V := by
      rw [hRin, ← Matrix.mul_assoc, elimR_mul_elimRinv_of_det hw.1.2, Matrix.one_mul]
    have h6 := frobeniusSq_mul_le hR6 (Rin * V)
    rw [hRR] at h6
    linarith
  -- Step 7 itself.
  have hsqU : Real.sqrt (frobeniusSq U) ^ 2 = frobeniusSq U := Real.sq_sqrt hUn
  have hsqV : Real.sqrt (frobeniusSq V) ^ 2 = frobeniusSq V := Real.sq_sqrt hVn
  have key := elimination_comparability (Real.sqrt (frobeniusSq U)) (Real.sqrt (frobeniusSq V))
    (U * X) (Rin * V)
    (by rw [← frobeniusSq_eq_norm_sq', hsqU]; exact hPb)
    (by rw [← frobeniusSq_eq_norm_sq', hsqV]; exact hQlo)
    (by rw [← frobeniusSq_eq_norm_sq', hsqV]; exact hQhi)
  rw [hsqU, hsqV, ← frobeniusSq_eq_norm_sq'] at key
  rw [elim_step6_at_psi J w hw.1.1 hw.1.2, ← hU, ← hX, ← hRin, ← hV]
  rw [hVsplit] at key
  exact ⟨by linarith [key.1], by linarith [key.2]⟩

end Step6AtPsi



/-! ## Restricting a chart to a smaller domain

`bijOn_elimPsiProd` is a bijection of `ElimChartDomain` onto `ElimChartImage`, but Step 7's
comparison holds only on the smaller `ElimChartNbhd`. Print says as much: "take `O` to be the
preimage under `Ψ` of a small open box inside `N₀`".

Restricting a bijection is trivial; the content is that the restricted *image* is still open.
It is, because the image can be written as `t ∩ Φ⁻¹(s')` — the inverse is continuous on `t`,
so that is an intersection of two open sets. Nothing about the elimination chart enters. -/

section Restrict

variable {E F : Type*}

/-- The image of a subset under a bijection with a two-sided inverse, as a preimage. -/
public theorem image_eq_inter_preimage {f : E → F} {g : F → E} {s : Set E} {t : Set F}
    {s' : Set E} (hbij : Set.BijOn f s t) (hinv : Set.InvOn g f s t) (hs' : s' ⊆ s) :
    f '' s' = t ∩ g ⁻¹' s' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hbij.mapsTo (hs' hx), by simp only [Set.mem_preimage, hinv.1 (hs' hx)]; exact hx⟩
  · rintro ⟨hy, hgy⟩
    exact ⟨g y, hgy, hinv.2 hy⟩

/-- A bijection with a two-sided inverse restricts to any subset of its domain. -/
public theorem bijOn_restrict {f : E → F} {g : F → E} {s : Set E} {t : Set F} {s' : Set E}
    (hbij : Set.BijOn f s t) (hinv : Set.InvOn g f s t) (hs' : s' ⊆ s) :
    Set.BijOn f s' (t ∩ g ⁻¹' s') ∧ Set.InvOn g f s' (t ∩ g ⁻¹' s') := by
  rw [← image_eq_inter_preimage hbij hinv hs']
  refine ⟨⟨Set.mapsTo_image _ _, fun x hx x' hx' hEq => hbij.injOn (hs' hx) (hs' hx') hEq,
    Set.surjOn_image _ _⟩, fun x hx => hinv.1 (hs' hx), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  rw [hinv.1 (hs' hx)]

end Restrict

/-! ## Normalizing a chart, with its inverse

`normalized_chart` moves the base point to `0` but says nothing about `Φ`, and
`HasEliminationChartAt` asks for both directions. The translated inverse is
`y ↦ Φ(y + Ψ(w₀))`; the two round trips and its analyticity are one line each, since
translation is an analytic bijection of the whole space. -/

section NormalizeInv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The translated inverse is a two-sided inverse of the translated chart. -/
public theorem invOn_sub_const {f : E → F} {g : F → E} {s : Set E} {t : Set F} (c : F)
    (hinv : Set.InvOn g f s t) :
    Set.InvOn (fun y => g (y + c)) (fun x => f x - c) s ((fun y => y - c) '' t) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · show g (f x - c + c) = x
    rw [sub_add_cancel, hinv.1 hx]
  · rintro y ⟨z, hz, rfl⟩
    show f (g (z - c + c)) - c = z - c
    rw [sub_add_cancel, hinv.2 hz]

/-- Translation preserves analyticity of the inverse, on the translated set. -/
public theorem analyticOnNhd_comp_add_const {g : F → E} {t : Set F} (c : F)
    (hg : AnalyticOnNhd ℝ g t) :
    AnalyticOnNhd ℝ (fun y => g (y + c)) ((fun y => y - c) '' t) := by
  rintro y ⟨z, hz, rfl⟩
  have htr : AnalyticAt ℝ (fun y : F => y + c) (z - c) :=
    (analyticAt_id).add analyticAt_const
  have hmid : AnalyticAt ℝ g (z - c + c) := by rw [sub_add_cancel]; exact hg z hz
  exact AnalyticAt.comp (g := g) (f := fun y : F => y + c) hmid htr

end NormalizeInv


/-! ## The coordinate equivalence does not move the comparison function

`comparisonGerm` reads three of `ChartSpace`'s four components. Two of them — `Y₀` and `S_Z` —
are carried across unchanged, because their index types are already `Fin`-shaped. The third,
`u`, packs `U` and `T′` into a single Euclidean coordinate, and the packing is an isometry, so
`‖u‖² = ‖U‖²_F + ‖T′‖²_F`.

Together: the germ measured in `ChartSpace` is print's `NF = ‖U‖² + ‖T′‖² + ‖Y₀S_Z‖²`, which is
what Step 7 bounds. Without this the transported chart would carry an unrelated germ. -/

section CoordGerm

variable {M N H r a b : ℕ}

/-- `Y₀` passes through the coordinate equivalence unchanged. -/
public theorem elimCoordEquiv_Y0 (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (c : ElimCoordsProd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
      (Fin (elimN N a)) (Fin (elimP M b))) :
    (elimCoordEquiv haH hra hrb hab haN hbM c).2.1 = c.2.2.1 := rfl

/-- `S_Z` passes through unchanged. -/
public theorem elimCoordEquiv_SZ (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (c : ElimCoordsProd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
      (Fin (elimN N a)) (Fin (elimP M b))) :
    (elimCoordEquiv haH hra hrb hab haN hbM c).2.2.1 = c.2.2.2.1 := rfl

/-- **`‖u‖² = ‖U‖²_F + ‖T′‖²_F`.** The `u`-block packing is an isometry, and reindexing does not
move the Frobenius square. -/
public theorem norm_sq_elimCoordEquiv_fst (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (c : ElimCoordsProd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
      (Fin (elimN N a)) (Fin (elimP M b))) :
    ‖(elimCoordEquiv haH hra hrb hab haN hbM c).1‖ ^ 2
      = frobeniusSq c.1 + frobeniusSq c.2.1 := by
  show ‖euclCongr (elimQ_eq_add hbM haN).symm
      (matrixPairEucl M a b (elimN N a)
        (Matrix.reindex (elimOutputIdx hbM hrb) (elimAIdx hra) c.1,
          Matrix.reindex (elimBIdx hrb) (Equiv.refl (Fin (elimN N a))) c.2.1))‖ ^ 2 = _
  rw [norm_sq_euclCongr, norm_sq_matrixPairEucl, frobeniusSq_reindex, frobeniusSq_reindex]

/-- **The transported germ is print's `NF`.** -/
public theorem comparisonGerm_elimCoordEquiv (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (c : ElimCoordsProd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
      (Fin (elimN N a)) (Fin (elimP M b))) :
    comparisonGerm (elimCoordEquiv haH hra hrb hab haN hbM c).1
        (elimCoordEquiv haH hra hrb hab haN hbM c).2.1
        (elimCoordEquiv haH hra hrb hab haN hbM c).2.2.1
      = frobeniusSq c.1 + frobeniusSq c.2.1 + frobeniusSq (c.2.2.1 * c.2.2.2.1) := by
  rw [comparisonGerm, norm_sq_elimCoordEquiv_fst, elimCoordEquiv_Y0, elimCoordEquiv_SZ]

end CoordGerm


/-! ## `2K` on the parameter side

`HasEliminationChartAt` measures the loss with `rrrLoss` at `Fin`-indexed matrices, while
Step 6 computes a Frobenius square over `Sum` index types. The two are the same number: the
product of two reindexed matrices is the reindexed product, the truth matrix is
`partialIdMatrix` read through the same equivalences, and reindexing does not move the
Frobenius square. -/

section LossTransport

variable {M N H r a b : ℕ}

private theorem submatrix_sub' {ι κ ι' κ' : Type*} (A B : Matrix ι κ ℝ) (e : ι' → ι)
    (f : κ' → κ) : A.submatrix e f - B.submatrix e f = (A - B).submatrix e f := by
  ext i j
  rfl

/-- **`2K` is Step 6's Frobenius square**, transported to the parameter space. -/
public theorem two_mul_rrrLoss_elimParamEquivNF (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (w : PairSpace (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
      (Fin (elimN N a)) (Fin (elimP M b))) :
    2 * rrrLoss (partialIdMatrix M N r)
        (elimParamEquivNF haH hra hrb hab haN hbM w).1
        (elimParamEquivNF haH hra hrb hab haN hbM w).2
      = frobeniusSq (w.2 * w.1
          - elimCmat (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (Fin (a - r))
              (Fin (elimN N a))) := by
  have hC : partialIdMatrix M N r
      = (elimCmat (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) (Fin (a - r))
          (Fin (elimN N a))).submatrix (elimOutputIdx hbM hrb).symm
            (elimInputIdx haN hra).symm := by
    rw [← partialIdMatrix_reindex hra hrb haN hbM, Matrix.submatrix_submatrix]
    simp
  have hprod : (elimParamEquivNF haH hra hrb hab haN hbM w).2
        * (elimParamEquivNF haH hra hrb hab haN hbM w).1
      = (w.2 * w.1).submatrix (elimOutputIdx hbM hrb).symm (elimInputIdx haN hra).symm := by
    show (w.2.submatrix (elimOutputIdx hbM hrb).symm
        (elimHiddenIdxNF haH hra hrb hab).symm)
      * (w.1.submatrix (elimHiddenIdxNF haH hra hrb hab).symm
        (elimInputIdx haN hra).symm) = _
    exact Matrix.submatrix_mul_equiv w.2 w.1 _ (elimHiddenIdxNF haH hra hrb hab).symm _
  rw [two_mul_rrrLoss_eq_frobeniusSq, hprod, hC, submatrix_sub',
    frobeniusSq_submatrix_equiv]

end LossTransport


/-! ## The chart on print's neighborhood

Everything so far is assembled here: the chart restricted to `ElimChartNbhd`, its image, and
the analyticity of both directions there. -/

section NbhdChart

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
variable [DecidableEq π]

/-- `Φ` is a two-sided inverse of `Ψ` in the product presentation, on print's open set. This is
`elimPsi_invOn` read through `elimCoordsEquivProd`. -/
public theorem elimPsiProd_invOn (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set.InvOn (elimPhiProd J) (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
      (ElimChartDomain ρ σ τ η ν π J) (ElimChartImage ρ σ τ η ν π J) := by
  refine ⟨fun w hw => ?_, fun c hc => ?_⟩
  · show elimPhiProd J (elimPsiProd J w.1 w.2) = w
    rw [elimPhiProd, elimPsiProd, Equiv.symm_apply_apply, elimPhi_elimPsi J hw.1 hw.2]
  · show elimPsiProd J (elimPhiProd J c).1 (elimPhiProd J c).2 = c
    rw [elimPsiProd, elimPhiProd,
      elimPsi_elimPhi (J := J) (c := elimCoordsEquivProd.symm c) hc.1.1 hc.1.2,
      Equiv.apply_symm_apply]

/-- Print's `O'` for the restricted chart: the image of `ElimChartNbhd`. -/
@[expose] public noncomputable def ElimNbhdImage (ρ σ τ η ν π : Type*) [Fintype ρ] [Fintype σ]
    [Fintype τ] [Fintype η] [Fintype ν] [Fintype π] [DecidableEq ρ] [DecidableEq σ]
    [DecidableEq τ] [DecidableEq η] [DecidableEq ν] [DecidableEq π]
    (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) : Set (ElimCoordsProd ρ σ τ η ν π) :=
  ElimChartImage ρ σ τ η ν π J ∩ elimPhiProd J ⁻¹' ElimChartNbhd ρ σ τ η ν π J

/-- **The restricted image is open.** `Φ` is continuous where its own denominator survives,
and `ElimChartImage` sits inside that set. -/
public theorem isOpen_ElimNbhdImage (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimNbhdImage ρ σ τ η ν π J) := by
  have hs : IsOpen {c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_coord_A11_det
  have hcont : ContinuousOn (elimPhiProd J)
      {c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} :=
    (analyticOnNhd_elimPhiProd J).continuousOn
  have hpre : IsOpen ({c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} ∩
      elimPhiProd J ⁻¹' ElimChartNbhd ρ σ τ η ν π J) :=
    hcont.isOpen_inter_preimage hs (isOpen_ElimChartNbhd J)
  have heq : ElimNbhdImage ρ σ τ η ν π J =
      ElimChartImage ρ σ τ η ν π J ∩
        ({c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} ∩
          elimPhiProd J ⁻¹' ElimChartNbhd ρ σ τ η ν π J) := by
    ext c
    simp only [ElimNbhdImage, ElimChartImage, ElimCoordDomain, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage, isUnit_iff_ne_zero]
    tauto
  rw [heq]
  exact (isOpen_ElimChartImage J).inter hpre

/-- **The chart restricted to print's neighborhood** is still a bijection with a two-sided
inverse. -/
public theorem bijOn_elimPsiProd_nbhd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set.BijOn (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
        (ElimChartNbhd ρ σ τ η ν π J) (ElimNbhdImage ρ σ τ η ν π J)
      ∧ Set.InvOn (elimPhiProd J)
        (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
        (ElimChartNbhd ρ σ τ η ν π J) (ElimNbhdImage ρ σ τ η ν π J) :=
  bijOn_restrict (bijOn_elimPsiProd J) (elimPsiProd_invOn J) Set.inter_subset_left

/-- `Φ` is analytic on the restricted image. -/
public theorem analyticOnNhd_elimPhiProd_nbhd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    AnalyticOnNhd ℝ (elimPhiProd J) (ElimNbhdImage ρ σ τ η ν π J) :=
  (analyticOnNhd_elimPhiProd J).mono fun _c hc => IsUnit.ne_zero hc.1.1.1

/-- `Ψ` is analytic on print's neighborhood. -/
public theorem analyticOnNhd_elimPsiProd_nbhd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    AnalyticOnNhd ℝ (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
      (ElimChartNbhd ρ σ τ η ν π J) :=
  (analyticOnNhd_elimPsiProd J).mono Set.inter_subset_left

end NbhdChart



/-! ## The normalization does not move the germ

Print normalizes the chart by carrying `A₁₁ − I_a` and `D − D*` instead of `A₁₁` and `D`. In
the present form the normalization is a single subtraction of `Ψ(A*, B*)`, and it is harmless
for exactly the reason print's is: the four coordinates `comparisonGerm` reads already vanish
at the base point, so the subtraction changes only the two gauge coordinates the germ ignores.

The lemma states equality of the composed germs, not of one projected coordinate. -/

section NormalizedGerm

variable {M N H r a b : ℕ}

/-- **The transported, normalized germ is print's `NF`.** -/
public theorem comparisonGerm_transported (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (w : PairSpace (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
      (Fin (elimN N a)) (Fin (elimP M b))) :
    comparisonGerm
        ((elimCoordEquiv haH hra hrb hab haN hbM)
          (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2
            - elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
                (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)).1
        ((elimCoordEquiv haH hra hrb hab haN hbM)
          (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2
            - elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
                (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)).2.1
        ((elimCoordEquiv haH hra hrb hab haN hbM)
          (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2
            - elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
                (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)).2.2.1
      = frobeniusSq (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2).U
        + frobeniusSq (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2).Tp
        + frobeniusSq
            ((elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2).Y0
              * (elimPsi (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2).SZ) := by
  obtain ⟨hU0, hTp0, hY00, hSZ0⟩ :=
    elimPsi_elimBasePoint_comparison (r := r) (a := a) (b := b) (M := M) (N := N) (H := H)
  have hc1 : (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
      (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2).1 = 0 := hU0
  have hc2 : (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
      (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2).2.1 = 0 := hTp0
  have hz1 : ((elimCoordEquiv haH hra hrb hab haN hbM)
      (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
        (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)).1 = 0 := by
    have hn := norm_sq_elimCoordEquiv_fst haH hra hrb hab haN hbM
      (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
        (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)
    simp only [hc1, hc2, frobeniusSq_zero, add_zero] at hn
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hn)
  have hz2 : ((elimCoordEquiv haH hra hrb hab haN hbM)
      (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
        (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)).2.1 = 0 := by
    rw [elimCoordEquiv_Y0]
    exact hY00
  have hz3 : ((elimCoordEquiv haH hra hrb hab haN hbM)
      (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
        (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)).2.2.1 = 0 := by
    rw [elimCoordEquiv_SZ]
    exact hSZ0
  rw [map_sub, Prod.fst_sub, hz1, sub_zero, Prod.snd_sub, Prod.fst_sub, hz2, sub_zero,
    Prod.snd_sub, Prod.fst_sub, hz3, sub_zero, comparisonGerm_elimCoordEquiv]
  rfl

end NormalizedGerm

/-! ## Theorem 5.1

Every piece is now in place:

* the chart is a bijection of `ElimChartNbhd` onto an open set, with an analytic two-sided
  inverse (`bijOn_elimPsiProd_nbhd`, `isOpen_ElimNbhdImage`);
* the canonical representative is in that neighborhood (`elimBasePoint_mem_ElimChartNbhd`) and
  is the base point `IsEliminationChart` names (`elimParamEquivNF_elimBasePoint`);
* subtracting `Ψ(A*, B*)` moves it to `0` without touching the comparison coordinates, since
  those already vanish there (`elimPsi_elimBasePoint_comparison`);
* the two equivalences carry the chart across without moving either side of the comparison
  (`comparisonGerm_elimCoordEquiv`, `two_mul_rrrLoss_elimParamEquivNF`); and
* on the neighborhood the comparison holds with print's constants
  (`elim_comparison_on_nbhd`).

The hypotheses are exactly the feasibility conditions that make print's five `ℕ` subtractions
exact. `a ≤ H` is not among them: it follows from `a + b ≤ H + r` and `r ≤ b`. -/

section Final

variable {M N H r a b : ℕ}

/-- **Theorem 5.1 (Elimination), p. 10, at every feasible stratum.**

At the canonical representative of the stratum `(a, b, r)` there is an open neighborhood
carrying an analytic chart in which `2K` is two-sidedly comparable to `‖u‖² + ‖Y₀S_Z‖²_F` with
print's uniform constants `1/12` and `6`.

This replaces `isEliminationChart_zero`, which established only the degenerate stratum, as the
inhabitant of `IsEliminationChart`; that theorem remains as the `r = a = b = 0` sanity check. -/
public theorem isEliminationChart_of_feasible (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M) :
    IsEliminationChart M N H r a b := by
  have haH : a ≤ H := by omega
  obtain ⟨hU0, hTp0, hY00, hSZ0⟩ :=
    elimPsi_elimBasePoint_comparison (r := r) (a := a) (b := b) (M := M) (N := N) (H := H)
  obtain ⟨hbij0, hinv0⟩ :=
    bijOn_elimPsiProd_nbhd (ρ := Fin r) (σ := Fin (a - r)) (τ := Fin (b - r))
      (η := Fin (elimH H r a b)) (ν := Fin (elimN N a)) (π := Fin (elimP M b))
      (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ :=
    normalized_chart
      (f := fun w : PairSpace (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
        (Fin (elimN N a)) (Fin (elimP M b)) =>
        elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))) w.1 w.2)
      (elimBasePoint r a b M N H) elimBasePoint_mem_ElimChartNbhd
      (isOpen_ElimChartNbhd _) (isOpen_ElimNbhdImage _) hbij0
      (analyticOnNhd_elimPsiProd_nbhd _)
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
    chart_transport (elimParamEquivNF haH hra hrb hab haN hbM)
      (elimCoordEquiv haH hra hrb hab haN hbM) n1 n2 n3 n4
      (invOn_sub_const _ hinv0) n5
      (analyticOnNhd_comp_add_const _ (analyticOnNhd_elimPhiProd_nbhd _)) n6
  have hbase : (elimParamEquivNF haH hra hrb hab haN hbM) (elimBasePoint r a b M N H)
      = (canonicalA N H a b r, canonicalB M H b r) :=
    elimParamEquivNF_elimBasePoint haH hra hrb hab haN hbM
  refine ⟨(elimParamEquivNF haH hra hrb hab haN hbM) ''
      ElimChartNbhd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
        (Fin (elimN N a)) (Fin (elimP M b)) (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b))),
    (elimCoordEquiv haH hra hrb hab haN hbM) ''
      ((fun y => y - elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
          (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2) ''
        ElimNbhdImage (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
          (Fin (elimN N a)) (Fin (elimP M b)) (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))),
    (fun x => (elimCoordEquiv haH hra hrb hab haN hbM)
      (elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
          ((elimParamEquivNF haH hra hrb hab haN hbM).symm x).1
          ((elimParamEquivNF haH hra hrb hab haN hbM).symm x).2
        - elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
            (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2)),
    (fun y => (elimParamEquivNF haH hra hrb hab haN hbM)
      (elimPhiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
        ((elimCoordEquiv haH hra hrb hab haN hbM).symm y
          + elimPsiProd (elimJ (Fin r) (Fin (b - r)) (Fin (elimP M b)))
              (elimBasePoint r a b M N H).1 (elimBasePoint r a b M N H).2))),
    t1, t2, ?_, t4, t5, t6, t7, ?_, ?_⟩
  · rw [← hbase]; exact t3
  · rw [← hbase]; exact t8
  rintro x ⟨w, hw, rfl⟩
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [comparisonGerm_transported haH hra hrb hab haN hbM w,
    two_mul_rrrLoss_elimParamEquivNF haH hra hrb hab haN hbM w]
  exact elim_comparison_on_nbhd _ hw

end Final

end AISafetyAtlas.SingularLearning
