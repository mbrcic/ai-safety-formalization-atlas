module

public import AISafetyAtlas.LinearSystems
public import AISafetyAtlas.LinearSystems.BlockBound
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Two two-state systems, one observable and one not

The smallest pair that separates the observability criterion, and the smallest
statement of what its failure costs.

Both systems have state space `Fin 2 → ℚ` and a single scalar output.

* **The shift.** `A = ![![0, 1], ![0, 0]]` moves the second coordinate into the
  first; `C = ![![1, 0]]` reads the first. One step later the output reveals the
  second coordinate, so the state is determined: `shift_isObservable`.
* **The frozen system.** `A = 1` and the same `C`. The second coordinate never
  moves into view, so it is never read: `frozen_not_isObservable`.

`frozen_indistinguishable` is the part worth having. It exhibits **two distinct
states whose entire output sequence agrees** — every `C * A ^ k` sends them to
the same vector. That is as close as this algebraic layer gets to "the state
cannot be reconstructed from the outputs": there is no trajectory in this file,
only the family of maps a trajectory is read through. The reading itself is
proved elsewhere and no longer waits on anything —
`AISafetyAtlas.LinearSystems.determinesStateOn_iff_isObservable` is the
equivalence and `AISafetyAtlas.Examples.LinearSystems.blind_not_determinesStateOn`
is a system whose state its outputs do not determine.

The controllability side is the same two matrices read dually:
`reachable_isControllable` drives the shift to any state with a scalar input.
-/

namespace AISafetyAtlas.Examples.LinearSystems

open AISafetyAtlas.LinearSystems Matrix

/-- The output map: read the first coordinate. -/
@[expose] public def readFirst : Matrix (Fin 1) (Fin 2) ℚ := ![![1, 0]]

/-- The shift: the second coordinate becomes the first. -/
@[expose] public def shift : Matrix (Fin 2) (Fin 2) ℚ := ![![0, 1], ![0, 0]]

/-- The input map: drive the second coordinate. -/
@[expose] public def driveSecond : Matrix (Fin 2) (Fin 1) ℚ := ![![0], ![1]]

/-! ## The shift is observable -/

public theorem shift_isObservable : IsObservable shift readFirst := by
  intro x hx
  have h0 := congrFun (hx 0) 0
  have h1 := congrFun (hx 1) 0
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, pow_zero, Matrix.mul_one] at h0
  rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, pow_one,
    ← Matrix.mulVec_mulVec] at h1
  simp [readFirst, shift, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-! ## The frozen system is not, and two states collide -/

/-- The frozen system never moves the second coordinate into view. -/
private lemma readFirst_mul_one_pow (k : ℕ) :
    readFirst * (1 : Matrix (Fin 2) (Fin 2) ℚ) ^ k = readFirst := by
  rw [one_pow, Matrix.mul_one]

public theorem frozen_not_isObservable :
    ¬ IsObservable (1 : Matrix (Fin 2) (Fin 2) ℚ) readFirst := by
  intro h
  have hx : ![(0 : ℚ), 1] = 0 := by
    refine h ![0, 1] fun k => ?_
    rw [readFirst_mul_one_pow]
    funext i
    fin_cases i
    simp [readFirst, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have := congrFun hx 1
  norm_num at this

/-- **The output sequence does not separate the states.** Two distinct states of
the frozen system are sent to the same vector by every `C * A ^ k`. -/
public theorem frozen_indistinguishable :
    ![(0 : ℚ), 0] ≠ ![(0 : ℚ), 1] ∧
      ∀ k : ℕ,
        (readFirst * (1 : Matrix (Fin 2) (Fin 2) ℚ) ^ k) *ᵥ ![(0 : ℚ), 0]
          = (readFirst * (1 : Matrix (Fin 2) (Fin 2) ℚ) ^ k) *ᵥ ![(0 : ℚ), 1] := by
  refine ⟨fun h => ?_, fun k => ?_⟩
  · have := congrFun h 1
    norm_num at this
  · rw [readFirst_mul_one_pow]
    funext i
    fin_cases i
    simp [readFirst, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ## The controllability side -/

public theorem reachable_isControllable : IsControllable shift driveSecond := by
  intro x
  refine ⟨![![x 1], ![x 0]], ?_⟩
  rw [Fin.sum_univ_two]
  simp only [show ((0 : Fin 2) : ℕ) = 0 from rfl, show ((1 : Fin 2) : ℕ) = 1 from rfl,
    pow_zero, pow_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  funext i
  fin_cases i
  · simp [shift, driveSecond, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [shift, driveSecond, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ## The Klamka bound is not vacuous

The frozen system again, over the complex numbers so the Hautus route applies:
the identity has a two-dimensional eigenspace at `μ = 1`, and one input column
cannot cover it. This inhabits the hypothesis of
`not_isControllable_of_finrank_ker_gt_width`, so that theorem is not a statement
about an empty class.
-/

/-- The frozen complex system: nothing moves. -/
@[expose] public def frozenC : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- One input column, driving the second coordinate. -/
@[expose] public def oneColumn : Matrix (Fin 2) (Fin 1) ℂ := ![![0], ![1]]

/-- At `μ = 1` the eigenspace of the frozen system is everything. -/
public theorem frozenC_finrank_ker :
    Module.finrank ℂ
        (LinearMap.ker ((1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - frozenC).mulVecLin)
      = 2 := by
  have h0 : (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - frozenC = 0 := by
    rw [frozenC, one_smul, sub_self]
  rw [h0, Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top, Module.finrank_pi,
    Fintype.card_fin]

/-- **The bound applies, and the system really is uncontrollable.** -/
public theorem frozenC_not_isControllable : ¬ IsControllable frozenC oneColumn := by
  refine not_isControllable_of_finrank_ker_gt_width frozenC oneColumn 1 ?_
  rw [frozenC_finrank_ker]
  norm_num


/-! ## Print's own antecedent, at the same witness

`AISafetyAtlas.LinearSystems.BlockBound` states Klamka's test in the two
multiplicities print uses rather than in the eigenspace dimension. The same
frozen system inhabits *that* hypothesis, so the print-form statements are not
about an empty class either.
-/

/-- The generalized eigenspace chain of the frozen system has already stopped at
step one: the whole space is an eigenspace. -/
public theorem frozenC_stabilizes :
    Module.End.maxGenEigenspace (Matrix.mulVecLin frozenC) 1
      = Module.End.genEigenspace (Matrix.mulVecLin frozenC) 1 ((1 : ℕ) : ℕ∞) := by
  have hzero : Matrix.mulVecLin frozenC - (1 : ℂ) • (1 : Module.End ℂ (Fin 2 → ℂ)) = 0 := by
    rw [frozenC, Matrix.mulVecLin_one, one_smul, ← Module.End.one_eq_id, sub_self]
  have htop : Module.End.genEigenspace (Matrix.mulVecLin frozenC) 1 ((1 : ℕ) : ℕ∞) = ⊤ := by
    rw [Nat.cast_one, Module.End.genEigenspace_one, hzero, LinearMap.ker_zero]
  rw [htop, eq_top_iff, ← htop]
  exact Module.End.genEigenspace_le_maximal (Matrix.mulVecLin frozenC) 1 1

/-- Its characteristic polynomial has `1` as a double root — print's `nᵢ = 2`. -/
public theorem frozenC_rootMultiplicity :
    frozenC.charpoly.rootMultiplicity 1 = 2 := by
  have hchar : frozenC.charpoly
      = (Polynomial.X - Polynomial.C (1 : ℂ)) ^ 2 := by
    rw [← charpoly_mulVecLin, frozenC, Matrix.mulVecLin_one]
    rw [← Module.End.one_eq_id, LinearMap.charpoly_one]
    congr 1
    simp
  rw [hchar]
  simpa using Polynomial.rootMultiplicity_X_sub_C_pow (1 : ℂ) 2

/-- **Print's test fires, at print's own quantities.** With `nᵢ = 2` and a
stabilizing exponent of `1`, the ceiling is `2`, which exceeds the single input
column. -/
public theorem frozenC_not_isControllable_klamka : ¬ IsControllable frozenC oneColumn := by
  refine not_isControllable_of_ceil_div_gt_width frozenC oneColumn 1
    Nat.one_pos frozenC_stabilizes ?_
  rw [frozenC_rootMultiplicity]
  norm_num

/-! ## Print's index, at the same witness

`AISafetyAtlas.LinearSystems.BlockBound` identifies the stage at which the
generalized eigenspace chain stops growing with the multiplicity of the
eigenvalue in the **minimal** polynomial — print's `νᵢ`, the quantity print's
test is stated in and the one print cites Zadeh and Desoer for. The frozen
system carries both numbers.
-/

/-- The frozen system's minimal polynomial is `X - 1`, so print's `νᵢ` is `1`
while its `nᵢ` is `2`. -/
public theorem frozenC_minpoly_rootMultiplicity :
    (minpoly ℂ frozenC).rootMultiplicity 1 = 1 := by
  have h : minpoly ℂ frozenC = Polynomial.X - Polynomial.C (1 : ℂ) := by
    rw [frozenC, minpoly.one]
    simp
  rw [h]
  exact Polynomial.rootMultiplicity_X_sub_C_self

/-- **The identification, at the witness.** The stabilization index of the
frozen system at `μ = 1` is `1`, and so is the multiplicity of `1` in its
minimal polynomial. -/
public theorem frozenC_maxGenEigenspaceIndex :
    Module.End.maxGenEigenspaceIndex (Matrix.mulVecLin frozenC) 1 = 1 := by
  rw [maxGenEigenspaceIndex_eq_rootMultiplicity_minpoly, minpoly_mulVecLin,
    frozenC_minpoly_rootMultiplicity]

/-- **Print's test fires in print's own vocabulary.** With `nᵢ = 2` and `νᵢ = 1`
read off the two polynomials of `A` alone, the ceiling is `2`, which exceeds the
single input column. No exponent is supplied by the caller. -/
public theorem frozenC_not_isControllable_klamka_minpoly :
    ¬ IsControllable frozenC oneColumn := by
  refine not_isControllable_of_ceil_div_minpoly_gt_width frozenC oneColumn 1
    (by rw [frozenC_minpoly_rootMultiplicity]; norm_num) ?_
  rw [frozenC_rootMultiplicity, frozenC_minpoly_rootMultiplicity]
  norm_num

/-! ## The remaining Klamka corollaries and matrix lemma, at the same witness -/

/-- One output row, reading the second coordinate — the observability twin of
`oneColumn`. -/
@[expose] public def oneRow : Matrix (Fin 1) (Fin 2) ℂ := ![![0, 1]]

/-- `frozenC` is symmetric, so its transpose has the same eigenspace dimension
at `μ = 1`. -/
public theorem frozenCT_finrank_ker :
    Module.finrank ℂ
        (LinearMap.ker ((1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - frozenCᵀ).mulVecLin)
      = 2 := by
  rw [show frozenCᵀ = frozenC from by rw [frozenC]; exact Matrix.transpose_one]
  exact frozenC_finrank_ker

/-- **Klamka's Corollary 2**, at the frozen system: one output row cannot see
a two-dimensional eigenspace. -/
public theorem frozenC_not_isObservable_klamka_corollary2 :
    ¬ IsObservable frozenC oneRow :=
  not_isObservable_of_finrank_ker_gt_height frozenC oneRow 1
    (by rw [frozenCT_finrank_ker]; norm_num)

/-- **Klamka's Theorem 1 in print's own vocabulary**, against the *rank* of the
input matrix rather than its width: one column has rank at most one, and print's
ceiling is `2`. -/
public theorem frozenC_not_isControllable_klamka_minpoly_rank :
    ¬ IsControllable frozenC oneColumn := by
  refine not_isControllable_of_ceil_div_minpoly_gt_rank frozenC oneColumn 1
    (by rw [frozenC_minpoly_rootMultiplicity]; norm_num) ?_
  have hB := oneColumn.rank_le_card_width
  rw [Fintype.card_fin] at hB
  rw [frozenC_rootMultiplicity, frozenC_minpoly_rootMultiplicity]
  omega

/-- **Klamka's Theorem 2 in print's own vocabulary**, against the rank of the
output matrix. -/
public theorem frozenC_not_isObservable_klamka_minpoly_rank :
    ¬ IsObservable frozenC oneRow := by
  have hT : frozenCᵀ = frozenC := by rw [frozenC]; exact Matrix.transpose_one
  refine not_isObservable_of_ceil_div_minpoly_gt_rank frozenC oneRow 1
    (by rw [hT, frozenC_minpoly_rootMultiplicity]; norm_num) ?_
  have hC := oneRow.rank_le_card_height
  rw [Fintype.card_fin] at hC
  rw [hT, frozenC_minpoly_rootMultiplicity, frozenC_rootMultiplicity]
  omega

/-- **Klamka's Corollary 2 in print's own vocabulary**, at the transposed frozen
system print's duality sentence sends it to. -/
public theorem frozenC_not_isObservable_klamka_minpoly :
    ¬ IsObservable frozenC oneRow := by
  have hT : frozenCᵀ = frozenC := by rw [frozenC]; exact Matrix.transpose_one
  refine not_isObservable_of_ceil_div_minpoly_gt_height frozenC oneRow 1
    (by rw [hT, frozenC_minpoly_rootMultiplicity]; norm_num) ?_
  rw [hT, frozenC_minpoly_rootMultiplicity, frozenC_rootMultiplicity]
  norm_num

/-- **Klamka's Corollary 4**, at the frozen system: the same eigenspace defeats
both a one-column input and a one-row output at once. -/
public theorem frozenC_not_controllable_not_observable_klamka_corollary4 :
    ¬ IsControllable frozenC oneColumn ∧ ¬ IsObservable frozenC oneRow :=
  not_isControllable_and_not_isObservable_of_finrank_ker_gt_dims frozenC oneColumn oneRow 1
    (by rw [frozenC_finrank_ker]; norm_num)

/-- **Klamka's Corollary 3 in print's own vocabulary**, at the frozen system:
one input column and one output row are each of rank at most one, and print's
ceiling is `2`. -/
public theorem frozenC_klamka_minpoly_corollary3 :
    ¬ IsControllable frozenC oneColumn ∧ ¬ IsObservable frozenC oneRow := by
  refine not_isControllable_and_not_isObservable_of_ceil_div_minpoly_gt_ranks
    frozenC oneColumn oneRow 1
    (by rw [frozenC_minpoly_rootMultiplicity]; norm_num) ?_
  have hB := oneColumn.rank_le_card_width
  have hC := oneRow.rank_le_card_height
  rw [Fintype.card_fin] at hB hC
  rw [frozenC_rootMultiplicity, frozenC_minpoly_rootMultiplicity]
  have : max oneColumn.rank oneRow.rank ≤ 1 := max_le hB hC
  omega

/-- **Klamka's Corollary 4 in print's own vocabulary**, at the same witness:
the two dimensions alone. -/
public theorem frozenC_klamka_minpoly_corollary4 :
    ¬ IsControllable frozenC oneColumn ∧ ¬ IsObservable frozenC oneRow := by
  refine not_isControllable_and_not_isObservable_of_ceil_div_minpoly_gt_dims
    frozenC oneColumn oneRow 1
    (by rw [frozenC_minpoly_rootMultiplicity]; norm_num) ?_
  rw [frozenC_rootMultiplicity, frozenC_minpoly_rootMultiplicity]
  norm_num

/-- **The unobservable subspace is `A`-invariant**, exhibited at its zero
vector — a genuine member of the subspace, since every subspace contains it. -/
public theorem frozenC_A_mulVec_zero_mem_unobservableSubspace :
    frozenC *ᵥ (0 : Fin 2 → ℂ) ∈ unobservableSubspace frozenC oneRow :=
  A_mulVec_mem_unobservableSubspace_of_mem (Submodule.zero_mem _)

/-- **A stacked matrix's rank is at most the sum of its pieces' ranks**, at
`frozenC` stacked on itself. -/
public theorem rank_fromRows_frozenC_le :
    (Matrix.fromRows frozenC frozenC).rank ≤ frozenC.rank + frozenC.rank :=
  MatrixLemmas.rank_fromRows_le frozenC frozenC

/-- **The generalized eigenspace is no bigger than the index times the
eigenspace.** Print's counting step with the index in place of an arbitrary
stabilizing exponent — the form in which print states it, and the one the
numbered results are read at once the index is known.

At the frozen system the index is `1`, so the bound reads `dim ≤ 1 · dim` and is
an equality; that is the degenerate case, and it is the one this file's numbers
live in. Nothing had run the statement at a matrix. -/
public theorem frozenC_finrank_maxGenEigenspace_le :
    Module.finrank ℂ (Module.End.maxGenEigenspace (Matrix.mulVecLin frozenC) 1)
      ≤ Module.End.maxGenEigenspaceIndex (Matrix.mulVecLin frozenC) 1 *
          Module.finrank ℂ (Module.End.eigenspace (Matrix.mulVecLin frozenC) 1) :=
  finrank_maxGenEigenspace_le_index_mul (Matrix.mulVecLin frozenC) 1

end AISafetyAtlas.Examples.LinearSystems
