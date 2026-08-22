module

public import AISafetyAtlas.Causal.ModelSpace

/-!
# Rounding a model, on a worked table

`AISafetyAtlas.Causal.ModelSpace` rounds a model's tables onto a grid so that
estimates range over a countable set. This module runs the construction on a
table one can check by hand, and gives the error bound its teeth.

The bound is `dim c · ε`, not `ε`, because the last entry of each conditional
absorbs the rounding error of all the others. That factor is not slack:
`abs_cpt_roundDown_sub_not_le_eps` exhibits a three-state table whose last entry
moves by `0.198` at `ε = 0.1`, so no bound `k · ε` with `k < 2` can hold for
three-state variables.
-/

namespace AISafetyAtlas.Examples.Causal.ModelSpace

open AISafetyAtlas.Causal

/-- One chance variable with three states and no parents. -/
public abbrev V := Fin 1

public abbrev dim3 : V → ℕ := fun _ ↦ 3

/-- The table `(0.199, 0.199, 0.602)`. Both leading entries sit just under the
grid point `0.2`, so each loses almost `ε = 0.1` when rounded down, and the last
entry absorbs both losses. -/
@[expose] public noncomputable def skewTable : Fin 3 → ℝ :=
  fun a ↦ if a = 0 then 199 / 1000 else if a = 1 then 199 / 1000 else 602 / 1000

/-- A model whose single variable carries `skewTable`. -/
public noncomputable def skewed : Model V dim3 ℝ where
  dim_pos := fun _ ↦ by norm_num
  parents := fun _ ↦ ∅
  acyclic := ⟨fun _ ↦ 0, by simp⟩
  cpt := fun _ a _ ↦ skewTable a
  cpt_parents := fun _ _ _ _ _ ↦ rfl
  cpt_nonneg := fun _ a _ ↦ by
    fin_cases a <;> norm_num [skewTable]
  cpt_sum := fun _ _ ↦ by
    rw [Fin.sum_univ_three]
    norm_num [skewTable, Fin.ext_iff]

/-- The grid spacing used throughout: `ε = 1/10`. -/
public theorem eps_pos : (0 : ℝ) < 1 / 10 := by norm_num

private theorem floor_skew : ⌊(199 : ℝ) / 100⌋ = 1 := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num

private theorem floorMul_skew : floorMul (1 / 10 : ℝ) (199 / 1000) = 1 / 10 := by
  have hdiv : ((199 : ℝ) / 1000) / (1 / 10) = 199 / 100 := by norm_num
  rw [floorMul, hdiv, floor_skew]
  norm_num

/-! ## The rounded table -/

/-- Each leading entry drops to the grid point below it. -/
public theorem cpt_roundDown_zero (v : Assignment V dim3) :
    (skewed.roundDown eps_pos).cpt 0 0 v = 1 / 10 := by
  simp only [Model.roundDown]
  rw [if_neg (by norm_num)]
  exact floorMul_skew

/-- The last entry is the remainder, and it is **larger** than the original: the
mass freed by rounding the other two down has to go somewhere. -/
public theorem cpt_roundDown_last (v : Assignment V dim3) :
    (skewed.roundDown eps_pos).cpt 0 2 v = 8 / 10 := by
  have hnot : Finset.univ.filter (fun b : Fin 3 ↦ ¬ ((b : ℕ) + 1 = 3)) = {0, 1} := by
    decide
  simp only [Model.roundDown]
  rw [if_pos (by norm_num), hnot]
  have h0 : skewed.cpt 0 0 v = 199 / 1000 := rfl
  have h1 : skewed.cpt 0 1 v = 199 / 1000 := rfl
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, h0, h1, floorMul_skew]
  norm_num

/-- The rounded model still carries the same graph, so `modelError` compares the
two on its table branch rather than on its graph branch. -/
public theorem parents_roundDown_skewed :
    (skewed.roundDown eps_pos).parents = skewed.parents := rfl

/-! ## The `dim c` factor has teeth

The last entry moves by `0.198`, which is almost `2ε`. So the bound
`|cpt' − cpt| ≤ dim c · ε` cannot be tightened to `ε`, and the extra factor is
not an artefact of the proof. -/

public theorem abs_cpt_roundDown_sub_not_le_eps (v : Assignment V dim3) :
    ¬ |(skewed.roundDown eps_pos).cpt 0 2 v - skewed.cpt 0 2 v| ≤ 1 / 10 := by
  have horig : skewed.cpt 0 2 v = 602 / 1000 := rfl
  rw [cpt_roundDown_last v, horig,
    show |(8 : ℝ) / 10 - 602 / 1000| = 198 / 1000 by
      rw [abs_of_nonneg (by norm_num)]; norm_num]
  norm_num

/-- The bound the library does prove, on this table: `dim c · ε = 3/10`. -/
public theorem abs_cpt_roundDown_sub_skewed (v : Assignment V dim3) :
    |(skewed.roundDown eps_pos).cpt 0 2 v - skewed.cpt 0 2 v|
      ≤ (dim3 0 : ℝ) * (1 / 10) :=
  skewed.abs_cpt_roundDown_sub eps_pos 0 2 v

/-! ## The error bound, on a concrete pair -/

/-- `modelError` against the rounded model is within `3 · ε` of the error
against the original, which is the printed statement instantiated. -/
public theorem modelError_roundDown_skewed (M : Model V dim3 ℝ) :
    |modelError M (skewed.roundDown eps_pos) - modelError M skewed|
      ≤ (3 : ℝ) * (1 / 10) :=
  modelError_roundDown_le M skewed eps_pos 3 fun _ ↦ le_refl 3

end AISafetyAtlas.Examples.Causal.ModelSpace
