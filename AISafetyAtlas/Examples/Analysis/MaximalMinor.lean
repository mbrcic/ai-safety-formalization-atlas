module

public import AISafetyAtlas.Analysis.MaximalMinor

/-!
# Worked examples for the maximal-minor lemma

Two witnesses: that the lemma applies at the smallest interesting shape, and that
its hypothesis is doing work.
-/

namespace AISafetyAtlas.Examples.Analysis.MaximalMinor

open Matrix AISafetyAtlas.Analysis

/-- **Two independent vectors in `ℝ³` are separated by two of the coordinates.**
The lemma supplies the row selection; nothing here has to name it. -/
public theorem exists_det_ne_zero_pair :
    ∃ f : Fin 2 → Fin 3,
      (Matrix.of fun a b : Fin 2 => (![![1, 0, 0], ![0, 1, 0]] : Fin 2 → Fin 3 → ℝ) b (f a)).det
        ≠ 0 := by
  refine exists_det_ne_zero_of_linearIndependent (LinearIndependent.pair_iff.2 ?_)
  intro s t hst
  refine ⟨?_, ?_⟩
  · have h0 := congrFun hst 0
    simpa using h0
  · have h1 := congrFun hst 1
    simpa using h1

/-- **The hypothesis is not decoration.** A dependent family has every maximal
minor zero, so no row selection can work. -/
public theorem det_eq_zero_of_dependent (f : Fin 2 → Fin 3) :
    (Matrix.of fun a b : Fin 2 => (![![1, 0, 0], ![2, 0, 0]] : Fin 2 → Fin 3 → ℝ) b (f a)).det
      = 0 := by
  have hkey : ∀ i : Fin 3, (![2, 0, 0] : Fin 3 → ℝ) i = 2 * (![1, 0, 0] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simp
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hkey (f 0), hkey (f 1)]
  ring

end AISafetyAtlas.Examples.Analysis.MaximalMinor
