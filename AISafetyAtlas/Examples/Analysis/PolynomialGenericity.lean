module

public import AISafetyAtlas.Analysis.PolynomialGenericity
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Worked models for `AISafetyAtlas.Analysis.PolynomialGenericity`

Three things a reader should be able to check about the genericity lemma: that
something satisfies it, that the `p ≠ 0` hypothesis is what carries it, and that
it reaches the statement genericity arguments actually want.

| declaration | says |
|---|---|
| `ae_det_ne_zero` | almost every real square matrix is nonsingular |
| `ae_isUnit_det` | the same in `IsUnit` form |
| `ae_eval_ne_zero_two` | a concrete two-variable instance |
| `not_ae_eval_ne_zero_zero` | the hypothesis `p ≠ 0` is load-bearing |

`ae_det_ne_zero` is the archetypal use, and it is the reason
`ae_eval_ne_zero_fintype` is stated at an arbitrary finite variable type: the
determinant's indeterminates are indexed by `Fin m × Fin m`, not by `Fin n`.
-/

namespace AISafetyAtlas.Examples.Analysis

open MeasureTheory MvPolynomial AISafetyAtlas.Analysis

/-- **Almost every real square matrix is nonsingular.** The determinant is a
nonzero polynomial in the entries, so the singular matrices are a null set. -/
public theorem ae_det_ne_zero {m : ℕ} :
    ∀ᵐ s : Fin m × Fin m → ℝ, (Matrix.of fun i j => s (i, j)).det ≠ 0 := by
  have hp : (Matrix.mvPolynomialX (Fin m) (Fin m) ℝ).det ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin m) ℝ
  filter_upwards [ae_eval_ne_zero_fintype hp] with s hs
  rwa [Matrix.eval_det_mvPolynomialX] at hs

/-- The same, in the form a linear-algebra consumer asks for. -/
public theorem ae_isUnit_det {m : ℕ} :
    ∀ᵐ s : Fin m × Fin m → ℝ, IsUnit (Matrix.of fun i j => s (i, j)).det := by
  filter_upwards [ae_det_ne_zero (m := m)] with s hs
  exact isUnit_iff_ne_zero.2 hs

/-- A concrete instance: `x₀x₁ - 1` is nonzero almost everywhere on the plane.
Nonzeroness of the polynomial is itself witnessed by a point, which is the
cheapest way to discharge it. -/
public theorem ae_eval_ne_zero_two :
    ∀ᵐ x : Fin 2 → ℝ,
      MvPolynomial.eval x (X 0 * X 1 - 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
  refine ae_eval_ne_zero ?_
  intro h
  have := congrArg (MvPolynomial.eval (fun _ => (0 : ℝ))) h
  simp at this

/-- **`p ≠ 0` is load-bearing.** At the zero polynomial every point is a root, so
the conclusion fails outright — the lemma is not true for want of a hypothesis
nothing satisfies. -/
public theorem not_ae_eval_ne_zero_zero {n : ℕ} :
    ¬ ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x (0 : MvPolynomial (Fin n) ℝ) ≠ 0 := by
  intro h
  have huniv :
      {x : Fin n → ℝ | ¬ (MvPolynomial.eval x (0 : MvPolynomial (Fin n) ℝ) ≠ 0)} = Set.univ := by
    simp
  rw [MeasureTheory.ae_iff, huniv] at h
  have hbox :
      (volume : Measure (Fin n → ℝ)) (Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1) = 1 := by
    rw [MeasureTheory.volume_pi_pi]
    simp
  rw [measure_mono_null (Set.subset_univ _) h] at hbox
  exact zero_ne_one hbox

end AISafetyAtlas.Examples.Analysis
