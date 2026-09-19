module

public import AISafetyAtlas.SingularLearning.QuadraticSolve

/-!
# A worked model for the congruence equation

The smallest normed algebra the module applies to is `ℝ` itself, where the equation
`2X + X C X = D` at `C = 1` reads `2x + x² = d` and has the closed-form solution
`x = √(1 + d) - 1` for `d ≥ -1`.

Two things are witnessed here, and they are different things.

The first is that the equation is *solvable*, exhibited by a formula rather than by an
inverse function theorem. This is what stops `quadSolve` from being a name for an empty
promise: `eventually_quadMap_quadSolve` asserts a solution near the origin, and the
closed form shows there really is one, on an explicit interval, with no appeal to the
theorem being witnessed.

The second is that the general machinery fires at all: `exists_lipschitzOnWith_quadSolve`
is the hypothesis `hasLocalVolumeOrder_comp_of_lipschitz` consumes, and it
is instantiated below at `ℝ` to check that the instance side conditions — completeness,
the normed-algebra structure, the nonzero derivative — are actually met by something.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The closed-form solution of `2x + x² = d` on `ℝ`. -/
example {d : ℝ} (hd : -1 ≤ d) : quadMap (1 : ℝ) (Real.sqrt (1 + d) - 1) = d := by
  have h : Real.sqrt (1 + d) ^ 2 = 1 + d := Real.sq_sqrt (by linarith)
  simp only [quadMap, smul_eq_mul, mul_one]
  nlinarith [h]

/-- The rung point solves the homogeneous equation, in any normed algebra and here. -/
example (c : ℝ) : quadMap c 0 = 0 := quadMap_zero c

/-- The solution operator fixes the origin. -/
example (c : ℝ) : quadSolve c (0 : ℝ) = 0 := quadSolve_zero c

/-- The equation really is solved near the origin by the operator the module defines. -/
example (c : ℝ) : ∀ᶠ d in nhds (0 : ℝ), quadMap c (quadSolve c d) = d :=
  eventually_quadMap_quadSolve c

/-- The Lipschitz bound the volume transport consumes is available at `ℝ`. -/
example (c : ℝ) : ∃ K : NNReal, ∃ t ∈ nhds (0 : ℝ), LipschitzOnWith K (quadSolve c) t :=
  exists_lipschitzOnWith_quadSolve c

end AISafetyAtlas.Examples.SingularLearning
