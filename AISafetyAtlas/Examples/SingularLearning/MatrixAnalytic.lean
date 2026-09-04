module

public import AISafetyAtlas.SingularLearning.MatrixAnalytic

/-!
# Worked models for analyticity of matrix inversion

This module exists to unblock one step. Theorem 5.1's chart `Ψ` is polynomial in
the entries except for two denominators, `det A₁₁` and `det P_{top}`, so the whole
"analytic diffeomorphism" clause reduces to analyticity of matrix inversion on
the nonsingular locus.

## The Mathlib gap

Mathlib has analyticity of `Ring.inverse` on the units of a normed algebra
(`analyticOnNhd_inverse`), the scalar `analyticAt_inv`, and `contDiffAt_ringInverse`.
For **matrices** it has `Continuous.matrix_det`, `Continuous.matrix_adjugate`
and `continuousAt_matrix_inv` — and the chain stops there. There is no
differentiability or analyticity statement about `Matrix.det`, `Matrix.adjugate`
or `Matrix.inv` as maps of the entries.

The Banach-algebra route is additionally blocked: `NormedAddCommGroup (Matrix …)`
does not synthesise at all — there is no global normed instance on `Matrix` — so
the statement does not even typecheck without a scoped instance, and
`Matrix.frobeniusNormedRing` is a different structure from the
`frobeniusNormedAddCommGroup` this layer installs.

So the proof goes by Cramer instead: `A⁻¹ = (det A)⁻¹ • adjugate A`, where `det`
and `adjugate` are polynomial in the entries and the scalar inverse is analytic
away from zero. No operator-norm machinery is needed.

## A naming caveat worth knowing

Dot notation does not work for these. A lemma named AnalyticAt.matrix_det
declared in this namespace is not reached by writing hf.matrix_det: Lean unfolds
`AnalyticAt` to `Exists` and looks for a field of `Exists` instead, which nothing
declares. Hence the composition-suffixed names throughout —
`analyticAt_det_comp hf` rather than dot notation.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open scoped Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **Matrix inversion is analytic on the nonsingular locus**, at a general
index type. -/
example {n : Type*} [Fintype n] [DecidableEq n] :
    AnalyticOnNhd ℝ (fun A : Matrix n n ℝ => A⁻¹) {A : Matrix n n ℝ | A.det ≠ 0} :=
  analyticOnNhd_inv

/-- The determinant is analytic — the ingredient Mathlib stops short of, having
only `Continuous.matrix_det`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    AnalyticAt ℝ (fun B : Matrix n n ℝ => B.det) A :=
  analyticAt_det A

end AISafetyAtlas.Examples.SingularLearning
