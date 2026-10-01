module

public import AISafetyAtlas.Decision.Expect

/-!
# The expectation, at a concrete PMF

`expect_const` and `expect_eq_integral` had no worked instance anywhere in
the tree. Both are exercised at the same constant integrand, over `Bool`
with a point-mass law: constancy makes the Mathlib integral bridge free of
any summability argument, since `MeasureTheory.integrable_const` closes it
unconditionally.
-/

namespace AISafetyAtlas.Examples.Decision

open AISafetyAtlas.Decision

/-- **A constant integrand comes out of the expectation**, at a point mass
on `Bool`. -/
public theorem pure_expect_const :
    expect (PMF.pure true) (fun _ : Bool => (5 : ℝ)) = 5 :=
  expect_const (PMF.pure true) 5

/-- **The bridge to Mathlib's integral**, at the same witness: a constant
integrand is trivially integrable against any probability measure. -/
public theorem pure_expect_eq_integral :
    expect (PMF.pure true) (fun _ : Bool => (5 : ℝ)) =
      ∫ s, (fun _ : Bool => (5 : ℝ)) s ∂(PMF.pure true).toMeasure :=
  expect_eq_integral (PMF.pure true) (fun _ : Bool => (5 : ℝ))
    (MeasureTheory.integrable_const 5)

end AISafetyAtlas.Examples.Decision
