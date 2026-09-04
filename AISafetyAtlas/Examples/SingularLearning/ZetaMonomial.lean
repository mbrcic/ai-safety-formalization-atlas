module

public import AISafetyAtlas.SingularLearning.ZetaMonomial
public import AISafetyAtlas.Examples.SingularLearning.LocalPair

/-!
# Worked examples: the two normalizations agree at `x₀²`

`ZetaPair.lean` states print's zeta definition of the local pair and records that no
general passage to it from the ball-volume definition can hold. `ZetaMonomial.lean`
computes the zeta side for the smallest singular germ. `LocalPair.lean`'s
`hasExactLocalPair_sq` already computed the volume side for the same germ. Putting
them together is the point of this file.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **The calibration.** One germ, two definitions, the same pair `(1/2, 1)`, and
neither side assumes anything.

This does not prove `O70ZetaPoleBridge`, and is not an instance of it — `x₀²` is not
a reduced-rank loss. What it settles is the question the bridge would otherwise leave
open: whether print's zeta definition is satisfiable at all, and whether it agrees
with the ball-volume definition anywhere the atlas can check. A frontier whose
conclusion is never witnessed is indistinguishable from one that cannot be
satisfied — and the general form of the bridge fails exactly by asserting
a conclusion its hypothesis could not reach. -/
example :
    HasExactLocalPair (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 (1/2) 1
      ∧ HasZetaPoleOrder (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 (1/2) 1 :=
  ⟨hasExactLocalPair_sq, hasZetaPoleOrder_sqGerm⟩

/-- The zeta integral at `x = 0` is the length of the interval, as it must be:
`K^0 = 1` pointwise and the ball is `(-1, 1)`. -/
example : zetaIntegral sqGerm 0 1 0 = 2 := by
  rw [zetaIntegral_sqGerm (by norm_num)]
  norm_num

/-- The pole is where print says the threshold is. At `x = -1/2` the formula
`2/(2x+1)` has a vanishing denominator, and to the right of it the integral is
finite — this is the boundary of convergence, not an artefact of the continuation. -/
example {x : ℝ} (hx : -(1/2) < x) : 0 < zetaIntegral sqGerm 0 1 x := by
  rw [zetaIntegral_sqGerm hx]
  have : (0 : ℝ) < 2 * x + 1 := by linarith
  positivity

/-- The multiplicity is `1` and not `2`: the pole is simple, so `meromorphicOrderAt`
is `-1`. A germ with a double pole would be `-2`, and the sign convention is Mathlib's
— order is negative at a pole. -/
example : meromorphicOrderAt zetaSq (-((1/2 : ℝ) : ℂ)) = ((-1 : ℤ) : WithTop ℤ) :=
  meromorphicOrderAt_zetaSq

/-- The continuation really is the zeta integral where the integral converges. This
is the clause that makes `HasZetaPoleOrder` a statement about the germ rather than
about an arbitrary meromorphic function. -/
example {x : ℝ} (hx : -(1/2) < x) : zetaSq (x : ℂ) = (zetaIntegral sqGerm 0 1 x : ℂ) := by
  rw [zetaIntegral_sqGerm hx, zetaSq]
  push_cast
  ring

end AISafetyAtlas.Examples.SingularLearning
