module

public import AISafetyAtlas.SingularLearning.LossAnalytic

/-!
# Worked examples: the reduced-rank loss is real-analytic

`MAIS-A6.tex` `def:local` takes the local pair of a nonnegative **real-analytic**
`K`. `rrrLoss_nonneg` gives the first adjective; `LossAnalytic.lean` gives the
second. Together they say the O70 germs lie in the class print's definition is
about — which is the class the general form of the zeta bridge dropped, and why
that general form was false.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The germ at a factorization — the point the local pair is taken at — is analytic. -/
example (M N H : ℕ) (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    AnalyticAt ℝ (fun y => rrrLoss C ((matrixPairEquiv M N H).symm y).1
      ((matrixPairEquiv M N H).symm y).2) (matrixPairCoords A B) :=
  analyticAt_rrrLoss_symm_coords C _

/-- The toolkit form: any analytic family of parameters gives an analytic loss. Here
the ray `s ↦ K(sA, sB)`, a quartic in `s`. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => rrrLoss C (s • A) (s • B)) t :=
  analyticAt_rrrLoss_of_entries C (fun _ _ => analyticAt_id.mul analyticAt_const)
    (fun _ _ => analyticAt_id.mul analyticAt_const)

/-- What the continuity corollary is for: every sublevel set of the germ is
measurable, so the ball volumes `HasExactLocalPair` speaks about exist. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) (e : ℝ) :
    MeasurableSet {y : EuclideanSpace ℝ (Fin (H * N + M * H)) |
      rrrLoss C ((matrixPairEquiv M N H).symm y).1 ((matrixPairEquiv M N H).symm y).2 ≤ e} :=
  measurableSet_le (continuous_rrrLoss_symm_coords C).measurable measurable_const

end AISafetyAtlas.Examples.SingularLearning
