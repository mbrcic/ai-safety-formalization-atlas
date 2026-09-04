module

public import AISafetyAtlas.SingularLearning.TauberianLog

/-!
# Worked models: the Tauberian bridge with a logarithm

`Tauberian.lean`'s own worked checks exercise the pure-power transfer. These exercise the parts
that only the logarithmic version has: the range on which the logarithm is pinned between `1`
and `log T`, the multiplicity-two scale that a pure-power comparison cannot see, and the two
degenerate multiplicities `m = 0` and `m = 1`, which name the same scale because `m - 1` is
natural-number subtraction.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-! ### The scales -/

/-- `m = 0` and `m = 1` name the same scale: `m - 1` is `ℕ`-subtraction. This is why the
transfer theorems do not carry `1 ≤ m` — it would be an unused hypothesis. -/
example (lam ε : ℝ) : volumeScale lam 0 ε = volumeScale lam 1 ε := rfl

example (lam T : ℝ) : laplaceScale lam 0 T = laplaceScale lam 1 T := rfl

/-- **The multiplicity-two scale is not a power.** At `m = 2` the scale carries one logarithm,
which is exactly the factor `Tauberian.lean`'s statements cannot see. -/
example (lam ε : ℝ) : volumeScale lam 2 ε = ε ^ lam * Real.log (1 / ε) := by
  rw [volumeScale]
  norm_num

/-- The mirror identity, at multiplicity two. -/
example (lam : ℝ) {T : ℝ} (hT : 0 < T) :
    laplaceScale lam 2 T = volumeScale lam 2 (1 / T) :=
  laplaceScale_eq_volumeScale lam 2 hT

/-! ### The step that carries the logarithm -/

/-- **The logarithm is pinned on the range the split uses.** On `(1/T, s₁]` with `s₁ < e⁻¹`,
`volumeScale` is dominated by `s ^ lam` times the constant `(log T)^{m-1}` — which is what lets
the far piece of the split be a multiple of `gammaTail`. -/
example {lam s₁ T s : ℝ} {m : ℕ} (hs₁ : s₁ < Real.exp (-1)) (hT : Real.exp 1 ≤ T)
    (hs : 1 / T < s) (hsle : s ≤ s₁) :
    volumeScale lam m s ≤ s ^ lam * Real.log T ^ (m - 1) :=
  volumeScale_le_rpow_mul_log hs₁ hT hs hsle

/-- **The scale dominates the pure power**, which is what makes the exponentially small tail
negligible without a second limit. -/
example {lam T : ℝ} {m : ℕ} (hT : Real.exp 1 ≤ T) : T ^ (-lam) ≤ laplaceScale lam m T :=
  rpow_le_laplaceScale hT

/-! ### The transfer, on the constant-zero germ

The degenerate case is not vacuous: `laplaceAverage` of the zero function is `0`, and the upper
half of the transfer returns `0 ≤ 0`. -/

example (T : ℝ) : laplaceAverage (fun _ => (0:ℝ)) T = 0 := by
  simp [laplaceAverage]

/-- A bounded monotone function is integrable against `e^{-Ts}` — the hypothesis the logarithmic
version uses in place of a global power bound. -/
example {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun s => Real.exp (-T * s) * (0:ℝ))
      (Set.Ioi 0) :=
  integrableOn_of_bounded (V := fun _ => (0:ℝ)) monotone_const (fun _ _ => le_refl 0)
    (fun _ => le_refl 0) hT

end AISafetyAtlas.Examples.SingularLearning
