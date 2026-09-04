module

public import AISafetyAtlas.SingularLearning.ZetaPair

/-!
# Worked examples: the zeta normalization

`ZetaPair.lean` states print's *primary* definition of the local pair and the
hypothesis under which the atlas's volume form may be substituted for it. Nothing
there is proved, and nothing here proves it either. What these examples do is fix
the reading, so that a later attempt to discharge `O70ZetaPoleBridge` cannot quietly
be an attempt to discharge something else.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The zeta integral at `x = 0` is the volume of the ball, whatever the germ:
`K y ^ (0 : ℝ) = 1` pointwise, by `Real.rpow_zero`, including where `K y = 0`. This
pins the convention — `^` here is `Real.rpow`, not a natural power — and it is the
one value of the zeta integral that needs no analysis. -/
example {n : ℕ} (K : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n))
    (δ : ℝ) :
    zetaIntegral K w δ 0 = (MeasureTheory.volume (Metric.ball w δ)).toReal := by
  simp [zetaIntegral, MeasureTheory.integral_const, MeasureTheory.measureReal_def]

/-- **The degenerate germ is why the bridge carries a nondegeneracy hypothesis.**
For `K ≡ 0` the zeta integral vanishes at every `x > 0`, so no continuation of it
has a pole anywhere — while `HasExactLocalPair` hands that germ the neutral pair
`(0, 1)`. Dropping the hypothesis would therefore not weaken `O70ZetaPoleBridge`;
it would make it false. -/
example {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    zetaIntegral (fun _ => (0 : ℝ)) w δ x = 0 := by
  simp [zetaIntegral, Real.zero_rpow hx.ne']

/-- The neutral branch really does apply to that germ, so the two halves of the
previous example are about the same `(lam, m)`. -/
example {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    HasExactLocalPair (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)) w 0 1 :=
  Or.inl ⟨Filter.Eventually.of_forall fun _ => rfl, rfl, rfl⟩

/-- `HasZetaPoleOrder` asks for a pole, and Mathlib's order is negative there:
a pole of order `m` is `meromorphicOrderAt = -m`, not `m`. Spelled out at `m = 2`
so a sign slip in the definition would show up here. -/
example : ((-((2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) := by
  norm_num

/-- **Where the counterexample lives.** A germ with exact local pair `(lam, 1)` whose
sublevel volume carries a `1 / log (1 / ε)` correction still satisfies
`HasExactLocalPair` — the defining ratio tends to `1` regardless — which is why no
general passage from the volume form to the pole form can hold. This records the
`ε → 0` half of that: the correction is invisible to the limit.

Nothing here relates the two predicates. That passage is the frontier
`O70ZetaPoleBridge`, stated at the O70 germs in `Conjectures/MAIS/O70.lean`. -/
example :
    Filter.Tendsto (fun ε : ℝ => 1 + 1 / Real.log (1 / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h : Filter.Tendsto (fun ε : ℝ => Real.log (1 / ε))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simp only [one_div, Real.log_inv]
    exact Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h0 : Filter.Tendsto (fun ε : ℝ => 1 / Real.log (1 / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact Filter.Tendsto.congr (fun x => by simp [one_div]) h.inv_tendsto_atTop
  simpa using h0.const_add 1

end AISafetyAtlas.Examples.SingularLearning
