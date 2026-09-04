module

public import AISafetyAtlas.SingularLearning.ZetaPair
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The quadratic germ has a zeta pair, and it is the volume pair

`ZetaPair.lean` states print's primary definition of the local pair,
`HasZetaPoleOrder`, and records that no general passage from the ball-volume form
to it can hold. That leaves a question the atlas must not dodge: is
`HasZetaPoleOrder` inhabited at all, by a germ whose volume pair is also known?

It is, and this module proves it for the smallest singular germ, `K(x) = x₀²` on
the line. `Examples/SingularLearning/LocalPair.lean` already proves
`hasExactLocalPair_sq`, that its ball-volume pair is `(1/2, 1)`. Here the zeta
function of the same germ is computed exactly and its pole order read off, with no
hypothesis of any kind:

    ζ(z) = ∫_{|t| < 1} |t|^{2z} dt = 2 / (2z + 1) ,

entire except for a simple pole at `z = -1/2`. Threshold `1/2`, pole order `1` —
the same pair.

**What this is evidence for, and what it is not.** `O70ZetaPoleBridge` asserts that
the two definitions agree at every O70 germ. This module does not prove that and is
not a special case of it: `x₀²` is not a reduced-rank loss. What it does is close
the vacuity question. Before it, nothing in the atlas exhibited a single germ
satisfying `HasZetaPoleOrder`, so a reader had no way to tell whether the
frontier's conclusion was reachable at all — and the general form of the bridge is
false precisely because its conclusion fails on germs its hypothesis admits. A frontier whose conclusion is never witnessed is indistinguishable from
one that cannot be satisfied.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory intervalIntegral

/-- The germ `K(x) = x₀²` on `EuclideanSpace ℝ (Fin 1)`, the same one
`hasExactLocalPair_sq` computes the ball-volume pair of. -/
@[expose] public def sqGerm : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => x 0 ^ 2

/-- Collapsing `EuclideanSpace ℝ (Fin 1)` to `ℝ` preserves Lebesgue measure. The
same composite `hasExactLocalPair_sq` uses for the volume side. -/
public theorem measurePreserving_coord :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 1) => x 0) volume volume :=
  (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).comp
    (PiLp.volume_preserving_ofLp (ι := Fin 1))

public theorem norm_eq_abs_coord (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

/-- The unit ball of `EuclideanSpace ℝ (Fin 1)` is the preimage of `(-1, 1)`. -/
public theorem ball_eq_preimage_Ioo :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1
      = (fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹' Set.Ioo (-1) 1 := by
  ext x
  simp only [Metric.mem_ball, dist_zero_right, norm_eq_abs_coord, Set.mem_preimage,
    Set.mem_Ioo, abs_lt]

/-- The coordinate collapse is a measurable embedding: it is `ofLp` followed by the
collapse of a one-element product, both measurable equivalences. -/
public theorem measurableEmbedding_coord :
    MeasurableEmbedding (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by
  have h : (fun x : EuclideanSpace ℝ (Fin 1) => x 0)
      = ⇑(((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm).trans
          (MeasurableEquiv.funUnique (Fin 1) ℝ)) := rfl
  rw [h]
  exact MeasurableEquiv.measurableEmbedding _

/-! ## The zeta function of `x₀²`, computed

`(t²)^x = |t|^{2x}` pointwise, the integrand is even, and on `(0, 1)` the exponent
`2x` exceeds `-1` exactly when `x > -1/2`, which is where the integral converges.
`integral_rpow` gives `1/(2x+1)` for the half, and reflection doubles it.
-/

public theorem rpow_sq_eq_abs_rpow (t : ℝ) (x : ℝ) : (t ^ 2) ^ x = |t| ^ (2 * x) := by
  rw [← sq_abs t, ← Real.rpow_natCast |t| 2, ← Real.rpow_mul (abs_nonneg t)]
  norm_num

/-- On `[0, 1]` the absolute value is invisible, so `intervalIntegrable_rpow'` applies. -/
public theorem intervalIntegrable_abs_rpow_zero_one {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun t : ℝ => |t| ^ r) volume 0 1 := by
  refine (intervalIntegrable_rpow' hr).congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  rw [abs_of_pos ht.1]

/-- The negative half by reflection, which fixes `|t|`. -/
public theorem intervalIntegrable_abs_rpow_neg_zero {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun t : ℝ => |t| ^ r) volume (-1) 0 := by
  rw [IntervalIntegrable.iff_comp_neg]
  simpa only [abs_neg, neg_neg, neg_zero] using (intervalIntegrable_abs_rpow_zero_one hr).symm

public theorem intervalIntegral_abs_rpow_zero_one {r : ℝ} (hr : -1 < r) :
    (∫ t in (0 : ℝ)..1, |t| ^ r) = 1 / (r + 1) := by
  have hcongr : (∫ t in (0 : ℝ)..1, |t| ^ r) = ∫ t in (0 : ℝ)..1, t ^ r := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [abs_of_nonneg ht.1]
  have hne : r + 1 ≠ 0 := by linarith
  rw [hcongr, integral_rpow (Or.inl hr), Real.zero_rpow hne, Real.one_rpow]
  ring

/-- **The zeta function of `x₀²` on the unit ball.** Exactly `2/(2x+1)` wherever the
integral converges, which is `x > -1/2`. -/
public theorem zetaIntegral_sqGerm {x : ℝ} (hx : -(1/2) < x) :
    zetaIntegral sqGerm 0 1 x = 2 / (2 * x + 1) := by
  have hr : (-1 : ℝ) < 2 * x := by linarith
  have htrans : zetaIntegral sqGerm 0 1 x = ∫ t in Set.Ioo (-1 : ℝ) 1, |t| ^ (2 * x) := by
    rw [zetaIntegral, ball_eq_preimage_Ioo]
    have h := measurePreserving_coord.setIntegral_preimage_emb measurableEmbedding_coord
      (fun t : ℝ => |t| ^ (2 * x)) (Set.Ioo (-1 : ℝ) 1)
    simp only [sqGerm]
    simpa only [rpow_sq_eq_abs_rpow] using h
  have hIoc : (∫ t in Set.Ioo (-1 : ℝ) 1, |t| ^ (2 * x))
      = ∫ t in (-1 : ℝ)..1, |t| ^ (2 * x) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc
  have hsplit : (∫ t in (-1 : ℝ)..1, |t| ^ (2 * x))
      = (∫ t in (-1 : ℝ)..0, |t| ^ (2 * x)) + ∫ t in (0 : ℝ)..1, |t| ^ (2 * x) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_abs_rpow_neg_zero hr) (intervalIntegrable_abs_rpow_zero_one hr)).symm
  have hrefl : (∫ t in (-1 : ℝ)..0, |t| ^ (2 * x)) = ∫ t in (0 : ℝ)..1, |t| ^ (2 * x) := by
    have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 0)
      (f := fun t : ℝ => |t| ^ (2 * x))
    simpa only [abs_neg, neg_zero, neg_neg] using h
  have hne : 2 * x + 1 ≠ 0 := by linarith
  rw [htrans, hIoc, hsplit, hrefl, intervalIntegral_abs_rpow_zero_one hr]
  field_simp
  ring

/-! ## The pole, and the pair

`2/(2z+1)` is `(z + 1/2)⁻¹`, so it is analytic everywhere to the right of `-1/2`,
meromorphic at `-1/2`, and its order there is `-1` — a simple pole. Threshold `1/2`,
pole order `1`.
-/

/-- The continuation of the zeta function of `x₀²`: entire except a simple pole. -/
@[expose] public noncomputable def zetaSq : ℂ → ℂ := fun z => 2 / (2 * z + 1)

public theorem zetaSq_ne_zero_denom {z : ℂ} (hz : -(1/2 : ℝ) < z.re) : 2 * z + 1 ≠ 0 := by
  intro h
  have hz' : z = -(1/2 : ℂ) := by linear_combination h / 2
  rw [hz'] at hz
  norm_num at hz

public theorem analyticAt_zetaSq {z : ℂ} (hz : -(1/2 : ℝ) < z.re) : AnalyticAt ℂ zetaSq z := by
  refine analyticAt_const.div ?_ (zetaSq_ne_zero_denom hz)
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

public theorem zetaSq_eq_inv (z : ℂ) : zetaSq z = (z + 1/2)⁻¹ := by
  rcases eq_or_ne (z + 1/2) 0 with h | h
  · have h2 : 2 * z + 1 = 0 := by linear_combination 2 * h
    rw [zetaSq, h2, h]
    simp
  · rw [zetaSq]
    field_simp

public theorem meromorphicAt_zetaSq : MeromorphicAt zetaSq (-((1/2 : ℝ) : ℂ)) := by
  have hz : MeromorphicAt (fun z : ℂ => (z + 1/2)⁻¹) (-((1/2 : ℝ) : ℂ)) :=
    (AnalyticAt.add analyticAt_id analyticAt_const).meromorphicAt.inv
  exact hz.congr (Filter.Eventually.of_forall fun z => (zetaSq_eq_inv z).symm)

public theorem meromorphicOrderAt_zetaSq :
    meromorphicOrderAt zetaSq (-((1/2 : ℝ) : ℂ)) = ((-1 : ℤ) : WithTop ℤ) := by
  refine (meromorphicOrderAt_eq_int_iff meromorphicAt_zetaSq).2 ⟨fun _ => 1, analyticAt_const,
    one_ne_zero, ?_⟩
  filter_upwards with z
  rw [zetaSq_eq_inv, smul_eq_mul, mul_one, zpow_neg, zpow_one, sub_neg_eq_add]
  push_cast
  ring_nf

/-- **The quadratic germ has zeta pair `(1/2, 1)`**, with no hypothesis. Its
ball-volume pair is `(1/2, 1)` too, by `hasExactLocalPair_sq`, so this is a germ at
which print's two normalizations demonstrably agree. -/
public theorem hasZetaPoleOrder_sqGerm : HasZetaPoleOrder sqGerm 0 (1/2) 1 := by
  refine ⟨1, zero_lt_one, zetaSq, ?_, ?_, meromorphicAt_zetaSq, ?_⟩
  · intro x hx
    rw [zetaIntegral_sqGerm hx, zetaSq]
    push_cast
    ring
  · intro z hz
    exact analyticAt_zetaSq hz
  · simpa using meromorphicOrderAt_zetaSq

end AISafetyAtlas.SingularLearning
