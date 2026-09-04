module

public import AISafetyAtlas.SingularLearning.LayerCake

/-!
# Worked models: the layer cake

The identification `∫_B e^{-T K} = laplaceAverage (sublevelVolume K w δ) T` is the one thing
`Tauberian.lean` assumed and did not prove. These check the pieces of the substitution that
carries it, and the identity itself on the germ where both sides can be read off.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory

/-! ### The substitution -/

/-- `ε ↦ e^{-Tε}` is a bijection of `(0, ∞)` onto `(0, 1)`: the range of the substitution is
exactly the range `(0, 1]` that Mathlib's layer cake produces, up to the endpoint. -/
example : (fun ε : ℝ => Real.exp (-1 * ε)) '' Set.Ioi 0 = Set.Ioo 0 1 :=
  image_exp_neg_mul_Ioi one_pos

example : Set.InjOn (fun ε : ℝ => Real.exp (-2 * ε)) (Set.Ioi 0) :=
  injOn_exp_neg_mul (by norm_num)

/-- The superlevel set of `e^{-TK}` at `t = e^{-Tε}` is the sublevel set of `K` at `ε`. This is
the step that turns Mathlib's tail-probability formula into a statement about the object
`HasLocalVolumeOrder` speaks of. -/
example {n : ℕ} (K : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) :
    {x | Real.exp (-1 * ε) ≤ Real.exp (-1 * K x)} = {x | K x ≤ ε} :=
  superlevel_exp_eq_sublevel one_pos

/-! ### The identity -/

/-- **The zero germ.** Both sides are the volume of the ball: the sublevel set is everything, so
`sublevelVolume` is constant, and `T ∫₀^∞ e^{-Ts} ds = 1`. The identity is not vacuous — it is
checked against a germ whose two sides can be computed independently. -/
example {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (δ : ℝ) {T : ℝ} (hT : 0 < T) :
    ∫ _x in Metric.ball w δ, Real.exp (-T * (0:ℝ))
      = laplaceAverage (sublevelVolume (fun _ => (0:ℝ)) w δ) T :=
  integral_exp_neg_mul_eq_laplaceAverage (fun _ => (0:ℝ)) w δ hT (fun _ => le_refl 0)
    measurable_const

/-- **A nonconstant germ**: the squared distance to the centre, which is what the quadratic
block of the elimination chart contributes. Nonnegative and continuous, so the hypotheses are
met. -/
example {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (δ : ℝ) {T : ℝ} (hT : 0 < T) :
    ∫ x in Metric.ball w δ, Real.exp (-T * ‖x - w‖ ^ 2)
      = laplaceAverage (sublevelVolume (fun x => ‖x - w‖ ^ 2) w δ) T :=
  integral_exp_neg_mul_eq_laplaceAverage (fun x => ‖x - w‖ ^ 2) w δ hT
    (fun _ => by positivity)
    ((measurable_id.sub measurable_const).norm.pow_const 2)

end AISafetyAtlas.Examples.SingularLearning
