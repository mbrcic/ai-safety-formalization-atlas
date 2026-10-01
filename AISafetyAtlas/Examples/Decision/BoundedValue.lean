module

public import AISafetyAtlas.Decision.BoundedValue
public import AISafetyAtlas.Examples.Decision.DiscountedValue

/-!
# The bounded value layer, worked on an infinite state space

`AISafetyAtlas.Decision.BoundedValue` widens `vPi` off finite state types. A
widening is worth nothing unless something inhabits the wider setting, so this
module runs it where the narrower development **cannot be stated at all**: the
state type is `ℕ`.

`ladder` steps from `s` to `s + 1` forever, with one action. Two rewards are
valued on it, at discount `1/2`:

* `ladderOne` pays `1` at every state, and the value is the constant `2` — the
  geometric series `1 / (1 - 1/2)`, obtained by handing the constant function to
  `vPiBdd_unique`, so the uniqueness theorem does the work.
* `ladderTip` pays `1` at state `0` only, and the value is **not constant**: it
  is `1` at `0` and `0` everywhere else. Without it this module would only show
  that the bounded fixed point can be a constant function, which a development
  about constants would also show.

`loop_vPiBdd_eq_vPi` then runs the join on the finite model of
`AISafetyAtlas.Examples.Decision.DiscountedValue`, where both value functions are
defined: the bounded fixed point there is that module's `vPi`, and hence `2`.
-/

namespace AISafetyAtlas.Examples.Decision

open AISafetyAtlas.Decision

open scoped NNReal

/-! ## An infinite state space -/

/-- **The ladder**: states `ℕ`, one action, and `s ↦ s + 1` forever. No finite
state development reaches this model. -/
@[expose] public noncomputable def ladder : MDP ℕ Unit :=
  ⟨fun s _ => PMF.pure (s + 1)⟩

/-- The only policy the one-action ladder has. -/
@[expose] public def step : ℕ → Unit := fun _ => ()

/-- **A reward of `1` at every state.** -/
@[expose] public def ladderOne : ℕ → Unit → ℝ := fun _ _ => 1

/-- That reward is bounded by `1`, which is the side condition `vPiBdd` carries
in place of finiteness. -/
public theorem ladderOne_abs_le : ∀ s, |ladderOne s (step s)| ≤ 1 := by
  intro s
  simp [ladderOne]

/-- **The value of the ladder under a unit reward is the constant `2`.**

`2 = 1 / (1 - 1/2)` is the geometric series, and it is obtained here by checking
that the constant function solves the Bellman equation and is bounded, then
invoking `vPiBdd_unique`. On an infinite state type boundedness is a real
hypothesis rather than a formality, which is why it is discharged explicitly. -/
public theorem ladderOne_vPiBdd :
    vPiBdd ladder ladderOne half_lt_one step ladderOne_abs_le = fun _ => (2 : ℝ) := by
  refine (vPiBdd_unique ladder ladderOne half_lt_one step ladderOne_abs_le
    ⟨2, fun s => by norm_num⟩ (fun s => ?_)).symm
  simp [bellmanPolicyOp, qVal, ladder, ladderOne, half]
  norm_num

/-- **A reward of `1` at state `0` and nothing elsewhere.** -/
@[expose] public def ladderTip : ℕ → Unit → ℝ := fun s _ => if s = 0 then 1 else 0

/-- Bounded by `1` as well. -/
public theorem ladderTip_abs_le : ∀ s, |ladderTip s (step s)| ≤ 1 := by
  intro s
  by_cases h : s = 0 <;> simp [ladderTip, h]

/-- **The value under the tip reward is not a constant function**: `1` at the
paying state, `0` at every state the walk has already left behind.

This is the witness that the bounded fixed point is a function rather than a
number in disguise. -/
public theorem ladderTip_vPiBdd :
    vPiBdd ladder ladderTip half_lt_one step ladderTip_abs_le
      = fun s => if s = 0 then (1 : ℝ) else 0 := by
  refine (vPiBdd_unique ladder ladderTip half_lt_one step ladderTip_abs_le
    ⟨1, fun s => by by_cases h : s = 0 <;> simp [h]⟩ (fun s => ?_)).symm
  simp [bellmanPolicyOp, qVal, ladder, ladderTip, half]

/-- The two values genuinely differ, so the development is not insensitive to the
reward it is handed. -/
public theorem ladderTip_ne_ladderOne :
    vPiBdd ladder ladderTip half_lt_one step ladderTip_abs_le
      ≠ vPiBdd ladder ladderOne half_lt_one step ladderOne_abs_le := by
  rw [ladderTip_vPiBdd, ladderOne_vPiBdd]
  intro h
  have := congr_fun h 0
  norm_num at this

/-! ## The recursion, the packaged uniqueness, and the shape transfer

The three results above identify a value function in closed form. The three
below use the parts of the layer that hold when no closed form is available,
which is the case the widening is for. -/

/-- **One step of the recursion**, before any closed form: the ladder's Bellman
equation says the value at `s` is one plus half the value at `s + 1`. -/
public theorem ladderOne_vPiBdd_step (s : ℕ) :
    vPiBdd ladder ladderOne half_lt_one step ladderOne_abs_le s
      = 1 + (1 / 2) * vPiBdd ladder ladderOne half_lt_one step ladderOne_abs_le (s + 1) := by
  have h := vPiBdd_bellman ladder ladderOne half_lt_one step ladderOne_abs_le s
  simpa [ladder, ladderOne, half] using h

/-- **Existence and uniqueness, packaged.** Exactly one bounded function on `ℕ`
solves the ladder's Bellman equation. -/
public theorem ladderOne_existsUnique_bdd :
    ∃! v : ℕ → ℝ, Blackwell.UniformBounded v ∧
      ∀ s, v s = bellmanPolicyOp ladder ladderOne half step v s :=
  Blackwell.existsUnique_bdd_fixedPoint
    (bellmanPolicyOp_contractingWith_bdd ladder ladderOne half_lt_one step ladderOne_abs_le)

/-- **A reward with no closed form to hand**: `+1` at even states, `-1` at odd
ones. -/
@[expose] public def ladderAlt : ℕ → Unit → ℝ := fun s _ => if s % 2 = 0 then 1 else -1

/-- Bounded by `1`. -/
public theorem ladderAlt_abs_le : ∀ s, |ladderAlt s (step s)| ≤ 1 := by
  intro s
  by_cases h : s % 2 = 0 <;> simp [ladderAlt, h]

/-- **Boundedness without computation.** Nothing above identifies this value
function, and `vPiBdd_bounded` still bounds it — which is the whole point of
carrying boundedness as a hypothesis rather than inheriting it from finiteness. -/
public theorem ladderAlt_vPiBdd_bounded :
    Blackwell.UniformBounded (vPiBdd ladder ladderAlt half_lt_one step ladderAlt_abs_le) :=
  vPiBdd_bounded ladder ladderAlt half_lt_one step ladderAlt_abs_le

/-- And the bound feeds back through the Bellman equation to bound the value by
the reward plus half of it, still without identifying the function. -/
public theorem ladderAlt_vPiBdd_abs_le :
    ∃ B : ℝ, ∀ s,
      |vPiBdd ladder ladderAlt half_lt_one step ladderAlt_abs_le s| ≤ 1 + (1 / 2) * B := by
  obtain ⟨B, hB⟩ := ladderAlt_vPiBdd_bounded
  refine ⟨B, fun s => ?_⟩
  have hexpect : |expect (ladder.transition s (step s))
      (vPiBdd ladder ladderAlt half_lt_one step ladderAlt_abs_le)| ≤ B :=
    abs_expect_le _ hB
  rw [vPiBdd_bellman ladder ladderAlt half_lt_one step ladderAlt_abs_le s]
  refine (abs_add_le _ _).trans (add_le_add (ladderAlt_abs_le s) ?_)
  rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ ((half : ℝ≥0) : ℝ) by positivity)]
  have hhalf : ((half : ℝ≥0) : ℝ) = 1 / 2 := by simp [half]
  rw [hhalf]
  exact mul_le_mul_of_nonneg_left hexpect (by norm_num)

/-- **Shape transfer.** The nonnegative bounded functions are a nonempty closed
set that the ladder's Bellman operator preserves, so every bounded solution of
its equation is nonnegative — a property of the value function read off the
operator, with the function itself never computed. -/
public theorem ladderOne_vPiBdd_nonneg_mem :
    Blackwell.toBddFun (vPiBdd ladder ladderOne half_lt_one step ladderOne_abs_le)
        (vPiBdd_bounded ladder ladderOne half_lt_one step ladderOne_abs_le)
      ∈ {f : Blackwell.BddFun (S := ℕ) | ∀ x, 0 ≤ f x} := by
  set C : Set (Blackwell.BddFun (S := ℕ)) := {f | ∀ x, 0 ≤ f x} with hC_def
  have hC_nonempty : C.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hC_def]
    intro x
    simp
  have hC_closed : IsClosed C := by
    have hset : C = ⋂ x, {f : Blackwell.BddFun (S := ℕ) | 0 ≤ f x} := by
      rw [hC_def]; ext f; simp
    rw [hset]
    exact isClosed_iInter fun x =>
      isClosed_le continuous_const
        (BoundedContinuousFunction.lipschitz_eval_const x).continuous
  have hC_inv : Set.MapsTo
      (Blackwell.liftBddFun (bellmanPolicyOp ladder ladderOne half step)
        (bellmanPolicyOp_uniformBounded ladder ladderOne half step ladderOne_abs_le)) C C := by
    intro f hf x
    rw [Blackwell.liftBddFun_apply]
    have hnonneg : (0 : ℝ) ≤ expect (ladder.transition x (step x)) (f : Blackwell.DState → ℝ) :=
      expect_nonneg _ fun t => hf t
    simp only [bellmanPolicyOp, qVal, ladderOne]
    positivity
  exact Blackwell.isFixedPt_mem_of_isClosed
    (bellmanPolicyOp_contractingWith_bdd ladder ladderOne half_lt_one step ladderOne_abs_le)
    hC_nonempty hC_closed hC_inv _
    (fun s => vPiBdd_bellman ladder ladderOne half_lt_one step ladderOne_abs_le s)

/-! ## The join, on the finite model -/

/-- The reward of `AISafetyAtlas.Examples.Decision.loop` under the acting policy
is bounded, which the finite development never had to say. -/
public theorem loopReward_act_abs_le : ∀ s, |loopReward s (act s)| ≤ 1 := by
  intro s
  simp [loopReward, act]

/-- **The join, run.** On the one-state model both value functions are defined,
and `vPiBdd_eq_vPi` says they are the same function — so the widening is a
widening rather than a second development with similar names. -/
public theorem loop_vPiBdd_eq_vPi :
    vPiBdd loop loopReward half_lt_one act loopReward_act_abs_le
      = vPi loop loopReward half_lt_one act :=
  vPiBdd_eq_vPi loop loopReward half_lt_one act loopReward_act_abs_le

/-- And therefore the bounded fixed point of the finite model is `2`, through the
finite development's own `vPi_act`. -/
public theorem loop_vPiBdd_eq_two :
    vPiBdd loop loopReward half_lt_one act loopReward_act_abs_le = fun _ => (2 : ℝ) :=
  loop_vPiBdd_eq_vPi.trans vPi_act

end AISafetyAtlas.Examples.Decision
