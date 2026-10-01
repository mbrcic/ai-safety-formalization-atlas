module

public import AISafetyAtlas.Decision.DiscountedValue

/-!
# The discounted value layer, worked

`AISafetyAtlas.Decision.DiscountedValue` states the Bellman equation and its
uniqueness as theorems about a fixed point that is never computed. This module
computes it in the smallest model where the answer is known in closed form, so
that the uniqueness theorem is used rather than merely stated.

`loop` is one state and two actions, both of which return to that state. The
reward is `1` for `act` and `0` for `idle`, and the discount is `1/2`. Then:

* `vPi_idle` is `0`: the do-nothing policy earns nothing forever.
* `vPi_act` is `2 = 1 / (1 - 1/2)`: the geometric series, obtained by handing the
  constant function `2` to `vPi_unique` — so the theorem does the work, and the
  fixed point is identified rather than approximated.
* `vStar_loop` is also `2`, and `qVal_lt_qVal` records that the optimality
  operator's maximum over actions is not degenerate here: the two actions have
  different values, so `bellmanOptOp` really chooses.

The point of the last one is that a `sup'` over a one-action alphabet would prove
nothing about the maximum.
-/

namespace AISafetyAtlas.Examples.Decision

open AISafetyAtlas.Decision

open scoped NNReal

/-- **One state, two actions, both self-looping.** The dynamics carry no reward;
the reward is supplied separately, as `loopReward`. -/
@[expose] public noncomputable def loop : MDP Unit Bool :=
  ⟨fun _ _ => PMF.pure ()⟩

/-- The reward: `1` for the action `true`, nothing for `false`. -/
@[expose] public def loopReward : Unit → Bool → ℝ := fun _ a => if a then 1 else 0

/-- The discount, `1/2`. -/
@[expose] public noncomputable def half : ℝ≥0 := 1 / 2

/-- The discount is a legitimate contraction modulus. -/
public theorem half_lt_one : half < 1 := by
  unfold half
  norm_num

/-- The policy that always acts. -/
@[expose] public def act : Unit → Bool := fun _ => true

/-- The policy that never acts. -/
@[expose] public def idle : Unit → Bool := fun _ => false

/-- **Every expectation in this model is evaluation at the one state.**

Since 2026-09-10 the two `simp` proofs below no longer need to be handed this
lemma: `AISafetyAtlas.Decision.expect_pure` became `@[simp]` when the atlas's
four copies of the expectation were merged into one, and it discharges the
transition here directly. The lemma is kept because it is the statement worth
making about this model, and the two `norm_num` proofs still use it. -/
public theorem expect_loop (v : Unit → ℝ) (s : Unit) (a : Bool) :
    expect (loop.transition s a) v = v () := by
  simp [expect, loop]

/-- **The do-nothing policy is worth nothing.** The constant zero function solves
the Bellman equation, so by `vPi_unique` it *is* the value. -/
public theorem vPi_idle : vPi loop loopReward half_lt_one idle = fun _ => 0 := by
  refine (vPi_unique loop loopReward half_lt_one idle (v := fun _ => 0) ?_).symm
  funext s
  simp [bellmanPolicyOp, qVal, loopReward, idle]

/-- **The acting policy is worth `2`**, which is `1 / (1 - 1/2)`.

The proof is `vPi_unique` applied to the constant function `2`: the closed form
is *checked against the Bellman equation*, and uniqueness turns that check into
an identification of the fixed point. -/
public theorem vPi_act : vPi loop loopReward half_lt_one act = fun _ => 2 := by
  refine (vPi_unique loop loopReward half_lt_one act (v := fun _ => 2) ?_).symm
  funext s
  simp [bellmanPolicyOp, qVal, loopReward, act, half]
  norm_num

/-- The acting branch is worth `2` at the constant value function `2`. -/
public theorem qVal_true (s : Unit) :
    qVal loop loopReward half (fun _ => 2) s true = 2 := by
  norm_num [qVal, expect_loop, loopReward, half]

/-- The idling branch is worth `1` there. -/
public theorem qVal_false (s : Unit) :
    qVal loop loopReward half (fun _ => 2) s false = 1 := by
  norm_num [qVal, expect_loop, loopReward, half]

/-- **The two actions really differ at the optimal value.** `act` is worth `2`
where `idle` is worth `1`, so the maximum in `bellmanOptOp` is a choice and not a
formality; a `sup'` over a one-action alphabet would prove nothing about the
maximum. -/
public theorem qVal_lt_qVal :
    qVal loop loopReward half (fun _ => 2) () false
      < qVal loop loopReward half (fun _ => 2) () true := by
  rw [qVal_true, qVal_false]
  norm_num

/-- **The optimal value is `2`.** The constant function `2` solves the Bellman
optimality equation — the maximum over the two actions is attained at `act` — so
`vStar_unique` identifies it. -/
public theorem vStar_loop : vStar loop loopReward half_lt_one = fun _ => 2 := by
  refine (vStar_unique loop loopReward half_lt_one (v := fun _ => 2) ?_).symm
  funext s
  have hle : (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
      (fun a => qVal loop loopReward half (fun _ => 2) s a) ≤ 2 := by
    refine Finset.sup'_le _ _ fun a _ => ?_
    cases a
    · rw [qVal_false]; norm_num
    · rw [qVal_true]
  have hge : (2 : ℝ) ≤ (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
      (fun a => qVal loop loopReward half (fun _ => 2) s a) := by
    have h := Finset.le_sup'
      (fun a => qVal loop loopReward half (fun _ => 2) s a) (Finset.mem_univ true)
    rw [qVal_true] at h
    exact h
  have : (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
      (fun a => qVal loop loopReward half (fun _ => 2) s a) = 2 :=
    le_antisymm hle hge
  simpa [bellmanOptOp] using this

/-! ## The Bellman equations and value iteration, at this model

Both value functions are now known in closed form, so the general statements
below are about limits and fixed points this file has already identified rather
than about unevaluated ones.
-/

/-- **The policy Bellman equation** at the acting policy. -/
public theorem loop_vPi_bellman (s : Unit) :
    vPi loop loopReward half_lt_one act s
      = loopReward s (act s)
        + (half : ℝ) * expect (loop.transition s (act s))
            (vPi loop loopReward half_lt_one act) :=
  vPi_bellman loop loopReward half_lt_one act s

/-- **The Bellman optimality equation**, whose maximum over actions is not
degenerate here -- `qVal_lt_qVal` is the record that the two actions differ. -/
public theorem loop_vStar_bellman (s : Unit) :
    vStar loop loopReward half_lt_one s
      = (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
          (fun a => loopReward s a + (half : ℝ)
            * expect (loop.transition s a) (vStar loop loopReward half_lt_one)) :=
  vStar_bellman loop loopReward half_lt_one s

/-- The optimal value as the maximum of the optimal state-action values. -/
public theorem loop_vStar_eq_sup_qStar (s : Unit) :
    vStar loop loopReward half_lt_one s
      = (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
          (fun a => qStar loop loopReward half_lt_one s a) :=
  vStar_eq_sup_qStar loop loopReward half_lt_one s

/-- **Value iteration for a fixed policy converges to `2`**, from any starting
value function -- the limit is the one `vPi_act` identified, not an abstract
fixed point. -/
public theorem loop_tendsto_iterate_vPi (v : Unit -> Real) :
    Filter.Tendsto (fun n => (bellmanPolicyOp loop loopReward half act)^[n] v)
      Filter.atTop (nhds (fun _ => 2)) := by
  simpa [vPi_act] using tendsto_iterate_vPi loop loopReward half_lt_one act v

/-- **And optimal value iteration converges to `2` as well.** -/
public theorem loop_tendsto_iterate_vStar (v : Unit -> Real) :
    Filter.Tendsto (fun n => (bellmanOptOp loop loopReward half)^[n] v)
      Filter.atTop (nhds (fun _ => 2)) := by
  simpa [vStar_loop] using tendsto_iterate_vStar loop loopReward half_lt_one v

/-- **The a-priori geometric rate**, at discount `1/2`. -/
public theorem loop_dist_iterate_vStar_le (v : Unit -> Real) (n : Nat) :
    dist ((bellmanOptOp loop loopReward half)^[n] v)
        (vStar loop loopReward half_lt_one)
      ≤ dist v (bellmanOptOp loop loopReward half v)
          * (half : ℝ) ^ n / (1 - (half : ℝ)) :=
  dist_iterate_vStar_le loop loopReward half_lt_one v n

end AISafetyAtlas.Examples.Decision
