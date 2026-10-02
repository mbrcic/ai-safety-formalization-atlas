module

public import AISafetyAtlas.Preference.Knowability

/-!
# Worked witnesses for reward unidentifiability

`AISafetyAtlas.Preference.not_knowable_reward` quantifies over all planner/reward
pairs, and a `¬ Knowable` statement is exactly the kind that can be true because
nothing inhabits its setting. These are the concrete objects.

- `payOne` and `payMinusOne` are two pairs over `Bool` states and `Bool` actions
  that induce the **same** policy and carry **different** rewards, which is the
  collision the theorem runs on, exhibited rather than asserted.
- `not_knowable_reward_bool` is the theorem at that instance.
- `knowable_reward_empty_state` is the other side of the scope boundary: with no
  states the reward is recoverable, so the `[Nonempty S]` hypothesis is doing
  work rather than being carried for safety.
-/

namespace AISafetyAtlas.Examples.Preference

open AISafetyAtlas.Knowledge AISafetyAtlas.Preference

/-- A planner that ignores the reward and always plays `true`. -/
def constPlanner : Planner (RewardFn Bool Bool) (Policy Bool Bool) :=
  fun _ => fun _ => true

/-- The pair that pays `1` everywhere. -/
def payOne : Pair Bool Bool := (constPlanner, fun _ _ => 1)

/-- Its anti-rational twin, paying `-1` everywhere. -/
def payMinusOne : Pair Bool Bool := op4 payOne

/-- The two pairs induce the **same** policy: the observation cannot separate them. -/
theorem op3_payMinusOne : op3 payMinusOne = op3 payOne :=
  op3_op4 payOne

/-- Their rewards **differ**, at a state and action exhibited by name. -/
theorem reward_differs : payMinusOne.2 false false ≠ payOne.2 false false := by
  show -(1 : ℝ) ≠ 1
  norm_num

/-- The collision is therefore real, and not an artefact of an empty setting. -/
theorem not_knowable_reward_bool :
    ¬ Knowable (op3 (S := Bool) (A := Bool))
      (Prod.snd : Pair Bool Bool → RewardFn Bool Bool) :=
  not_knowable_reward

/-- The scope boundary, instantiated: with no states, recovery succeeds. -/
theorem knowable_reward_empty_state :
    Knowable (op3 (S := Empty) (A := Bool))
      (Prod.snd : Pair Empty Bool → RewardFn Empty Bool) :=
  knowable_reward_of_isEmpty_state

/-!
## Theorem 1, policy form, at a concrete policy and reward

`policy_reward_unidentifiable` and `policy_neg_twin` restate the kernel's
`exists_planner`/`neg_twin` at the intended `Policy`/`RewardFn` reading. Reuse
`constPlanner` and `payOne`'s reward for the instance.
-/

/-- Every policy admits a planner explaining it from `payOne`'s reward. -/
theorem exists_planner_at_payOne :
    ∃ p : Planner (RewardFn Bool Bool) (Policy Bool Bool),
      Explains p payOne.2 (op3 payOne) :=
  policy_reward_unidentifiable (op3 payOne) payOne.2

/-- The anti-rational twin of `constPlanner` at `payOne`'s reward. -/
theorem constPlanner_neg_twin :
    Explains (fun R' => constPlanner (-R')) (-payOne.2) (constPlanner payOne.2) :=
  policy_neg_twin constPlanner payOne.2

/-!
## A composed refinement, using `Determines.trans`

Three observations of the same world, each coarser than the last: the whole pair,
the policy it induces, and that policy's action at `false`. Informativeness
composes, so the first determines the third — and `Knowable.mono` then carries
any decoder backwards along the chain.
-/

/-- The action the induced policy takes at state `false`. -/
def actionAtFalse (x : Pair Bool Bool) : Bool := op3 x false

/-- The full pair determines the induced policy. -/
theorem determines_op3 : Determines (id : Pair Bool Bool → Pair Bool Bool) op3 :=
  ⟨op3, fun _ => rfl⟩

/-- The induced policy determines its action at `false`. -/
theorem determines_actionAtFalse : Determines (op3 (S := Bool) (A := Bool)) actionAtFalse :=
  ⟨fun π => π false, fun _ => rfl⟩

/-- Composed: the full pair determines the action at `false`. -/
theorem determines_actionAtFalse_of_id :
    Determines (id : Pair Bool Bool → Pair Bool Bool) actionAtFalse :=
  determines_op3.trans determines_actionAtFalse

/-- `Determines.refl`, at the observation this file is about. -/
theorem determines_op3_self : Determines (op3 (S := Bool) (A := Bool)) op3 :=
  Determines.refl _

/-- The action at `false` is knowable from the induced policy — read it off. -/
theorem knowable_actionAtFalse_from_policy :
    Knowable (op3 (S := Bool) (A := Bool)) actionAtFalse :=
  ⟨fun π => π false, fun _ => rfl⟩

/--
And `Knowable.mono` carries that decoder back along `Determines id op3`, so the
action is knowable from the whole pair. This is the transport the chain buys:
the decoder is composed, never rebuilt.
-/
theorem knowable_actionAtFalse_from_pair :
    Knowable (id : Pair Bool Bool → Pair Bool Bool) actionAtFalse :=
  Knowable.mono determines_op3 knowable_actionAtFalse_from_policy

/-! ## Lemma 6, collected, at a policy

`lemma_six` bundles the three compatibility results the source states together.
Its three components were each witnessed here already; the collected form was
not applied anywhere, so the bundle itself was unfalsifiable even though its
parts were not. -/

/-- A policy over two states and two actions that always plays `true`. -/
def alwaysTrue : Policy Bool Bool := fun _ => true

/-- **Lemma 6, applied.** All three pairs -- the indifferent planner at the zero
reward, the greedy planner at `rewardOf`, and the anti-rational planner at its
negation -- are compatible with one concrete policy. -/
theorem alwaysTrue_lemma_six :
    Explains (indifferentPlanner alwaysTrue) (0 : RewardFn Bool Bool) alwaysTrue ∧
    Explains greedyPlanner (rewardOf alwaysTrue) alwaysTrue ∧
    Explains (negPlanner greedyPlanner) (-rewardOf alwaysTrue) alwaysTrue :=
  lemma_six alwaysTrue

end AISafetyAtlas.Examples.Preference
