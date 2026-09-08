module

public import AISafetyAtlas.Preference.Reasonable
public import AISafetyAtlas.Knowledge
public import Mathlib.Tactic.Linarith

/-!
# Reward unidentifiability, in the shared knowability vocabulary

## Statement intent

- **Objects.** The planner/reward pair `Pair S A` as the world, the evaluated
  policy `op3` as the observation, and the reward `Prod.snd` as the hidden
  property.
- **Conclusion.** `not_knowable_reward`: no decoder recovers the reward from the
  resulting policy, uniformly over all planner/reward pairs.
- **Obstruction.** The source's own anti-rational negation `op4`, together with
  the invariance `op3_op4` it already proves. Negating both planner and reward
  leaves the behaviour untouched and moves the reward, which is exactly
  `AISafetyAtlas.Knowledge.not_knowable_of_invariant_transform`.

## Explicit non-claims

- **Not new mathematics, and not new BY-011 coverage.**
  `AISafetyAtlas.Preference.policy_neg_twin` already states this content in the
  source's own form: the negated pair explains the same policy. The neighbouring
  `policy_reward_unidentifiable` is a *different* statement — for every policy
  and reward some planner explains the pair — and is not what this restates. What is new here is that the same obstruction is expressed in the
  vocabulary `AISafetyAtlas.Knowledge` shares with `Wireheading` and
  `Oversight`, so a consumer holding a knowability question can reach it. Any
  ledger row must record it as a shared-API formulation, never as coverage the
  survey row did not already have.
- **Not** an audit or an extension of the source's proof. Restating a theorem
  through `Knowable` checks nothing about the printed argument.
- **Not** a claim that the reward is unrecoverable on every model class. The
  statement quantifies over *all* pairs; recovery may well succeed after
  restricting the admissible planners, or for a coarser target such as a
  reward equivalence class. `knowable_reward_of_isEmpty_state` below is one
  such restriction, and it is a real one.
- **Not** a statement about `AISafetyAtlas.Preference.Complexity`'s non-claim on
  the anti-rational pair. That module declines to treat `(-p_g, -R_π̇)` as a
  complexity comparison; this module uses `op4` only as a collision, and asserts
  nothing about complexity.

## Scope boundary

`[Nonempty S]` and `[Nonempty A]` are load-bearing rather than decorative. With
`S` empty the reward type `S → A → ℝ` is a subsingleton, every reward equals
every other, and the property **is** knowable — `knowable_reward_of_isEmpty_state`
proves it. A reader who deletes the instances gets a false statement, not a
failed proof.
-/

namespace AISafetyAtlas.Preference

open AISafetyAtlas.Knowledge

variable {S A : Type*}

/--
**The reward is not knowable from the policy.** No single decoder recovers the
reward from the evaluated policy across all planner/reward pairs.

`op4` is an observation-preserving transform: `op3_op4` says every pair and its
negation induce the same policy, and at the exhibited pair the rewards are `1`
and `-1`. So this is `not_knowable_of_invariant_transform`, the same law
`AISafetyAtlas.Wireheading.ObservationLimits.not_knowable_trueReturn` uses
with the environment complement.

This restates `policy_neg_twin` — `Explains (fun R' => p (-R')) (-R) (p R)` — in
the shared vocabulary of `AISafetyAtlas.Knowledge`, and the proof uses exactly
that content through `op3_op4`. It is **not** a restatement of
`policy_reward_unidentifiable`, which says something else: that every
policy/reward pair admits *some* explaining planner. See this module's
non-claims.
-/
public theorem not_knowable_reward [Nonempty S] [Nonempty A] :
    ¬ Knowable (op3 (S := S) (A := A)) (Prod.snd : Pair S A → RewardFn S A) := by
  classical
  set x : Pair S A := (fun _ _ => Classical.arbitrary A, fun _ _ => 1) with hx
  refine not_knowable_of_invariant_transform op4 op3_op4 x ?_
  intro h
  have hh := congrFun (congrFun h (Classical.arbitrary S)) (Classical.arbitrary A)
  simp only [hx, op4, Pi.neg_apply] at hh
  linarith only [hh]

/--
**The scope boundary is real.** With no states, the reward type is a
subsingleton and the constant decoder succeeds, so `not_knowable_reward`'s
`[Nonempty S]` cannot be dropped.
-/
public theorem knowable_reward_of_isEmpty_state [IsEmpty S] :
    Knowable (op3 (S := S) (A := A)) (Prod.snd : Pair S A → RewardFn S A) :=
  ⟨fun _ => 0, fun _ => funext fun s => isEmptyElim s⟩

end AISafetyAtlas.Preference
