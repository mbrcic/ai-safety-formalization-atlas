module

public import AISafetyAtlas.Decision.BoundedValue

/-!
# The finite-horizon (episodic) value of a stationary policy

`AISafetyAtlas.Decision.DiscountedValue` and `AISafetyAtlas.Decision.BoundedValue`
value a stationary deterministic policy by an infinite-horizon *discounted*
return. Armstrong and Mindermann's setting (§3, PDF p. 3) says *"the results of
this paper apply to both discounted rewards and episodic environments
settings"*, and leaves the return unspecified. This module supplies the other
reading: the expected **undiscounted** sum of a state-action reward over a
horizon of `T` steps, by backward recursion on the horizon.

## What is here

* `vPiEpisodic M r T π` — the `T`-step value, on an arbitrary state type, with no
  discount and no finiteness: `v₀ = 0` and `v_{T+1}(s) = r(s, π s) + E[v_T(s')]`.
* `abs_vPiEpisodic_le` — a reward bounded by `C` along the policy gives values
  bounded by `T · C`.
* `vPiEpisodic_const_reward` — a policy earning `k` at every state has value
  `T · k`.
* vPiStopped M term r T π — the episode ends on reaching a terminal state
  (term), so its length is random: the T-step value with the reward masked
  to 0 at terminal states and no continuation after them.
  `vPiStopped_eq_vPiEpisodic` identifies it with `vPiEpisodic` on the MDP whose
  terminal states are absorbing (`stopMDP`) at the masked reward (`maskReward`),
  and `vPiStopped_empty` with `vPiEpisodic` when nothing is terminal.
* vPiTerm M term r π — the undiscounted return up to termination: the limit
  of the stopped T-step values as T → ∞, with no horizon fixed.
  `vPiTerm_eq_of_tendsto` reads it off any convergent sequence.

## Scope

As with `vPi`, the value is *defined* by the Bellman recursion, not proved equal
to the expected reward sum along `AISafetyAtlas.Decision.MDP.run`; that
identification is owed, exactly as it is for the discounted value. The policy is
stationary and deterministic. `AISafetyAtlas.Wireheading.StochasticCRMDP` carries
a run-based `t`-step return for state rewards and history-dependent policies;
this module is the state-action-reward, stationary-policy recursion the regret
and override models consume.
-/

namespace AISafetyAtlas.Decision

variable {State Action : Type*}

/-- **The `T`-step undiscounted value of a stationary deterministic policy**: the
reward the policy earns now plus the expected `(T−1)`-step value of the
successor, and `0` at horizon `0`. -/
@[expose] public noncomputable def vPiEpisodic (M : MDP State Action)
    (r : State → Action → ℝ) : ℕ → (State → Action) → State → ℝ
  | 0, _ => fun _ => 0
  | T + 1, π => fun s => r s (π s) + expect (M.transition s (π s)) (vPiEpisodic M r T π)

/-- At horizon `0` the value is `0`. -/
@[simp] public theorem vPiEpisodic_zero (M : MDP State Action) (r : State → Action → ℝ)
    (π : State → Action) (s : State) : vPiEpisodic M r 0 π s = 0 := rfl

/-- **The finite-horizon Bellman equation.** -/
public theorem vPiEpisodic_succ (M : MDP State Action) (r : State → Action → ℝ) (T : ℕ)
    (π : State → Action) (s : State) :
    vPiEpisodic M r (T + 1) π s =
      r s (π s) + expect (M.transition s (π s)) (vPiEpisodic M r T π) := rfl

/-- **Rewards bounded by `C` along the policy give `T`-step values bounded by
`T · C`.** -/
public theorem abs_vPiEpisodic_le (M : MDP State Action) (r : State → Action → ℝ)
    (π : State → Action) {C : ℝ} (hr : ∀ s, |r s (π s)| ≤ C) (T : ℕ) (s : State) :
    |vPiEpisodic M r T π s| ≤ T * C := by
  induction T generalizing s with
  | zero => simp
  | succ T ih =>
    rw [vPiEpisodic_succ]
    calc |r s (π s) + expect (M.transition s (π s)) (vPiEpisodic M r T π)|
        ≤ |r s (π s)| + |expect (M.transition s (π s)) (vPiEpisodic M r T π)| :=
          abs_add_le _ _
      _ ≤ C + T * C := add_le_add (hr s) (abs_expect_le _ ih)
      _ = ((T + 1 : ℕ) : ℝ) * C := by push_cast; ring

/-- **A policy earning the same reward `k` at every state has `T`-step value
`T · k`** everywhere. -/
public theorem vPiEpisodic_const_reward (M : MDP State Action) (r : State → Action → ℝ)
    (π : State → Action) (k : ℝ) (hk : ∀ s, r s (π s) = k) (T : ℕ) :
    vPiEpisodic M r T π = fun _ => T * k := by
  induction T with
  | zero => funext s; simp
  | succ T ih =>
    funext s
    rw [vPiEpisodic_succ, ih, expect_const, hk s]
    push_cast
    ring

/-! ## Random termination: the episode ends at a terminal state

Print's *"episodic environments settings"* (§3) fixes neither a horizon nor a
termination rule. A fixed horizon is `vPiEpisodic`; the other reading lets the
episode end when the process reaches a terminal state, after a random number of
steps, and sums the undiscounted reward up to then. -/

open Classical in
/-- **The T-step stopped value**: the undiscounted reward collected before the
first terminal state (a state of term) or the horizon T, whichever comes
first. A terminal state contributes nothing and stops the sum: its reward is
masked to 0 and there is no continuation. -/
@[expose] public noncomputable def vPiStopped (M : MDP State Action) (term : Set State)
    (r : State → Action → ℝ) : ℕ → (State → Action) → State → ℝ
  | 0, _ => fun _ => 0
  | T + 1, π => fun s =>
      if s ∈ term then 0 else r s (π s) + expect (M.transition s (π s)) (vPiStopped M term r T π)

/-- At horizon 0 the stopped value is 0. -/
@[simp] public theorem vPiStopped_zero (M : MDP State Action) (term : Set State)
    (r : State → Action → ℝ) (π : State → Action) (s : State) :
    vPiStopped M term r 0 π s = 0 := rfl

/-- A terminal state has stopped value 0 at every horizon. -/
public theorem vPiStopped_of_mem (M : MDP State Action) {term : Set State}
    (r : State → Action → ℝ) (T : ℕ) (π : State → Action) {s : State} (hs : s ∈ term) :
    vPiStopped M term r T π s = 0 := by
  cases T with
  | zero => rfl
  | succ T => simp [vPiStopped, hs]

/-- **The stopped Bellman equation** off the terminal set. -/
public theorem vPiStopped_succ_of_notMem (M : MDP State Action) {term : Set State}
    (r : State → Action → ℝ) (T : ℕ) (π : State → Action) {s : State} (hs : s ∉ term) :
    vPiStopped M term r (T + 1) π s =
      r s (π s) + expect (M.transition s (π s)) (vPiStopped M term r T π) := by
  simp [vPiStopped, hs]

open Classical in
/-- **The MDP stopped at term**: terminal states are absorbing, every other
transition is M's. -/
@[expose] public noncomputable def stopMDP (M : MDP State Action) (term : Set State) :
    MDP State Action where
  transition s a := if s ∈ term then PMF.pure s else M.transition s a

open Classical in
/-- **The reward masked to 0 at terminal states.** -/
@[expose] public noncomputable def maskReward (term : Set State) (r : State → Action → ℝ) :
    State → Action → ℝ :=
  fun s a => if s ∈ term then 0 else r s a

/-- On the stopped MDP at the masked reward, a terminal state earns nothing at
any horizon. -/
public theorem vPiEpisodic_stopMDP_of_mem (M : MDP State Action) {term : Set State}
    (r : State → Action → ℝ) (T : ℕ) (π : State → Action) {s : State} (hs : s ∈ term) :
    vPiEpisodic (stopMDP M term) (maskReward term r) T π s = 0 := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have ht : (stopMDP M term).transition s (π s) = PMF.pure s := by simp [stopMDP, hs]
    rw [vPiEpisodic_succ, ht, expect_pure, ih]
    simp [maskReward, hs]

/-- **The stopped value is the episodic value of the stopped MDP at the masked
reward**: making terminal states absorbing and masking their reward to 0 is
the same as stopping the sum there. -/
public theorem vPiStopped_eq_vPiEpisodic (M : MDP State Action) (term : Set State)
    (r : State → Action → ℝ) (T : ℕ) (π : State → Action) :
    vPiStopped M term r T π = vPiEpisodic (stopMDP M term) (maskReward term r) T π := by
  induction T with
  | zero => rfl
  | succ T ih =>
    funext s
    by_cases hs : s ∈ term
    · rw [vPiStopped_of_mem M r _ π hs, vPiEpisodic_stopMDP_of_mem M r _ π hs]
    · rw [vPiStopped_succ_of_notMem M r T π hs, vPiEpisodic_succ, ih]
      simp [stopMDP, maskReward, hs]

/-- With no terminal state the stopped value is the T-step value. -/
public theorem vPiStopped_empty (M : MDP State Action) (r : State → Action → ℝ) (T : ℕ)
    (π : State → Action) : vPiStopped M ∅ r T π = vPiEpisodic M r T π := by
  induction T with
  | zero => rfl
  | succ T ih =>
    funext s
    rw [vPiStopped_succ_of_notMem M r T π (Set.notMem_empty s), vPiEpisodic_succ, ih]

/-- **The undiscounted return up to termination**: the limit, as the horizon
grows, of the stopped T-step values. No horizon and no discount is fixed; the
episode's length is the random time at which the process first enters the
terminal set.

`Filter.limUnder` is a junk value when the sequence diverges. Print presupposes that the
expected return exists (*"the expected return of reward function R from state
s"*, §4.1.2); `vPiTerm_eq_of_tendsto` reads the value off any convergent
sequence. -/
@[expose] public noncomputable def vPiTerm (M : MDP State Action) (term : Set State)
    (r : State → Action → ℝ) (π : State → Action) (s : State) : ℝ :=
  Filter.limUnder Filter.atTop fun T => vPiStopped M term r T π s

/-- **When the stopped values converge, `vPiTerm` is their limit.** -/
public theorem vPiTerm_eq_of_tendsto (M : MDP State Action) (term : Set State)
    (r : State → Action → ℝ) (π : State → Action) (s : State) {v : ℝ}
    (h : Filter.Tendsto (fun T => vPiStopped M term r T π s) Filter.atTop (nhds v)) :
    vPiTerm M term r π s = v :=
  h.limUnder_eq

end AISafetyAtlas.Decision
