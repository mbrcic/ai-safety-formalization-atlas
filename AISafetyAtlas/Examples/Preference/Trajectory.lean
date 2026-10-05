module

public import AISafetyAtlas.Preference.Trajectory

/-!
# The trajectory degeneracy, in a world where trajectories differ

`consistent_rewards_of_trajectory_eq_univ` says the rewards consistent with an
observed run are all of them. Read at a world where every policy produces the
same run it would be true and empty, so this file fixes a world where they do
not: one bit of state, the action overwrites it, and the agent sees the state.

`run_differs` is that separation stated as a theorem. The agent that repeats
what it sees stays where it started; the agent that contradicts what it sees is
somewhere else after one step. So the run genuinely reports the policy — and
the degeneracy still says that reading the reward off it is impossible.
-/

namespace AISafetyAtlas.Examples.Preference.Trajectory

open AISafetyAtlas.Preference

/-- The world: the action becomes the state. -/
@[expose] public def flipWorld : Bool → Bool → Bool := fun _ a => a

/-- The agent sees the state. -/
@[expose] public def seeState : Bool → Bool := id

/-- The agent that repeats what it sees. -/
@[expose] public def copy : Policy Bool Bool := id

/-- The agent that contradicts what it sees. -/
@[expose] public def contradict : Policy Bool Bool := not

/-- **They are different policies**, which `ofMemoryless_injective` then carries
to the carrier. -/
public theorem copy_ne_contradict : copy ≠ contradict := by
  intro h
  have := congrFun h false
  simp [copy, contradict] at this

/-- **And so different history policies.** The embedding loses nothing. -/
public theorem ofMemoryless_copy_ne_contradict :
    ofMemoryless copy ≠ ofMemoryless contradict :=
  fun h => copy_ne_contradict (ofMemoryless_injective h)

/-- **The two agents are somewhere different after one step**, so the run
reports the policy and the world is not one where every trajectory coincides. -/
public theorem run_differs :
    AISafetyAtlas.Decision.detStateAt flipWorld seeState (ofMemoryless copy) false 1
      ≠ AISafetyAtlas.Decision.detStateAt flipWorld seeState
          (ofMemoryless contradict) false 1 := by
  rw [detStateAt_ofMemoryless_succ, detStateAt_ofMemoryless_succ]
  simp [flipWorld, seeState, copy, contradict,
    AISafetyAtlas.Decision.detStateAt, AISafetyAtlas.Decision.detRun]

/-- The memoryless recursion at the witness: one step of `contradict` from
`false` lands on `true`. -/
public theorem contradict_step :
    AISafetyAtlas.Decision.detStateAt flipWorld seeState
      (ofMemoryless contradict) false 1 = true := by
  rw [detStateAt_ofMemoryless_succ]
  simp [flipWorld, seeState, contradict,
    AISafetyAtlas.Decision.detStateAt, AISafetyAtlas.Decision.detRun]

/--
**Even so, the trajectory identifies no reward.** Watch `contradict` in this
world for as long as you like: the set of rewards consistent with what you saw
is everything.
-/
public theorem consistent_rewards_eq_univ_at_witness :
    {R : RewardFn Bool Bool |
        ∃ p : Planner (RewardFn Bool Bool) (Policy Bool Bool),
          ∀ n, AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState
                  (ofMemoryless (p R)) false n
              = AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState
                  (ofMemoryless contradict) false n} = Set.univ :=
  consistent_rewards_of_trajectory_eq_univ flipWorld seeState false contradict

/-- The same at a named reward, with the explaining planner exhibited rather
than only known to exist. -/
public theorem zero_reward_explains_contradict :
    ∃ p : Planner (RewardFn Bool Bool) (Policy Bool Bool),
      Explains p (fun _ _ => 0) contradict ∧
      ∀ n, AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState
              (ofMemoryless (p (fun _ _ => 0))) false n
          = AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState
              (ofMemoryless contradict) false n :=
  trajectory_reward_unidentifiable flipWorld seeState false contradict (fun _ _ => 0)

/-- The last observation of a fresh history is the one it starts at, which is
the base case the recursion reads. -/
public theorem lastObs_start : lastObs ((false, []) : AISafetyAtlas.Decision.History Bool Bool)
    = false := rfl

/-- And appending a step moves the reading forward. -/
public theorem lastObs_after_step (a o : Bool) :
    lastObs ((false, [(a, o)]) : AISafetyAtlas.Decision.History Bool Bool) = o :=
  lastObs_append (false, []) (a, o)

end AISafetyAtlas.Examples.Preference.Trajectory
