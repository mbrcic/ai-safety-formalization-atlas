module

public import AISafetyAtlas.Preference
public import AISafetyAtlas.Decision.MDP

/-!
# Preference unidentifiability, about a trajectory rather than a function

`AISafetyAtlas.Preference` states Armstrong and Mindermann's degeneracy at
`Policy S A = S → A`: fix an observed policy, and every reward is still
consistent with it. That is the source's own reading, and as a statement about
a function it is complete.

It is also unobservable. Nobody sees a policy; what is seen is a **trajectory** —
the actions an agent took and the observations that followed. The two are not
the same object, and until a policy could be run there was no way to say whether
the degeneracy survives the difference. This module says it does.

## The bridge

A memoryless policy is a history policy that reads only the last observation.
`ofMemoryless` is that embedding into `AISafetyAtlas.Decision.DetPolicy`, and it
is **injective**, so the `Decision` carrier does not identify policies that
`Preference` distinguishes. `detStateAt_ofMemoryless_succ` is the content: the
run under an induced policy satisfies the memoryless recursion, so nothing in
the history beyond the last observation is being consulted.

## The statement that needed the bridge

`consistent_rewards_of_trajectory_eq_univ` is the degeneracy at the trajectory:
**the set of rewards consistent with an observed run is all of them.** Fix a
world, a start, and everything an agent was seen to do, for as many steps as
anyone cares to watch; the rewards this rules out are none.

The proof is short, and that is the point — the difficulty was never the
argument, it was that the statement could not be *written* while a policy and a
run lived in different trees.

## Explicit non-claims

* **Memoryless policies only.** A history policy that genuinely consults its
  past is not in the image of `ofMemoryless`, and nothing here says the
  degeneracy extends to one. It does, trivially, by the same planner — what is
  absent is a reason to state it, since `Preference`'s object is memoryless.
* **Determined runs only.** The drawn run is a `PMF`; this module does not
  touch it.
* **No optimality anywhere.** A planner here is unconstrained, exactly as in
  `AISafetyAtlas.Preference`. Nothing is maximized, so nothing follows about
  inverse reinforcement learning under a rationality assumption.

Landscape entry: `LAND-PREF-TRAJECTORY-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference

variable {Obs Action State : Type*}

/-! ## A memoryless policy, read on the carrier -/

/-- **The observation a history ends at** — its last one, or the initial
observation when nothing has happened yet. -/
@[expose] public def lastObs (h : Decision.History Obs Action) : Obs :=
  match h.2.getLast? with
  | none => h.1
  | some p => p.2

/-- Appending a step moves the reading to the observation just reached. -/
public theorem lastObs_append (h : Decision.History Obs Action) (q : Action × Obs) :
    lastObs (h.1, h.2 ++ [q]) = q.2 := by
  simp [lastObs]

/-- **A memoryless policy as a history policy**: read the last observation and
act on it. -/
@[expose] public def ofMemoryless (π : Policy Obs Action) :
    Decision.DetPolicy Obs Action :=
  fun h => π (lastObs h)

/-- **The carrier does not identify policies that `Preference` distinguishes.**
Two memoryless policies differing anywhere induce different history policies, so
nothing is lost in passing to the run. -/
public theorem ofMemoryless_injective :
    Function.Injective (ofMemoryless (Obs := Obs) (Action := Action)) := by
  intro π₁ π₂ h
  funext o
  have := congrFun h ((o, []) : Decision.History Obs Action)
  simpa [ofMemoryless, lastObs] using this

/-! ## The run is memoryless -/

/-- The history a run has reached ends at the observation of the state it has
reached. -/
public theorem lastObs_detHistoryUpTo (f : State → Action → State) (obs : State → Obs)
    (π : Policy Obs Action) (s₀ : State) (n : ℕ) :
    lastObs (Decision.detHistoryUpTo f obs (ofMemoryless π) s₀ n)
      = obs (Decision.detStateAt f obs (ofMemoryless π) s₀ n) := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [Decision.detHistoryUpTo, Decision.detStateAt, Decision.detRun]
      exact lastObs_append _ _

/--
**The induced run obeys the memoryless recursion.**

The next state is the transition applied to the action the policy takes at the
*current observation* — no part of the history beyond it is consulted. This is
what makes `ofMemoryless` an embedding of a memoryless agent rather than a
re-encoding that quietly gains memory.
-/
public theorem detStateAt_ofMemoryless_succ (f : State → Action → State)
    (obs : State → Obs) (π : Policy Obs Action) (s₀ : State) (n : ℕ) :
    Decision.detStateAt f obs (ofMemoryless π) s₀ (n + 1)
      = f (Decision.detStateAt f obs (ofMemoryless π) s₀ n)
          (π (obs (Decision.detStateAt f obs (ofMemoryless π) s₀ n))) := by
  show f (Decision.detRun f obs (ofMemoryless π) s₀ n).1
      (ofMemoryless π (Decision.detRun f obs (ofMemoryless π) s₀ n).2) = _
  rw [show (Decision.detRun f obs (ofMemoryless π) s₀ n).2
        = Decision.detHistoryUpTo f obs (ofMemoryless π) s₀ n from rfl]
  rw [ofMemoryless, lastObs_detHistoryUpTo]
  rfl

/-! ## The degeneracy, at what is actually observed -/

/--
**Every reward is consistent with every observed trajectory.**

`policy_reward_unidentifiable` fixes a policy; this fixes the run — the world,
the start, and every action taken and observation reached, for as many steps as
anyone watches. The rewards ruled out are none.
-/
public theorem trajectory_reward_unidentifiable (f : State → Action → State)
    (obs : State → Obs) (s₀ : State) (π : Policy Obs Action)
    (R : RewardFn Obs Action) :
    ∃ p : Planner (RewardFn Obs Action) (Policy Obs Action),
      Explains p R π ∧
      ∀ n, Decision.detHistoryUpTo f obs (ofMemoryless (p R)) s₀ n
          = Decision.detHistoryUpTo f obs (ofMemoryless π) s₀ n :=
  ⟨fun _ => π, rfl, fun _ => rfl⟩

/-- **The set form**, which is where the emptiness of the inference is plainest:
the consistent rewards are not merely many, they are everything. -/
public theorem consistent_rewards_of_trajectory_eq_univ (f : State → Action → State)
    (obs : State → Obs) (s₀ : State) (π : Policy Obs Action) :
    {R : RewardFn Obs Action |
        ∃ p : Planner (RewardFn Obs Action) (Policy Obs Action),
          ∀ n, Decision.detHistoryUpTo f obs (ofMemoryless (p R)) s₀ n
              = Decision.detHistoryUpTo f obs (ofMemoryless π) s₀ n} = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨fun _ => π, fun _ => rfl⟩

end AISafetyAtlas.Preference
