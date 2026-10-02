module

public import AISafetyAtlas.Compositional.TraceSystem

/-!
# A policy set, its traces, and a safety property it breaks

`exists_bad_trajectories_of_isKSafety` takes a k-safety hyperproperty and a
policy set that violates it. Both halves have to be real or the theorem is a
hypothesis chain nothing satisfies, so this file supplies both.

The world is one bit that the action overwrites. `nothingHasHappened` is the
hyperproperty *"no trace in this system records a step"* — and it is 1-safety,
with `nothingHasHappened_isKSafety` proving it rather than assuming it: a system
that violates it contains a trace of positive length, that single trace is the
bad observation, and every system realizing it violates too.

Any policy set violates it after one step. `bad_trajectory_exists` is the
conclusion in the form it matters: the violation is reported as **one partial
trajectory of a named policy**, not as an abstract set of prefixes.
-/

namespace AISafetyAtlas.Examples.Compositional.TraceSystem

open AISafetyAtlas.Compositional.Hyperproperties

/-- The world: the action becomes the state. -/
@[expose] public def flipWorld : Bool → Bool → Bool := fun _ a => a

/-- The agent sees the state. -/
@[expose] public def seeState : Bool → Bool := id

/-- Act one way. -/
@[expose] public def alwaysTrue : AISafetyAtlas.Decision.DetPolicy Bool Bool :=
  fun _ => true

/-- Act the other. -/
@[expose] public def alwaysFalse : AISafetyAtlas.Decision.DetPolicy Bool Bool :=
  fun _ => false

/-- Both of them. -/
@[expose] public def bothPolicies : Set (AISafetyAtlas.Decision.DetPolicy Bool Bool) :=
  {alwaysTrue, alwaysFalse}

/-- The system their runs generate. -/
@[expose] public def system : TraceSystem (AISafetyAtlas.Decision.History Bool Bool) :=
  runTraces flipWorld seeState false bothPolicies

/-- **The system is inhabited.** -/
public theorem system_nonempty : system.Nonempty :=
  runTraces_nonempty flipWorld seeState false ⟨alwaysTrue, Or.inl rfl⟩

/-- **And it holds more than the empty history**: one step of `alwaysTrue` is in
it, and that trace records a step. -/
public theorem step_mem_system :
    AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState alwaysTrue false 1 ∈ system :=
  mem_runTraces flipWorld seeState false (Or.inl rfl) 1

/-- That trace has length one, which is what makes it a violation below. -/
public theorem step_length :
    (AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState alwaysTrue false 1).2.length = 1 :=
  AISafetyAtlas.Decision.detHistoryUpTo_length flipWorld seeState alwaysTrue false 1

/-- **A run's stages are prefixes of each other.** The empty history is a prefix
of the one-step history, so the prefixes of a trajectory are its own past and
nothing had to be invented to observe it. -/
public theorem stage_prefix_stage :
    HistoryPrefix
      (AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState alwaysTrue false 0)
      (AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState alwaysTrue false 1) :=
  detHistoryUpTo_prefix_succ flipWorld seeState alwaysTrue false 0

/-- **Dropping a policy can only shrink the system.** One agent's runs are among
two agents' runs. -/
public theorem one_policy_subset :
    runTraces flipWorld seeState false {alwaysTrue} ⊆ system :=
  runTraces_mono flipWorld seeState false (by
    intro π hπ
    simp only [Set.mem_singleton_iff] at hπ
    exact Or.inl hπ)

/-! ## A hyperproperty, and a proof that it is 1-safety -/

/-- **Nothing has happened yet**: no trace in the system records a step. -/
@[expose] public def nothingHasHappened :
    Hyperproperty (AISafetyAtlas.Decision.History Bool Bool) :=
  {S | ∀ t ∈ S, t.2.length = 0}

/--
**It is 1-safety**, and this is proved rather than assumed. A violating system
holds a trace of positive length; that one trace is the bad observation, because
anything realizing it holds a trace at least as long.
-/
public theorem nothingHasHappened_isKSafety :
    IsKSafety (HistoryPrefix (Obs := Bool) (Action := Bool)) 1 nothingHasHappened := by
  intro S hS
  simp only [nothingHasHappened, Set.mem_ofPred_eq, not_forall] at hS
  obtain ⟨t, htS, hlen⟩ := hS
  refine ⟨{t}, by simp, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_singleton] at hp
    exact ⟨t, htS, hp ▸ ⟨rfl, List.prefix_refl _⟩⟩
  · intro S' hS' hmem
    obtain ⟨t', ht'S, hpre⟩ := hS' t (by simp)
    exact hlen (Nat.le_zero.mp (hmem t' ht'S ▸ hpre.2.length_le))

/-- **The system violates it**, because one step really happened. -/
public theorem system_violates : system ∉ nothingHasHappened := by
  intro h
  have := h _ step_mem_system
  rw [step_length] at this
  exact one_ne_zero this

/--
**So the violation is reported as one partial trajectory of a named policy.**

Not an abstract prefix set: a policy in the set, a number of steps, and a
history that extends into that run.
-/
public theorem bad_trajectory_exists :
    ∃ M : Finset (AISafetyAtlas.Decision.History Bool Bool),
      M.card ≤ 1 ∧
      IsBadObservation HistoryPrefix nothingHasHappened M ∧
      ∀ p ∈ M, ∃ π ∈ bothPolicies, ∃ n,
        HistoryPrefix p (AISafetyAtlas.Decision.detHistoryUpTo flipWorld seeState π false n) :=
  exists_bad_trajectories_of_isKSafety flipWorld seeState false bothPolicies 1
    nothingHasHappened_isKSafety system_violates

end AISafetyAtlas.Examples.Compositional.TraceSystem
