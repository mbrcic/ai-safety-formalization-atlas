module

public import AISafetyAtlas.Causal.GoalDynamics

/-!
# Worked policies, trajectory laws and bounded agents

`AISafetyAtlas.Causal.GoalDynamics` renders the probabilistic half of MAIS-A2's
goal setting. This module checks that the definitions have content:

* `firstActionMap` reads the agent's first action from a start state and a goal,
  and reads nothing else — checked on an agent that branches on the state;
* the empty composite goal is achieved with probability zero, so `achieveProb` is
  not the constant `1`;
* `IsDeltaBounded` is **inhabited**: over a one-action environment every agent is
  `(δ,n)`-bounded at every `δ ≥ 0`, because there is only one policy and the
  supremum is attained by it.

The last one is a non-vacuity check on the predicate, not a MAIS instance:
`prob:corruption` quantifies over instances with `|𝐀| ≥ 2`. Building a bounded
agent over a two-action environment is what the splice needs, and the splice
needs the `traj` congruence lemma `AISafetyAtlas.Causal.GoalDynamics` records as
missing.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.GoalDynamics

open AISafetyAtlas.Causal MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## The first-action map reads the start state and the goal -/

/-- An agent that plays action `1` from state `0` and action `0` elsewhere,
whatever the goal. -/
@[expose] public def branchingAgent : GoalConditionedAgent (Fin 2) (Fin 2) :=
  fun _ _ h ↦ if h ⟨0, by simp⟩ = 0 then 1 else 0

public theorem firstActionMap_branching_zero (Ψ : CompositeGoal (Fin 2) (Fin 2)) :
    firstActionMap branchingAgent 0 Ψ = 1 := by
  simp [firstActionMap, branchingAgent]

public theorem firstActionMap_branching_one (Ψ : CompositeGoal (Fin 2) (Fin 2)) :
    firstActionMap branchingAgent 1 Ψ = 0 := by
  simp [firstActionMap, branchingAgent]

/-! ## The empty goal is never achieved -/

/-- A disjunction of no disjuncts is satisfied by nothing, so `achieveProb` is
not constantly one. -/
public theorem achieveProb_empty {S A : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : ControlledMarkovProcess S A) (π : GoalPolicy S A) (s₀ : S) :
    achieveProb E π s₀ ∅ = 0 := by
  have hset : {ω : ℕ → S | CompositeSatisfies (∅ : CompositeGoal S A) (statePairs π ω)} = ∅ := by
    ext ω
    simp [CompositeSatisfies]
  rw [achieveProb, hset, measure_empty]

/-! ## `IsDeltaBounded` is inhabited -/

/-- A one-action environment: the uniform kernel on two states. -/
@[expose] public noncomputable def oneActionEnv : ControlledMarkovProcess (Fin 2) (Fin 1) where
  prob := fun _ _ _ ↦ 1 / 2
  prob_nonneg := by intro _ _ _; norm_num
  prob_sum := by
    intro _ _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

/-- With one action there is exactly one policy. -/
public instance : Subsingleton (GoalPolicy (Fin 2) (Fin 1)) := inferInstance

/-- So every policy attains the supremum. -/
public theorem achieve_eq_optimal (π : GoalPolicy (Fin 2) (Fin 1)) (s₀ : Fin 2)
    (Ψ : CompositeGoal (Fin 2) (Fin 1)) :
    achieveProb oneActionEnv π s₀ Ψ = optimalProb oneActionEnv s₀ Ψ := by
  refine le_antisymm (achieveProb_le_optimalProb _ _ _ _) ?_
  refine iSup_le fun π' ↦ ?_
  rw [Subsingleton.elim π' π]

/-- **`(δ,n)`-boundedness is satisfiable.** Over the one-action environment every
agent is bounded at every `δ ≥ 0`, `δ = 0` included — so the predicate is not
empty for the reason that would make every MAIS-O33 statement vacuous. -/
public theorem isDeltaBounded_oneAction (agent : GoalConditionedAgent (Fin 2) (Fin 1))
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : IsDeltaBounded oneActionEnv agent n δ :=
  isDeltaBounded_of_achieve_eq_optimal hδ fun Ψ s₀ ↦ achieve_eq_optimal _ s₀ Ψ

end AISafetyAtlas.Examples.Causal.GoalDynamics
