module

public import AISafetyAtlas.Causal.ControlledProcess
public import AISafetyAtlas.Causal.Goal
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Deterministic policies, trajectory laws, and print's `(δ,n)`-bounded agents

The probabilistic half of MAIS-A2's goal setting: what a deterministic
goal-conditioned agent does to a controlled Markov process, and the achievement
probability print's `(δ,n)`-boundedness compares against.

## Why the state sequence carries everything

Print's agent is a **deterministic** map from (history, goal) pairs to actions,
and print's history is the trajectory prefix `(s₀, a₀, …, s_t)` — states *and*
actions. Determinism makes the recorded actions a function of the states before
them, so nothing is left to chance but the transitions, the process lives on
`ℕ → 𝐒`, one application of Ionescu–Tulcea suffices with `X n = 𝐒` throughout,
and `statePairs` recovers the state–action trajectory the goal semantics reads.

**This is proved, not assumed.** `FullPolicy` is print's type, `inducedPolicy`
computes the action a trajectory-prefix policy takes as a function of the states
by running the same rule at earlier times, `liftPolicy` embeds back, and
`inducedPolicy_liftPolicy` says the round trip is the identity. Hence
`optimalProbFull_eq` — print's `max_{π'}` and this module's supremum have the
same value — and `isDeltaBoundedFull_lift_iff`: the two `(δ,n)`-boundedness
clauses select the same agents, and `firstActionMapFull_lift` says they show the
analyst the same data.

## `max` versus `⨆`

Print writes

    P(τ ⊨ ψ | π, s₀) ≥ (1 - δ) · max_{π'} P(τ ⊨ ψ | π', s₀),

which **presupposes** the maximum is attained. Attainment is a theorem — optimal
deterministic policies exist for reachability objectives on a finite process —
and Mathlib does not carry it. `optimalProb` is the supremum, which is what is
available without that theorem and which agrees with print's `max` wherever the
presupposition holds. At `δ = 0` the two readings differ and the attainment
theorem is unavoidable; at any `δ > 0` they do not, because a policy within a
factor `(1 - δ)` of a supremum exists by approximation. That is why
`docs/provenance/mais-o33-statability.md` runs MAIS issue #9's construction at
`δ = 1/2` rather than at the `δ = 0` the note chose.

The two readings also differ in *strength*, and in the safe direction for a
negative result: `⨆ ≥ max`, so an agent bounded here is bounded in print's sense
whether or not the maximum exists.

## What the achievement probability is

`achieveProb` applies the trajectory law to `{ω | CompositeSatisfies Ψ …}`, and
`measurableSet_compositeSatisfies` proves that event measurable, so the value is
print's probability rather than the measure's canonical extension to an
arbitrary set. The proof follows print's own semantics: a sub-goal reads one
state–action pair, that pair at time `t` is a function of the states up to `t`
because the policy is deterministic, *Now* and *Next* fix the time, *Eventually*
is a countable union over it with a finite minimality condition, a sequential
goal is a countable union over its head's achievement time, and a composite goal
is a finite union over its disjuncts.

Nothing below depends on that theorem — every step touching `achieveProb` is
monotone (`measure_mono`) or an almost-everywhere congruence (`measure_congr`),
both valid for the extension, and `optimalProb` is the supremum of the same
functional — but without it `achieveProb` would only be *bounded by* print's
probability, and the row that transcribes print's `P(τ ⊨ ψ | π, s₀)` would be
carrying a different number.

## What is not here

Nothing that MAIS-O33 needs. In particular the splice is here and unconditional:
`exists_isDeltaBounded_prescribing` builds a `(δ,n)`-bounded agent from
per-`(s₀, Ψ)` approximations on an **action-independent** environment, where
`trajectoryLaw_congr` makes the two laws being compared the same measure. On a
general environment the same construction would need a congruence lemma for
`ProbabilityTheory.Kernel.traj` that Mathlib does not state; no result in this
tree asks for one.
-/

namespace AISafetyAtlas.Causal

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-! ## Policies -/

/-- The history a deterministic policy reads at time `n`: the states up to `n`,
which determine the actions taken along them. -/
public abbrev GoalHistory (S : Type*) (n : ℕ) := ↥(Finset.Iic n) → S

/-- A deterministic policy, at one goal. -/
public abbrev GoalPolicy (S A : Type*) := (n : ℕ) → GoalHistory S n → A

/-- Print's goal-conditioned agent: one policy per composite goal, which is the
same data as a map from (history, goal) pairs to actions. -/
public abbrev GoalConditionedAgent (S A : Type*) := CompositeGoal S A → GoalPolicy S A

/-- The state–action trajectory a state sequence induces under a policy. -/
@[expose] public def statePairs (π : GoalPolicy S A) (ω : ℕ → S) : ℕ → S × A :=
  fun t ↦ (ω t, π t fun i ↦ ω i)

/-- **All the analyst sees**: the agent's first action from a start state under a
goal. -/
@[expose] public def firstActionMap (π : GoalConditionedAgent S A) (s₀ : S)
    (Ψ : CompositeGoal S A) : A :=
  π Ψ 0 fun _ ↦ s₀

/-! ## Print's history, and the reduction to the state sequence

Print's history is the trajectory prefix `(s₀, a₀, …, s_t)` — states **and**
actions — and `GoalHistory` carries the states. The two are not merely
behaviourally similar: `inducedPolicy` is the reduction, and it is exact.

A full-history policy is read along a run by handing it the actions it itself
played, and those are a function of the states, computed by the same rule one
step earlier. `inducedPolicy` performs that recursion, so the action a
full-history policy takes at time `t` on a run is a function of `s₀, …, s_t`
alone. Nothing is lost: `liftPolicy` embeds the state policies back, and
`inducedPolicy_liftPolicy` says the round trip is the identity. Hence
`optimalProbFull_eq`: print's `max_{π'}` over trajectory-prefix policies is the
supremum this module takes, so the two `(δ,n)`-boundedness clauses select the
same agents. -/

/-- Print's history at time `t`: the trajectory prefix `(s₀, a₀, …, s_t)`, as
its states up to `t` and its actions strictly before `t`. -/
public abbrev FullHistory (S A : Type*) (t : ℕ) :=
  (↥(Finset.Iic t) → S) × (↥(Finset.range t) → A)

/-- Print's goal-conditioned policy at one goal: a deterministic map from
trajectory prefixes to actions. -/
public abbrev FullPolicy (S A : Type*) := (t : ℕ) → FullHistory S A t → A

/-- Print's goal-conditioned agent: one trajectory-prefix policy per composite
goal. -/
public abbrev FullAgent (S A : Type*) := CompositeGoal S A → FullPolicy S A

/-- **The reduction.** The action a trajectory-prefix policy takes at time `t`,
as a function of the states alone: the recorded actions are the ones it played,
so they are computed by the same rule at earlier times. -/
public def inducedPolicy (π : FullPolicy S A) : (t : ℕ) → GoalHistory S t → A
  | t, h => π t (h, fun j ↦
      inducedPolicy π j.1 fun i ↦ h ⟨i.1, Finset.mem_Iic.mpr
        ((Finset.mem_Iic.mp i.2).trans (le_of_lt (Finset.mem_range.mp j.2)))⟩)
  decreasing_by exact Finset.mem_range.mp j.2

/-- A state policy read as a trajectory-prefix policy that ignores the recorded
actions. -/
@[expose] public def liftPolicy (π : GoalPolicy S A) : FullPolicy S A := fun t h ↦ π t h.1

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] public theorem inducedPolicy_liftPolicy (π : GoalPolicy S A) :
    inducedPolicy (liftPolicy π) = π := by
  funext t h
  rw [inducedPolicy]
  rfl

/-! ## The trajectory law -/

/-- One row of the kernel, as a distribution on the next state. -/
@[expose] public noncomputable def stepPMF (E : ControlledMarkovProcess S A)
    (s : S) (a : A) : PMF S :=
  PMF.ofFintype (fun s' ↦ ENNReal.ofReal (E.prob s a s')) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun s' _ ↦ E.prob_nonneg s a s', E.prob_sum,
      ENNReal.ofReal_one])

/-- The transition kernel a policy induces at time `n`: the row at the current
state and the action the policy takes on the history so far. -/
@[expose] public noncomputable def stepKernel (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (n : ℕ) : Kernel (GoalHistory S n) S :=
  Kernel.ofFunOfCountable fun h ↦
    (stepPMF E (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (π n h)).toMeasure

public instance (E : ControlledMarkovProcess S A) (π : GoalPolicy S A) (n : ℕ) :
    IsMarkovKernel (stepKernel E π n) :=
  ⟨fun _ ↦ PMF.toMeasure.isProbabilityMeasure _⟩

/-- **The law of the trajectory** from a start state: Ionescu–Tulcea applied to
the kernels the policy induces. -/
@[expose] public noncomputable def trajectoryLaw (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) : Measure (ℕ → S) :=
  Kernel.traj (X := fun _ ↦ S) (stepKernel E π) 0 fun _ ↦ s₀

public instance (E : ControlledMarkovProcess S A) (π : GoalPolicy S A) (s₀ : S) :
    IsProbabilityMeasure (trajectoryLaw E π s₀) := by
  unfold trajectoryLaw
  infer_instance

/-! ## The goal event is measurable

`achieveProb` below applies the trajectory law to `{ω | CompositeSatisfies Ψ …}`,
and this section proves that set is measurable, so the value is print's
probability and not merely the canonical outer-measure extension. The argument is
print's own reading of the semantics: a sub-goal inspects one state–action pair,
a state–action pair at time `t` is a function of the states up to `t`, *Now* and
*Next* fix the time, *Eventually* is a countable union over it, a sequential goal
is a countable union over the head's achievement time, and a composite goal is a
finite union over its disjuncts. -/

omit [DecidableEq S] in
/-- Every set of histories is measurable: `𝐒` is finite with measurable
singletons, so `GoalHistory S m` is a finite product of discrete spaces. -/
public theorem measurableSet_goalHistory {m : ℕ} (t : Set (GoalHistory S m)) :
    MeasurableSet t := by
  have hsingle : ∀ v : GoalHistory S m, MeasurableSet ({v} : Set (GoalHistory S m)) := by
    intro v
    rw [← Set.univ_pi_singleton]
    exact MeasurableSet.univ_pi fun i ↦ measurableSet_singleton (v i)
  rw [← Set.biUnion_of_singleton t]
  exact MeasurableSet.biUnion (Set.toFinite t).countable fun v _ ↦ hsingle v

omit [Fintype S] [DecidableEq S] [MeasurableSingletonClass S] in
/-- Reading off the states up to `m` is measurable. -/
public theorem measurable_toGoalHistory (m : ℕ) :
    Measurable fun ω : ℕ → S ↦ (fun i : ↥(Finset.Iic m) ↦ ω i) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

omit [DecidableEq S] in
/-- **The base case**: whether the pair at time `m` lies in a target set depends
on the states up to `m` alone. -/
public theorem measurableSet_statePairs_mem (π : GoalPolicy S A) (m : ℕ)
    (g : Finset (S × A)) :
    MeasurableSet {ω : ℕ → S | statePairs π ω m ∈ g} := by
  have hset : {ω : ℕ → S | statePairs π ω m ∈ g}
      = (fun ω : ℕ → S ↦ (fun i : ↥(Finset.Iic m) ↦ ω i)) ⁻¹'
        {h : GoalHistory S m | (h ⟨m, Finset.mem_Iic.mpr le_rfl⟩, π m h) ∈ g} := rfl
  rw [hset]
  exact measurable_toGoalHistory m (measurableSet_goalHistory _)

omit [DecidableEq S] in
/-- *Now* and *Next* pin the achievement time; *Eventually* adds a finite
minimality condition. -/
public theorem measurableSet_isAchievementTime (π : GoalPolicy S A) (α : SubGoal S A)
    (k T : ℕ) :
    MeasurableSet {ω : ℕ → S | IsAchievementTime α (fun t ↦ statePairs π ω (k + t)) T} := by
  simp only [IsAchievementTime]
  cases hop : α.op
  · by_cases hT : T = 0
    · subst hT; simpa using measurableSet_statePairs_mem π (k + 0) α.target
    · simp [hT]
  · by_cases hT : T = 1
    · subst hT; simpa using measurableSet_statePairs_mem π (k + 1) α.target
    · simp [hT]
  · have hmin : MeasurableSet
        {ω : ℕ → S | ∀ t < T, statePairs π ω (k + t) ∉ α.target} := by
      have hset : {ω : ℕ → S | ∀ t < T, statePairs π ω (k + t) ∉ α.target}
          = ⋂ t, ⋂ _ : t < T, {ω : ℕ → S | statePairs π ω (k + t) ∈ α.target}ᶜ := by
        ext ω; simp
      rw [hset]
      exact MeasurableSet.iInter fun t ↦ MeasurableSet.iInter fun _ ↦
        (measurableSet_statePairs_mem π (k + t) α.target).compl
    exact (measurableSet_statePairs_mem π (k + T) α.target).inter hmin

omit [DecidableEq S] in
/-- **The recursion**: satisfaction of a sequential goal on the trajectory
shifted by `k` is a countable union over the head's achievement time. -/
public theorem measurableSet_satisfies (π : GoalPolicy S A) :
    ∀ (ψ : SequentialGoal S A) (k : ℕ),
      MeasurableSet {ω : ℕ → S | Satisfies ψ fun t ↦ statePairs π ω (k + t)}
  | [], _ => by simp [Satisfies]
  | α :: rest, k => by
      have hset : {ω : ℕ → S | Satisfies (α :: rest) fun t ↦ statePairs π ω (k + t)}
          = ⋃ T : ℕ,
              ({ω : ℕ → S | IsAchievementTime α (fun t ↦ statePairs π ω (k + t)) T} ∩
                {ω : ℕ → S | Satisfies rest fun t ↦ statePairs π ω (k + T + 1 + t)}) := by
        ext ω
        simp only [Satisfies, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
          ← Nat.add_assoc]
      rw [hset]
      exact MeasurableSet.iUnion fun T ↦
        (measurableSet_isAchievementTime π α k T).inter
          (measurableSet_satisfies π rest (k + T + 1))

omit [DecidableEq S] in
/-- **The goal event is measurable.** A composite goal is a finite union of
sequential ones. -/
public theorem measurableSet_compositeSatisfies (π : GoalPolicy S A)
    (Ψ : CompositeGoal S A) :
    MeasurableSet {ω : ℕ → S | CompositeSatisfies Ψ (statePairs π ω)} := by
  have hset : {ω : ℕ → S | CompositeSatisfies Ψ (statePairs π ω)}
      = ⋃ ψ ∈ (Ψ : Set (SequentialGoal S A)),
          {ω : ℕ → S | Satisfies ψ fun t ↦ statePairs π ω (0 + t)} := by
    ext ω; simp [CompositeSatisfies]
  rw [hset]
  exact MeasurableSet.biUnion Ψ.finite_toSet.countable fun ψ _ ↦
    measurableSet_satisfies π ψ 0

/-! ## Achievement probability, and print's bound -/

/-- `P(τ ⊨ Ψ | π, s₀)`. -/
@[expose] public noncomputable def achieveProb (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) (Ψ : CompositeGoal S A) : ℝ≥0∞ :=
  trajectoryLaw E π s₀ {ω | CompositeSatisfies Ψ (statePairs π ω)}

omit [DecidableEq S] in
public theorem achieveProb_le_one (E : ControlledMarkovProcess S A) (π : GoalPolicy S A)
    (s₀ : S) (Ψ : CompositeGoal S A) : achieveProb E π s₀ Ψ ≤ 1 :=
  prob_le_one

/-- Print's *"best achievable"*, as a supremum rather than a maximum — see the
module note. -/
@[expose] public noncomputable def optimalProb (E : ControlledMarkovProcess S A)
    (s₀ : S) (Ψ : CompositeGoal S A) : ℝ≥0∞ :=
  ⨆ π : GoalPolicy S A, achieveProb E π s₀ Ψ

omit [DecidableEq S] in
public theorem achieveProb_le_optimalProb (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) (Ψ : CompositeGoal S A) :
    achieveProb E π s₀ Ψ ≤ optimalProb E s₀ Ψ :=
  le_iSup (fun π' ↦ achieveProb E π' s₀ Ψ) π

omit [DecidableEq S] in
public theorem optimalProb_le_one [Nonempty A] (E : ControlledMarkovProcess S A)
    (s₀ : S) (Ψ : CompositeGoal S A) : optimalProb E s₀ Ψ ≤ 1 :=
  iSup_le fun π ↦ achieveProb_le_one E π s₀ Ψ

omit [DecidableEq S] in
/-- Print's *"best achievable"* read over **trajectory-prefix** policies, which
is the class print's `max_{π'}` ranges over. -/
@[expose] public noncomputable def optimalProbFull (E : ControlledMarkovProcess S A)
    (s₀ : S) (Ψ : CompositeGoal S A) : ℝ≥0∞ :=
  ⨆ π : FullPolicy S A, achieveProb E (inducedPolicy π) s₀ Ψ

omit [DecidableEq S] in
/-- **Trajectory prefixes buy nothing.** The supremum over print's full-history
policies is the supremum over state policies, so the two readings of
`(δ,n)`-boundedness admit the same agents. This is the axis the goal layer used
to record as an unproved reading. -/
public theorem optimalProbFull_eq (E : ControlledMarkovProcess S A) (s₀ : S)
    (Ψ : CompositeGoal S A) : optimalProbFull E s₀ Ψ = optimalProb E s₀ Ψ := by
  refine le_antisymm (iSup_le fun π ↦ achieveProb_le_optimalProb E _ s₀ Ψ)
    (iSup_le fun π ↦ le_iSup_of_le (liftPolicy π) ?_)
  rw [inducedPolicy_liftPolicy]

/-- **All the analyst sees**, at print's own agent type. -/
@[expose] public def firstActionMapFull (π : FullAgent S A) (s₀ : S)
    (Ψ : CompositeGoal S A) : A :=
  inducedPolicy (π Ψ) 0 fun _ ↦ s₀

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] public theorem firstActionMapFull_lift (π : GoalConditionedAgent S A) :
    firstActionMapFull (fun Ψ ↦ liftPolicy (π Ψ)) = firstActionMap π := by
  funext s₀ Ψ
  rw [firstActionMapFull, inducedPolicy_liftPolicy]
  rfl

/-- **`(δ,n)`-bounded**, at print's multiplicative form: a failure *rate*
relative to the best achievable, at every goal of depth at most `n` and every
start state. -/
@[expose] public def IsDeltaBounded [Fintype A] [DecidableEq A] (E : ControlledMarkovProcess S A)
    (π : GoalConditionedAgent S A) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ Ψ ∈ compositeGoals n, ∀ s₀ : S,
    ENNReal.ofReal (1 - δ) * optimalProb E s₀ Ψ ≤ achieveProb E (π Ψ) s₀ Ψ

/-! ## The start state

`Kernel.traj` does not merely have the right first marginal: it fixes the
coordinates it is initialised at, pointwise on almost every trajectory. That is
what lets a policy read the start state off the history it is handed. -/

omit [DecidableEq S] in
/-- **Almost every trajectory starts where the law was started.** -/
public theorem trajectoryLaw_startState (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) :
    trajectoryLaw E π s₀ {ω | ω 0 = s₀} = 1 := by
  have hmeas : MeasurableSet {ω : ℕ → S | ω 0 = s₀} := by
    have hset : {ω : ℕ → S | ω 0 = s₀} = (fun ω : ℕ → S ↦ ω 0) ⁻¹' {s₀} := rfl
    rw [hset]
    exact (measurable_pi_apply 0) (measurableSet_singleton s₀)
  have h := Kernel.traj_map_updateFinset (X := fun _ ↦ S) (κ := stepKernel E π) (n := 0)
    (fun _ ↦ s₀)
  unfold trajectoryLaw
  conv_lhs => rw [← h]
  rw [Measure.map_apply (by fun_prop) hmeas]
  have hpre : (fun x : ℕ → S ↦ Function.updateFinset x (Finset.Iic 0) fun _ ↦ s₀) ⁻¹'
      {ω | ω 0 = s₀} = Set.univ := by
    ext ω
    simp [Function.updateFinset]
  rw [hpre]
  exact measure_univ

omit [DecidableEq S] in
public theorem eventually_startState (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) :
    ∀ᵐ ω ∂(trajectoryLaw E π s₀), ω 0 = s₀ := by
  have hmeas : MeasurableSet {ω : ℕ → S | ω 0 = s₀} := by
    have hset : {ω : ℕ → S | ω 0 = s₀} = (fun ω : ℕ → S ↦ ω 0) ⁻¹' {s₀} := rfl
    rw [hset]
    exact (measurable_pi_apply 0) (measurableSet_singleton s₀)
  rw [ae_iff]
  have hcompl : {ω : ℕ → S | ¬ ω 0 = s₀} = {ω : ℕ → S | ω 0 = s₀}ᶜ := rfl
  rw [hcompl, prob_compl_eq_zero_iff hmeas]
  exact trajectoryLaw_startState E π s₀

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The history a trajectory presents at time zero is the constant at its start
state, which is how a policy recovers `s₀` from what it is handed. -/
public theorem history_zero_const {ω : ℕ → S} {s₀ : S} (h : ω 0 = s₀) :
    (fun i : ↥(Finset.Iic (0 : ℕ)) ↦ ω i) = fun _ ↦ s₀ := by
  funext i
  have hi : (i : ℕ) = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
  rw [hi, h]

/-! ## Action-independent environments

Print's own myopic converse is stated over environments whose transition law
does not read the action. Nothing in `prob:rate` or `prob:corruption` excludes
them, and on them the state process is exogenous: the policy still decides which
state–action pairs a goal sees, but not which states occur. That is what makes
the splice below unconditional — no congruence lemma for `Kernel.traj` is
needed, because the two laws being compared are *the same measure*. -/

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
public theorem stepPMF_congr {E : ControlledMarkovProcess S A} (hE : E.ActionIndependent)
    (s : S) (a a' : A) : stepPMF E s a = stepPMF E s a' := by
  unfold stepPMF
  congr 1
  funext s'
  rw [hE s a a' s']

omit [DecidableEq S] in
public theorem stepKernel_congr {E : ControlledMarkovProcess S A} (hE : E.ActionIndependent)
    (π π' : GoalPolicy S A) (n : ℕ) : stepKernel E π n = stepKernel E π' n := by
  unfold stepKernel
  congr 1
  funext h
  rw [stepPMF_congr hE _ (π n h) (π' n h)]

omit [DecidableEq S] in
/-- **On an action-independent environment the trajectory law does not read the
policy at all.** The two measures are equal because the kernels Ionescu–Tulcea
composes along are equal, so no congruence lemma for `Kernel.traj` is needed. -/
public theorem trajectoryLaw_congr {E : ControlledMarkovProcess S A} (hE : E.ActionIndependent)
    (π π' : GoalPolicy S A) (s₀ : S) : trajectoryLaw E π s₀ = trajectoryLaw E π' s₀ := by
  have hk : stepKernel E π = stepKernel E π' := funext (stepKernel_congr hE π π')
  unfold trajectoryLaw
  simp only [hk]

omit [DecidableEq S] in
/-- **Achievement probability reads the policy only along trajectories starting
where the law starts.** Two policies agreeing on every history whose first entry
is `s₀` give the same probability at `s₀`. -/
public theorem achieveProb_congr {E : ControlledMarkovProcess S A} (hE : E.ActionIndependent)
    (π π' : GoalPolicy S A) (s₀ : S) (Ψ : CompositeGoal S A)
    (hagree : ∀ (t : ℕ) (h : GoalHistory S t),
      h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩ = s₀ → π t h = π' t h) :
    achieveProb E π s₀ Ψ = achieveProb E π' s₀ Ψ := by
  unfold achieveProb
  rw [trajectoryLaw_congr hE π π' s₀]
  refine measure_congr ?_
  filter_upwards [eventually_startState E π' s₀] with ω hω
  have hstate : statePairs π ω = statePairs π' ω := by
    funext t
    have hval : π t (fun i ↦ ω i) = π' t (fun i ↦ ω i) := hagree t _ hω
    simp only [statePairs, hval]
  show CompositeSatisfies Ψ (statePairs π ω) = CompositeSatisfies Ψ (statePairs π' ω)
  rw [hstate]

/-! ## The two ways a bounded agent is built -/

/-- **An outright win costs nothing to honour.** If the goal carries an
immediate-win disjunct for `(s₀, a)` and the agent opens with `a`, the goal is
achieved on every trajectory the law puts mass on — whatever the agent does
afterwards, and whatever the environment is. -/
public theorem achieveProb_eq_one_of_immediateWin [Fintype A] [DecidableEq A]
    (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) (Ψ : CompositeGoal S A) {a : A}
    {ψ : SequentialGoal S A} (hψ : ψ ∈ immediateWins s₀ a) (hmem : ψ ∈ Ψ)
    (hact : π 0 (fun _ ↦ s₀) = a) :
    achieveProb E π s₀ Ψ = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← trajectoryLaw_startState E π s₀]
  refine measure_mono fun ω hω ↦ ?_
  have hω0 : ω 0 = s₀ := hω
  refine compositeSatisfies_of_immediateWin hψ hmem (τ := statePairs π ω) ?_
  have hh : (fun i : ↥(Finset.Iic (0 : ℕ)) ↦ ω i) = fun _ ↦ s₀ := history_zero_const hω0
  simp only [statePairs, hh, hact, hω0]

omit [DecidableEq S] in
/-- **A near-optimal policy exists at every positive failure rate.** This is
ordinary supremum approximation, and it is why `δ > 0` needs no
optimal-policy-attainment theorem: nothing here claims the supremum is met. -/
public theorem exists_achieveProb_ge [Nonempty A] (E : ControlledMarkovProcess S A)
    (s₀ : S) (Ψ : CompositeGoal S A) {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ π : GoalPolicy S A,
      ENNReal.ofReal (1 - δ) * optimalProb E s₀ Ψ ≤ achieveProb E π s₀ Ψ := by
  classical
  rcases eq_or_ne (optimalProb E s₀ Ψ) 0 with h0 | h0
  · exact ⟨fun _ _ ↦ Classical.arbitrary A, by simp [h0]⟩
  · have htop : optimalProb E s₀ Ψ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (optimalProb_le_one E s₀ Ψ)
    have hlt1 : ENNReal.ofReal (1 - δ) < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
    have hmul : ENNReal.ofReal (1 - δ) * optimalProb E s₀ Ψ < optimalProb E s₀ Ψ := by
      have hstep := ENNReal.mul_lt_mul_left h0 htop hlt1
      rwa [one_mul] at hstep
    obtain ⟨π, hπ⟩ := lt_iSup_iff.mp hmul
    exact ⟨π, hπ.le⟩

/-- **The splice.** On an action-independent environment there is a
`(δ,n)`-bounded agent that opens with a prescribed action `a` at every
(start state, goal) pair where `a` wins outright, and at every goal outside
`𝚿_n`. The pairs left free are exactly the ones the counting lemma bounds:
goals of depth at most `n` carrying no immediate win for `(s, a)`.

The construction chooses a near-optimal policy for each pair and reads the pair
back off the history, which is legitimate because a history determines its own
start state. No optimal policy is used, and no attainment theorem. -/
public theorem exists_isDeltaBounded_prescribing [Fintype A] [DecidableEq A]
    {E : ControlledMarkovProcess S A} (hE : E.ActionIndependent) (n : ℕ) {δ : ℝ}
    (hδ0 : 0 < δ) (a : A) :
    ∃ π : GoalConditionedAgent S A, IsDeltaBounded E π n δ ∧
      ∀ (s : S) (Ψ : CompositeGoal S A),
        ¬ (Ψ ∈ compositeGoals n ∧ Disjoint Ψ (immediateWins s a)) →
        firstActionMap π s Ψ = a := by
  classical
  have hne : Nonempty A := ⟨a⟩
  choose Φ hΦ using fun p : S × CompositeGoal S A ↦
    exists_achieveProb_ge E p.1 p.2 hδ0
  refine ⟨fun Ψ t h ↦
    if Ψ ∈ compositeGoals n ∧
        Disjoint Ψ (immediateWins (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩) a) then
      Φ (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩, Ψ) t h else a, ?_, ?_⟩
  · intro Ψ hΨ s₀
    by_cases hd : Disjoint Ψ (immediateWins s₀ a)
    · have hcongr : achieveProb E
          (fun t (h : GoalHistory S t) ↦
            if Ψ ∈ compositeGoals n ∧
                Disjoint Ψ (immediateWins (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩) a) then
              Φ (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩, Ψ) t h else a) s₀ Ψ
          = achieveProb E (Φ (s₀, Ψ)) s₀ Ψ := by
        refine achieveProb_congr hE _ _ s₀ Ψ fun t h hh ↦ ?_
        rw [hh, if_pos ⟨hΨ, hd⟩]
      rw [hcongr]
      exact hΦ (s₀, Ψ)
    · obtain ⟨ψ, hψΨ, hψw⟩ := Finset.not_disjoint_iff.mp hd
      have hact : (fun t (h : GoalHistory S t) ↦
          if Ψ ∈ compositeGoals n ∧
              Disjoint Ψ (immediateWins (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩) a) then
            Φ (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le t)⟩, Ψ) t h else a) 0
          (fun _ ↦ s₀) = a := if_neg (fun hc ↦ hd hc.2)
      rw [achieveProb_eq_one_of_immediateWin E _ s₀ Ψ hψw hψΨ hact]
      have hle : ENNReal.ofReal (1 - δ) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      calc ENNReal.ofReal (1 - δ) * optimalProb E s₀ Ψ
          ≤ 1 * 1 := mul_le_mul' hle (optimalProb_le_one E s₀ Ψ)
        _ = 1 := one_mul _
  · intro s Ψ hns
    exact if_neg hns



/-- **Print's `(δ,n)`-bounded agent**, at print's own history type. -/
@[expose] public def IsDeltaBoundedFull [Fintype A] [DecidableEq A]
    (E : ControlledMarkovProcess S A) (π : FullAgent S A) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ Ψ ∈ compositeGoals n, ∀ s₀ : S,
    ENNReal.ofReal (1 - δ) * optimalProbFull E s₀ Ψ
      ≤ achieveProb E (inducedPolicy (π Ψ)) s₀ Ψ

/-- **The two boundedness clauses agree.** A state agent is `(δ,n)`-bounded
exactly when its lift is, in print's sense, so the witnesses built by
`exists_isDeltaBounded_prescribing` are print's agents and nothing about the
history type has to be taken on trust. -/
public theorem isDeltaBoundedFull_lift_iff [Fintype A] [DecidableEq A]
    {E : ControlledMarkovProcess S A} {π : GoalConditionedAgent S A} {n : ℕ} {δ : ℝ} :
    IsDeltaBoundedFull E (fun Ψ ↦ liftPolicy (π Ψ)) n δ ↔ IsDeltaBounded E π n δ := by
  constructor <;> intro h Ψ hΨ s₀ <;> have := h Ψ hΨ s₀ <;>
    simpa [optimalProbFull_eq, inducedPolicy_liftPolicy] using this

/-- An agent that is optimal at every goal and start state is `(δ,n)`-bounded for
every `δ ≥ 0`, which is print's `δ = 0` case and the only route to it that does
not need the attainment theorem: here optimality is *supplied*, not derived. -/
public theorem isDeltaBounded_of_achieve_eq_optimal [Fintype A] [DecidableEq A]
    {E : ControlledMarkovProcess S A}
    {π : GoalConditionedAgent S A} {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ Ψ, ∀ s₀ : S, achieveProb E (π Ψ) s₀ Ψ = optimalProb E s₀ Ψ) :
    IsDeltaBounded E π n δ := by
  intro Ψ _ s₀
  rw [h Ψ s₀]
  calc ENNReal.ofReal (1 - δ) * optimalProb E s₀ Ψ
      ≤ 1 * optimalProb E s₀ Ψ := by
        refine mul_le_mul_left ?_ _
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = optimalProb E s₀ Ψ := one_mul _

end AISafetyAtlas.Causal
