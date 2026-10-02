module

public import AISafetyAtlas.Decision.MDP
public import AISafetyAtlas.Wireheading.Corruption
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A corrupt-reward MDP, and the complement construction inside it

`AISafetyAtlas.Wireheading.Corruption` proves the half-maximal regret bound from
`ComplementedClass`, which records only the *consequence* of the source's
construction: complement closure together with attained extrema.  Nothing there
builds a corrupt-reward MDP, so the source's hypotheses never appear.

This module supplies the missing structure and derives that consequence.

## The dynamics are not this module's

`run`, `stateAt` and `historyUpTo` are `AISafetyAtlas.Decision.detRun` and its
projections, at the observation map `Env.channel`. The dynamics live on the
rewardless carrier `AISafetyAtlas.Decision.MDP`, which has a transition and
nothing else; the reward, the corruption channel and the observation map are
what this module adds on top. In particular the **policy type is not part of the
carrier**: a policy here reads the observed history *including corrupted
rewards*, which is the whole point of the cluster, and a bare Markov decision
process has no observation channel at all.

## What is modelled

Following Everitt, Krakovna, Orseau, Hutter and Legg, *Reinforcement Learning
with a Corrupted Reward Channel* (IJCAI 2017; long version
<https://arxiv.org/abs/1705.08417>):

* states, actions, and a deterministic transition function fixed for one
  `Model`;
* a true reward function `Ṙ : S → [0,1]` and a corruption function
  `C : S → [0,1] → [0,1]`, which vary across the class;
* the observed reward `R̂(s) = C_s(Ṙ(s))`;
* histories labelled by observed rewards, and policies that see them;
* finite-horizon true return.

The class is *complete* by construction: an environment is any pair of a true
reward and a corruption function over the fixed dynamics, so the complement of a
member is automatically a member.  That is the structural form of the source's
"the hypothesis classes contain all functions".

## What is proved

* `observed_complement`: `Ṙ⁻(s) = 1 - Ṙ(s)` with `C⁻_s(x) = C_s(1 - x)` leaves
  the observed reward unchanged.  This is the source's indistinguishability
  step, and it is what makes the argument bite: it is proved, not assumed.
* `history_complement`: consequently *no* policy can separate an environment
  from its complement, since both generate the identical observed history.
* `return_add_complement`: the source's equation (3), `G_t(μ,π) + G_t(μ⁻,π) = t`,
  for the unit-scaled reward range.
* `toComplementedClass`: packaging as a `ComplementedClass`, whence
  `everitt_theorem_eleven` applies at the MDP level.

## Explicit non-claims

* **Deterministic transitions.**  The source uses a stochastic kernel and
  reasons about the induced measure over histories.  Here the transition is a
  function and `history_complement` is an equality of histories rather than of
  measures.  The stochastic case is not covered.
* **One fixed transition.** The source's complete CRMDP hypothesis class may
  range over transition kernels as well as true-reward and corruption
  functions. One Lean `Model` fixes its transition and ranges only over the
  full product of true-reward and corruption functions. This is enough for the
  complement argument, but is a specialization of the source class.
* **Attained extrema are hypotheses, not derived.**  `bestPolicy`,
  `worstEnvironment` and `worstPolicy` are supplied as arguments.  In the source
  they follow from finiteness of the state, action and reward-grid sets; that
  derivation is not carried out, because the policy type here is a function
  space and no finiteness argument is given for it.
* **No uniform discretization.**  The source restricts rewards to a finite
  uniform grid in `[0,1]`. Rewards here range over the whole closed interval.
  Boundedness is retained because it is load-bearing for nonzero models with
  attained worst environments; finiteness, and hence the source's generic
  derivation of extrema, is still absent.
* **Not decoupled feedback** and not the source's later learnability results.

Survey row: **BY-039**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.CRMDP

/-- The source's unit-scaled reward range, without its finite-grid restriction. -/
public abbrev Reward : Type := Set.Icc (0 : ℝ) 1

/-- One observed step: the state reached and the reward observed there. -/
public abbrev Obs (State : Type*) : Type _ := State × Reward

/--
An observed history in the source's shape: the initial observation followed by
the actions taken and observations reached.

This is `AISafetyAtlas.Decision.History` at the observation alphabet `Obs State`;
the carrier leaves the alphabet a parameter precisely because what an agent sees
is not part of the dynamics.
-/
public abbrev History (State Action : Type*) : Type _ :=
  Decision.History (Obs State) Action

/-- A policy sees the observed history, **including observed rewards**, and picks
an action.  This is what makes the indistinguishability step non-trivial, and it
is why the policy type is not a field of `AISafetyAtlas.Decision.MDP`: a bare
Markov decision process has no observation channel to corrupt. -/
public abbrev Policy (State Action : Type*) : Type _ :=
  Decision.DetPolicy (Obs State) Action

/--
An environment: a true reward function and a corruption function over fixed
dynamics.

The dynamics are *not* part of this `Env`: one Lean `Model` fixes them while
`Ṙ` and `C` range over their full function spaces. The source's general
hypothesis class can also range over transition kernels, so fixing the
transition is a specialization. Since `Env` is the full product of the
remaining two function spaces, it is closed under the complement below.
-/
public structure Env (State : Type*) where
  /-- The true reward at a state, the source's `Ṙ`. -/
  trueReward : State → Reward
  /-- The corruption channel at a state, the source's `C_s`. -/
  corruption : State → Reward → Reward

namespace Env

variable {State : Type*}

/-- The observed reward `R̂(s) = C_s(Ṙ(s))`. -/
@[expose] public def observed (μ : Env State) (s : State) : Reward :=
  μ.corruption s (μ.trueReward s)

/-- Complement a unit-interval reward. -/
@[expose] public def rewardComplement (x : Reward) : Reward :=
  ⟨1 - x.1, by
    constructor
    · linarith [x.2.2]
    · linarith [x.2.1]⟩

/-- Reward complementation is involutive. -/
public theorem rewardComplement_involutive :
    Function.Involutive rewardComplement := by
  intro x
  apply Subtype.ext
  simp [rewardComplement]

/--
The complement environment `μ⁻`: negate the true reward within `[0,1]` and
pre-compose the corruption channel with the same negation.
-/
@[expose] public def complement (μ : Env State) : Env State where
  trueReward := fun s => rewardComplement (μ.trueReward s)
  corruption := fun s x => μ.corruption s (rewardComplement x)

/-- Complementing twice is the identity. -/
public theorem complement_involutive :
    Function.Involutive (complement (State := State)) := by
  intro μ
  cases μ with
  | mk r c =>
      have hr : (fun s => rewardComplement (rewardComplement (r s))) = r := by
        funext s
        exact rewardComplement_involutive (r s)
      have hc : (fun s x => c s (rewardComplement (rewardComplement x))) = c := by
        funext s x
        rw [rewardComplement_involutive]
      simp only [complement]
      rw [hr, hc]

/--
**Indistinguishability.**  An environment and its complement induce the same
observed reward function.

This is the source's load-bearing step: `C_s(Ṙ(s)) = C⁻_s(Ṙ⁻(s))`.
-/
public theorem observed_complement (μ : Env State) (s : State) :
    μ.complement.observed s = μ.observed s := by
  change μ.corruption s (rewardComplement (rewardComplement (μ.trueReward s))) =
    μ.corruption s (μ.trueReward s)
  rw [rewardComplement_involutive]

/--
**The observation channel of an environment**: the state reached, labelled by the
reward observed there.

This is the observation map `AISafetyAtlas.Decision.MDP.run` takes.  Everything
this cluster proves about complements being invisible to a trajectory is
`Decision.MDP.run_congr_obs` — the run sees the world only through this map —
together with `channel_complement` below.
-/
@[expose] public def channel (μ : Env State) (s : State) : Obs State :=
  (s, μ.observed s)

/-- **An environment and its complement present the same channel.**  This is
`observed_complement` in the form the carrier's run consumes. -/
public theorem channel_complement (μ : Env State) (s : State) :
    μ.complement.channel s = μ.channel s := by
  rw [channel, channel, observed_complement]

end Env

/-! ## Trajectories and observed histories -/

variable {State Action : Type*}

/--
One run of the system: after `n` steps, the state reached and the observed
history, defined together because the policy's next action depends on the
history so far.
-/
@[expose] public def run (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) :
    ℕ → State × History State Action :=
  Decision.detRun transition (Env.channel μ) π s₀

/-- The state reached after `n` steps. -/
@[expose] public def stateAt (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) : State :=
  Decision.detStateAt transition (Env.channel μ) π s₀ n

/-- The observed history after `n` steps: the states visited, each labelled by
the reward observed there, together with every action taken. -/
@[expose] public def historyUpTo (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    History State Action :=
  Decision.detHistoryUpTo transition (Env.channel μ) π s₀ n

/--
**No policy separates an environment from its complement.**

Both the visited states and the observed history coincide at every step, so a
policy, which sees only the observed history, behaves identically in `μ` and
`μ⁻`.
-/
public theorem run_complement (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) : ∀ n : ℕ,
    run transition μ.complement π s₀ n = run transition μ π s₀ n :=
  Decision.detRun_congr_obs transition (Env.channel_complement μ) π s₀

/-- Visited states agree between an environment and its complement. -/
public theorem stateAt_complement (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stateAt transition μ.complement π s₀ n = stateAt transition μ π s₀ n :=
  Decision.detStateAt_congr_obs transition (Env.channel_complement μ) π s₀ n

/-- Observed histories agree between an environment and its complement. -/
public theorem history_complement (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    historyUpTo transition μ.complement π s₀ n =
      historyUpTo transition μ π s₀ n :=
  Decision.detHistoryUpTo_congr_obs transition (Env.channel_complement μ) π s₀ n

/-- Finite-horizon true return: the sum of true rewards over the first `t`
transitions, the source's `G_t(μ, π, s₀)`. -/
@[expose] public def returnOver (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) : ℝ :=
  ∑ k ∈ Finset.range t,
    (μ.trueReward (stateAt transition μ π s₀ (k + 1)) : ℝ)

/--
**The source's equation (3).**  True returns in an environment and its
complement sum to the horizon.

The visited states agree by `history_complement`, and the true rewards are
pointwise complementary, so the two sums add termwise to `1` each.
-/
public theorem return_add_complement (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) :
    returnOver transition t s₀ μ π +
        returnOver transition t s₀ μ.complement π = (t : ℝ) := by
  unfold returnOver
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ k ∈ Finset.range t,
      (μ.trueReward (stateAt transition μ π s₀ (k + 1)) : ℝ) +
        (μ.complement.trueReward
          (stateAt transition μ.complement π s₀ (k + 1)) : ℝ) = 1 := by
    intro k _
    rw [stateAt_complement transition μ π s₀ (k + 1)]
    show (μ.trueReward _ : ℝ) + (1 - (μ.trueReward _ : ℝ)) = 1
    linarith
  rw [Finset.sum_congr rfl hterm]
  simp

/-! ## Definition 10 as printed, and why the proof of Theorem 11 cannot use it

The source defines the return twice and the two do not agree. Definition 10
prints `Ġ_t(μ, π, s₀) = 𝔼[∑_{k=0}^{t} Ṙ(s_k)]`, which counts the start state and
has `t + 1` terms. The proof of Theorem 11 writes an undotted `G_t`, defines it
nowhere, and computes with `∑_{k=1}^{t}` in the display under equation (3).

`returnOver` above is the proof's sum. The two declarations here render the
printed Definition 10 instead, and settle which of the two equation (3) admits:
the printed one makes it read `t + 1`, so `return_add_complement` is false for
it and the whole regret argument collapses. This is recorded rather than
silently resolved.
-/

/-- **Definition 10 exactly as printed**: `Ġ_t`, summing the true reward from
the start state, so `t + 1` terms rather than `returnOver`'s `t`. -/
@[expose] public def returnWithStart (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) : ℝ :=
  ∑ k ∈ Finset.range (t + 1),
    (μ.trueReward (stateAt transition μ π s₀ k) : ℝ)

/-- The printed return is the proof's return plus the start state's reward. -/
public theorem returnWithStart_eq_returnOver_add (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) :
    returnWithStart transition t s₀ μ π =
      returnOver transition t s₀ μ π + (μ.trueReward s₀ : ℝ) := by
  unfold returnWithStart returnOver
  rw [Finset.sum_range_succ']
  simp [stateAt, Decision.detStateAt, Decision.detRun, add_comm]

/--
**Print's equation (3) fails for print's own Definition 10.**

With the printed `Ġ_t` the complementary returns sum to `t + 1`, not to `t`, so
the identity the proof of Theorem 11 calls equation (3) is unavailable at the
definition the paper actually gives. The atlas follows the proof.
-/
public theorem returnWithStart_add_complement (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) :
    returnWithStart transition t s₀ μ π +
        returnWithStart transition t s₀ μ.complement π = (t : ℝ) + 1 := by
  rw [returnWithStart_eq_returnOver_add, returnWithStart_eq_returnOver_add,
    show ((μ.complement.trueReward s₀ : ℝ)) = 1 - (μ.trueReward s₀ : ℝ) from rfl]
  have h := return_add_complement transition t s₀ μ π
  linarith

/--
**The discrepancy does not reach Definition 10's regret.**

`Reg` is a difference of two returns in the same environment from the same start
state, so the start-state term the printed `Ġ` adds cancels. Definition 10's
regret is therefore the regret the atlas builds on `returnOver`, and the
`k = 0` versus `k = 1` disagreement bites in exactly one place: equation (3),
where the returns are added rather than subtracted.
-/
public theorem returnWithStart_sub (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π π' : Policy State Action) :
    returnWithStart transition t s₀ μ π' - returnWithStart transition t s₀ μ π =
      returnOver transition t s₀ μ π' - returnOver transition t s₀ μ π := by
  rw [returnWithStart_eq_returnOver_add, returnWithStart_eq_returnOver_add]
  ring

/-- The inconsistency, stated as such: the printed return never satisfies
equation (3). -/
public theorem returnWithStart_add_complement_ne (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) :
    returnWithStart transition t s₀ μ π +
        returnWithStart transition t s₀ μ.complement π ≠ (t : ℝ) := by
  rw [returnWithStart_add_complement]
  linarith

/--
A corrupt-reward MDP together with the extrema the regret argument needs.

The dynamics, horizon and start state are shared by the whole environment class.
The three extrema fields are hypotheses, not derived; see the module's
non-claims.
-/
public structure Model (State Action : Type*) where
  /-- Shared deterministic dynamics. -/
  transition : State → Action → State
  /-- Finite horizon. -/
  horizon : ℕ
  /-- Start state. -/
  start : State
  /-- An optimal policy for each environment. -/
  bestPolicy : Env State → Policy State Action
  /-- It is optimal. -/
  bestPolicy_best : ∀ μ π,
    returnOver transition horizon start μ π ≤
      returnOver transition horizon start μ (bestPolicy μ)
  /-- An environment witnessing a policy's worst-case regret. -/
  worstEnvironment : Policy State Action → Env State
  /-- It witnesses it. -/
  worstEnvironment_worst : ∀ π μ,
    returnOver transition horizon start μ (bestPolicy μ) -
        returnOver transition horizon start μ π ≤
      returnOver transition horizon start (worstEnvironment π)
          (bestPolicy (worstEnvironment π)) -
        returnOver transition horizon start (worstEnvironment π) π
  /-- A policy with maximal worst-case regret. -/
  worstPolicy : Policy State Action
  /-- It has it. -/
  worstPolicy_worst : ∀ π,
    returnOver transition horizon start (worstEnvironment π)
          (bestPolicy (worstEnvironment π)) -
        returnOver transition horizon start (worstEnvironment π) π ≤
      returnOver transition horizon start (worstEnvironment worstPolicy)
          (bestPolicy (worstEnvironment worstPolicy)) -
        returnOver transition horizon start (worstEnvironment worstPolicy) worstPolicy

namespace Model

variable (M : Model State Action)

/--
Every corrupt-reward MDP is a `ComplementedClass`.

Completeness of the hypothesis classes is structural here: `Env` is the full
product of the true-reward and corruption function spaces, so `Env.complement`
lands back in the class with no side condition. `complement_return` is the
source's equation (3), proved rather than assumed.
-/
@[expose] public def toComplementedClass :
    Corruption.ComplementedClass (Env State) (Policy State Action) where
  returnValue := returnOver M.transition M.horizon M.start
  horizon := (M.horizon : ℝ)
  complement := Env.complement
  complement_involutive := Env.complement_involutive
  complement_return := return_add_complement M.transition M.horizon M.start
  bestPolicy := M.bestPolicy
  bestPolicy_best := M.bestPolicy_best
  worstEnvironment := M.worstEnvironment
  worstEnvironment_worst := M.worstEnvironment_worst
  worstPolicy := M.worstPolicy
  worstPolicy_worst := M.worstPolicy_worst

/--
**Everitt et al. Theorem 11 at the corrupt-reward-MDP level.**

Every policy suffers at least half the worst-case regret of a worst policy, now
stated for a model that actually carries states, actions, transitions, a true
reward, a corruption channel, observed rewards and finite-horizon returns.

The complement construction is verified inside the model rather than recorded as
an assumption: `Env.observed_complement` proves indistinguishability and
`return_add_complement` proves the complementary returns.
-/
public theorem everitt_theorem_eleven (π : Policy State Action) :
    M.toComplementedClass.worstCaseRegret M.toComplementedClass.worstPolicy / 2 ≤
      M.toComplementedClass.worstCaseRegret π :=
  M.toComplementedClass.everitt_theorem_eleven π

/-- The half-maximal regret certificate consumed by the BY-011 bridge. -/
public theorem halfMaximalRegretBound :
    AISafetyAtlas.Preference.HalfMaximalRegretBound M.toComplementedClass.toRegretModel :=
  M.toComplementedClass.halfMaximalRegretBound

/--
**Armstrong and Mindermann §4.1.2, at the corrupt-reward-MDP level.**

For any observed human behaviour and any policy the agent might follow, some
environment in the class both remains compatible with the observation and
inflicts at least half-maximal regret on the agent.

This is the combination Armstrong and Mindermann make: their Theorem 1 supplies
the compatible planner, and Everitt et al. Theorem 11 supplies the bound. The
bound is no longer assumed anywhere: it is discharged by
`Model.halfMaximalRegretBound`, which is proved from the complement
construction inside this model.
-/
public theorem cannot_rule_out_half_maximal_regret
    (πh πa : Policy State Action) :
    ∃ (μ : Env State)
      (p : AISafetyAtlas.Preference.Planner (Env State) (Policy State Action)),
      AISafetyAtlas.Preference.Explains p μ πh ∧
        M.toComplementedClass.toRegretModel.worstCaseRegret
            M.toComplementedClass.toRegretModel.worstPolicy / 2 ≤
          M.toComplementedClass.toRegretModel.regret μ πa :=
  M.toComplementedClass.toRegretModel.cannot_rule_out_half_maximal_regret
    M.halfMaximalRegretBound πh πa

end Model

end AISafetyAtlas.Wireheading.CRMDP
