module

public import AISafetyAtlas.Wireheading.CRMDP
public import AISafetyAtlas.Decision.Expect
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Corrupt-reward MDPs with stochastic dynamics

`AISafetyAtlas.Wireheading.CRMDP` renders Everitt, Krakovna, Orseau, Hutter and
Legg's corrupt-reward MDP with a **deterministic** transition,
`State → Action → State`. Print's `T` is a Markov kernel, so that is a
specialization, and the coverage audit records it as the one axis the cluster is
narrow on.

This module widens the transition to a distribution and shows the existing
development is exactly the degenerate case: `stochRun` at a point-mass transition
is the point mass at `run`. Nothing already proved about the deterministic model
is lost, and nothing here re-proves it.

## Where the carrier came from

`AISafetyAtlas.Decision.MDP` is the rewardless triple `⟨S, A, T⟩` this module's
transition became, and the run below is its run. What follows is the record of
why that carrier has the shape it has.

## Why `PMF` and not a port

The reuse search ran over the Lean ecosystem by declaration shape rather than by
topic. Three independent libraries carry an MDP, and on the transition they
agree:

* `danlyng/Econlib` has the whole ladder: an unbounded deterministic MDP whose
  transition is a plain function into states, a finite MDP whose transition lands
  in its own finite-distribution type, and a stochastic MDP over measures.
* `nikhgarg/EconCSLib` has a bounded stochastic-reward MDP whose transition lands
  in `PMF` and whose boundedness field asserts the reward lies in
  `Set.Icc (0 : ℝ) 1` -- which is this cluster's `Reward` exactly.
* `lean-dojo/TorchLean` uses Mathlib's own Markov kernels from state-action pairs
  to states.

All three are Apache-2.0 and none is on this toolchain, so any of them would be a
port. **None was ported**, because the carrier they agree on is already in the
pinned Mathlib: `PMF` with `pure`, `bind` and `map`. The search's value was
telling us which shape three libraries independently converged on, not supplying
code — and `AISafetyAtlas.Decision.MDP` is that shape, written down once and
rewardless, as Turner and Tadepalli's Definition D.6 has it.

`PMF` rather than `Kernel` because the states here carry no measurable structure
and the source's state space is finite; a kernel would demand `MeasurableSpace`
instances the cluster has no use for. Moving to `Kernel` later is a further
widening on a different axis, and this module does not take it.

## What is here and what is not

Here: the stochastic run, that it specializes, the expected return, the source's
equation (3) for it, and Theorem 11 over stochastic dynamics.

The last of those costs almost nothing, and the reason is worth stating.
`Corruption.ComplementedClass` is abstract in its `returnValue`: it asks only
that returns in an environment and its complement sum to the horizon. So once the
**expected** return satisfies equation (3), Theorem 11 follows for stochastic
dynamics by the same route the deterministic model already takes, with no second
proof of the regret argument. The whole content of the widening is
`stochReturn_add_complement`.

**Not** here: the move from `PMF` to `Kernel`, discounting, and the source's
learnability results.
-/

namespace AISafetyAtlas.Wireheading.CRMDP

universe u v

variable {State : Type u} {Action : Type v}

/-! ## One run, generic in the monad

`AISafetyAtlas.Decision.detRun` and `AISafetyAtlas.Decision.MDP.run` are the same
recursion with different notions of "the next state": determined, or drawn.
`AISafetyAtlas.Decision.genRun` writes it once over an arbitrary monad, so that
the specialization theorems below are instances of a single fact rather than a
resemblance. All three live on the carrier.
-/

/--
**The stochastic run.** As in `CRMDP.run`, but the successor state is drawn from
the transition's distribution rather than determined, so the whole trajectory is
a distribution over state-and-history pairs.

This is `Decision.MDP.run` at this environment's channel and at a point-mass
policy; nothing is redefined, and print's `T` is the carrier's transition.
-/
@[expose] public noncomputable def stochRun (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) :
    ℕ → PMF (State × History State Action) :=
  M.run μ.channel (Decision.Policy.ofDet π) s₀

/--
**The deterministic model is the degenerate stochastic one.**

At a point-mass transition the trajectory distribution is the point mass at the
deterministic trajectory, so every statement `CRMDP` proves about `run` is a
statement about `stochRun` at `Decision.MDP.ofDet`. This is what makes the
widening free: the existing development is recovered rather than replaced.
-/
public theorem stochRun_ofDet (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stochRun (Decision.MDP.ofDet transition) μ π s₀ n
      = PMF.pure (run transition μ π s₀ n) :=
  Decision.MDP.run_ofDet transition μ.channel π s₀ n

/-- The state distribution after `n` steps. -/
@[expose] public noncomputable def stochStateAt (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) : PMF State :=
  M.stateAt μ.channel (Decision.Policy.ofDet π) s₀ n

/-- And it too specializes. -/
public theorem stochStateAt_ofDet (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stochStateAt (Decision.MDP.ofDet transition) μ π s₀ n
      = PMF.pure (stateAt transition μ π s₀ n) :=
  Decision.MDP.stateAt_ofDet transition μ.channel π s₀ n

/-- The distribution over **observed histories** after `n` steps.

This is the object print's equation (1) names: the interaction of a policy with a
corrupt-reward MDP induces a distribution over histories. Print's policy may be
stochastic and this one may not, so the distribution here comes from the dynamics
alone. -/
@[expose] public noncomputable def stochHistoryUpTo (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    PMF (History State Action) :=
  M.historyUpTo μ.channel (Decision.Policy.ofDet π) s₀ n

/-- At a point-mass transition it is the point mass at the deterministic history,
so `historyUpTo` is the degenerate case. -/
public theorem stochHistoryUpTo_ofDet (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stochHistoryUpTo (Decision.MDP.ofDet transition) μ π s₀ n
      = PMF.pure (historyUpTo transition μ π s₀ n) :=
  Decision.MDP.historyUpTo_ofDet transition μ.channel π s₀ n

/-! ## Expected rewards

`Corruption.ComplementedClass` asks for a real-valued return. Under stochastic
dynamics the state at a given step is a distribution, so the return is an
expectation. Mathlib's integral against a `PMF` needs a `MeasurableSpace` and a
`MeasurableSingletonClass` on the state type, which this cluster has no use for
and print does not assume, so the expectation is taken as the sum it is.
-/

/-- **The expected value of a reward under a distribution over states.**

This is `AISafetyAtlas.Decision.expect` at a reward-valued integrand. The two
clusters wrote the same expectation independently -- this one as a `tsum` because
a corrupt-reward MDP has no finiteness to spend, and the discounted value layer as
a finite sum -- and `Decision.Expect` is now the single implementation. -/
@[expose] public noncomputable def expectReward (p : PMF State) (f : State → Reward) : ℝ :=
  Decision.expect p fun s => (f s : ℝ)

/-- The summand of `expectReward` is summable, because rewards are at most one. -/
public theorem summable_expectReward (p : PMF State) (f : State → Reward) :
    Summable fun s => (p s).toReal * (f s : ℝ) :=
  Decision.summable_of_bounded p _ (fun s => (f s).2.1) (fun s => (f s).2.2)

/-- At a point mass the expectation is the value there. -/
public theorem expectReward_pure (a : State) (f : State → Reward) :
    expectReward (PMF.pure a) f = (f a : ℝ) :=
  Decision.expect_pure a _

/--
**Rewards and their complements have expectations summing to one.**

This is `Env.rewardComplement`'s defining property carried through the
expectation, and it is the only fact about expectations that equation (3) below
needs.
-/
public theorem expectReward_add_complement (p : PMF State) (f : State → Reward) :
    expectReward p f + expectReward p (fun s => Env.rewardComplement (f s)) = 1 := by
  rw [expectReward, expectReward, Decision.expect, Decision.expect,
    ← Summable.tsum_add (summable_expectReward p f)
      (summable_expectReward p fun s => Env.rewardComplement (f s))]
  rw [tsum_congr fun s => show
      (p s).toReal * (f s : ℝ) + (p s).toReal * ((Env.rewardComplement (f s) : Reward) : ℝ)
        = (p s).toReal by
    show (p s).toReal * (f s : ℝ) + (p s).toReal * (1 - (f s : ℝ)) = (p s).toReal
    ring]
  exact Decision.tsum_prob p

/-! ## The stochastic return, and the source's equation (3) -/

/--
**The trajectory distribution does not see the complement.**

The recursion mentions the environment only through `Env.observed`, and
`Env.observed_complement` says an environment and its complement induce the same
observed rewards. So the policy cannot tell them apart, which is the source's
indistinguishability step at the level of whole trajectories rather than single
observations.
-/
public theorem stochRun_complement (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stochRun M μ.complement π s₀ n = stochRun M μ π s₀ n :=
  Decision.MDP.run_congr_obs M (Env.channel_complement μ) (Decision.Policy.ofDet π) s₀ n

/-- Hence neither does the state distribution. -/
public theorem stochStateAt_complement (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stochStateAt M μ.complement π s₀ n = stochStateAt M μ π s₀ n :=
  Decision.MDP.stateAt_congr_obs M (Env.channel_complement μ) (Decision.Policy.ofDet π) s₀ n

/-- Finite-horizon **expected** true return: the source's `G_t(μ, π, s₀)` when the
dynamics are a distribution rather than a function. -/
@[expose] public noncomputable def stochReturnOver (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) : ℝ :=
  ∑ k ∈ Finset.range t, expectReward (stochStateAt M μ π s₀ (k + 1)) μ.trueReward

/-- The deterministic return is the degenerate expected one. -/
public theorem stochReturnOver_ofDet (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) :
    stochReturnOver (Decision.MDP.ofDet transition) t s₀ μ π
      = returnOver transition t s₀ μ π := by
  rw [stochReturnOver, returnOver]
  exact Finset.sum_congr rfl fun k _ => by
    rw [stochStateAt_ofDet, expectReward_pure]

/--
**The source's equation (3), under stochastic dynamics.**

Expected true returns in an environment and its complement sum to the horizon.
The visited-state *distributions* agree by `stochStateAt_complement`, and the
expected true rewards are complementary at each step by
`expectReward_add_complement`, so the two sums add termwise to `1`.
-/
public theorem stochReturn_add_complement (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) :
    stochReturnOver M t s₀ μ π + stochReturnOver M t s₀ μ.complement π = (t : ℝ) := by
  rw [stochReturnOver, stochReturnOver, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun k _ => show
      expectReward (stochStateAt M μ π s₀ (k + 1)) μ.trueReward +
          expectReward (stochStateAt M μ.complement π s₀ (k + 1)) μ.complement.trueReward = 1 by
    rw [stochStateAt_complement]
    exact expectReward_add_complement _ _]
  simp

/-! ## Theorem 11 over stochastic dynamics

Nothing below re-proves the regret argument. `Corruption.ComplementedClass` is
abstract in its return function and already carries Theorem 11; the two
paragraphs of work were `stochStateAt_complement` and
`expectReward_add_complement`, and `stochReturn_add_complement` above is what
they buy.
-/

/--
A corrupt-reward MDP with **stochastic** dynamics, together with the extrema the
regret argument needs.

Field for field this is `CRMDP.Model` with a distribution-valued transition and
expected returns. The three extrema are hypotheses here exactly as they are
there, and for the same reason: the source derives them from finiteness of the
reward grid, which this rendering does not impose.
-/
public structure StochModel (State Action : Type*) where
  /-- Shared stochastic dynamics: the rewardless Markov decision process the
  whole environment class runs on. -/
  mdp : Decision.MDP State Action
  /-- Finite horizon. -/
  horizon : ℕ
  /-- Start state. -/
  start : State
  /-- An optimal policy for each environment. -/
  bestPolicy : Env State → Policy State Action
  /-- It is optimal. -/
  bestPolicy_best : ∀ μ π,
    stochReturnOver mdp horizon start μ π ≤
      stochReturnOver mdp horizon start μ (bestPolicy μ)
  /-- An environment witnessing a policy's worst-case regret. -/
  worstEnvironment : Policy State Action → Env State
  /-- It witnesses it. -/
  worstEnvironment_worst : ∀ π μ,
    stochReturnOver mdp horizon start μ (bestPolicy μ) -
        stochReturnOver mdp horizon start μ π ≤
      stochReturnOver mdp horizon start (worstEnvironment π)
          (bestPolicy (worstEnvironment π)) -
        stochReturnOver mdp horizon start (worstEnvironment π) π
  /-- A policy with maximal worst-case regret. -/
  worstPolicy : Policy State Action
  /-- It has it. -/
  worstPolicy_worst : ∀ π,
    stochReturnOver mdp horizon start (worstEnvironment π)
          (bestPolicy (worstEnvironment π)) -
        stochReturnOver mdp horizon start (worstEnvironment π) π ≤
      stochReturnOver mdp horizon start (worstEnvironment worstPolicy)
          (bestPolicy (worstEnvironment worstPolicy)) -
        stochReturnOver mdp horizon start (worstEnvironment worstPolicy) worstPolicy

namespace StochModel

variable (M : StochModel State Action)

/--
Every stochastic corrupt-reward MDP is a `Corruption.ComplementedClass`.

The complement closure is structural for the same reason it is in the
deterministic case: `Env` is the full product of the true-reward and corruption
function spaces, so `Env.complement` lands back in the class with no side
condition. What changes is only which equation (3) discharges
`complement_return`.
-/
@[expose] public noncomputable def toComplementedClass :
    Corruption.ComplementedClass (Env State) (Policy State Action) where
  returnValue := stochReturnOver M.mdp M.horizon M.start
  horizon := (M.horizon : ℝ)
  complement := Env.complement
  complement_involutive := Env.complement_involutive
  complement_return := stochReturn_add_complement M.mdp M.horizon M.start
  bestPolicy := M.bestPolicy
  bestPolicy_best := M.bestPolicy_best
  worstEnvironment := M.worstEnvironment
  worstEnvironment_worst := M.worstEnvironment_worst
  worstPolicy := M.worstPolicy
  worstPolicy_worst := M.worstPolicy_worst

/--
**Everitt et al. Theorem 11 for stochastic corrupt-reward MDPs.**

Every policy suffers at least half the worst-case regret of a worst policy, for a
model whose transition is a distribution over successor states rather than a
function to one.

The deterministic statement `CRMDP.Model.everitt_theorem_eleven` is the special
case at a point-mass transition; `Model.toStoch_returnValue` below is the
identification that makes it one.
-/
public theorem everitt_theorem_eleven (π : Policy State Action) :
    M.toComplementedClass.worstCaseRegret M.toComplementedClass.worstPolicy / 2 ≤
      M.toComplementedClass.worstCaseRegret π :=
  M.toComplementedClass.everitt_theorem_eleven π

end StochModel

/-! ## The deterministic model is a stochastic model -/

namespace Model

variable (M : Model State Action)

/-- **Every deterministic corrupt-reward MDP is a stochastic one**, at the
point-mass transition. The three extrema hypotheses transport along
`stochReturnOver_ofDet`, which says the expected return at a point-mass
transition is the deterministic return. -/
@[expose] public noncomputable def toStoch : StochModel State Action where
  mdp := Decision.MDP.ofDet M.transition
  horizon := M.horizon
  start := M.start
  bestPolicy := M.bestPolicy
  bestPolicy_best := by
    simpa only [stochReturnOver_ofDet] using M.bestPolicy_best
  worstEnvironment := M.worstEnvironment
  worstEnvironment_worst := by
    simpa only [stochReturnOver_ofDet] using M.worstEnvironment_worst
  worstPolicy := M.worstPolicy
  worstPolicy_worst := by
    simpa only [stochReturnOver_ofDet] using M.worstPolicy_worst

/-- And it computes the same returns, so the deterministic Theorem 11 and the
stochastic one are statements about the same numbers. -/
public theorem toStoch_returnValue (μ : Env State) (π : Policy State Action) :
    M.toStoch.toComplementedClass.returnValue μ π
      = M.toComplementedClass.returnValue μ π :=
  stochReturnOver_ofDet M.transition M.horizon M.start μ π

end Model

end AISafetyAtlas.Wireheading.CRMDP
