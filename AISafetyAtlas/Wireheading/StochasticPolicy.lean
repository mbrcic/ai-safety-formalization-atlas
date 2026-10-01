module

public import AISafetyAtlas.Wireheading.StochasticCRMDP
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Corrupt-reward MDPs with possibly stochastic policies

`AISafetyAtlas.Wireheading.StochasticCRMDP` widened the transition from a
function to a distribution and carried Everitt, Krakovna, Orseau, Hutter and
Legg's Theorem 11 across it. One axis of the printed statement was left open.
Print's equation (1) quantifies over a **possibly stochastic** policy; every
policy there is a function `History State Action → Action`, so the induced
distribution averaged over the dynamics and not over the agent.

This module closes that axis. `StochPolicy` is a history-indexed distribution
over actions, `mixedRun` binds it into the recursion beside the transition, and
`mixedReturnOver` is the expected true return under both sources of randomness.
`StochPolicy.ofDet` embeds a deterministic policy as a point mass, and the four
specialization lemmas — `mixedRun_ofDet`, `mixedStateAt_ofDet`,
`mixedHistoryUpTo_ofDet` and `mixedReturnOver_ofDet` — say the previous
development is exactly the degenerate case. Nothing already proved is lost and
nothing is reproved.

## Why the widening costs one lemma rather than a second proof

`Corruption.ComplementedClass` is abstract in its `returnValue`: it asks only
that the returns of an environment and of its complement sum to the horizon. So
the whole content of this widening is `mixedReturn_add_complement`, and that in
turn rests on `mixedRun_complement` — the recursion mentions the environment
only through `Env.observed`, and `Env.observed_complement` says an environment
and its complement agree there.

Drawing the action from a distribution changes neither fact. That is *why* the
complement argument survives possibly stochastic policies, rather than merely
that it does: the agent's randomness is bound in on the outside of the step, and
the environment enters the step only through a channel the complement leaves
fixed.

## The two carriers of `MixedModel`

`MixedModel` takes an environment class `E` and a **policy class** `P`, each read
into its concrete type by a field. The policy class is what makes the three
extrema fields satisfiable once the policy quantifier widens: taking `P` to be
all of `StochPolicy State Action` with `pol := id` is print's own quantifier,
while `pol := StochPolicy.ofDet` recovers `StochModel`, which `StochModel.toMixed`
does. `StochModel.toMixed_returnValue` shows the two statements are about the
same numbers rather than merely analogous.

## What is not here

The three extrema are fields, as they are in `StochModel` and unlike
`AISafetyAtlas.Wireheading.RewardGrid`, where they are derived from finiteness.
Deriving them over a policy class that is itself a space of distributions takes
two steps, and neither is carried out here: the grid extrema over a
`AISafetyAtlas.Decision.MDP` first, then affinity for mixed policies, which is
the affine-functional argument named in `RewardGrid`'s header. The second alone
is not the obstruction. Neither is the move from `PMF` to `Kernel`, nor discounting.

**The first step is done, and it was not the refactor it looked like.**
`AISafetyAtlas.Decision.exists_max_of_truncates` derives both extrema over the
whole policy space for a drawn transition, from `MDP.run_congr_policy`: a run of
`n` steps consults a policy only on histories shorter than `n`, and over finite
observation and action alphabets there are finitely many of those. `CRMDP.Obs`
is `State × Reward` and so infinite, but `Decision.MDP.run` is generic in the
observation type, and a grid environment's real channel is finite. `History.mapObs`
and `MDP.stateAt_mapObs` relate a run to the same run at the alphabet underneath
it, so nothing had to be duplicated and no type had to change.
`AISafetyAtlas.Wireheading.RewardGrid.everitt_theorem_eleven_stochGridClass` is
the result: Theorem 11 over print's class, transition drawn, all three extrema
derived.

**Both steps are done, as of 2026-09-19, and neither was what it looked like.**
The first is `AISafetyAtlas.Decision.exists_max_of_truncates`, over a finite
alphabet reached by `Decision.MDP.stateAt_mapObs` rather than by changing any
type. The second is `Decision.MDP.run_update_decomp` with
`Decision.le_of_affine_of_det_le`: the run is affine in what the policy does at
one history, so replacing distributions by point masses one history at a time
bounds the mixed policies by the deterministic ones, and no mixture
decomposition or value recursion is involved.
`AISafetyAtlas.Wireheading.RewardGrid.everitt_theorem_eleven_fullMixedClass` is
the result, at every axis print states Theorem 11 with.

The three extrema below stay fields, and that is now a choice rather than a
debt: `MixedModel` is the abstract carrier, and a caller that wants them derived
takes the grid class instead.

A worked model inhabiting `MixedModel` — with a genuinely stochastic policy, not
a point mass, attaining the factor of two exactly — is in
`AISafetyAtlas.Examples.Wireheading.StochasticPolicy`.
-/

namespace AISafetyAtlas.Wireheading.CRMDP

universe u v

variable {State : Type u} {Action : Type v}

/-! ## Two facts about probabilities

Both are about `PMF` and neither mentions a corrupt-reward MDP; they sit beside
`Decision.tsum_prob` for the same reason it does, which is that the expected return is
taken as a sum rather than through Mathlib's `PMF` integral. -/

/-- A probability, read as a real, is at most one. -/
public theorem prob_toReal_le_one {α : Type*} (p : PMF α) (a : α) : (p a).toReal ≤ 1 := by
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_le_toReal (PMF.apply_ne_top p a) ENNReal.one_ne_top |>.mpr
    (PMF.coe_le_one p a)

/-- The two masses of a distribution on `Bool` sum to one. -/
public theorem prob_bool_add (p : PMF Bool) : (p false).toReal + (p true).toReal = 1 := by
  rw [← tsum_bool (f := fun b => (p b).toReal)]
  exact Decision.tsum_prob p

/-! ## Possibly stochastic policies -/

/-- A **possibly stochastic policy**: a history determines a distribution over
actions rather than an action.

This is `AISafetyAtlas.Decision.Policy` at the observation alphabet `Obs State`.
The policy is a parameter of the carrier's run and not a field of
`AISafetyAtlas.Decision.MDP`, because a bare Markov decision process has no
observation channel: what makes a policy here interesting is that it reads
observed rewards, which the dynamics do not supply. -/
@[expose] public def StochPolicy (State : Type u) (Action : Type v) : Type (max u v) :=
  Decision.Policy (Obs State) Action

/-- The point-mass policy induced by a deterministic one. -/
@[expose] public noncomputable def StochPolicy.ofDet (π : Policy State Action) :
    StochPolicy State Action :=
  Decision.Policy.ofDet π

/-- **The run against a possibly stochastic policy.**  This is the carrier's run
`AISafetyAtlas.Decision.MDP.run` outright: an MDP, an observation map, and a
policy over what is observed. -/
@[expose] public noncomputable def mixedRun (M : Decision.MDP State Action)
    (μ : Env State) (σ : StochPolicy State Action) (s₀ : State) :
    ℕ → PMF (State × History State Action) :=
  M.run μ.channel σ s₀

/-- At a point-mass policy the run is `stochRun` — by definition, since both are
the carrier's run and they differ only in the policy handed to it. -/
public theorem mixedRun_ofDet (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    mixedRun M μ (StochPolicy.ofDet π) s₀ n = stochRun M μ π s₀ n := rfl

/-- **The trajectory distribution does not see the complement**, even when the
action is drawn rather than determined. -/
public theorem mixedRun_complement (M : Decision.MDP State Action)
    (μ : Env State) (σ : StochPolicy State Action) (s₀ : State) (n : ℕ) :
    mixedRun M μ.complement σ s₀ n = mixedRun M μ σ s₀ n :=
  Decision.MDP.run_congr_obs M (Env.channel_complement μ) σ s₀ n

/-- The state distribution after `n` steps, under a possibly stochastic policy. -/
@[expose] public noncomputable def mixedStateAt (M : Decision.MDP State Action)
    (μ : Env State) (σ : StochPolicy State Action) (s₀ : State) (n : ℕ) : PMF State :=
  M.stateAt μ.channel σ s₀ n

/-- And it too specializes. -/
public theorem mixedStateAt_ofDet (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    mixedStateAt M μ (StochPolicy.ofDet π) s₀ n = stochStateAt M μ π s₀ n := rfl

/-- Hence the state distribution does not see the complement either. -/
public theorem mixedStateAt_complement (M : Decision.MDP State Action)
    (μ : Env State) (σ : StochPolicy State Action) (s₀ : State) (n : ℕ) :
    mixedStateAt M μ.complement σ s₀ n = mixedStateAt M μ σ s₀ n :=
  Decision.MDP.stateAt_congr_obs M (Env.channel_complement μ) σ s₀ n

/-- The distribution over **observed histories** after `n` steps: print's
equation (1), with both the dynamics and the agent contributing randomness. -/
@[expose] public noncomputable def mixedHistoryUpTo (M : Decision.MDP State Action)
    (μ : Env State) (σ : StochPolicy State Action) (s₀ : State) (n : ℕ) :
    PMF (History State Action) :=
  M.historyUpTo μ.channel σ s₀ n

/-- At a point-mass policy it is `stochHistoryUpTo`. -/
public theorem mixedHistoryUpTo_ofDet (M : Decision.MDP State Action)
    (μ : Env State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    mixedHistoryUpTo M μ (StochPolicy.ofDet π) s₀ n = stochHistoryUpTo M μ π s₀ n := rfl

/-- Finite-horizon **expected** true return against a possibly stochastic
policy: print's `G_t(μ, π, s₀)` with the expectation over both sources of
randomness print allows. -/
@[expose] public noncomputable def mixedReturnOver (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (μ : Env State) (σ : StochPolicy State Action) : ℝ :=
  ∑ k ∈ Finset.range t, expectReward (mixedStateAt M μ σ s₀ (k + 1)) μ.trueReward

/-- The deterministic-policy return is the degenerate case. -/
public theorem mixedReturnOver_ofDet (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (μ : Env State) (π : Policy State Action) :
    mixedReturnOver M t s₀ μ (StochPolicy.ofDet π) = stochReturnOver M t s₀ μ π := by
  rw [mixedReturnOver, stochReturnOver]
  exact Finset.sum_congr rfl fun k _ => by rw [mixedStateAt_ofDet]

/-- **The source's equation (3), at print's own quantifiers.** -/
public theorem mixedReturn_add_complement (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (μ : Env State) (σ : StochPolicy State Action) :
    mixedReturnOver M t s₀ μ σ + mixedReturnOver M t s₀ μ.complement σ = (t : ℝ) := by
  rw [mixedReturnOver, mixedReturnOver, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun k _ => show
      expectReward (mixedStateAt M μ σ s₀ (k + 1)) μ.trueReward +
          expectReward (mixedStateAt M μ.complement σ s₀ (k + 1)) μ.complement.trueReward = 1 by
    rw [mixedStateAt_complement]
    exact expectReward_add_complement _ _]
  simp

/-! ## Theorem 11 over stochastic dynamics and stochastic policies -/

/--
A corrupt-reward MDP with **stochastic dynamics and possibly stochastic
policies**, together with the extrema the regret argument needs.

Two carriers, and both of them earn their place.

`E` is the environment class, read into `Env State` by `env`. `StochModel` fixes
it to the whole of `Env State`; here it is a parameter, because a *class*
parameter is what makes the extrema fields satisfiable once the policy quantifier
widens. Print's own class is a proper subclass of `Env State` too, so the
parameter is closer to print rather than further from it. `complement_env` is
what ties the class's complement to the environment complement, and it is the
only thing equation (3) needs.

`P` is the policy class, read into `StochPolicy State Action` by `pol`. Taking
`pol := StochPolicy.ofDet` recovers `StochModel`; taking `P` to be
`StochPolicy State Action` itself and `pol := id` is print's "possibly
stochastic".
-/
public structure MixedModel (State : Type u) (Action : Type v)
    (E : Type*) (P : Type*) where
  /-- Shared stochastic dynamics: the rewardless Markov decision process the
  whole environment class runs on. -/
  mdp : Decision.MDP State Action
  /-- Finite horizon. -/
  horizon : ℕ
  /-- Start state. -/
  start : State
  /-- How a member of the class is read as an environment. -/
  env : E → Env State
  /-- How a member of the policy class is read as a possibly stochastic policy. -/
  pol : P → StochPolicy State Action
  /-- The class's complement operation. -/
  complement : E → E
  /-- It is an involution. -/
  complement_involutive : Function.Involutive complement
  /-- And it is the environment complement. -/
  complement_env : ∀ e, env (complement e) = (env e).complement
  /-- An optimal policy for each environment. -/
  bestPolicy : E → P
  /-- It is optimal. -/
  bestPolicy_best : ∀ e p,
    mixedReturnOver mdp horizon start (env e) (pol p) ≤
      mixedReturnOver mdp horizon start (env e) (pol (bestPolicy e))
  /-- An environment witnessing a policy's worst-case regret. -/
  worstEnvironment : P → E
  /-- It witnesses it. -/
  worstEnvironment_worst : ∀ p e,
    mixedReturnOver mdp horizon start (env e) (pol (bestPolicy e)) -
        mixedReturnOver mdp horizon start (env e) (pol p) ≤
      mixedReturnOver mdp horizon start (env (worstEnvironment p))
          (pol (bestPolicy (worstEnvironment p))) -
        mixedReturnOver mdp horizon start (env (worstEnvironment p)) (pol p)
  /-- A policy with maximal worst-case regret. -/
  worstPolicy : P
  /-- It has it. -/
  worstPolicy_worst : ∀ p,
    mixedReturnOver mdp horizon start (env (worstEnvironment p))
          (pol (bestPolicy (worstEnvironment p))) -
        mixedReturnOver mdp horizon start (env (worstEnvironment p)) (pol p) ≤
      mixedReturnOver mdp horizon start (env (worstEnvironment worstPolicy))
          (pol (bestPolicy (worstEnvironment worstPolicy))) -
        mixedReturnOver mdp horizon start (env (worstEnvironment worstPolicy))
          (pol worstPolicy)

namespace MixedModel

variable {E P : Type*} (M : MixedModel State Action E P)

/--
Every such model is a `Corruption.ComplementedClass`.

The only step is `complement_return`: `complement_env` moves the class's
complement onto `Env.complement`, and `mixedReturn_add_complement` is equation
(3) there.
-/
@[expose] public noncomputable def toComplementedClass :
    Corruption.ComplementedClass E P where
  returnValue := fun e p => mixedReturnOver M.mdp M.horizon M.start (M.env e) (M.pol p)
  horizon := (M.horizon : ℝ)
  complement := M.complement
  complement_involutive := M.complement_involutive
  complement_return := by
    intro e p
    rw [M.complement_env]
    exact mixedReturn_add_complement M.mdp M.horizon M.start (M.env e) (M.pol p)
  bestPolicy := M.bestPolicy
  bestPolicy_best := M.bestPolicy_best
  worstEnvironment := M.worstEnvironment
  worstEnvironment_worst := M.worstEnvironment_worst
  worstPolicy := M.worstPolicy
  worstPolicy_worst := M.worstPolicy_worst

/--
**Everitt et al. Theorem 11 at print's own quantifiers over the policy.**

Every policy suffers at least half the worst-case regret of a worst policy, for a
model whose transition is a distribution over successor states and whose policies
may randomise over actions.

Nothing of the regret argument is reproved: `Corruption.ComplementedClass` is
abstract in its return function, so `mixedReturn_add_complement` is the whole
content of this widening, exactly as `stochReturn_add_complement` was of the
previous one.
-/
public theorem everitt_theorem_eleven (p : P) :
    M.toComplementedClass.worstCaseRegret M.toComplementedClass.worstPolicy / 2 ≤
      M.toComplementedClass.worstCaseRegret p :=
  M.toComplementedClass.everitt_theorem_eleven p

end MixedModel

/-! ## The deterministic-policy model is the degenerate case -/

namespace StochModel

variable (M : StochModel State Action)

/-- **Every stochastic corrupt-reward MDP is a mixed one**, at the policy class
of point masses. The three extrema hypotheses transport along
`mixedReturnOver_ofDet`, which says the expected return against a point-mass
policy is the return against the deterministic policy it concentrates on. -/
@[expose] public noncomputable def toMixed :
    MixedModel State Action (Env State) (Policy State Action) where
  mdp := M.mdp
  horizon := M.horizon
  start := M.start
  env := id
  pol := StochPolicy.ofDet
  complement := Env.complement
  complement_involutive := Env.complement_involutive
  complement_env := fun _ => rfl
  bestPolicy := M.bestPolicy
  bestPolicy_best := by
    simpa only [id_eq, mixedReturnOver_ofDet] using M.bestPolicy_best
  worstEnvironment := M.worstEnvironment
  worstEnvironment_worst := by
    simpa only [id_eq, mixedReturnOver_ofDet] using M.worstEnvironment_worst
  worstPolicy := M.worstPolicy
  worstPolicy_worst := by
    simpa only [id_eq, mixedReturnOver_ofDet] using M.worstPolicy_worst

/-- And it computes the same returns, so the two Theorem 11 statements are about
the same numbers. -/
public theorem toMixed_returnValue (μ : Env State) (π : Policy State Action) :
    M.toMixed.toComplementedClass.returnValue μ π
      = M.toComplementedClass.returnValue μ π :=
  mixedReturnOver_ofDet M.mdp M.horizon M.start μ π

end StochModel

end AISafetyAtlas.Wireheading.CRMDP

