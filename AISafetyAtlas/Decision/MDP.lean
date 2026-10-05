module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Fintype.Vector

/-!
# A rewardless Markov decision process, and the run it induces

The atlas had no `MDP`. What it had was a distribution-valued transition inside
`AISafetyAtlas.Wireheading.CRMDP` with a docstring saying it was the shape of
one, and a recursion beside it that unrolled the transition against a policy.
This module supplies the carrier, and the run moves onto it.

## The carrier, and why it has no reward

`MDP` is `⟨S, A, T⟩` with `T : S → A → PMF S` and **nothing else**. That is
Turner and Tadepalli, *Parametrically Retargetable Decision-Makers Tend To Seek
Power* (arXiv:2206.13477v2), as restated at their Definition D.6 -- which they
attribute in turn to Turner et al. 2021 -- naming exactly this triple a
*rewardless MDP*; the reward is what a consumer adds.

**Corrected 2026-09-10.** This paragraph said three Lean libraries outside this
repository "independently converged on the same split". They did not, and the
claim had been checked in the wrong direction: what those trees agree on is that
the *transition* is a standalone distribution-valued function, not that the
carrier is rewardless. Every external MDP structure opened on 2026-09-10 puts
the **reward inside the structure**, and two of the three put the discount there
as well -- Econlib/Optimization/DynamicProgramming/Core/MDP.lean carries
`reward` together with a discount and its two bounds;
AppliedModelingLib/Foundations/Probability/MDP.lean carries `reward`; and
proofs/GoodhartProofs/MDP/Defs.lean in audieleon/goodhart carries both. The
TorchLean carriers were not re-examined on this axis and nothing is claimed of
them here.

The split below is therefore this repository's, taken from D.6 rather than from
the ecosystem, and it is taken because `AISafetyAtlas.Wireheading.CRMDP` needs
it: its reward is a field of an environment ranging over a class, not of the
dynamics, which no carrier with a reward field can express.

Two differences from Definition D.6 are deliberate and neither is a
strengthening. D.6 requires `S` and `A` **finite**; nothing here does, and no
statement below needs it. D.6 also carries a discount rate as a variable; there
is no discounting here at all, because the finite-horizon consumer sums
undiscounted.

`PMF` rather than `MeasureTheory.Kernel` because the state type carries no
measurable structure, and every consumer so far has a finite state set. Moving
to `Kernel` is a widening on a different axis and this module does not take it.

## The run, and the boundary that fixes its shape

**The policy type is not part of the MDP.** A bare MDP has no observation
channel; a policy that reads a corrupted reward reads something the dynamics do
not supply. So the run is parameterised by three things — an MDP, an
**observation map** `obs : State → Obs`, and a policy over what is observed —
and a consumer chooses the observation map. `AISafetyAtlas.Wireheading.CRMDP`
passes `fun s => (s, μ.observed s)`, which is why an environment and its
complement are indistinguishable to it.

That parameterisation buys the consumer's load-bearing lemma outright:
`MDP.run_congr_obs` says the run depends on the environment **only** through the
observation map. Everything the corrupt-reward cluster proves about complements
being invisible to a trajectory is that lemma plus the fact that complementing
does not change the observed reward.

## What is here

* `MDP`, `MDP.ofDet`, `History`, `Policy`, `DetPolicy`, `Policy.ofDet`.
* `detRun`, `detStateAt`, `detHistoryUpTo` — the determined run, for a
  deterministic transition and a deterministic policy.
* `MDP.run`, `MDP.stateAt`, `MDP.historyUpTo` — the drawn run.
* `run_congr_obs` and its projections: the run sees the environment only through
  `obs`.
* `run_history_length`, `run_congr_policy`, `stateAt_congr_policy`: a run of `n`
  steps sees a policy only on histories shorter than `n`.
* `TruncHist`, `exists_max_of_truncates`, `exists_min_of_truncates`: hence, over
  **finite** observation and action alphabets, any quantity a run of `n` steps
  determines attains its extrema over the whole policy space, which is itself
  infinite. This is the drawn-transition counterpart of the reduction
  `AISafetyAtlas.Wireheading.RewardGrid` does by hand through `Fin t → Action`.
* `run_ofDet` and its projections: at a point-mass transition and a point-mass
  policy the drawn run is the point mass at the determined one, so the
  determined development is recovered rather than replaced.
* `genRun`, `genRun_id`, `genRun_pmf`: the two runs are one recursion at two
  monads, which is why the specialization lemmas are instances of a single fact.

No AI-system bridge is asserted; this is a carrier.
-/

namespace AISafetyAtlas.Decision

universe u v w

/--
**A rewardless Markov decision process**, Turner and Tadepalli's Definition D.6:
a state type, an action type, and a transition sending a state and an action to
a distribution over successor states.

There is no reward, no discount and no start state. A consumer that needs a
reward carries it separately — in `AISafetyAtlas.Wireheading.CRMDP` the reward
ranges over an environment class while the dynamics stay fixed, which is only
expressible because the dynamics are a separate object.

Unlike Definition D.6 the state and action types are not required to be finite.
-/
public structure MDP (State : Type u) (Action : Type v) where
  /-- The transition kernel, print's `T : S × A → Δ(S)`. -/
  transition : State → Action → PMF State

namespace MDP

variable {State : Type u} {Action : Type v} {Obs : Type w}

/-- The point-mass Markov decision process of a deterministic transition. -/
@[expose] public noncomputable def ofDet (f : State → Action → State) :
    MDP State Action where
  transition := fun s a => PMF.pure (f s a)

end MDP

/-- An **observed history**: the first observation, then the actions taken and
the observations reached. The observation alphabet is a parameter, because what
an agent sees is not determined by the dynamics. -/
public abbrev History (Obs : Type w) (Action : Type v) : Type (max w v) :=
  Obs × List (Action × Obs)

/-- Relabel the observations in a history. -/
@[expose] public def History.mapObs {O₁ O₂ : Type w} {A : Type v} (f : O₁ → O₂)
    (h : History O₁ A) : History O₂ A :=
  (f h.1, h.2.map fun p => (p.1, f p.2))

/-- An injective relabelling is injective on histories, so a policy over the
larger alphabet can realise any policy over the smaller one. -/
public theorem History.mapObs_injective {O₁ O₂ : Type w} {A : Type v} {f : O₁ → O₂}
    (hf : Function.Injective f) :
    Function.Injective (History.mapObs (A := A) f) := by
  rintro ⟨o₁, l₁⟩ ⟨o₂, l₂⟩ h
  have h1 : f o₁ = f o₂ := congrArg Prod.fst h
  have h2 : l₁.map (fun p => (p.1, f p.2)) = l₂.map (fun p => (p.1, f p.2)) :=
    congrArg Prod.snd h
  have hpair : Function.Injective (fun p : A × O₁ => (p.1, f p.2)) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hp
    have hab : a = b := congrArg Prod.fst hp
    have hxy : f x = f y := congrArg Prod.snd hp
    rw [hab, hf hxy]
  rw [hf h1, List.map_injective_iff.mpr hpair h2]

/-- A **possibly stochastic policy** over observed histories. -/
public abbrev Policy (Obs : Type w) (Action : Type v) : Type (max w v) :=
  History Obs Action → PMF Action

/-- A **deterministic policy** over observed histories. -/
public abbrev DetPolicy (Obs : Type w) (Action : Type v) : Type (max w v) :=
  History Obs Action → Action

/-- The point-mass policy induced by a deterministic one. -/
@[expose] public noncomputable def Policy.ofDet {Obs : Type w} {Action : Type v}
    (π : DetPolicy Obs Action) : Policy Obs Action :=
  fun h => PMF.pure (π h)

/-! ## The determined run -/

variable {State : Type u} {Action : Type v} {Obs : Type w}

/--
**The determined run.** After `n` steps: the state reached, and the observed
history, defined together because the policy's next action depends on the
history so far.

The transition is a function and the policy is a function, so nothing is drawn.
`run_ofDet` below identifies this with the drawn run at point masses.
-/
@[expose] public def detRun (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) :
    ℕ → State × History Obs Action
  | 0 => (s₀, (obs s₀, []))
  | n + 1 =>
      let prev := detRun f obs π s₀ n
      let a := π prev.2
      let s := f prev.1 a
      (s, (prev.2.1, prev.2.2 ++ [(a, obs s)]))

/-- The state reached after `n` determined steps. -/
@[expose] public def detStateAt (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) : State :=
  (detRun f obs π s₀ n).1

/-- The observed history after `n` determined steps. -/
@[expose] public def detHistoryUpTo (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) : History Obs Action :=
  (detRun f obs π s₀ n).2

/--
**A determined run of `n` steps records exactly `n` of them.**

The stochastic `run_history_length` says this of the drawn run; this is the same
fact about the determined one, and it is what lets a consumer count *steps*
where the carrier counts list entries. `AISafetyAtlas.Wireheading.AgentHistory`
uses it to name a window in steps, and
`AISafetyAtlas.Verification.Robot.ofBehavior` uses it to read a history's length
as an operational cycle.
-/
public theorem detHistoryUpTo_length (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) :
    ∀ n : ℕ, (detHistoryUpTo f obs π s₀ n).2.length = n
  | 0 => rfl
  | n + 1 => by
      simp only [detHistoryUpTo, detRun, List.length_append, List.length_cons,
        List.length_nil]
      have ih := detHistoryUpTo_length f obs π s₀ n
      simp only [detHistoryUpTo] at ih
      omega

/--
**The determined run sees the world only through the observation map.**

Two observation maps that agree pointwise induce the same run, whatever else
differs behind them. This is the whole of the indistinguishability argument in
`AISafetyAtlas.Wireheading.CRMDP`, stated where it belongs.
-/
public theorem detRun_congr_obs (f : State → Action → State)
    {obs₁ obs₂ : State → Obs} (hobs : ∀ s, obs₁ s = obs₂ s)
    (π : DetPolicy Obs Action) (s₀ : State) :
    ∀ n : ℕ, detRun f obs₁ π s₀ n = detRun f obs₂ π s₀ n := by
  intro n
  induction n with
  | zero => simp only [detRun, hobs]
  | succ n ih => simp only [detRun, ih, hobs]

/-- Hence the visited states agree. -/
public theorem detStateAt_congr_obs (f : State → Action → State)
    {obs₁ obs₂ : State → Obs} (hobs : ∀ s, obs₁ s = obs₂ s)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) :
    detStateAt f obs₁ π s₀ n = detStateAt f obs₂ π s₀ n := by
  unfold detStateAt
  rw [detRun_congr_obs f hobs π s₀ n]

/-- And so do the observed histories. -/
public theorem detHistoryUpTo_congr_obs (f : State → Action → State)
    {obs₁ obs₂ : State → Obs} (hobs : ∀ s, obs₁ s = obs₂ s)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) :
    detHistoryUpTo f obs₁ π s₀ n = detHistoryUpTo f obs₂ π s₀ n := by
  unfold detHistoryUpTo
  rw [detRun_congr_obs f hobs π s₀ n]

/-! ## The drawn run -/

namespace MDP

/--
**The run of a Markov decision process** against an observation map and a
possibly stochastic policy: the successor state is drawn from the transition and
the action is drawn from the policy, so the whole trajectory is a distribution
over state-and-history pairs.

The recursion is `detRun` with `bind` where it had `let`.
-/
@[expose] public noncomputable def run (M : MDP State Action) (obs : State → Obs)
    (σ : Policy Obs Action) (s₀ : State) :
    ℕ → PMF (State × History Obs Action)
  | 0 => PMF.pure (s₀, (obs s₀, []))
  | n + 1 =>
      PMF.bind (M.run obs σ s₀ n) fun prev =>
        PMF.bind (σ prev.2) fun a =>
          PMF.bind (M.transition prev.1 a) fun s =>
            PMF.pure (s, (prev.2.1, prev.2.2 ++ [(a, obs s)]))

/-- The state distribution after `n` steps. -/
@[expose] public noncomputable def stateAt (M : MDP State Action) (obs : State → Obs)
    (σ : Policy Obs Action) (s₀ : State) (n : ℕ) : PMF State :=
  PMF.bind (M.run obs σ s₀ n) fun p => PMF.pure p.1

/-- The distribution over observed histories after `n` steps. -/
@[expose] public noncomputable def historyUpTo (M : MDP State Action) (obs : State → Obs)
    (σ : Policy Obs Action) (s₀ : State) (n : ℕ) : PMF (History Obs Action) :=
  PMF.bind (M.run obs σ s₀ n) fun p => PMF.pure p.2

/--
**The trajectory distribution sees the world only through the observation map.**

`detRun_congr_obs` under randomness: the recursion mentions the world outside the
dynamics only through `obs`, and drawing the successor state or the action does
not change that. As stated, the hypothesis makes the two observation maps agree
everywhere, so the lemma is a congruence; the reading above describes the shape
of `run`, which the lemma records.
-/
public theorem run_congr_obs (M : MDP State Action)
    {obs₁ obs₂ : State → Obs} (hobs : ∀ s, obs₁ s = obs₂ s)
    (σ : Policy Obs Action) (s₀ : State) :
    ∀ n : ℕ, M.run obs₁ σ s₀ n = M.run obs₂ σ s₀ n := by
  intro n
  induction n with
  | zero => simp only [run, hobs]
  | succ n ih => simp only [run, ih, hobs]

/-- Hence neither does the state distribution. -/
public theorem stateAt_congr_obs (M : MDP State Action)
    {obs₁ obs₂ : State → Obs} (hobs : ∀ s, obs₁ s = obs₂ s)
    (σ : Policy Obs Action) (s₀ : State) (n : ℕ) :
    M.stateAt obs₁ σ s₀ n = M.stateAt obs₂ σ s₀ n := by
  rw [stateAt, stateAt, run_congr_obs M hobs σ s₀ n]

/-- Nor the distribution over observed histories. -/
public theorem historyUpTo_congr_obs (M : MDP State Action)
    {obs₁ obs₂ : State → Obs} (hobs : ∀ s, obs₁ s = obs₂ s)
    (σ : Policy Obs Action) (s₀ : State) (n : ℕ) :
    M.historyUpTo obs₁ σ s₀ n = M.historyUpTo obs₂ σ s₀ n := by
  rw [historyUpTo, historyUpTo, run_congr_obs M hobs σ s₀ n]

/-! ### What of the policy the run can see

`run` appends one `(action, observation)` pair per step, so after `n` steps every
history in the support has length exactly `n`, and the policy has been consulted
only at histories shorter than `n`. Two policies agreeing that far therefore give
the same run. This is what makes a maximum over the policy space attainable when
the observation and action alphabets are finite: the run cannot tell apart
policies that agree on the finitely many histories it can reach.
-/

private theorem bind_congr_on_support {α β : Type*} (p : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a (by simpa [PMF.mem_support_iff] using ha)]

/-- After `n` steps every history the run can produce has length exactly `n`. -/
public theorem run_history_length (M : MDP State Action) (obs : State → Obs)
    (σ : Policy Obs Action) (s₀ : State) :
    ∀ (n : ℕ) (p : State × History Obs Action),
      p ∈ (M.run obs σ s₀ n).support → p.2.2.length = n := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rw [run, PMF.mem_support_pure_iff] at hp
      subst hp
      rfl
  | succ n ih =>
      intro p hp
      rw [run, PMF.mem_support_bind_iff] at hp
      obtain ⟨prev, hprev, hp⟩ := hp
      rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨a, -, hp⟩ := hp
      rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨s, -, hp⟩ := hp
      rw [PMF.mem_support_pure_iff] at hp
      subst hp
      simp [ih prev hprev]

/--
**The run sees the policy only on histories it can reach.**

Two policies that agree on every history shorter than `n` induce the same run
after `n` steps, whatever they do elsewhere.
-/
public theorem run_congr_policy (M : MDP State Action) (obs : State → Obs)
    {σ₁ σ₂ : Policy Obs Action} (s₀ : State) :
    ∀ n : ℕ,
      (∀ h : History Obs Action, h.2.length < n → σ₁ h = σ₂ h) →
        M.run obs σ₁ s₀ n = M.run obs σ₂ s₀ n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      have hih : M.run obs σ₁ s₀ n = M.run obs σ₂ s₀ n :=
        ih fun hst hlt => h hst (Nat.lt_succ_of_lt hlt)
      rw [run, run, hih]
      refine bind_congr_on_support _ fun prev hprev => ?_
      rw [h prev.2
        (by rw [run_history_length M obs σ₂ s₀ n prev hprev]; exact Nat.lt_succ_self n)]

/-- Hence neither does the state distribution see more of the policy. -/
public theorem stateAt_congr_policy (M : MDP State Action) (obs : State → Obs)
    {σ₁ σ₂ : Policy Obs Action} (s₀ : State) (n : ℕ)
    (h : ∀ hst : History Obs Action, hst.2.length < n → σ₁ hst = σ₂ hst) :
    M.stateAt obs σ₁ s₀ n = M.stateAt obs σ₂ s₀ n := by
  rw [stateAt, stateAt, run_congr_policy M obs s₀ n h]

/-! ### One coordinate of a possibly stochastic policy

A policy is consulted at each history separately, so the run is *affine* in what
the policy does at any single history: drawing the action at `h` first and then
running with that action fixed there gives the same distribution. Iterating this
over the finitely many histories a run can reach is what reduces a maximum over
possibly stochastic policies to a maximum over deterministic ones, which is the
policy axis of Everitt et al.'s Theorem 11.
-/

/--
**The run is affine in the policy at a single history.**

Drawing the action at `h` up front and running with a point mass there gives the
same trajectory distribution as running with the policy itself.
-/
public theorem run_update_decomp (M : MDP State Action) (obs : State → Obs)
    [DecidableEq Obs] [DecidableEq Action] (σ : Policy Obs Action)
    (hh : History Obs Action) (s₀ : State) :
    ∀ n : ℕ,
      M.run obs σ s₀ n
        = (σ hh).bind fun a => M.run obs (Function.update σ hh (PMF.pure a)) s₀ n := by
  intro n
  induction n with
  | zero =>
      have hfun : (fun a : Action => M.run obs (Function.update σ hh (PMF.pure a)) s₀ 0)
          = fun _ => M.run obs σ s₀ 0 := rfl
      rw [hfun, PMF.bind_const]
  | succ n ih =>
      by_cases hlt : hh.2.length < n
      · -- the update is invisible to the step, and the inductive hypothesis
        -- supplies the decomposition of the first `n` steps
        rw [run, ih, PMF.bind_bind]
        refine congrArg (PMF.bind (σ hh)) (funext fun a => ?_)
        rw [run]
        refine bind_congr_on_support _ fun prev hprev => ?_
        have hlen := run_history_length M obs (Function.update σ hh (PMF.pure a)) s₀ n prev hprev
        have hne : prev.2 ≠ hh := by
          intro hEq
          rw [hEq] at hlen
          omega
        rw [Function.update_of_ne hne]
      · by_cases heq : hh.2.length = n
        · -- the step consults the policy exactly at length-`n` histories, one of
          -- which is `hh`; commuting the two draws is the whole content
          have hrun : ∀ a : Action,
              M.run obs (Function.update σ hh (PMF.pure a)) s₀ n = M.run obs σ s₀ n := by
            intro a
            refine run_congr_policy M obs s₀ n fun h' hlt' => ?_
            have hne : h' ≠ hh := by
              intro hEq
              rw [hEq, heq] at hlt'
              exact lt_irrefl _ hlt'
            rw [Function.update_of_ne hne]
          have hfun : (fun a : Action => M.run obs (Function.update σ hh (PMF.pure a)) s₀ (n + 1))
              = fun a : Action => PMF.bind (M.run obs σ s₀ n)
                  (fun prev => PMF.bind ((Function.update σ hh (PMF.pure a)) prev.2)
                    (fun act => PMF.bind (M.transition prev.1 act)
                      (fun s => PMF.pure (s, (prev.2.1, prev.2.2 ++ [(act, obs s)]))))) := by
            funext a
            rw [run, hrun a]
          rw [hfun, run, PMF.bind_comm]
          refine congrArg (PMF.bind (M.run obs σ s₀ n)) (funext fun prev => ?_)
          by_cases hp : prev.2 = hh
          · rw [hp]
            refine congrArg (PMF.bind (σ hh)) (funext fun a => ?_)
            rw [Function.update_self, PMF.pure_bind]
          · have hupd : ∀ a : Action, (Function.update σ hh (PMF.pure a)) prev.2 = σ prev.2 :=
              fun a => Function.update_of_ne hp _ _
            simp only [hupd]
            rw [PMF.bind_const]
        · -- `hh` is longer than the run, so the update is invisible outright
          have hrun : ∀ a : Action,
              M.run obs (Function.update σ hh (PMF.pure a)) s₀ (n + 1)
                = M.run obs σ s₀ (n + 1) := by
            intro a
            refine run_congr_policy M obs s₀ (n + 1) fun h' hlt' => ?_
            have hne : h' ≠ hh := by
              intro hEq
              rw [hEq] at hlt'
              omega
            rw [Function.update_of_ne hne]
          rw [funext hrun, PMF.bind_const]

/-- Hence the state distribution is affine in the policy at a single history. -/
public theorem stateAt_update_decomp (M : MDP State Action) (obs : State → Obs)
    [DecidableEq Obs] [DecidableEq Action] (σ : Policy Obs Action)
    (hh : History Obs Action) (s₀ : State) (n : ℕ) :
    M.stateAt obs σ s₀ n
      = (σ hh).bind fun a => M.stateAt obs (Function.update σ hh (PMF.pure a)) s₀ n := by
  rw [stateAt, run_update_decomp M obs σ hh s₀ n, PMF.bind_bind]
  rfl

/-! ### Relabelling the observation alphabet

`run` is generic in the observation type, so an environment whose channel factors
as `f \circ obs` runs the same way as one observing through `obs` alone, provided
the policy is read through `f` as well. Nothing is duplicated: this is one run
compared with itself at two alphabets.

The point of it is that a **finite** alphabet can sit underneath an infinite one.
`AISafetyAtlas.Wireheading.CRMDP` observes `State \times Reward` with `Reward` a
real interval, so its policy domain is infinite whatever the state space; a grid
environment only ever emits finitely many rewards, and `run_mapObs` is what lets
the finite alphabet carry the argument.
-/

/--
**The run at a relabelled alphabet is the pushforward of the run underneath it.**
-/
public theorem run_mapObs (M : MDP State Action) {O₁ O₂ : Type w} (f : O₁ → O₂)
    (obs : State → O₁) (σ : Policy O₂ Action) (s₀ : State) :
    ∀ n : ℕ,
      M.run (fun s => f (obs s)) σ s₀ n
        = PMF.bind (M.run obs (fun h => σ (History.mapObs f h)) s₀ n)
            fun p => PMF.pure (p.1, History.mapObs f p.2) := by
  intro n
  induction n with
  | zero => simp [run, History.mapObs]
  | succ n ih =>
      rw [run, run, ih]
      simp only [PMF.bind_bind, PMF.pure_bind, History.mapObs, List.map_append,
        List.map_cons, List.map_nil]

/-- Hence the state distribution does not see the labelling at all. -/
public theorem stateAt_mapObs (M : MDP State Action) {O₁ O₂ : Type w} (f : O₁ → O₂)
    (obs : State → O₁) (σ : Policy O₂ Action) (s₀ : State) (n : ℕ) :
    M.stateAt (fun s => f (obs s)) σ s₀ n
      = M.stateAt obs (fun h => σ (History.mapObs f h)) s₀ n := by
  rw [stateAt, stateAt, run_mapObs M f obs σ s₀ n]
  simp only [PMF.bind_bind, PMF.pure_bind]

/--
**The determined run is the degenerate drawn one.**

At a point-mass transition and a point-mass policy the trajectory distribution is
the point mass at the determined trajectory, so every statement about `detRun` is
a statement about `run`.
-/
public theorem run_ofDet (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) :
    (MDP.ofDet f).run obs (Policy.ofDet π) s₀ n
      = PMF.pure (detRun f obs π s₀ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run, ih, PMF.pure_bind]
      simp only [Policy.ofDet, ofDet, PMF.pure_bind]
      rfl

/-- And so the state distribution is the point mass at the determined state. -/
public theorem stateAt_ofDet (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) :
    (MDP.ofDet f).stateAt obs (Policy.ofDet π) s₀ n
      = PMF.pure (detStateAt f obs π s₀ n) := by
  rw [stateAt, run_ofDet, PMF.pure_bind]
  rfl

/-- And the observed-history distribution the point mass at the determined
history. -/
public theorem historyUpTo_ofDet (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) :
    (MDP.ofDet f).historyUpTo obs (Policy.ofDet π) s₀ n
      = PMF.pure (detHistoryUpTo f obs π s₀ n) := by
  rw [historyUpTo, run_ofDet, PMF.pure_bind]
  rfl

end MDP

/-! ## A maximum over the policy space, from finitely much of a policy

`MDP.run_congr_policy` says a run of `n` steps sees a policy only on histories
shorter than `n`. Over finite observation and action alphabets there are finitely
many such histories, so any quantity that depends on the policy through a run of
`n` steps factors through a **finite** function space, and its maximum and
minimum over the whole policy space are attained.

`AISafetyAtlas.Wireheading.RewardGrid` carries this out by hand for a
deterministic transition, where the history is determined by the action sequence
and the reduction can go through `Fin t → Action`. Here the transition may be a
distribution, the history is not determined, and the reduction has to go through
the histories themselves.
-/

/-- The histories a run of `n` steps can consult: an initial observation and
fewer than `n` action-observation pairs, indexed by how many. -/
@[expose] public def TruncHist (Obs : Type w) (Action : Type v) (n : ℕ) : Type (max w v) :=
  Σ k : Fin n, Obs × List.Vector (Action × Obs) (k : ℕ)

public instance TruncHist.instFintype {Obs : Type w} {Action : Type v} {n : ℕ}
    [Fintype Obs] [Fintype Action] : Fintype (TruncHist Obs Action n) :=
  inferInstanceAs (Fintype (Σ k : Fin n, Obs × List.Vector (Action × Obs) (k : ℕ)))

public instance TruncHist.instDecidableEq {Obs : Type w} {Action : Type v} {n : ℕ}
    [DecidableEq Obs] [DecidableEq Action] : DecidableEq (TruncHist Obs Action n) :=
  inferInstanceAs (DecidableEq (Σ k : Fin n, Obs × List.Vector (Action × Obs) (k : ℕ)))

/-- A deterministic policy's restriction to what a run of `n` steps can see. -/
@[expose] public def truncatePolicy {Obs : Type w} {Action : Type v} (n : ℕ)
    (π : DetPolicy Obs Action) : TruncHist Obs Action n → Action :=
  fun x => π (x.2.1, x.2.2.val)

/-- And back: read a finite table as a policy, answering `a₀` on the histories no
run of `n` steps reaches. The fallback is an explicit argument rather than an
`Inhabited` instance, so a caller holding only `Nonempty Action` can use this. -/
@[expose] public def ofTruncPolicy {Obs : Type w} {Action : Type v} {n : ℕ}
    (a₀ : Action) (f : TruncHist Obs Action n → Action) : DetPolicy Obs Action :=
  fun h => if hh : h.2.length < n then f ⟨⟨h.2.length, hh⟩, (h.1, ⟨h.2, rfl⟩)⟩ else a₀

/-- The round trip changes nothing a run of `n` steps can see. -/
public theorem ofTruncPolicy_truncatePolicy {Obs : Type w} {Action : Type v}
    {n : ℕ} (a₀ : Action) (π : DetPolicy Obs Action)
    (h : History Obs Action) (hh : h.2.length < n) :
    ofTruncPolicy a₀ (truncatePolicy n π) h = π h := by
  rw [ofTruncPolicy, dif_pos hh]
  rfl

/--
**Any quantity a run of `n` steps determines attains its maximum over the whole
policy space**, when the alphabets are finite.

The hypothesis is `MDP.run_congr_policy`'s conclusion stated for the quantity
rather than for the run, so a caller discharges it by rewriting with that lemma.
-/
public theorem exists_max_of_truncates {Obs : Type w} {Action : Type v}
    [Fintype Obs] [DecidableEq Obs] [Fintype Action] [DecidableEq Action]
    {n : ℕ} (a₀ : Action) (F : DetPolicy Obs Action → ℝ)
    (hF : ∀ π₁ π₂ : DetPolicy Obs Action,
      (∀ h : History Obs Action, h.2.length < n → π₁ h = π₂ h) → F π₁ = F π₂) :
    ∃ best : DetPolicy Obs Action, ∀ π : DetPolicy Obs Action, F π ≤ F best := by
  classical
  obtain ⟨g, -, hg⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (TruncHist Obs Action n → Action))
      (fun f => F (ofTruncPolicy a₀ f)) ⟨fun _ => a₀, Finset.mem_univ _⟩
  refine ⟨ofTruncPolicy a₀ g, fun π => ?_⟩
  have hπ : F π = F (ofTruncPolicy a₀ (truncatePolicy n π)) :=
    hF _ _ fun h hh => (ofTruncPolicy_truncatePolicy a₀ π h hh).symm
  rw [hπ]
  exact hg _ (Finset.mem_univ _)

/-- The same for a minimum. -/
public theorem exists_min_of_truncates {Obs : Type w} {Action : Type v}
    [Fintype Obs] [DecidableEq Obs] [Fintype Action] [DecidableEq Action]
    {n : ℕ} (a₀ : Action) (F : DetPolicy Obs Action → ℝ)
    (hF : ∀ π₁ π₂ : DetPolicy Obs Action,
      (∀ h : History Obs Action, h.2.length < n → π₁ h = π₂ h) → F π₁ = F π₂) :
    ∃ worst : DetPolicy Obs Action, ∀ π : DetPolicy Obs Action, F worst ≤ F π := by
  classical
  obtain ⟨g, -, hg⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (TruncHist Obs Action n → Action))
      (fun f => F (ofTruncPolicy a₀ f)) ⟨fun _ => a₀, Finset.mem_univ _⟩
  refine ⟨ofTruncPolicy a₀ g, fun π => ?_⟩
  have hπ : F π = F (ofTruncPolicy a₀ (truncatePolicy n π)) :=
    hF _ _ fun h hh => (ofTruncPolicy_truncatePolicy a₀ π h hh).symm
  rw [hπ]
  exact hg _ (Finset.mem_univ _)

/-! ## From possibly stochastic policies down to deterministic ones

A quantity that is affine in the policy at each history, and that a run of `t`
steps determines, is bounded by its values at **deterministic** policies. Over
finite alphabets there are finitely many histories a run of `t` steps can reach,
so replacing the policy's distribution by a point mass one history at a time
terminates, and each replacement can only move the value towards an extreme.

This is the policy axis of Everitt et al.'s Theorem 11: print quantifies over a
*possibly stochastic* policy, and this says the maximum over those is the maximum
over the deterministic ones.
-/

section AffineReduction

variable {Obs : Type w} {Action : Type v}
  [Fintype Obs] [DecidableEq Obs] [Fintype Action] [DecidableEq Action]

/-- The finitely many histories a run of `t` steps can consult, as a `Finset`. -/
public noncomputable def shortHistories (Obs : Type w) (Action : Type v)
    [Fintype Obs] [Fintype Action] [DecidableEq Obs] [DecidableEq Action] (t : ℕ) :
    Finset (History Obs Action) :=
  Finset.image (fun x : TruncHist Obs Action t => ((x.2.1, x.2.2.val) : History Obs Action))
    Finset.univ

public theorem mem_shortHistories {t : ℕ} (h : History Obs Action)
    (hh : h.2.length < t) : h ∈ shortHistories Obs Action t := by
  refine Finset.mem_image.mpr ⟨⟨⟨h.2.length, hh⟩, (h.1, ⟨h.2, rfl⟩)⟩, Finset.mem_univ _, ?_⟩
  rfl

/-- **A value affine in each coordinate is bounded by its deterministic
values.** -/
public theorem le_of_affine_of_det_le {t : ℕ} (a₀ : Action)
    (F : Policy Obs Action → ℝ) (B : ℝ)
    (hcongr : ∀ σ₁ σ₂ : Policy Obs Action,
      (∀ h : History Obs Action, h.2.length < t → σ₁ h = σ₂ h) → F σ₁ = F σ₂)
    (haff : ∀ (σ : Policy Obs Action) (h : History Obs Action), h.2.length < t →
      F σ = ∑ a, (σ h a).toReal * F (Function.update σ h (PMF.pure a)))
    (hB : ∀ ρ : DetPolicy Obs Action, F (Policy.ofDet ρ) ≤ B)
    (σ : Policy Obs Action) : F σ ≤ B := by
  classical
  have key : ∀ (S : Finset (History Obs Action)) (σ : Policy Obs Action)
      (ρ : DetPolicy Obs Action),
      (∀ h : History Obs Action, h.2.length < t → h ∉ S → σ h = PMF.pure (ρ h)) →
        F σ ≤ B := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro σ ρ hinv
        have : F σ = F (Policy.ofDet ρ) :=
          hcongr _ _ fun h hlen => hinv h hlen (Finset.notMem_empty h)
        rw [this]
        exact hB ρ
    | insert h S hhS ih =>
        intro σ ρ hinv
        by_cases hlen : h.2.length < t
        · rw [haff σ h hlen]
          have hle : ∀ a : Action, F (Function.update σ h (PMF.pure a)) ≤ B := by
            intro a
            refine ih (Function.update σ h (PMF.pure a)) (Function.update ρ h a) ?_
            intro h' hlen' hnot
            by_cases hEq : h' = h
            · rw [hEq, Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hEq, Function.update_of_ne hEq]
              exact hinv h' hlen' (fun hmem => by
                rcases Finset.mem_insert.mp hmem with h1 | h2
                · exact hEq h1
                · exact hnot h2)
          have hcoe : (∑ a : Action, (σ h) a) = 1 :=
            (tsum_fintype (fun a : Action => (σ h) a)).symm.trans (PMF.tsum_coe (σ h))
          have hsum : ∑ a : Action, ((σ h) a).toReal = 1 := by
            rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top (σ h) a), hcoe,
              ENNReal.toReal_one]
          calc ∑ a, ((σ h) a).toReal * F (Function.update σ h (PMF.pure a))
              ≤ ∑ a : Action, ((σ h) a).toReal * B :=
                Finset.sum_le_sum fun a _ =>
                  mul_le_mul_of_nonneg_left (hle a) ENNReal.toReal_nonneg
            _ = B := by rw [← Finset.sum_mul, hsum, one_mul]
        · refine ih σ ρ fun h' hlen' hnot => hinv h' hlen' ?_
          intro hmem
          rcases Finset.mem_insert.mp hmem with h1 | h2
          · exact hlen (h1 ▸ hlen')
          · exact hnot h2
  exact key (shortHistories Obs Action t) σ (fun _ => a₀)
    fun h hlen hnot => absurd (mem_shortHistories h hlen) hnot

/-- The mirror, for a lower bound. -/
public theorem le_of_affine_of_le_det {t : ℕ} (a₀ : Action)
    (F : Policy Obs Action → ℝ) (B : ℝ)
    (hcongr : ∀ σ₁ σ₂ : Policy Obs Action,
      (∀ h : History Obs Action, h.2.length < t → σ₁ h = σ₂ h) → F σ₁ = F σ₂)
    (haff : ∀ (σ : Policy Obs Action) (h : History Obs Action), h.2.length < t →
      F σ = ∑ a, (σ h a).toReal * F (Function.update σ h (PMF.pure a)))
    (hB : ∀ ρ : DetPolicy Obs Action, B ≤ F (Policy.ofDet ρ))
    (σ : Policy Obs Action) : B ≤ F σ := by
  classical
  have key : ∀ (S : Finset (History Obs Action)) (σ : Policy Obs Action)
      (ρ : DetPolicy Obs Action),
      (∀ h : History Obs Action, h.2.length < t → h ∉ S → σ h = PMF.pure (ρ h)) →
        B ≤ F σ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro σ ρ hinv
        have : F σ = F (Policy.ofDet ρ) :=
          hcongr _ _ fun h hlen => hinv h hlen (Finset.notMem_empty h)
        rw [this]
        exact hB ρ
    | insert h S hhS ih =>
        intro σ ρ hinv
        by_cases hlen : h.2.length < t
        · rw [haff σ h hlen]
          have hle : ∀ a : Action, B ≤ F (Function.update σ h (PMF.pure a)) := by
            intro a
            refine ih (Function.update σ h (PMF.pure a)) (Function.update ρ h a) ?_
            intro h' hlen' hnot
            by_cases hEq : h' = h
            · rw [hEq, Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hEq, Function.update_of_ne hEq]
              exact hinv h' hlen' (fun hmem => by
                rcases Finset.mem_insert.mp hmem with h1 | h2
                · exact hEq h1
                · exact hnot h2)
          have hcoe : (∑ a : Action, (σ h) a) = 1 :=
            (tsum_fintype (fun a : Action => (σ h) a)).symm.trans (PMF.tsum_coe (σ h))
          have hsum : ∑ a : Action, ((σ h) a).toReal = 1 := by
            rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top (σ h) a), hcoe,
              ENNReal.toReal_one]
          calc B = ∑ a : Action, ((σ h) a).toReal * B := by
                rw [← Finset.sum_mul, hsum, one_mul]
            _ ≤ ∑ a, ((σ h) a).toReal * F (Function.update σ h (PMF.pure a)) :=
                Finset.sum_le_sum fun a _ =>
                  mul_le_mul_of_nonneg_left (hle a) ENNReal.toReal_nonneg
        · refine ih σ ρ fun h' hlen' hnot => hinv h' hlen' ?_
          intro hmem
          rcases Finset.mem_insert.mp hmem with h1 | h2
          · exact hlen (h1 ▸ hlen')
          · exact hnot h2
  exact key (shortHistories Obs Action t) σ (fun _ => a₀)
    fun h hlen hnot => absurd (mem_shortHistories h hlen) hnot

end AffineReduction

/-! ## One recursion, two monads

`detRun` and `MDP.run` are the same recursion with different notions of "the next
state" and "the next action": determined, or drawn. Writing it once over an
arbitrary monad makes that literal rather than a resemblance.
-/

section Generic

variable {S A O : Type u}

/--
**The run, over any monad.** `m` is how a successor state and an action are
delivered: `Id` for determined, `PMF` for drawn.

`S`, `A` and `O` share a universe here, where the rest of the module lets them
differ. That is a universe restriction and not a mathematical one: `m` has to
accept the state type, the action type and the state-history pair, so they must
live in one universe. Both instantiations used below, `Id` and `PMF`, are
`Type u → Type u`.
-/
@[expose] public def genRun {m : Type u → Type u} [Monad m]
    (T : S → A → m S) (obs : S → O) (σ : History O A → m A) (s₀ : S) :
    ℕ → m (S × History O A)
  | 0 => pure (s₀, (obs s₀, []))
  | n + 1 => do
      let prev ← genRun T obs σ s₀ n
      let a ← σ prev.2
      let s ← T prev.1 a
      pure (s, (prev.2.1, prev.2.2 ++ [(a, obs s)]))

/-- **The determined run is the identity monad's instance.** -/
public theorem genRun_id (f : S → A → S) (obs : S → O) (π : DetPolicy O A) (s₀ : S)
    (n : ℕ) :
    genRun (m := Id) f obs π s₀ n = detRun f obs π s₀ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [genRun, detRun, ih]; rfl

/-- **And the drawn run is `PMF`'s instance.** So the two runs are one recursion
at two monads, which is what makes `MDP.run_ofDet` an instance of a single fact
rather than a coincidence. -/
public theorem genRun_pmf (M : MDP S A) (obs : S → O) (σ : Policy O A) (s₀ : S)
    (n : ℕ) :
    genRun (m := PMF) M.transition obs σ s₀ n = M.run obs σ s₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [genRun, MDP.run, ih]
      rfl

end Generic

end AISafetyAtlas.Decision
