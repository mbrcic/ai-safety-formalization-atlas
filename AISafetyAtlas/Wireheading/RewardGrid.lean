module

public import AISafetyAtlas.Wireheading.CRMDP
public import AISafetyAtlas.Wireheading.StochasticCRMDP
public import AISafetyAtlas.Wireheading.StochasticPolicy
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# Theorem 11's own hypothesis class: the uniform reward grid

Everitt, Krakovna, Orseau, Hutter and Legg, *Reinforcement Learning with a
Corrupted Reward Channel*, arXiv:1705.08417v2, Theorem 11 opens:

> Let `R = {r₁, …, rₙ} ⊂ [0,1]` be a uniform discretisation of `[0,1]`,
> `0 = r₁ < r₂ < ⋯ < rₙ = 1`. If the hypothesis classes `Ṙ` and `C` contain all
> functions `Ṙ : S → R` and `C : S × R → R`, then for any `π`, `s₀`, `t`, …

`AISafetyAtlas.Wireheading.CRMDP` proves the conclusion for a class whose
rewards range over the whole of `Set.Icc 0 1`. That class is closed under
`x ↦ 1 - x`, which is why the complement argument survives there — but print's
finite class is a **proper subclass of it that the atlas had no type for**, so
Theorem 11 at print's own hypotheses was not available. This module supplies
that type.

## Why the uniformity is load-bearing

It is the reason `x ↦ 1 - x` maps the grid to itself. With `rᵢ = (i - 1)/(n - 1)`
the complement of `rᵢ` is `r_{n+1-i}`, so complementing a true reward function
lands back in the class and the whole argument goes through *inside the finite
class*. A non-uniform discretisation of `[0,1]` containing `0` and `1` need not
have that property, and then "the classes contain all functions `S → R`" would
not give the complemented environment. `gridVal_gridRev` is the fact, and
`gridVal_strictMono`, `gridVal_zero` and `gridVal_last` are the rest of print's
sentence.

## What is proved

* `GridEnv` is print's environment: a true reward function and a corruption
  function, both into the grid, over a fixed transition.
* `toEnv` embeds it into `CRMDP.Env`, so nothing about runs, observed histories
  or returns is redefined. `run_congr_observed` is the one lemma that makes the
  embedding usable: a run depends on an environment only through its observed
  reward function.
* `Fintype (GridEnv m State)` for finite `State` — print's class is finite, and
  that is what its equations (4) and (5) silently use.
* `exists_max_gridReturn` / `exists_min_gridReturn`: the extrema over the
  **policy function space** are attained, derived rather than assumed. The
  argument is print's implicit one made explicit: at horizon `t` a return
  depends on a policy only through the `t` actions the rollout actually takes,
  every length-`t` action sequence is realised by some policy, and there are
  finitely many of those.
* `toComplementedClass`: print's class as a `Corruption.ComplementedClass`,
  **with all three extrema derived**, whence
  `everitt_theorem_eleven_gridClass` is Theorem 11 over print's own hypothesis
  class.

## What is still not print's

**Nothing, as of 2026-09-19.** `everitt_theorem_eleven_fullMixedClass` is
Theorem 11 at every axis print states it with: the class is Definition 9's -- a
given set of transitions crossed with the full product of grid-valued reward and
corruption functions -- the transitions are distributions, the policies are all
the possibly stochastic ones, and none of the three extrema is assumed. The
narrower statements are kept because they are what the wider one is built from
and because each is cheaper to read, and they are *chained* to it rather than
parallel: `fullMixedReturn_ofDet` identifies `everitt_theorem_eleven_fullClass`
as the determined instance.

Two axes closed on that day and each had been mispriced beforehand.

* **Deterministic transitions.** The obstruction was read as a refactor of the
  observation type, because `CRMDP.Obs` carries a real-valued reward and its
  short histories are not a finite set. No type had to change:
  `Decision.MDP.run` is generic in the observation type, a grid environment's
  real channel is finite (`gridChannel`), and `Decision.MDP.stateAt_mapObs`
  relates a run to the same run at the alphabet underneath it.
* **Deterministic policies.** The obstruction was read as needing a mixture
  decomposition or a value recursion, either of which would have rebuilt the run
  this module shares. Neither was needed. `Decision.MDP.run_update_decomp` says
  the run is affine in what the policy does at a *single* history, and
  `Decision.le_of_affine_of_det_le` iterates that over the finitely many
  histories a run of `t` steps can reach, so the derived deterministic extrema
  bound the mixed policies with nothing further assumed.

## On duplicating nothing

The reward carrier is the only thing this module adds. `run`, `stateAt`,
`historyUpTo` and `returnOver` are `CRMDP`'s, reached through `toEnv`, because
duplicating them would put two return functions in the tree with no theorem
relating them. The price is `toEnv`'s corruption field, which has to be defined
on the whole interval where print's `C` is defined on the grid: off the grid it
is the identity, and `toEnv_corruption_gridVal` says that choice is never
observed, since a corruption channel is only ever evaluated at a true reward and
every true reward is on the grid.

Survey row: **BY-039**, alongside `AISafetyAtlas.Wireheading.CRMDP`. Landscape
entry: `LAND-CRMDP-GRID-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.RewardGrid

open AISafetyAtlas.Wireheading.CRMDP

variable {State Action : Type*} {m : ℕ}

/-! ## The grid

Print's `R = {r₁, …, rₙ}` with `n = m + 2`, so that `n ≥ 2` is forced by the
type rather than assumed: `0 = r₁ < ⋯ < rₙ = 1` needs at least two points.
-/

/-- The `i`-th point of the uniform discretisation of `[0,1]` into `m + 2`
points, as an element of `CRMDP.Reward`. -/
@[expose] public noncomputable def gridVal (m : ℕ) (i : Fin (m + 2)) : Reward :=
  ⟨(i : ℝ) / (m + 1), by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      have hi : (i : ℕ) ≤ m + 1 := Nat.lt_succ_iff.mp i.isLt
      exact_mod_cast hi⟩

/-- The index of the complementary grid point, print's `r_{n+1-i}`. -/
@[expose] public def gridRev (m : ℕ) (i : Fin (m + 2)) : Fin (m + 2) :=
  ⟨m + 1 - (i : ℕ), by omega⟩

/-- `r₁ = 0`. -/
public theorem gridVal_zero : (gridVal m 0 : ℝ) = 0 := by
  simp [gridVal]

/-- `rₙ = 1`. -/
public theorem gridVal_last :
    (gridVal m (Fin.last (m + 1)) : ℝ) = 1 := by
  have hlast : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) = m + 1 := rfl
  have hpos : ((m : ℝ) + 1) ≠ 0 := by positivity
  show ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) / ((m : ℝ) + 1) = 1
  rw [hlast]
  push_cast
  field_simp

/-- The grid is increasing: `r₁ < r₂ < ⋯ < rₙ`. -/
public theorem gridVal_strictMono :
    StrictMono (fun i : Fin (m + 2) => (gridVal m i : ℝ)) := by
  intro i j hij
  have hlt : (i : ℕ) < (j : ℕ) := hij
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcast : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hlt
  simp only [gridVal]
  gcongr

/-- Grid points are distinct, so an index is recoverable from its value. -/
public theorem gridVal_injective :
    Function.Injective (gridVal (m := m)) := by
  intro i j hij
  have : (gridVal m i : ℝ) = (gridVal m j : ℝ) := by rw [hij]
  exact gridVal_strictMono.injective this

/-- **Uniformity is what closes the class under complementation**: the
complement of a grid point is a grid point, namely the reversed one. -/
public theorem gridVal_gridRev (i : Fin (m + 2)) :
    gridVal m (gridRev m i) = Env.rewardComplement (gridVal m i) := by
  apply Subtype.ext
  have hi : (i : ℕ) ≤ m + 1 := Nat.lt_succ_iff.mp i.isLt
  have hcast : ((m + 1 - (i : ℕ) : ℕ) : ℝ) = ((m : ℝ) + 1) - (i : ℝ) := by
    push_cast [Nat.cast_sub hi]
    ring
  have hpos : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp only [gridVal, gridRev, Env.rewardComplement]
  rw [hcast]
  field_simp

/-- Reversing an index twice is the identity. -/
public theorem gridRev_involutive :
    Function.Involutive (gridRev (m := m)) := by
  intro i
  apply Fin.ext
  have hi : (i : ℕ) ≤ m + 1 := Nat.lt_succ_iff.mp i.isLt
  show m + 1 - (m + 1 - (i : ℕ)) = (i : ℕ)
  omega

/-! ## Print's environment class -/

/--
An environment of print's class: a true reward function and a corruption
function, both valued in the grid, over a transition the whole class shares.

Print's Definition 9 builds the class as a product of *all* functions of these
two shapes, and this structure is exactly that product.
-/
public structure GridEnv (m : ℕ) (State : Type*) where
  /-- `Ṙ : S → R`. -/
  trueReward : State → Fin (m + 2)
  /-- `C : S × R → R`, curried. -/
  corruption : State → Fin (m + 2) → Fin (m + 2)

namespace GridEnv

variable {State : Type*}

/-- `R̂(s) = C_s(Ṙ(s))`, at grid indices. -/
@[expose] public def observed (g : GridEnv m State) (s : State) : Fin (m + 2) :=
  g.corruption s (g.trueReward s)

/-- Print's `μ⁻`: complement the true reward and pre-compose the channel with the
same complementation. Both stay inside the grid, which is the point. -/
@[expose] public def complement (g : GridEnv m State) : GridEnv m State where
  trueReward := fun s => gridRev m (g.trueReward s)
  corruption := fun s x => g.corruption s (gridRev m x)

/-- Complementing twice is the identity, so the class is closed under an
involution rather than merely under a map. -/
public theorem complement_involutive :
    Function.Involutive (complement (m := m) (State := State)) := by
  intro g
  cases g with
  | mk r c =>
      have hr : (fun s => gridRev m (gridRev m (r s))) = r := by
        funext s
        exact gridRev_involutive (r s)
      have hc : (fun s x => c s (gridRev m (gridRev m x))) = c := by
        funext s x
        rw [gridRev_involutive]
      simp only [complement]
      rw [hr, hc]

/-- **Indistinguishability inside the finite class.** -/
public theorem observed_complement (g : GridEnv m State) (s : State) :
    g.complement.observed s = g.observed s := by
  show g.corruption s (gridRev m (gridRev m (g.trueReward s)))
      = g.corruption s (g.trueReward s)
  rw [gridRev_involutive]

/-- The class is finite whenever the state space is, which is print's setting and
what makes every `max` and `min` in its equations (4) and (5) attained. -/
public noncomputable instance instFintype [Fintype State] [DecidableEq State] :
    Fintype (GridEnv m State) :=
  Fintype.ofEquiv ((State → Fin (m + 2)) × (State → Fin (m + 2) → Fin (m + 2)))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun g => (g.trueReward, g.corruption)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro g; cases g; rfl }

public instance instInhabited : Inhabited (GridEnv m State) :=
  ⟨{ trueReward := fun _ => 0, corruption := fun _ x => x }⟩

end GridEnv

/-! ## The embedding into `CRMDP.Env`

Nothing about runs, histories or returns is redefined; the grid class is carried
into the interval-valued class and the existing results are used there.
-/

open Classical in
/--
A grid environment as a `CRMDP.Env`.

Off the grid the corruption channel is the identity. That is a choice with no
consequences: `toEnv_corruption_gridVal` shows the channel is only ever
evaluated at grid points, because it is only ever evaluated at a true reward.
-/
@[expose] public noncomputable def toEnv (g : GridEnv m State) : Env State where
  trueReward := fun s => gridVal m (g.trueReward s)
  corruption := fun s x =>
    if h : ∃ i, x = gridVal m i then gridVal m (g.corruption s h.choose) else x

/-- On the grid, the embedded channel is the grid channel. -/
public theorem toEnv_corruption_gridVal (g : GridEnv m State) (s : State)
    (i : Fin (m + 2)) :
    (toEnv g).corruption s (gridVal m i) = gridVal m (g.corruption s i) := by
  have hex : ∃ j, gridVal m i = gridVal m j := ⟨i, rfl⟩
  have hchoose : hex.choose = i := (gridVal_injective hex.choose_spec).symm
  show (if h : ∃ j, gridVal m i = gridVal m j then
      gridVal m (g.corruption s h.choose) else gridVal m i) = _
  rw [dif_pos hex]
  congr 1
  rw [hchoose]

/-- The embedded observed reward is the grid observed reward. -/
public theorem toEnv_observed (g : GridEnv m State) (s : State) :
    (toEnv g).observed s = gridVal m (g.observed s) := by
  show (toEnv g).corruption s ((toEnv g).trueReward s) = _
  show (toEnv g).corruption s (gridVal m (g.trueReward s)) = _
  rw [toEnv_corruption_gridVal]
  rfl

/-- The embedded true reward is the grid true reward. -/
public theorem toEnv_trueReward (g : GridEnv m State) (s : State) :
    (toEnv g).trueReward s = gridVal m (g.trueReward s) := rfl

/-- A run depends on the environment **only through its observed reward
function**. This is what lets the embedding be a modelling convenience rather
than a second development.

Since `CRMDP.run` is `AISafetyAtlas.Decision.detRun` at `CRMDP.Env.channel`, this
is the carrier's `Decision.detRun_congr_obs` — the run sees the world only
through the observation map — with the observation of a state unfolded. -/
public theorem run_congr_observed (transition : State → Action → State)
    (μ ν : Env State) (π : Policy State Action) (s₀ : State)
    (hobs : ∀ s, μ.observed s = ν.observed s) :
    ∀ n : ℕ, run transition μ π s₀ n = run transition ν π s₀ n :=
  Decision.detRun_congr_obs transition
    (fun s => by rw [Env.channel, Env.channel, hobs]) π s₀

/-- The complement of an embedded environment is the embedding of its
complement, as far as anything observable is concerned. -/
public theorem observed_toEnv_complement (g : GridEnv m State) (s : State) :
    (toEnv g.complement).observed s = (toEnv g).complement.observed s := by
  rw [toEnv_observed, Env.observed_complement, toEnv_observed,
    GridEnv.observed_complement]

/-- Hence the two agree on every run. -/
public theorem stateAt_toEnv_complement (transition : State → Action → State)
    (g : GridEnv m State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stateAt transition (toEnv g.complement) π s₀ n =
      stateAt transition (toEnv g).complement π s₀ n :=
  Decision.detStateAt_congr_obs transition
    (fun s => by rw [Env.channel, Env.channel, observed_toEnv_complement g s]) π s₀ n


/-! ## Returns over the grid class -/

/-- Finite-horizon true return of a grid environment: `CRMDP.returnOver` at the
embedded environment, so there is one return function in the tree and not two. -/
@[expose] public noncomputable def gridReturn (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) : ℝ :=
  returnOver transition t s₀ (toEnv g) π

/-- Embedding commutes with complementation as far as the return is concerned. -/
public theorem returnOver_toEnv_complement (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    returnOver transition t s₀ (toEnv g.complement) π =
      returnOver transition t s₀ (toEnv g).complement π := by
  unfold returnOver
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stateAt_toEnv_complement transition g π s₀ (k + 1)]
  have : (toEnv g.complement).trueReward
      (stateAt transition (toEnv g).complement π s₀ (k + 1))
      = (toEnv g).complement.trueReward
        (stateAt transition (toEnv g).complement π s₀ (k + 1)) := by
    show gridVal m (gridRev m (g.trueReward _)) = _
    exact gridVal_gridRev _
  rw [this]

/-- **Print's equation (3) inside the finite class.** -/
public theorem gridReturn_add_complement (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    gridReturn transition t s₀ g π +
        gridReturn transition t s₀ g.complement π = (t : ℝ) := by
  unfold gridReturn
  rw [returnOver_toEnv_complement]
  exact return_add_complement transition t s₀ (toEnv g) π

/-! ## Extrema over the policy function space, derived from finiteness

Print's equations (4) and (5) take `max` and `min` over policies without
comment, which is legitimate because its state, action and reward sets are all
finite. The argument is spelled out here: a horizon-`t` return reads a policy
only at the `t` histories the rollout reaches, those histories have pairwise
distinct action-list lengths, so every length-`t` action sequence is realised by
some policy and conversely — and there are finitely many of those.
-/

/-- The state reached when the actions are read off a fixed sequence rather than
chosen by a policy. -/
@[expose] public def seqState (transition : State → Action → State) (s₀ : State)
    (as : ℕ → Action) : ℕ → State
  | 0 => s₀
  | k + 1 => transition (seqState transition s₀ as k) (as k)

/-- A rollout under a policy is a rollout under the action sequence it happens to
produce. -/
public theorem stateAt_eq_seqState (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) :
    ∀ n : ℕ, stateAt transition μ π s₀ n =
      seqState transition s₀ (fun j => π (historyUpTo transition μ π s₀ j)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show transition (stateAt transition μ π s₀ n)
          (π (historyUpTo transition μ π s₀ n)) = _
      rw [ih]
      rfl

/-- The history after `n` steps carries exactly `n` actions. -/
public theorem historyUpTo_length (transition : State → Action → State)
    (μ : Env State) (π : Policy State Action) (s₀ : State) :
    ∀ n : ℕ, (historyUpTo transition μ π s₀ n).2.length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show ((historyUpTo transition μ π s₀ n).2 ++ [_]).length = n + 1
      simp [ih]

/-- The policy that plays a fixed action sequence, indexed by how many actions
have already been taken. Every action sequence is realised this way, which is the
converse direction the attainment argument needs. -/
@[expose] public def seqPolicy (as : ℕ → Action) : Policy State Action :=
  fun h => as h.2.length

/-- And that policy's rollout is the sequence's rollout. -/
public theorem stateAt_seqPolicy (transition : State → Action → State)
    (μ : Env State) (s₀ : State) (as : ℕ → Action) :
    ∀ n : ℕ, stateAt transition μ (seqPolicy as) s₀ n =
      seqState transition s₀ as n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show transition (stateAt transition μ (seqPolicy as) s₀ n)
          (seqPolicy as (historyUpTo transition μ (seqPolicy as) s₀ n)) = _
      rw [ih]
      show transition _ (as (historyUpTo transition μ (seqPolicy as) s₀ n).2.length) = _
      rw [historyUpTo_length]
      simp only [seqState]

/-- A rollout of length `k` reads only the first `k` actions. -/
public theorem seqState_congr (transition : State → Action → State) (s₀ : State)
    (as bs : ℕ → Action) :
    ∀ k : ℕ, (∀ j, j < k → as j = bs j) →
      seqState transition s₀ as k = seqState transition s₀ bs k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      show transition (seqState transition s₀ as k) (as k) = _
      rw [ih (fun j hj => h j (by omega)), h k (by omega)]
      simp only [seqState]

/-- The return as a function of the action sequence. -/
@[expose] public noncomputable def seqReturn (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (as : ℕ → Action) : ℝ :=
  ∑ k ∈ Finset.range t,
    ((gridVal m (g.trueReward (seqState transition s₀ as (k + 1))) : Reward) : ℝ)

public theorem gridReturn_eq_seqReturn (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    gridReturn transition t s₀ g π =
      seqReturn transition t s₀ g
        (fun j => π (historyUpTo transition (toEnv g) π s₀ j)) := by
  unfold gridReturn returnOver seqReturn
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stateAt_eq_seqState transition (toEnv g) π s₀ (k + 1)]
  rfl

public theorem seqReturn_eq_gridReturn (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (as : ℕ → Action) :
    seqReturn transition t s₀ g as =
      gridReturn transition t s₀ g (seqPolicy as) := by
  unfold gridReturn returnOver seqReturn
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stateAt_seqPolicy transition (toEnv g) s₀ as (k + 1)]
  rfl

/-- A length-`t` action tuple, extended by a default action past the horizon. -/
@[expose] public def extendSeq (t : ℕ) (v : Fin t → Action) (a₀ : Action) :
    ℕ → Action :=
  fun j => if h : j < t then v ⟨j, h⟩ else a₀

/-- Only the first `t` actions matter, so the return factors through a finite
type. -/
public theorem seqReturn_extendSeq (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (as : ℕ → Action) (a₀ : Action) :
    seqReturn transition t s₀ g as =
      seqReturn transition t s₀ g (extendSeq t (fun i : Fin t => as i) a₀) := by
  unfold seqReturn
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkt : k < t := Finset.mem_range.mp hk
  rw [seqState_congr transition s₀ as (extendSeq t (fun i : Fin t => as i) a₀)
    (k + 1) (fun j hj => ?_)]
  have hjt : j < t := by omega
  show as j = extendSeq t (fun i : Fin t => as i) a₀ j
  rw [extendSeq, dif_pos hjt]

variable [Fintype Action] [Nonempty Action]

/-- **The maximum over the whole policy function space is attained.** -/
public theorem exists_max_gridReturn (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) :
    ∃ best : Policy State Action, ∀ π : Policy State Action,
      gridReturn transition t s₀ g π ≤ gridReturn transition t s₀ g best := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty Action›
  obtain ⟨v₀, -, hv₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin t → Action))
      (fun v => seqReturn transition t s₀ g (extendSeq t v a₀))
      ⟨fun _ => a₀, Finset.mem_univ _⟩
  refine ⟨seqPolicy (extendSeq t v₀ a₀), fun π => ?_⟩
  rw [← seqReturn_eq_gridReturn transition t s₀ g (extendSeq t v₀ a₀),
    gridReturn_eq_seqReturn transition t s₀ g π,
    seqReturn_extendSeq transition t s₀ g
      (fun j => π (historyUpTo transition (toEnv g) π s₀ j)) a₀]
  exact hv₀ _ (Finset.mem_univ _)

/-- **The minimum over the whole policy function space is attained.** -/
public theorem exists_min_gridReturn (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) :
    ∃ worst : Policy State Action, ∀ π : Policy State Action,
      gridReturn transition t s₀ g worst ≤ gridReturn transition t s₀ g π := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty Action›
  obtain ⟨v₀, -, hv₀⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin t → Action))
      (fun v => seqReturn transition t s₀ g (extendSeq t v a₀))
      ⟨fun _ => a₀, Finset.mem_univ _⟩
  refine ⟨seqPolicy (extendSeq t v₀ a₀), fun π => ?_⟩
  rw [← seqReturn_eq_gridReturn transition t s₀ g (extendSeq t v₀ a₀),
    gridReturn_eq_seqReturn transition t s₀ g π,
    seqReturn_extendSeq transition t s₀ g
      (fun j => π (historyUpTo transition (toEnv g) π s₀ j)) a₀]
  exact hv₀ _ (Finset.mem_univ _)

/-! ## Theorem 11 over print's own hypothesis class

Every field of `Corruption.ComplementedClass` is now discharged rather than
supplied: completeness of the class is structural, equation (3) is
`gridReturn_add_complement`, and the three extrema come from the two attainment
lemmas above together with finiteness of the class itself.

Binders here are written out rather than taken from a `variable` block, because
`m` occurs only in the *result* type of several of them.
-/

section Model

variable [Fintype State] [DecidableEq State]

/-- An optimal policy for an environment, **derived** from finiteness. -/
@[expose] public noncomputable def bestPolicy (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State)
    (g : GridEnv m State) : Policy State Action :=
  (exists_max_gridReturn transition t s₀ g).choose

omit [Fintype State] [DecidableEq State] in
public theorem bestPolicy_best (m : ℕ) (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    gridReturn transition t s₀ g π ≤
      gridReturn transition t s₀ g (bestPolicy m transition t s₀ g) :=
  (exists_max_gridReturn transition t s₀ g).choose_spec π

/-- A worst policy for an environment, likewise derived. -/
@[expose] public noncomputable def minPolicy (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State)
    (g : GridEnv m State) : Policy State Action :=
  (exists_min_gridReturn transition t s₀ g).choose

omit [Fintype State] [DecidableEq State] in
public theorem minPolicy_min (m : ℕ) (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    gridReturn transition t s₀ g (minPolicy m transition t s₀ g) ≤
      gridReturn transition t s₀ g π :=
  (exists_min_gridReturn transition t s₀ g).choose_spec π

/-- Print's Definition 10 regret, inside the finite class. -/
@[expose] public noncomputable def gridRegret (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State)
    (g : GridEnv m State) (π : Policy State Action) : ℝ :=
  gridReturn transition t s₀ g (bestPolicy m transition t s₀ g) -
    gridReturn transition t s₀ g π

/-- An environment witnessing a policy's worst-case regret, from finiteness of
the class. -/
@[expose] public noncomputable def worstEnvironment (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State)
    (π : Policy State Action) : GridEnv m State :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => gridRegret m transition t s₀ g π)
    ⟨default, Finset.mem_univ _⟩).choose

public theorem worstEnvironment_worst (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State)
    (π : Policy State Action) (g : GridEnv m State) :
    gridRegret m transition t s₀ g π ≤
      gridRegret m transition t s₀ (worstEnvironment m transition t s₀ π) π :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => gridRegret m transition t s₀ g π)
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 g (Finset.mem_univ g)

/-- The environment on which the spread between the best and the worst
achievable return is largest — print's `μ*`. -/
@[expose] public noncomputable def spreadEnv (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State) :
    GridEnv m State :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => gridReturn transition t s₀ g (bestPolicy m transition t s₀ g) -
      gridReturn transition t s₀ g (minPolicy m transition t s₀ g))
    ⟨default, Finset.mem_univ _⟩).choose

public theorem spreadEnv_max (m : ℕ) (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) :
    gridReturn transition t s₀ g (bestPolicy m transition t s₀ g) -
        gridReturn transition t s₀ g (minPolicy m transition t s₀ g) ≤
      gridReturn transition t s₀ (spreadEnv m transition t s₀)
          (bestPolicy m transition t s₀ (spreadEnv m transition t s₀)) -
        gridReturn transition t s₀ (spreadEnv m transition t s₀)
          (minPolicy m transition t s₀ (spreadEnv m transition t s₀)) :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => gridReturn transition t s₀ g (bestPolicy m transition t s₀ g) -
      gridReturn transition t s₀ g (minPolicy m transition t s₀ g))
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 g (Finset.mem_univ g)

/-- A policy of maximal worst-case regret: play worst in the widest-spread
environment. -/
@[expose] public noncomputable def worstPolicy (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State) :
    Policy State Action :=
  minPolicy m transition t s₀ (spreadEnv m transition t s₀)

public theorem worstPolicy_worst (m : ℕ) (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (π : Policy State Action) :
    gridRegret m transition t s₀ (worstEnvironment m transition t s₀ π) π ≤
      gridRegret m transition t s₀
        (worstEnvironment m transition t s₀ (worstPolicy m transition t s₀))
        (worstPolicy m transition t s₀) := by
  have h1 :
      gridReturn transition t s₀ (worstEnvironment m transition t s₀ π)
          (minPolicy m transition t s₀
            (worstEnvironment m transition t s₀ π)) ≤
        gridReturn transition t s₀ (worstEnvironment m transition t s₀ π) π :=
    minPolicy_min m transition t s₀ (worstEnvironment m transition t s₀ π) π
  have h2 := spreadEnv_max m transition t s₀ (worstEnvironment m transition t s₀ π)
  have h3 :
      gridRegret m transition t s₀ (spreadEnv m transition t s₀)
          (worstPolicy m transition t s₀) ≤
        gridRegret m transition t s₀
          (worstEnvironment m transition t s₀ (worstPolicy m transition t s₀))
          (worstPolicy m transition t s₀) :=
    worstEnvironment_worst m transition t s₀ (worstPolicy m transition t s₀)
      (spreadEnv m transition t s₀)
  unfold gridRegret at h3 ⊢
  unfold worstPolicy at h3 ⊢
  linarith

/--
**Print's hypothesis class as a complemented class**, with nothing assumed.

Completeness is structural — `GridEnv` is the full product of the two function
spaces print takes "all functions" of — equation (3) is proved, and all three
extrema are derived from finiteness rather than supplied.
-/
@[expose] public noncomputable def toComplementedClass (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State) :
    Corruption.ComplementedClass (GridEnv m State) (Policy State Action) where
  returnValue := gridReturn transition t s₀
  horizon := (t : ℝ)
  complement := GridEnv.complement
  complement_involutive := GridEnv.complement_involutive
  complement_return := gridReturn_add_complement transition t s₀
  bestPolicy := bestPolicy m transition t s₀
  bestPolicy_best := bestPolicy_best m transition t s₀
  worstEnvironment := worstEnvironment m transition t s₀
  worstEnvironment_worst := fun π g => worstEnvironment_worst m transition t s₀ π g
  worstPolicy := worstPolicy m transition t s₀
  worstPolicy_worst := worstPolicy_worst m transition t s₀

/--
**Everitt et al. Theorem 11 over print's own hypothesis class.**

Every policy's worst-case regret is at least half a worst policy's, where the
class is the full product of grid-valued true-reward and corruption functions
over a uniform discretisation of `[0,1]` — print's class, not a proxy for it —
and where the three extrema print takes without comment are attained rather than
assumed.

What separates this from print's statement is the transition: print's is a
stochastic kernel and its returns are expectations, and this is the
deterministic case. See the module header.
-/
public theorem everitt_theorem_eleven_gridClass (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State)
    (π : Policy State Action) :
    (toComplementedClass m transition t s₀).worstCaseRegret
        (toComplementedClass m transition t s₀).worstPolicy / 2 ≤
      (toComplementedClass m transition t s₀).worstCaseRegret π :=
  (toComplementedClass m transition t s₀).everitt_theorem_eleven π

/-- The half-maximal regret certificate, over print's class. -/
public theorem halfMaximalRegretBound (m : ℕ)
    (transition : State → Action → State) (t : ℕ) (s₀ : State) :
    AISafetyAtlas.Preference.HalfMaximalRegretBound
      (toComplementedClass m transition t s₀).toRegretModel :=
  (toComplementedClass m transition t s₀).halfMaximalRegretBound

/-! ## Print's Definition 9 in full: the product over transitions as well

`toComplementedClass` above shares one transition across the class, so the
`T`-component of print's Definition 9 is a singleton there. Definition 9 takes
the product over **all three** of `T`, the reward functions and the corruption
functions, where each is *a given set*. The class below is that product.

The transition component is an arbitrary index type together with its map into
transition functions, which is at least as general as print's "given set `T`":
any set of transitions is such a type, by its own inclusion. It is not
specialised to all functions, and it must not be -- `worstCaseRegret` is a
maximum over the class, and a maximum over a larger class is larger, so neither
a singleton `T` nor a full-function-space `T` gives print's arbitrary one.

The reward and corruption components stay as `GridEnv`, the full product of the
two function spaces, because that is what Theorem 11 *assumes* of them. Theorem
11 assumes nothing whatever about `T`, which is why it may be left arbitrary
here.

The fibre argument does not suffice, and that is why this is built rather than
derived: Theorem 11 on each fixed-transition fibre does not give Theorem 11 on
the product, for the same reason about maxima. Every extremum below is therefore
rederived over the product, which is finite whenever the index type is.
-/

/-- Print's Definition 9 class: a transition drawn from a given set, together
with the reward and corruption components. -/
public structure FullEnv (m : ℕ) (Trans State : Type*) where
  /-- The index of the transition, ranging over print's given set `T`. -/
  transition : Trans
  /-- The reward and corruption components. -/
  grid : GridEnv m State

variable {Trans : Type*}

/-- Print's complement on the full class: the transition is untouched, which is
what print's own construction does -- it moves the reward and the channel only. -/
@[expose] public def FullEnv.complement (e : FullEnv m Trans State) :
    FullEnv m Trans State :=
  ⟨e.transition, e.grid.complement⟩

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] in
public theorem FullEnv.complement_involutive :
    Function.Involutive
      (FullEnv.complement (m := m) (Trans := Trans) (State := State)) := by
  intro e
  cases e with
  | mk T g =>
      show (⟨T, g.complement.complement⟩ : FullEnv m Trans State) = ⟨T, g⟩
      rw [GridEnv.complement_involutive g]

public instance FullEnv.instInhabited [Inhabited Trans] :
    Inhabited (FullEnv m Trans State) :=
  ⟨{ transition := default, grid := default }⟩

/-- The class is finite whenever the given set of transitions is, which is
print's setting and what keeps every extremum below attained. -/
public noncomputable instance FullEnv.instFintype [Fintype Trans] :
    Fintype (FullEnv m Trans State) := by
  classical
  exact Fintype.ofEquiv (Trans × GridEnv m State)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun e => (e.transition, e.grid)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro e; cases e; rfl }

/-- The return of a member, at the transition its index names. -/
@[expose] public noncomputable def fullReturn
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (π : Policy State Action) : ℝ :=
  gridReturn (trans e.transition) t s₀ e.grid π

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] in
/-- **Equation (3) on the full class.** The complement keeps the transition, so
each fibre's own proof is the whole content. -/
public theorem fullReturn_add_complement
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (π : Policy State Action) :
    fullReturn trans t s₀ e π + fullReturn trans t s₀ e.complement π = (t : ℝ) :=
  gridReturn_add_complement (trans e.transition) t s₀ e.grid π

/-- An optimal policy for a member, derived as in each fibre. -/
@[expose] public noncomputable def fullBest (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) : Policy State Action :=
  bestPolicy m (trans e.transition) t s₀ e.grid

omit [Fintype State] [DecidableEq State] in
public theorem fullBest_best (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (π : Policy State Action) :
    fullReturn trans t s₀ e π ≤ fullReturn trans t s₀ e (fullBest m trans t s₀ e) :=
  bestPolicy_best m (trans e.transition) t s₀ e.grid π

/-- A worst policy for a member, likewise. -/
@[expose] public noncomputable def fullMin (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) : Policy State Action :=
  minPolicy m (trans e.transition) t s₀ e.grid

omit [Fintype State] [DecidableEq State] in
public theorem fullMin_min (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (π : Policy State Action) :
    fullReturn trans t s₀ e (fullMin m trans t s₀ e) ≤ fullReturn trans t s₀ e π :=
  minPolicy_min m (trans e.transition) t s₀ e.grid π

/-- Definition 10's regret, on the full class. -/
@[expose] public noncomputable def fullRegret (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (π : Policy State Action) : ℝ :=
  fullReturn trans t s₀ e (fullBest m trans t s₀ e) - fullReturn trans t s₀ e π

section FullExtrema

variable [Fintype Trans] [Inhabited Trans]

/-- The member witnessing a policy's worst-case regret, from finiteness of the
**product**. -/
@[expose] public noncomputable def fullWorstEnv (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (π : Policy State Action) : FullEnv m Trans State :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullRegret m trans t s₀ e π) ⟨default, Finset.mem_univ _⟩).choose

public theorem fullWorstEnv_worst (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (π : Policy State Action) (e : FullEnv m Trans State) :
    fullRegret m trans t s₀ e π ≤
      fullRegret m trans t s₀ (fullWorstEnv m trans t s₀ π) π :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullRegret m trans t s₀ e π)
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 e (Finset.mem_univ e)

/-- Print's `μ*`, now chosen over the transition index as well: the member whose
best-to-worst spread is largest. -/
@[expose] public noncomputable def fullSpreadEnv (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State) :
    FullEnv m Trans State :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullReturn trans t s₀ e (fullBest m trans t s₀ e) -
      fullReturn trans t s₀ e (fullMin m trans t s₀ e))
    ⟨default, Finset.mem_univ _⟩).choose

public theorem fullSpreadEnv_max (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) :
    fullReturn trans t s₀ e (fullBest m trans t s₀ e) -
        fullReturn trans t s₀ e (fullMin m trans t s₀ e) ≤
      fullReturn trans t s₀ (fullSpreadEnv m trans t s₀)
          (fullBest m trans t s₀ (fullSpreadEnv m trans t s₀)) -
        fullReturn trans t s₀ (fullSpreadEnv m trans t s₀)
          (fullMin m trans t s₀ (fullSpreadEnv m trans t s₀)) :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullReturn trans t s₀ e (fullBest m trans t s₀ e) -
      fullReturn trans t s₀ e (fullMin m trans t s₀ e))
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 e (Finset.mem_univ e)

/-- A policy of maximal worst-case regret over the product class. -/
@[expose] public noncomputable def fullWorstPolicy (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State) :
    Policy State Action :=
  fullMin m trans t s₀ (fullSpreadEnv m trans t s₀)

public theorem fullWorstPolicy_worst (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (π : Policy State Action) :
    fullRegret m trans t s₀ (fullWorstEnv m trans t s₀ π) π ≤
      fullRegret m trans t s₀
        (fullWorstEnv m trans t s₀ (fullWorstPolicy m trans t s₀))
        (fullWorstPolicy m trans t s₀) := by
  have h1 : fullReturn trans t s₀ (fullWorstEnv m trans t s₀ π)
      (fullMin m trans t s₀ (fullWorstEnv m trans t s₀ π)) ≤
        fullReturn trans t s₀ (fullWorstEnv m trans t s₀ π) π :=
    fullMin_min m trans t s₀ (fullWorstEnv m trans t s₀ π) π
  have h2 := fullSpreadEnv_max m trans t s₀ (fullWorstEnv m trans t s₀ π)
  have h3 : fullRegret m trans t s₀ (fullSpreadEnv m trans t s₀)
        (fullWorstPolicy m trans t s₀) ≤
      fullRegret m trans t s₀
        (fullWorstEnv m trans t s₀ (fullWorstPolicy m trans t s₀))
        (fullWorstPolicy m trans t s₀) :=
    fullWorstEnv_worst m trans t s₀ (fullWorstPolicy m trans t s₀)
      (fullSpreadEnv m trans t s₀)
  unfold fullRegret at h3 ⊢
  unfold fullWorstPolicy at h3 ⊢
  linarith

/--
**Print's Definition 9 class, in full, as a complemented class.**

The product runs over the given set of transitions as well as over the reward
and corruption functions, and all three extrema are still derived rather than
supplied.
-/
@[expose] public noncomputable def toFullComplementedClass (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State) :
    Corruption.ComplementedClass (FullEnv m Trans State) (Policy State Action) where
  returnValue := fullReturn trans t s₀
  horizon := (t : ℝ)
  complement := FullEnv.complement
  complement_involutive := FullEnv.complement_involutive
  complement_return := fullReturn_add_complement trans t s₀
  bestPolicy := fullBest m trans t s₀
  bestPolicy_best := fun e π => fullBest_best m trans t s₀ e π
  worstEnvironment := fullWorstEnv m trans t s₀
  worstEnvironment_worst := fun π e => fullWorstEnv_worst m trans t s₀ π e
  worstPolicy := fullWorstPolicy m trans t s₀
  worstPolicy_worst := fullWorstPolicy_worst m trans t s₀

/--
**Theorem 11 over print's Definition 9 class, transitions included.**

`everitt_theorem_eleven_gridClass` proves this at one transition.  Here the
`T`-component is print's own: an arbitrary given set of transitions, over which
the maximum defining `worstCaseRegret` ranges.
-/
public theorem everitt_theorem_eleven_fullClass (m : ℕ)
    (trans : Trans → State → Action → State) (t : ℕ) (s₀ : State)
    (π : Policy State Action) :
    (toFullComplementedClass m trans t s₀).worstCaseRegret
        (toFullComplementedClass m trans t s₀).worstPolicy / 2 ≤
      (toFullComplementedClass m trans t s₀).worstCaseRegret π :=
  (toFullComplementedClass m trans t s₀).everitt_theorem_eleven π

end FullExtrema

end Model

/-! ## A finite observation alphabet underneath the real-valued one

`CRMDP` observes `Obs State = State × Reward`, and `Reward` is `Set.Icc (0 : ℝ) 1`,
so the observation alphabet is **infinite** however small the state space is. That
is what stops `Decision.exists_max_of_truncates` from reaching this cluster: a
policy's domain never truncates to a finite table, so a maximum over the policy
space is not attained by counting.

A grid environment only ever emits grid points. `gridChannel` is the channel it
really has -- a state and a grid index, both finite -- and `gridLabel` is the
injection of that alphabet into print's real-valued one. `Decision.MDP.run` is
generic in the observation type, so nothing is duplicated: `channel_toEnv` says
the two are the same channel read at two alphabets, and
`Decision.MDP.stateAt_mapObs` does the rest.
-/

/-- The channel a grid environment really has: finite. -/
@[expose] public def gridChannel (g : GridEnv m State) (s : State) : State × Fin (m + 2) :=
  (s, g.observed s)

/-- The injection of the grid alphabet into `CRMDP`'s real-valued one. -/
@[expose] public noncomputable def gridLabel (m : ℕ) (p : State × Fin (m + 2)) :
    Obs State :=
  (p.1, gridVal m p.2)

omit [Fintype Action] [Nonempty Action] in
public theorem gridLabel_injective :
    Function.Injective (gridLabel (m := m) (State := State)) := by
  rintro ⟨s, i⟩ ⟨s', j⟩ h
  have h1 : s = s' := congrArg Prod.fst h
  have h2 : gridVal m i = gridVal m j := congrArg Prod.snd h
  rw [h1, gridVal_injective h2]

omit [Fintype Action] [Nonempty Action] in
/-- **The embedded channel is the grid channel, relabelled.** -/
public theorem channel_toEnv (g : GridEnv m State) (s : State) :
    Env.channel (toEnv g) s = gridLabel m (gridChannel g s) := by
  show ((s, (toEnv g).observed s) : Obs State) = (s, gridVal m (g.observed s))
  rw [toEnv_observed]

omit [Fintype Action] [Nonempty Action] in
/-- **The state distribution of a grid environment is computed at the finite
alphabet.** The real-valued labels are carried along and change nothing. -/
public theorem stochStateAt_toEnv (M : Decision.MDP State Action) (g : GridEnv m State)
    (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stochStateAt M (toEnv g) π s₀ n
      = M.stateAt (gridChannel g)
          (Decision.Policy.ofDet fun h => π (Decision.History.mapObs (gridLabel m) h))
          s₀ n := by
  rw [stochStateAt,
    Decision.MDP.stateAt_congr_obs M (fun s => channel_toEnv g s)
      (Decision.Policy.ofDet π) s₀ n]
  exact Decision.MDP.stateAt_mapObs M (gridLabel m) (gridChannel g)
    (Decision.Policy.ofDet π) s₀ n

/-! ## The extrema over the policy space, at a drawn transition

With the finite alphabet underneath, `Decision.exists_max_of_truncates` applies
and both extrema over the **whole** policy space are attained, for a transition
that may be a distribution. This is the step the module header called larger than
itself, and the one the Theorem 11 row needs for its join.
-/

/-- The expected return of a grid environment, read as a function of the policy
over the finite alphabet. -/
@[expose] public noncomputable def gridStochReturn (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (g : GridEnv m State)
    (ρ : Decision.DetPolicy (State × Fin (m + 2)) Action) : ℝ :=
  ∑ k ∈ Finset.range t,
    expectReward (M.stateAt (gridChannel g) (Decision.Policy.ofDet ρ) s₀ (k + 1))
      (toEnv g).trueReward

omit [Fintype Action] [Nonempty Action] in
/-- The real-alphabet return is the finite-alphabet return at the relabelled
policy. -/
public theorem stochReturnOver_toEnv (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    stochReturnOver M t s₀ (toEnv g) π
      = gridStochReturn M t s₀ g
          (fun h => π (Decision.History.mapObs (gridLabel m) h)) := by
  rw [stochReturnOver, gridStochReturn]
  exact Finset.sum_congr rfl fun k _ => by rw [stochStateAt_toEnv]

omit [Fintype Action] [Nonempty Action] in
/-- A run of `t` steps sees the grid policy only on histories shorter than `t`. -/
public theorem gridStochReturn_congr (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State)
    {ρ₁ ρ₂ : Decision.DetPolicy (State × Fin (m + 2)) Action}
    (h : ∀ hst : Decision.History (State × Fin (m + 2)) Action,
      hst.2.length < t → ρ₁ hst = ρ₂ hst) :
    gridStochReturn M t s₀ g ρ₁ = gridStochReturn M t s₀ g ρ₂ := by
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  refine Decision.MDP.stateAt_congr_policy M (gridChannel g) s₀ (k + 1) fun hst hlt => ?_
  simp only [Decision.Policy.ofDet,
    h hst (lt_of_lt_of_le hlt (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))]

section StochGridExtrema

variable [Fintype State] [DecidableEq State]

/-- **The maximum of the expected return over the whole policy space is
attained**, with the transition drawn rather than determined. -/
public theorem exists_max_stochGridReturn (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) :
    ∃ best : Policy State Action, ∀ π : Policy State Action,
      stochReturnOver M t s₀ (toEnv g) π ≤ stochReturnOver M t s₀ (toEnv g) best := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty Action›
  obtain ⟨ρ, hρ⟩ :=
    Decision.exists_max_of_truncates (n := t) a₀ (gridStochReturn M t s₀ g)
      (fun _ _ hagree => gridStochReturn_congr M t s₀ g hagree)
  have hinj := Decision.History.mapObs_injective (A := Action)
    (gridLabel_injective (m := m) (State := State))
  refine ⟨Function.extend (Decision.History.mapObs (gridLabel m)) ρ (fun _ => a₀), fun π => ?_⟩
  have hbest : (fun h => Function.extend (Decision.History.mapObs (gridLabel m)) ρ
      (fun _ => a₀) (Decision.History.mapObs (gridLabel m) h)) = ρ := by
    funext h
    exact hinj.extend_apply _ _ h
  rw [stochReturnOver_toEnv, stochReturnOver_toEnv, hbest]
  exact hρ _

/-- And the minimum. -/
public theorem exists_min_stochGridReturn (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) :
    ∃ worst : Policy State Action, ∀ π : Policy State Action,
      stochReturnOver M t s₀ (toEnv g) worst ≤ stochReturnOver M t s₀ (toEnv g) π := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty Action›
  obtain ⟨ρ, hρ⟩ :=
    Decision.exists_min_of_truncates (n := t) a₀ (gridStochReturn M t s₀ g)
      (fun _ _ hagree => gridStochReturn_congr M t s₀ g hagree)
  have hinj := Decision.History.mapObs_injective (A := Action)
    (gridLabel_injective (m := m) (State := State))
  refine ⟨Function.extend (Decision.History.mapObs (gridLabel m)) ρ (fun _ => a₀), fun π => ?_⟩
  have hbest : (fun h => Function.extend (Decision.History.mapObs (gridLabel m)) ρ
      (fun _ => a₀) (Decision.History.mapObs (gridLabel m) h)) = ρ := by
    funext h
    exact hinj.extend_apply _ _ h
  rw [stochReturnOver_toEnv, stochReturnOver_toEnv, hbest]
  exact hρ _

/-! ## Theorem 11 over print's class, with drawn dynamics and derived extrema

This is axes *(a)*, *(b)* and *(c)* of the Theorem 11 row in one statement: the
class is the full product of grid-valued reward and corruption functions, the
transition is a distribution, and all three extrema are derived from finiteness
rather than supplied as fields. Only *(d)*, print's possibly stochastic policy,
is still absent.
-/

omit [Fintype State] [DecidableEq State] in
/-- Embedding commutes with complementation, for the true reward. -/
public theorem trueReward_toEnv_complement (g : GridEnv m State) (s : State) :
    (toEnv g.complement).trueReward s = (toEnv g).complement.trueReward s := by
  show gridVal m (gridRev m (g.trueReward s)) = _
  exact gridVal_gridRev _

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] in
/-- And for the drawn state distribution. -/
public theorem stochStateAt_toEnv_complement (M : Decision.MDP State Action)
    (g : GridEnv m State) (π : Policy State Action) (s₀ : State) (n : ℕ) :
    stochStateAt M (toEnv g.complement) π s₀ n
      = stochStateAt M (toEnv g).complement π s₀ n := by
  rw [stochStateAt, stochStateAt]
  exact Decision.MDP.stateAt_congr_obs M
    (fun s => by rw [Env.channel, Env.channel, observed_toEnv_complement g s])
    (Decision.Policy.ofDet π) s₀ n

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] in
/-- Hence for the expected return. -/
public theorem stochReturnOver_toEnv_complement (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    stochReturnOver M t s₀ (toEnv g.complement) π
      = stochReturnOver M t s₀ (toEnv g).complement π := by
  unfold stochReturnOver
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stochStateAt_toEnv_complement]
  congr 1
  funext s
  exact trueReward_toEnv_complement g s

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] in
/-- **Print's equation (3) inside the finite class, with drawn dynamics.** -/
public theorem stochGridReturn_add_complement (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (π : Policy State Action) :
    stochReturnOver M t s₀ (toEnv g) π +
        stochReturnOver M t s₀ (toEnv g.complement) π = (t : ℝ) := by
  rw [stochReturnOver_toEnv_complement]
  exact stochReturn_add_complement M t s₀ (toEnv g) π

section StochGridClass

/-- An optimal policy for a grid environment under drawn dynamics, derived. -/
@[expose] public noncomputable def stochBestPolicy (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (g : GridEnv m State) :
    Policy State Action :=
  (exists_max_stochGridReturn M t s₀ g).choose

public theorem stochBestPolicy_best (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (g : GridEnv m State)
    (π : Policy State Action) :
    stochReturnOver M t s₀ (toEnv g) π ≤
      stochReturnOver M t s₀ (toEnv g) (stochBestPolicy m M t s₀ g) :=
  (exists_max_stochGridReturn M t s₀ g).choose_spec π

/-- A worst policy, likewise derived. -/
@[expose] public noncomputable def stochMinPolicy (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (g : GridEnv m State) :
    Policy State Action :=
  (exists_min_stochGridReturn M t s₀ g).choose

public theorem stochMinPolicy_min (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (g : GridEnv m State)
    (π : Policy State Action) :
    stochReturnOver M t s₀ (toEnv g) (stochMinPolicy m M t s₀ g) ≤
      stochReturnOver M t s₀ (toEnv g) π :=
  (exists_min_stochGridReturn M t s₀ g).choose_spec π

/-- Definition 10's regret, with drawn dynamics. -/
@[expose] public noncomputable def stochGridRegret (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (g : GridEnv m State)
    (π : Policy State Action) : ℝ :=
  stochReturnOver M t s₀ (toEnv g) (stochBestPolicy m M t s₀ g) -
    stochReturnOver M t s₀ (toEnv g) π

/-- The environment witnessing a policy's worst-case regret. -/
@[expose] public noncomputable def stochWorstEnv (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (π : Policy State Action) :
    GridEnv m State :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => stochGridRegret m M t s₀ g π) ⟨default, Finset.mem_univ _⟩).choose

public theorem stochWorstEnv_worst (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (π : Policy State Action)
    (g : GridEnv m State) :
    stochGridRegret m M t s₀ g π ≤ stochGridRegret m M t s₀ (stochWorstEnv m M t s₀ π) π :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => stochGridRegret m M t s₀ g π)
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 g (Finset.mem_univ g)

/-- Print's environment of widest spread. -/
@[expose] public noncomputable def stochSpreadEnv (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) : GridEnv m State :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => stochReturnOver M t s₀ (toEnv g) (stochBestPolicy m M t s₀ g) -
      stochReturnOver M t s₀ (toEnv g) (stochMinPolicy m M t s₀ g))
    ⟨default, Finset.mem_univ _⟩).choose

public theorem stochSpreadEnv_max (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (g : GridEnv m State) :
    stochReturnOver M t s₀ (toEnv g) (stochBestPolicy m M t s₀ g) -
        stochReturnOver M t s₀ (toEnv g) (stochMinPolicy m M t s₀ g) ≤
      stochReturnOver M t s₀ (toEnv (stochSpreadEnv m M t s₀))
          (stochBestPolicy m M t s₀ (stochSpreadEnv m M t s₀)) -
        stochReturnOver M t s₀ (toEnv (stochSpreadEnv m M t s₀))
          (stochMinPolicy m M t s₀ (stochSpreadEnv m M t s₀)) :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => stochReturnOver M t s₀ (toEnv g) (stochBestPolicy m M t s₀ g) -
      stochReturnOver M t s₀ (toEnv g) (stochMinPolicy m M t s₀ g))
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 g (Finset.mem_univ g)

/-- A policy of maximal worst-case regret. -/
@[expose] public noncomputable def stochWorstPolicy (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) : Policy State Action :=
  stochMinPolicy m M t s₀ (stochSpreadEnv m M t s₀)

public theorem stochWorstPolicy_worst (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (π : Policy State Action) :
    stochGridRegret m M t s₀ (stochWorstEnv m M t s₀ π) π ≤
      stochGridRegret m M t s₀ (stochWorstEnv m M t s₀ (stochWorstPolicy m M t s₀))
        (stochWorstPolicy m M t s₀) := by
  have h1 := stochMinPolicy_min m M t s₀ (stochWorstEnv m M t s₀ π) π
  have h2 := stochSpreadEnv_max m M t s₀ (stochWorstEnv m M t s₀ π)
  have h3 := stochWorstEnv_worst m M t s₀ (stochWorstPolicy m M t s₀) (stochSpreadEnv m M t s₀)
  unfold stochGridRegret at h3 ⊢
  unfold stochWorstPolicy at h3 ⊢
  linarith

/--
**Print's class as a complemented class, with drawn dynamics and nothing
assumed.**
-/
@[expose] public noncomputable def toStochComplementedClass (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) :
    Corruption.ComplementedClass (GridEnv m State) (Policy State Action) where
  returnValue := fun g π => stochReturnOver M t s₀ (toEnv g) π
  horizon := (t : ℝ)
  complement := GridEnv.complement
  complement_involutive := GridEnv.complement_involutive
  complement_return := fun g π => stochGridReturn_add_complement M t s₀ g π
  bestPolicy := stochBestPolicy m M t s₀
  bestPolicy_best := fun g π => stochBestPolicy_best m M t s₀ g π
  worstEnvironment := stochWorstEnv m M t s₀
  worstEnvironment_worst := fun π g => stochWorstEnv_worst m M t s₀ π g
  worstPolicy := stochWorstPolicy m M t s₀
  worstPolicy_worst := stochWorstPolicy_worst m M t s₀

/--
**Everitt et al. Theorem 11 over print's class, with a drawn transition and all
three extrema derived.**

Axes *(a)*, *(b)* and *(c)* of the Theorem 11 row at once.
`everitt_theorem_eleven_gridClass` has *(a)* and *(b)* with a determined
transition; `CRMDP.StochModel.everitt_theorem_eleven` has *(c)* with the extrema
assumed. Only print's possibly stochastic policy, axis *(d)*, is still missing.
-/
public theorem everitt_theorem_eleven_stochGridClass (m : ℕ) (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (π : Policy State Action) :
    (toStochComplementedClass m M t s₀).worstCaseRegret
        (toStochComplementedClass m M t s₀).worstPolicy / 2 ≤
      (toStochComplementedClass m M t s₀).worstCaseRegret π :=
  (toStochComplementedClass m M t s₀).everitt_theorem_eleven π

end StochGridClass

/-! ## Possibly stochastic policies: the last axis

Print's policy is *possibly stochastic*. `Decision.le_of_affine_of_det_le` says a
value affine in the policy at each history is bounded by its deterministic
values, so the extrema already derived over deterministic policies bound the
mixed ones too. All of it happens at the **finite** grid alphabet, since the set
of short histories over `CRMDP.Obs` is not finite.
-/

/-- The expected return against a possibly stochastic policy, read at the finite
alphabet. -/
@[expose] public noncomputable def gridMixedReturn (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (g : GridEnv m State)
    (σ : Decision.Policy (State × Fin (m + 2)) Action) : ℝ :=
  ∑ k ∈ Finset.range t,
    expectReward (M.stateAt (gridChannel g) σ s₀ (k + 1)) (toEnv g).trueReward

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] in
/-- At a point-mass policy it is the deterministic return. -/
public theorem gridMixedReturn_ofDet (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State)
    (ρ : Decision.DetPolicy (State × Fin (m + 2)) Action) :
    gridMixedReturn M t s₀ g (Decision.Policy.ofDet ρ) = gridStochReturn M t s₀ g ρ :=
  rfl

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] in
/-- A run of `t` steps sees the policy only on histories shorter than `t`. -/
public theorem gridMixedReturn_congr (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State)
    {σ₁ σ₂ : Decision.Policy (State × Fin (m + 2)) Action}
    (h : ∀ hst : Decision.History (State × Fin (m + 2)) Action,
      hst.2.length < t → σ₁ hst = σ₂ hst) :
    gridMixedReturn M t s₀ g σ₁ = gridMixedReturn M t s₀ g σ₂ := by
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  exact Decision.MDP.stateAt_congr_policy M (gridChannel g) s₀ (k + 1) fun hst hlt =>
    h hst (lt_of_lt_of_le hlt (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))

section MixedGrid

variable [DecidableEq Action]

omit [Nonempty Action] in
/-- **The return is affine in the policy at a single history.** -/
public theorem gridMixedReturn_affine (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State)
    (σ : Decision.Policy (State × Fin (m + 2)) Action)
    (hh : Decision.History (State × Fin (m + 2)) Action) :
    gridMixedReturn M t s₀ g σ
      = ∑ a, (σ hh a).toReal *
          gridMixedReturn M t s₀ g (Function.update σ hh (PMF.pure a)) := by
  classical
  unfold gridMixedReturn
  have hterm : ∀ k : ℕ,
      expectReward (M.stateAt (gridChannel g) σ s₀ (k + 1)) (toEnv g).trueReward
        = ∑ a, (σ hh a).toReal *
            expectReward (M.stateAt (gridChannel g)
              (Function.update σ hh (PMF.pure a)) s₀ (k + 1)) (toEnv g).trueReward := by
    intro k
    rw [Decision.MDP.stateAt_update_decomp M (gridChannel g) σ hh s₀ (k + 1)]
    exact Decision.expect_bind _ _ _
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

/-- **The deterministic extrema bound the possibly stochastic ones.** -/
public theorem gridMixedReturn_le (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) (B : ℝ)
    (hB : ∀ ρ : Decision.DetPolicy (State × Fin (m + 2)) Action,
      gridStochReturn M t s₀ g ρ ≤ B)
    (σ : Decision.Policy (State × Fin (m + 2)) Action) :
    gridMixedReturn M t s₀ g σ ≤ B := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty Action›
  exact Decision.le_of_affine_of_det_le (t := t) a₀ (gridMixedReturn M t s₀ g) B
    (fun _ _ hag => gridMixedReturn_congr M t s₀ g hag)
    (fun τ hh _ => gridMixedReturn_affine M t s₀ g τ hh)
    (fun ρ => by rw [gridMixedReturn_ofDet]; exact hB ρ) σ

/-- And the mirror. -/
public theorem le_gridMixedReturn (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) (B : ℝ)
    (hB : ∀ ρ : Decision.DetPolicy (State × Fin (m + 2)) Action,
      B ≤ gridStochReturn M t s₀ g ρ)
    (σ : Decision.Policy (State × Fin (m + 2)) Action) :
    B ≤ gridMixedReturn M t s₀ g σ := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty Action›
  exact Decision.le_of_affine_of_le_det (t := t) a₀ (gridMixedReturn M t s₀ g) B
    (fun _ _ hag => gridMixedReturn_congr M t s₀ g hag)
    (fun τ hh _ => gridMixedReturn_affine M t s₀ g τ hh)
    (fun ρ => by rw [gridMixedReturn_ofDet]; exact hB ρ) σ

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] [DecidableEq Action] in
/-- The mixed state distribution of a grid environment, at the finite alphabet. -/
public theorem mixedStateAt_toEnv (M : Decision.MDP State Action)
    (g : GridEnv m State) (σ : StochPolicy State Action) (s₀ : State) (n : ℕ) :
    mixedStateAt M (toEnv g) σ s₀ n
      = M.stateAt (gridChannel g)
          (fun h => σ (Decision.History.mapObs (gridLabel m) h)) s₀ n := by
  rw [mixedStateAt,
    Decision.MDP.stateAt_congr_obs M (fun s => channel_toEnv g s) σ s₀ n]
  exact Decision.MDP.stateAt_mapObs M (gridLabel m) (gridChannel g) σ s₀ n

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] [DecidableEq Action] in
/-- Hence the mixed return is the finite-alphabet mixed return. -/
public theorem mixedReturnOver_toEnv (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) (σ : StochPolicy State Action) :
    mixedReturnOver M t s₀ (toEnv g) σ
      = gridMixedReturn M t s₀ g
          (fun h => σ (Decision.History.mapObs (gridLabel m) h)) := by
  unfold mixedReturnOver gridMixedReturn
  exact Finset.sum_congr rfl fun k _ => by rw [mixedStateAt_toEnv]

omit [Fintype Action] [Fintype State] [DecidableEq State] [DecidableEq Action] in
/-- Every finite-alphabet deterministic policy is realised by one over print's
alphabet, so a bound at the latter is a bound at the former. -/
public theorem gridStochReturn_eq_lift (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State)
    (ρ : Decision.DetPolicy (State × Fin (m + 2)) Action) :
    ∃ π : Policy State Action,
      gridStochReturn M t s₀ g ρ = stochReturnOver M t s₀ (toEnv g) π := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty Action›
  have hinj := Decision.History.mapObs_injective (A := Action)
    (gridLabel_injective (m := m) (State := State))
  refine ⟨Function.extend (Decision.History.mapObs (gridLabel m)) ρ (fun _ => a₀), ?_⟩
  rw [stochReturnOver_toEnv]
  refine congrArg (gridStochReturn M t s₀ g) (funext fun h => ?_).symm
  exact hinj.extend_apply _ _ h

/-- **The derived deterministic maximum bounds every possibly stochastic
policy.** -/
public theorem mixedReturnOver_le_best (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) (σ : StochPolicy State Action) :
    mixedReturnOver M t s₀ (toEnv g) σ
      ≤ stochReturnOver M t s₀ (toEnv g) (stochBestPolicy m M t s₀ g) := by
  rw [mixedReturnOver_toEnv]
  refine gridMixedReturn_le M t s₀ g _ (fun ρ => ?_) _
  obtain ⟨π, hπ⟩ := gridStochReturn_eq_lift M t s₀ g ρ
  rw [hπ]
  exact stochBestPolicy_best m M t s₀ g π

/-- And the derived minimum bounds below. -/
public theorem min_le_mixedReturnOver (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (g : GridEnv m State) (σ : StochPolicy State Action) :
    stochReturnOver M t s₀ (toEnv g) (stochMinPolicy m M t s₀ g)
      ≤ mixedReturnOver M t s₀ (toEnv g) σ := by
  rw [mixedReturnOver_toEnv]
  refine le_gridMixedReturn M t s₀ g _ (fun ρ => ?_) _
  obtain ⟨π, hπ⟩ := gridStochReturn_eq_lift M t s₀ g ρ
  rw [hπ]
  exact stochMinPolicy_min m M t s₀ g π

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] [DecidableEq Action] in
/-- Embedding commutes with complementation, for the mixed return. -/
public theorem mixedReturnOver_toEnv_complement (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (σ : StochPolicy State Action) :
    mixedReturnOver M t s₀ (toEnv g.complement) σ
      = mixedReturnOver M t s₀ (toEnv g).complement σ := by
  unfold mixedReturnOver
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show mixedStateAt M (toEnv g.complement) σ s₀ (k + 1)
        = mixedStateAt M (toEnv g).complement σ s₀ (k + 1) from
      Decision.MDP.stateAt_congr_obs M
        (fun s => by rw [Env.channel, Env.channel, observed_toEnv_complement g s]) σ s₀ (k + 1)]
  congr 1
  funext s
  exact trueReward_toEnv_complement g s

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] [DecidableEq Action] in
/-- **Print's equation (3) with both sources of randomness.** -/
public theorem mixedGridReturn_add_complement (M : Decision.MDP State Action)
    (t : ℕ) (s₀ : State) (g : GridEnv m State) (σ : StochPolicy State Action) :
    mixedReturnOver M t s₀ (toEnv g) σ +
        mixedReturnOver M t s₀ (toEnv g.complement) σ = (t : ℝ) := by
  rw [mixedReturnOver_toEnv_complement]
  exact mixedReturn_add_complement M t s₀ (toEnv g) σ

/-- The environment witnessing a possibly stochastic policy's worst-case
regret. -/
@[expose] public noncomputable def mixedWorstEnv (m : ℕ)
    (M : Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (σ : StochPolicy State Action) : GridEnv m State :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => mixedReturnOver M t s₀ (toEnv g)
        (StochPolicy.ofDet (stochBestPolicy m M t s₀ g)) -
      mixedReturnOver M t s₀ (toEnv g) σ)
    ⟨default, Finset.mem_univ _⟩).choose

omit [DecidableEq Action] in
public theorem mixedWorstEnv_worst (m : ℕ) (M : Decision.MDP State Action) (t : ℕ)
    (s₀ : State) (σ : StochPolicy State Action) (g : GridEnv m State) :
    mixedReturnOver M t s₀ (toEnv g)
          (StochPolicy.ofDet (stochBestPolicy m M t s₀ g)) -
        mixedReturnOver M t s₀ (toEnv g) σ ≤
      mixedReturnOver M t s₀ (toEnv (mixedWorstEnv m M t s₀ σ))
          (StochPolicy.ofDet (stochBestPolicy m M t s₀ (mixedWorstEnv m M t s₀ σ))) -
        mixedReturnOver M t s₀ (toEnv (mixedWorstEnv m M t s₀ σ)) σ :=
  (Finset.exists_max_image (Finset.univ : Finset (GridEnv m State))
    (fun g => mixedReturnOver M t s₀ (toEnv g)
        (StochPolicy.ofDet (stochBestPolicy m M t s₀ g)) -
      mixedReturnOver M t s₀ (toEnv g) σ)
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 g (Finset.mem_univ g)

/--
**Print's class as a complemented class, at print's own policy quantifier.**

The environments are print's class, the policies are **all** possibly stochastic
ones, and every extremum is derived: the best and worst policies are the
deterministic ones already derived, and `mixedReturnOver_le_best` and
`min_le_mixedReturnOver` say they bound the mixed policies too.
-/
@[expose] public noncomputable def toMixedComplementedClass (m : ℕ)
    (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) :
    Corruption.ComplementedClass (GridEnv m State) (StochPolicy State Action) where
  returnValue := fun g σ => mixedReturnOver M t s₀ (toEnv g) σ
  horizon := (t : ℝ)
  complement := GridEnv.complement
  complement_involutive := GridEnv.complement_involutive
  complement_return := fun g σ => mixedGridReturn_add_complement M t s₀ g σ
  bestPolicy := fun g => StochPolicy.ofDet (stochBestPolicy m M t s₀ g)
  bestPolicy_best := fun g σ => by
    rw [mixedReturnOver_ofDet]
    exact mixedReturnOver_le_best M t s₀ g σ
  worstEnvironment := mixedWorstEnv m M t s₀
  worstEnvironment_worst := fun σ g => mixedWorstEnv_worst m M t s₀ σ g
  worstPolicy := StochPolicy.ofDet (stochWorstPolicy m M t s₀)
  worstPolicy_worst := by
    intro σ
    have h1 : mixedReturnOver M t s₀ (toEnv (mixedWorstEnv m M t s₀ σ))
          (StochPolicy.ofDet (stochMinPolicy m M t s₀ (mixedWorstEnv m M t s₀ σ)))
        ≤ mixedReturnOver M t s₀ (toEnv (mixedWorstEnv m M t s₀ σ)) σ := by
      rw [mixedReturnOver_ofDet]
      exact min_le_mixedReturnOver M t s₀ (mixedWorstEnv m M t s₀ σ) σ
    have h2 := stochSpreadEnv_max m M t s₀ (mixedWorstEnv m M t s₀ σ)
    have h3 := mixedWorstEnv_worst m M t s₀
      (StochPolicy.ofDet (stochWorstPolicy m M t s₀)) (stochSpreadEnv m M t s₀)
    simp only [mixedReturnOver_ofDet] at h1 h3 ⊢
    unfold stochWorstPolicy at h3 ⊢
    linarith

/--
**Everitt et al. Theorem 11, at every axis print states it with.**

The class is print's own product of grid-valued reward and corruption functions,
the transition is a distribution, the policy is possibly stochastic, and none of
the three extrema is assumed.
-/
public theorem everitt_theorem_eleven_mixedGridClass (m : ℕ)
    (M : Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (σ : StochPolicy State Action) :
    (toMixedComplementedClass m M t s₀).worstCaseRegret
        (toMixedComplementedClass m M t s₀).worstPolicy / 2 ≤
      (toMixedComplementedClass m M t s₀).worstCaseRegret σ :=
  (toMixedComplementedClass m M t s₀).everitt_theorem_eleven σ

/-! ## Definition 9's transition product, at print's policy quantifier

Print's Theorem 11 is stated over the class of **Definition 9**, whose
transition component is a given set. `FullEnv` holds an index and a `GridEnv`
and does not care what the index is read as, so reading it as a
`Decision.MDP` rather than a transition function reuses the structure verbatim
and adds the last axis.

A maximum over a larger class is larger, so this is not a corollary of the
fixed-transition statement: every extremum below ranges over the product.
-/

variable {Trans : Type*} [Fintype Trans] [Inhabited Trans]

/-- The mixed return of a member of Definition 9's class. -/
@[expose] public noncomputable def fullMixedReturn
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (σ : StochPolicy State Action) : ℝ :=
  mixedReturnOver (trans e.transition) t s₀ (toEnv e.grid) σ

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] [DecidableEq Action] [Fintype Trans] [Inhabited Trans] in
/-- **Equation (3) on the product, with both sources of randomness.** -/
public theorem fullMixedReturn_add_complement
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (σ : StochPolicy State Action) :
    fullMixedReturn trans t s₀ e σ + fullMixedReturn trans t s₀ e.complement σ = (t : ℝ) :=
  mixedGridReturn_add_complement (trans e.transition) t s₀ e.grid σ

omit [Fintype Action] [Nonempty Action] [Fintype State] [DecidableEq State] [DecidableEq Action] [Fintype Trans] [Inhabited Trans] in
/-- **The determined statement is the degenerate case of this one**, so the two
renderings are chained rather than merely analogous. -/
public theorem fullMixedReturn_ofDet (trans : Trans → State → Action → State)
    (t : ℕ) (s₀ : State) (e : FullEnv m Trans State) (π : Policy State Action) :
    fullMixedReturn (fun τ => Decision.MDP.ofDet (trans τ)) t s₀ e (StochPolicy.ofDet π)
      = fullReturn trans t s₀ e π := by
  unfold fullMixedReturn fullReturn gridReturn
  rw [mixedReturnOver_ofDet, stochReturnOver_ofDet]

/-- An optimal policy for a member, the derived deterministic one. -/
@[expose] public noncomputable def fullMixedBest (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) : StochPolicy State Action :=
  StochPolicy.ofDet (stochBestPolicy m (trans e.transition) t s₀ e.grid)

omit [Fintype Trans] [Inhabited Trans] in
public theorem fullMixedBest_best (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (σ : StochPolicy State Action) :
    fullMixedReturn trans t s₀ e σ ≤ fullMixedReturn trans t s₀ e (fullMixedBest m trans t s₀ e) := by
  unfold fullMixedReturn fullMixedBest
  rw [mixedReturnOver_ofDet]
  exact mixedReturnOver_le_best (trans e.transition) t s₀ e.grid σ

/-- A worst policy for a member, likewise. -/
@[expose] public noncomputable def fullMixedMin (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) : StochPolicy State Action :=
  StochPolicy.ofDet (stochMinPolicy m (trans e.transition) t s₀ e.grid)

omit [Fintype Trans] [Inhabited Trans] in
public theorem fullMixedMin_min (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) (σ : StochPolicy State Action) :
    fullMixedReturn trans t s₀ e (fullMixedMin m trans t s₀ e) ≤ fullMixedReturn trans t s₀ e σ := by
  unfold fullMixedReturn fullMixedMin
  rw [mixedReturnOver_ofDet]
  exact min_le_mixedReturnOver (trans e.transition) t s₀ e.grid σ

/-- The member witnessing a policy's worst-case regret, over the **product**. -/
@[expose] public noncomputable def fullMixedWorstEnv (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (σ : StochPolicy State Action) : FullEnv m Trans State :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullMixedReturn trans t s₀ e (fullMixedBest m trans t s₀ e) -
      fullMixedReturn trans t s₀ e σ) ⟨default, Finset.mem_univ _⟩).choose

omit [DecidableEq Action] in
public theorem fullMixedWorstEnv_worst (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (σ : StochPolicy State Action) (e : FullEnv m Trans State) :
    fullMixedReturn trans t s₀ e (fullMixedBest m trans t s₀ e) -
        fullMixedReturn trans t s₀ e σ ≤
      fullMixedReturn trans t s₀ (fullMixedWorstEnv m trans t s₀ σ)
          (fullMixedBest m trans t s₀ (fullMixedWorstEnv m trans t s₀ σ)) -
        fullMixedReturn trans t s₀ (fullMixedWorstEnv m trans t s₀ σ) σ :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullMixedReturn trans t s₀ e (fullMixedBest m trans t s₀ e) -
      fullMixedReturn trans t s₀ e σ)
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 e (Finset.mem_univ e)

/-- Print's member of widest spread, over the product. -/
@[expose] public noncomputable def fullMixedSpreadEnv (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State) :
    FullEnv m Trans State :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullMixedReturn trans t s₀ e (fullMixedBest m trans t s₀ e) -
      fullMixedReturn trans t s₀ e (fullMixedMin m trans t s₀ e))
    ⟨default, Finset.mem_univ _⟩).choose

omit [DecidableEq Action] in
public theorem fullMixedSpreadEnv_max (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (e : FullEnv m Trans State) :
    fullMixedReturn trans t s₀ e (fullMixedBest m trans t s₀ e) -
        fullMixedReturn trans t s₀ e (fullMixedMin m trans t s₀ e) ≤
      fullMixedReturn trans t s₀ (fullMixedSpreadEnv m trans t s₀)
          (fullMixedBest m trans t s₀ (fullMixedSpreadEnv m trans t s₀)) -
        fullMixedReturn trans t s₀ (fullMixedSpreadEnv m trans t s₀)
          (fullMixedMin m trans t s₀ (fullMixedSpreadEnv m trans t s₀)) :=
  (Finset.exists_max_image (Finset.univ : Finset (FullEnv m Trans State))
    (fun e => fullMixedReturn trans t s₀ e (fullMixedBest m trans t s₀ e) -
      fullMixedReturn trans t s₀ e (fullMixedMin m trans t s₀ e))
    ⟨default, Finset.mem_univ _⟩).choose_spec.2 e (Finset.mem_univ e)

/-- A policy of maximal worst-case regret over the product. -/
@[expose] public noncomputable def fullMixedWorstPolicy (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State) :
    StochPolicy State Action :=
  fullMixedMin m trans t s₀ (fullMixedSpreadEnv m trans t s₀)

public theorem fullMixedWorstPolicy_worst (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (σ : StochPolicy State Action) :
    fullMixedReturn trans t s₀ (fullMixedWorstEnv m trans t s₀ σ)
          (fullMixedBest m trans t s₀ (fullMixedWorstEnv m trans t s₀ σ)) -
        fullMixedReturn trans t s₀ (fullMixedWorstEnv m trans t s₀ σ) σ ≤
      fullMixedReturn trans t s₀
            (fullMixedWorstEnv m trans t s₀ (fullMixedWorstPolicy m trans t s₀))
          (fullMixedBest m trans t s₀
            (fullMixedWorstEnv m trans t s₀ (fullMixedWorstPolicy m trans t s₀))) -
        fullMixedReturn trans t s₀
          (fullMixedWorstEnv m trans t s₀ (fullMixedWorstPolicy m trans t s₀))
          (fullMixedWorstPolicy m trans t s₀) := by
  have h1 := fullMixedMin_min m trans t s₀ (fullMixedWorstEnv m trans t s₀ σ) σ
  have h2 := fullMixedSpreadEnv_max m trans t s₀ (fullMixedWorstEnv m trans t s₀ σ)
  have h3 := fullMixedWorstEnv_worst m trans t s₀
    (fullMixedWorstPolicy m trans t s₀) (fullMixedSpreadEnv m trans t s₀)
  unfold fullMixedWorstPolicy at h3 ⊢
  linarith

/--
**Print's Definition 9 class at print's policy quantifier, with nothing
assumed.**
-/
@[expose] public noncomputable def toFullMixedComplementedClass (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State) :
    Corruption.ComplementedClass (FullEnv m Trans State) (StochPolicy State Action) where
  returnValue := fullMixedReturn trans t s₀
  horizon := (t : ℝ)
  complement := FullEnv.complement
  complement_involutive := FullEnv.complement_involutive
  complement_return := fullMixedReturn_add_complement trans t s₀
  bestPolicy := fullMixedBest m trans t s₀
  bestPolicy_best := fun e σ => fullMixedBest_best m trans t s₀ e σ
  worstEnvironment := fullMixedWorstEnv m trans t s₀
  worstEnvironment_worst := fun σ e => fullMixedWorstEnv_worst m trans t s₀ σ e
  worstPolicy := fullMixedWorstPolicy m trans t s₀
  worstPolicy_worst := fullMixedWorstPolicy_worst m trans t s₀

/--
**Everitt et al. Theorem 11, at every axis print states it with.**

The class is Definition 9's: a given set of transitions crossed with the full
product of grid-valued reward and corruption functions. The transition is a
distribution, the policy is possibly stochastic, and none of the three extrema
is assumed.
-/
public theorem everitt_theorem_eleven_fullMixedClass (m : ℕ)
    (trans : Trans → Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (σ : StochPolicy State Action) :
    (toFullMixedComplementedClass m trans t s₀).worstCaseRegret
        (toFullMixedComplementedClass m trans t s₀).worstPolicy / 2 ≤
      (toFullMixedComplementedClass m trans t s₀).worstCaseRegret σ :=
  (toFullMixedComplementedClass m trans t s₀).everitt_theorem_eleven σ

end MixedGrid

end StochGridExtrema

end AISafetyAtlas.Wireheading.RewardGrid
