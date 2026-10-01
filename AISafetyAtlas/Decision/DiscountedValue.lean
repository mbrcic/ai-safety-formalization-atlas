module

public import AISafetyAtlas.Decision.MDP
public import AISafetyAtlas.Decision.Expect
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The discounted value layer, above the rewardless carrier

`AISafetyAtlas.Decision.MDP` is Turner and Tadepalli's Definition D.6 without
its finiteness and without its discount, and **rewardless**: a state type, an action type, and `T : S → A → PMF S`, with
no reward, no discount and no start state. This module is the first consumer
that adds a reward, and it adds it as a **parameter** rather than a field. A
reward function `r : State → Action → ℝ` and a discount `γ : ℝ≥0` are arguments
to every definition below; nothing here changes the carrier, and
`AISafetyAtlas.Wireheading.CRMDP` — whose reward ranges over an environment class
while the dynamics stay fixed — remains expressible for exactly that reason.

## What is here

* `expect` (from `AISafetyAtlas.Decision.Expect`) — the expectation of a value function under a `PMF`, on a finite
  state type.
* `qVal`, `bellmanPolicyOp`, `bellmanOptOp` — the state-action value at a value
  function, and the two Bellman operators.
* `bellmanPolicyOp_contractingWith`, `bellmanOptOp_contractingWith` — each is a
  `ContractingWith γ` map on `State → ℝ` under the sup metric.
* `vPi`, `vStar` — Banach fixed points, via `ContractingWith.fixedPoint`.
* `vPi_bellman`, `vStar_bellman` — the Bellman equation, pointwise, as theorems.
* `vPi_unique`, `vStar_unique` — uniqueness: any solution of the Bellman equation
  *is* the fixed point.
* `qStar`, `vStar_eq_sup_qStar` — the optimal state-action value and the
  identity relating it to `vStar`.
* `tendsto_iterate_vPi`, `tendsto_iterate_vStar`, `dist_iterate_vStar_le` —
  value iteration converges, with the geometric a-priori rate.

## SCOPE HONESTY: this is a foundation, not the join

**The discounted fixed point does not reach Turner and Tadepalli's appendix D,
and nothing here should be read as progress toward it.** Turner's D.10 is about
**average**-optimality, not discounted optimality. They are different optimality
criteria and **this module states no relationship between them** — not that one
specializes to the other, and not that it does not. Only D.6 is stated anywhere
in this repository: a content search for `D.7`, `D.8`, `D.9` and `D.10` over
`AISafetyAtlas/`, `docs/`, `registry.yaml` and `conjectures.yaml` on 2026-09-10
returned nothing but this paragraph. Until D.8 to D.10 are actually stated on
this layer, the join to the power-seeking results is open, and this module
closes no part of it. The one external tree that carries a comparable
development, `audieleon/goodhart`'s `GoodhartProofs/MDP/`, keeps a separate
`Undiscounted.lean` for exactly this reason.

Three further gaps, named here rather than left for a reader to find:

1. **`vPi` is for a stationary deterministic policy** `π : State → Action`. That
   is *not* the carrier's `AISafetyAtlas.Decision.Policy`, which is
   history-dependent and stochastic over an observation alphabet. No theorem
   below connects the two, and a stationary policy is not in general optimal
   among history-dependent ones without an argument this module does not make.
2. **`vPi` is *defined* as a fixed point, not as a return.** That it equals the
   discounted sum of rewards along `MDP.run` is not proved here. Everything
   below is therefore a statement about the Bellman operator; the identification
   with the trajectory semantics of the carrier is owed.
3. **The fixed points below need `[Fintype State]`, and that gap is now closed
   elsewhere.** Turner's D.6 requires both types finite, so the restriction is
   not narrower than print — but `AISafetyAtlas.Decision.MDP` deliberately
   dropped the finiteness and this module put it back. Finiteness is what makes
   `State → ℝ` a complete metric space under the sup metric with no boundedness
   side-condition, and what makes the maximum over actions attained.

   **Closed 2026-09-16 by `AISafetyAtlas.Decision.BoundedValue`**, which values a
   stationary deterministic policy on an arbitrary `Nonempty` state type in
   exchange for a uniform bound on the reward, and by
   `AISafetyAtlas.Decision.vPiBdd_eq_vPi`, which proves the two value functions
   are the same function wherever both are defined. Without that last theorem
   the wider module would be a parallel development rather than a widening.

   `qVal` and `bellmanPolicyOp` below **lost their `[Fintype State]` binders in
   the same change**, and `bellmanOptOp` kept only `Action`'s. None of the three
   definitions ever used finiteness of the state type; only the fixed point did.
   So there is one Bellman operator in the atlas, under two completeness
   arguments, rather than two operators that resemble each other.

   What is *not* closed: `vStar`. The optimality operator maximises over actions
   with `Finset.sup'`, so widening it is a statement about suprema over a
   possibly infinite action set, which is a different change and is not made.

   The route was **costed 2026-09-11** in
   `docs/agent/policy/lean-reuse-sources.md`: the widening is
   Econlib/Math/Analysis/Blackwell.lean and **not** its seventeen-file
   Optimization/DynamicProgramming/ subtree, whose three carriers are
   deterministic over an arbitrary state type, stochastic over `Fin n`, and
   measure-valued over `ℝ`, while this module's carrier is stochastic over an
   arbitrary state type — Econlib has stochastic, or unconstrained, never both.
   That costing measured the toolchain delta at one lemma name used twice; the
   port found three, none of them mathematics, and the correction is recorded in
   the same policy section and in registry row `LAND-BELLMAN-BDD-001`.

Reward is `State → Action → ℝ`, which is **wider** than a state-only reward
`R : State → ℝ`: the latter is the special case `fun s _ => R s`.

## Where this was searched for before it was built

**This section was rewritten on 2026-09-10 because three of its claims were
false, and one of them described a search that had not been run.** The retracted
text is named at each bullet, because a survey that was wrong once is evidence
about how much the rest of it is worth.

Five external Lean trees carry a discounted value layer or its neighbours. Two of
them were missed entirely by the first pass:

* `lean-dojo/TorchLean` at `12f5c651f03b3890ec012d0a6bb45e3ea698c8d3`, MIT.
  Toolchain `v4.33.0` and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d --
  **the same as ours**, and it is on the module system, so it is a port source
  rather than inspiration. Its NN/Spec/RL/ carries a tensor-valued finite MDP
  over `Fin n`, a measure-valued Markov MDP and a probability-vector finite
  stochastic MDP, each with a policy-Bellman and an optimality-Bellman operator.
  It does not use `ContractingWith` anywhere: its NN/Proofs/RL/ hand-rolls a
  sup-distance on value functions and proves contraction and fixed-point
  uniqueness directly. None of its three carriers is `PMF`-valued. *(This bullet
  stands as first written.)*
* `audieleon/goodhart` at `29128f3f9bcafb30d019682b63c1b582bcadf7b9`,
  Apache-2.0, toolchain `v4.30.0-rc2` against Mathlib
  9268b22206b0425419498769f780a91dee03bcf3. **This is the nearest thing to this
  module anywhere, and the first pass did not list it at all** -- although the
  paragraph above cites the same tree, and `registry.yaml` pins the same
  revision as reproduced. Its proofs/GoodhartProofs/MDP/Bellman.lean is
  sorry-free and reaches its fixed points through Mathlib's Lipschitz bound,
  `ContractingWith` and `ContractingWith.fixedPoint`, exactly as below.
  Fourteen of the twenty-two declarations in this module correspond to one of
  its, name for name and in the same order.
* `danlyng/Econlib` at `003655ccf010cdf44c4f67d6675167b54ce0e9df`, Apache-2.0,
  toolchain `v4.29.0` against our `v4.33.0`. **Retracted: this bullet said "not
  on the module system, so inspiration only", and said the tree goes through
  `ContractingWith` "in Econlib/Math/Analysis/Blackwell.lean".** The module-system
  claim is false -- Blackwell.lean opens with `module` and `public import` -- and
  it cites the wrong file. The dedicated development is
  Econlib/Optimization/DynamicProgramming/, seventeen files, every one of them on
  the module system, with Core/MDP.lean, Core/Bellman.lean,
  Core/BellmanOperator.lean, Core/Optimality.lean, Core/Stochastic.lean,
  Core/UnboundedOptimality.lean and Core/Weighted.lean. Blackwell.lean is a
  *different* and also relevant thing: a bounded fixed-point core on an arbitrary
  state type, which is the widening the third open gap above says is owed. The
  toolchain gap is real and is the whole of the port cost; it never made this a
  tree to take inspiration from rather than code.
* `nikhgarg/EconCSLib` at `e952266be81e96bbeecea6af83d639af324a4438`,
  Apache-2.0, toolchain `v4.30.0-rc2`. **Retracted: this bullet said "2106 Lean
  files and no MDP, Bellman, value-iteration or discounting content at all".**
  The file count is right and the rest is false. That revision holds
  AppliedModelingLib/Foundations/Probability/MDP.lean -- a finite MDP whose
  transition is `PMF`-valued and which **carries a reward field**, with a
  randomized Markov policy, a controlled kernel, a finite-horizon value, a
  Bellman-recursive optimal value and occupancy masses -- together with
  Foundations/Probability/StochasticRewardMDP.lean and a ten-file
  Learning/ReinforcementLearning/Preference/ subtree including PreferenceBellman
  and ApproximateDynamicProgramming. Over twenty files at that revision match
  bellman, discount or `ContractingWith`. The MDP file was added three days
  before the pinned revision, so the pin is not the excuse.
  `AISafetyAtlas.Wireheading.StochasticCRMDP` described this same tree correctly
  on the same branch, and the two should be read together.

`sup'_le_add_const` and `abs_sup'_sub_sup'_le` below -- both private -- are the
two lemmas this module states for itself, and the reason recorded for them was
wrong. It read that Mathlib does not carry them at the pinned revision and that
TorchLean/NN/Proofs/RL/FinsetSup.lean stating the first is *"evidence the gap is
real rather than a search failure"*. **Checked 2026-09-10: Mathlib does carry the additive shift, in
Mathlib/Algebra/Order/Group/Finset.lean, generated from its multiplicative form
by the additive-version attribute -- so the file has no literal theorem line
under the additive name and a search for that name finds nothing.** That is the
search failure the sentence denied.

What survives is narrower and is the honest reason: Mathlib's lemma is the
*equality* `s.sup' hs f + a = s.sup' hs (f · + a)`, and the two below are
*comparisons* -- from a pointwise `f i ≤ g i + c` to `sup' f ≤ sup' g + c`, and
the two-sided form. Those are four lines each from `Finset.sup'_le` and
`Finset.le_sup'`, they are not instances of the additive shift, and keeping them
private is the right call. What is retracted is the claim that Mathlib has
nothing adjacent and that another project's copy proves it.

**Why this layer was still written rather than ported.** Not because the trees
lack it -- three of them have it -- but for four differences that are load-bearing
here, and this is the comparison the first pass owed and did not make. (i) The
carrier below is rewardless, per Turner and Tadepalli's Definition D.6; every
external MDP named above puts the reward in the structure, and two of them put
the discount there as well. `AISafetyAtlas.Wireheading.CRMDP`, whose reward ranges
over an environment class while the dynamics stay fixed, is expressible only
because the reward is not a field. (ii) The reward here is a parameter, so a
state-action reward and a state-only reward are one development. (iii) `γ` is an
`ℝ≥0`, admitting `γ = 0`; audieleon/goodhart requires `0 < γ < 1` as structure
fields. (iv) The three convergence results at the end of this module are not in
any of the trees above. A port remains available and is costed nowhere yet; the
toolchain and Mathlib deltas are the whole of it, and both upstream licences
permit it.

**What this survey still does not cover.** The trees above were re-listed on
2026-09-10 from fresh clones at the revisions recorded here, by listing every
`.lean` path at the revision and reading the files whose paths or contents name
an MDP, a Bellman operator, a discount or a contraction. A declaration under a
name matching none of those, in a file whose path says nothing, would still be
missed. The first pass claimed to have run exactly that content search and had
not; a claim of this shape is worth nothing without the command and its output
beside it, and this one is offered on the same terms.
Toolchains and Mathlib revisions are each file's own `lean-toolchain` and
`lake-manifest.json` at the commit recorded above.
-/

namespace AISafetyAtlas.Decision

open scoped NNReal

universe u v

variable {State : Type u} {Action : Type v}

/-! ## The expectation of a value function -/

/-! The expectation itself is `AISafetyAtlas.Decision.expect`, shared with
`AISafetyAtlas.Wireheading.StochasticCRMDP`. `expect_eq_sum` turns it into the
finite sum this section's contraction argument works with. -/

/-- **A probability mass function sums to one after `toReal`.** No `PMF` value is
`⊤`, so `ENNReal.toReal` commutes with the finite sum. -/
public theorem sum_toReal_eq_one [Fintype State] (p : PMF State) :
    ∑ s, (p s).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [h, ENNReal.toReal_one]

/--
**Taking an expectation does not increase the sup distance.**

The step every contraction argument below needs: an average of values that differ
pointwise by at most `d` differs by at most `d`.
-/
public theorem abs_expect_sub_le [Fintype State] (p : PMF State)
    (v w : State → ℝ) :
    |expect p v - expect p w| ≤ dist v w := by
  have hsub : expect p v - expect p w
      = ∑ s, (p s).toReal * (v s - w s) := by
    simp only [expect_eq_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsub]
  calc |∑ s, (p s).toReal * (v s - w s)|
      ≤ ∑ s, |(p s).toReal * (v s - w s)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, (p s).toReal * |v s - w s| := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ s, (p s).toReal * dist v w := by
        refine Finset.sum_le_sum fun s _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [← Real.dist_eq]
        exact dist_le_pi_dist v w s
    _ = dist v w := by rw [← Finset.sum_mul, sum_toReal_eq_one, one_mul]

/-! ## The Bellman operators -/

/--
**The state-action value at a value function**: the reward taken now, plus the
discounted expectation of `v` at the successor state.

`γ : ℝ≥0` rather than a real with a nonnegativity hypothesis, because
`ContractingWith` takes its modulus in `ℝ≥0`. The condition `γ < 1` is a
hypothesis of the fixed-point definitions, never a field.
-/
@[expose] public noncomputable def qVal (M : MDP State Action)
    (r : State → Action → ℝ) (γ : ℝ≥0) (v : State → ℝ) (s : State)
    (a : Action) : ℝ :=
  r s a + (γ : ℝ) * expect (M.transition s a) v

/-- **The Bellman operator of a stationary deterministic policy.** -/
@[expose] public noncomputable def bellmanPolicyOp
    (M : MDP State Action) (r : State → Action → ℝ) (γ : ℝ≥0)
    (π : State → Action) (v : State → ℝ) : State → ℝ :=
  fun s => qVal M r γ v s (π s)

/-- **The Bellman optimality operator**: the maximum of `qVal` over actions.

The maximum is attained rather than assumed, because `Action` is a nonempty
`Fintype`. -/
@[expose] public noncomputable def bellmanOptOp [Fintype Action]
    [Nonempty Action] (M : MDP State Action) (r : State → Action → ℝ) (γ : ℝ≥0)
    (v : State → ℝ) : State → ℝ :=
  fun s => (Finset.univ : Finset Action).sup' Finset.univ_nonempty
    (fun a => qVal M r γ v s a)

/-- If `f` is dominated by `g` shifted by a constant, so is its supremum. Mathlib
does not carry this at the pinned revision;
TorchLean/NN/Proofs/RL/FinsetSup.lean states the same fact. -/
private theorem sup'_le_add_const {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f g : ι → ℝ) (c : ℝ) (hfg : ∀ i ∈ s, f i ≤ g i + c) :
    s.sup' hs f ≤ s.sup' hs g + c :=
  Finset.sup'_le hs f fun i hi => by
    have := Finset.le_sup' g hi
    have := hfg i hi
    linarith

/-- Two `sup'`s over the same nonempty finset differ by at most the sup of the
pointwise differences. -/
private theorem abs_sup'_sub_sup'_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f g : ι → ℝ) (c : ℝ) (hc : ∀ i ∈ s, |f i - g i| ≤ c) :
    |s.sup' hs f - s.sup' hs g| ≤ c := by
  have hfg : ∀ i ∈ s, f i ≤ g i + c := fun i hi => by
    have := (abs_le.mp (hc i hi)).2
    linarith
  have hgf : ∀ i ∈ s, g i ≤ f i + c := fun i hi => by
    have := (abs_le.mp (hc i hi)).1
    linarith
  have h₁ := sup'_le_add_const s hs f g c hfg
  have h₂ := sup'_le_add_const s hs g f c hgf
  rw [abs_le]
  constructor <;> linarith

/-! ## The two contractions -/

/-- **The policy Bellman operator is a `γ`-contraction** on `State → ℝ` under the
sup metric. -/
public theorem bellmanPolicyOp_contractingWith [Fintype State]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (π : State → Action) :
    ContractingWith γ (bellmanPolicyOp M r γ π) := by
  refine ⟨hγ, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  have hnn : (0 : ℝ) ≤ (γ : ℝ) * dist v w :=
    mul_nonneg γ.coe_nonneg dist_nonneg
  refine (dist_pi_le_iff hnn).mpr fun s => ?_
  rw [Real.dist_eq]
  have : bellmanPolicyOp M r γ π v s - bellmanPolicyOp M r γ π w s
      = (γ : ℝ) * (expect (M.transition s (π s)) v
          - expect (M.transition s (π s)) w) := by
    unfold bellmanPolicyOp qVal
    ring
  rw [this, abs_mul, abs_of_nonneg γ.coe_nonneg]
  exact mul_le_mul_of_nonneg_left
    (abs_expect_sub_le (M.transition s (π s)) v w) γ.coe_nonneg

/-- **The Bellman optimality operator is a `γ`-contraction.** The maximum over a
nonempty finite action set is Lipschitz in the family it maximises. -/
public theorem bellmanOptOp_contractingWith [Fintype State] [Fintype Action]
    [Nonempty Action] (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0}
    (hγ : γ < 1) :
    ContractingWith γ (bellmanOptOp M r γ) := by
  refine ⟨hγ, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  have hnn : (0 : ℝ) ≤ (γ : ℝ) * dist v w :=
    mul_nonneg γ.coe_nonneg dist_nonneg
  refine (dist_pi_le_iff hnn).mpr fun s => ?_
  rw [Real.dist_eq]
  refine abs_sup'_sub_sup'_le _ _ _ _ _ fun a _ => ?_
  have : qVal M r γ v s a - qVal M r γ w s a
      = (γ : ℝ) * (expect (M.transition s a) v
          - expect (M.transition s a) w) := by
    unfold qVal
    ring
  rw [this, abs_mul, abs_of_nonneg γ.coe_nonneg]
  exact mul_le_mul_of_nonneg_left
    (abs_expect_sub_le (M.transition s a) v w) γ.coe_nonneg

/-! ## The two value functions -/

/--
**The value of a stationary deterministic policy**, as the Banach fixed point of
its Bellman operator.

Read the scope note in the module docstring before using this: it is a fixed
point, and no theorem here identifies it with a discounted return along
`AISafetyAtlas.Decision.MDP.run`.
-/
@[expose] public noncomputable def vPi [Fintype State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action) :
    State → ℝ :=
  ContractingWith.fixedPoint (bellmanPolicyOp M r γ π)
    (bellmanPolicyOp_contractingWith M r hγ π)

/-- **The optimal value function**, as the Banach fixed point of the Bellman
optimality operator. -/
@[expose] public noncomputable def vStar [Fintype State] [Fintype Action]
    [Nonempty Action] (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0}
    (hγ : γ < 1) : State → ℝ :=
  ContractingWith.fixedPoint (bellmanOptOp M r γ) (bellmanOptOp_contractingWith M r hγ)

/-- **The optimal state-action value**, `qVal` at `vStar`. -/
@[expose] public noncomputable def qStar [Fintype State] [Fintype Action]
    [Nonempty Action] (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0}
    (hγ : γ < 1) (s : State) (a : Action) : ℝ :=
  qVal M r γ (vStar M r hγ) s a

/-! ## The Bellman equations, and uniqueness -/

/-- **The policy Bellman equation**, as an equation between functions. -/
public theorem vPi_isFixedPt [Fintype State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action) :
    bellmanPolicyOp M r γ π (vPi M r hγ π) = vPi M r hγ π :=
  (bellmanPolicyOp_contractingWith M r hγ π).fixedPoint_isFixedPt

/-- **The policy Bellman equation, pointwise**: the value at a state is the
reward the policy earns there plus the discounted expected value of the
successor. -/
public theorem vPi_bellman [Fintype State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action)
    (s : State) :
    vPi M r hγ π s
      = r s (π s) + (γ : ℝ) * expect (M.transition s (π s)) (vPi M r hγ π) := by
  conv_lhs => rw [← vPi_isFixedPt M r hγ π]
  rfl

/-- **Uniqueness.** Any solution of the policy Bellman equation is `vPi`. There is
no boundedness side-condition because `State` is finite. -/
public theorem vPi_unique [Fintype State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action)
    {v : State → ℝ} (hv : bellmanPolicyOp M r γ π v = v) :
    v = vPi M r hγ π :=
  (bellmanPolicyOp_contractingWith M r hγ π).fixedPoint_unique hv

/-- **The Bellman optimality equation**, as an equation between functions. -/
public theorem vStar_isFixedPt [Fintype State] [Fintype Action] [Nonempty Action]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) :
    bellmanOptOp M r γ (vStar M r hγ) = vStar M r hγ :=
  (bellmanOptOp_contractingWith M r hγ).fixedPoint_isFixedPt

/-- **The Bellman optimality equation, pointwise.** -/
public theorem vStar_bellman [Fintype State] [Fintype Action] [Nonempty Action]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (s : State) :
    vStar M r hγ s
      = (Finset.univ : Finset Action).sup' Finset.univ_nonempty
          (fun a => r s a + (γ : ℝ) * expect (M.transition s a) (vStar M r hγ)) := by
  conv_lhs => rw [← vStar_isFixedPt M r hγ]
  rfl

/-- **Uniqueness.** Any solution of the Bellman optimality equation is `vStar`. -/
public theorem vStar_unique [Fintype State] [Fintype Action] [Nonempty Action]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    {v : State → ℝ} (hv : bellmanOptOp M r γ v = v) :
    v = vStar M r hγ :=
  (bellmanOptOp_contractingWith M r hγ).fixedPoint_unique hv

/-- **The optimal value is the maximum of the optimal state-action values.** -/
public theorem vStar_eq_sup_qStar [Fintype State] [Fintype Action] [Nonempty Action]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (s : State) :
    vStar M r hγ s
      = (Finset.univ : Finset Action).sup' Finset.univ_nonempty
          (fun a => qStar M r hγ s a) := by
  conv_lhs => rw [← vStar_isFixedPt M r hγ]
  rfl

/-! ## Value iteration

Free from `ContractingWith`, and stated because the baseline this module was
measured against carries hand-rolled versions of both.
-/

/-- **Value iteration converges to `vPi`**, from any starting value function. -/
public theorem tendsto_iterate_vPi [Fintype State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action)
    (v : State → ℝ) :
    Filter.Tendsto (fun n => (bellmanPolicyOp M r γ π)^[n] v) Filter.atTop
      (nhds (vPi M r hγ π)) :=
  (bellmanPolicyOp_contractingWith M r hγ π).tendsto_iterate_fixedPoint v

/-- **Value iteration converges to `vStar`**, from any starting value function. -/
public theorem tendsto_iterate_vStar [Fintype State] [Fintype Action] [Nonempty Action]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (v : State → ℝ) :
    Filter.Tendsto (fun n => (bellmanOptOp M r γ)^[n] v) Filter.atTop
      (nhds (vStar M r hγ)) :=
  (bellmanOptOp_contractingWith M r hγ).tendsto_iterate_fixedPoint v

/-- **The a-priori geometric rate** for value iteration towards `vStar`. -/
public theorem dist_iterate_vStar_le [Fintype State] [Fintype Action] [Nonempty Action]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (v : State → ℝ) (n : ℕ) :
    dist ((bellmanOptOp M r γ)^[n] v) (vStar M r hγ)
      ≤ dist v (bellmanOptOp M r γ v) * (γ : ℝ) ^ n / (1 - (γ : ℝ)) :=
  (bellmanOptOp_contractingWith M r hγ).apriori_dist_iterate_fixedPoint_le v n

end AISafetyAtlas.Decision
