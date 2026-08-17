module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Finset.Max

/-!
# Preference unidentifiability — public surface (BY-011)

Planner/reward decomposition and related Armstrong–Mindermann material.
Root `AISafetyAtlas` also imports nested modules
`Preference.{Reasonable,SourceComplexity,Complexity,Regret,Override}`.

## Primary surface

| Role | Declaration | Import | One-line |
|---|---|---|---|
| **Boundary / law** | `exists_planner` | this module | Every reward explains every behaviour under some planner |
| **Boundary / law** | `exists_reward` | this module | Every behaviour in a planner's image has a realizing reward |
| **Law** | `lemma_six` | this module | Three degenerate pairs are compatible with a policy |
| **Source form** | `Source.ReasonableForF.proposition_seven` | `.SourceComplexity` | Prop. 7 at distance **c** (source parameterization) |
| **Source form** | `Source.ReasonableForF.proposition_eight` | `.SourceComplexity` | Prop. 8 both directions at **c** |
| **Helper** | `ReasonableLanguage.proposition_seven` | `.Reasonable` | Reparameterized Prop. 7 at **2c** (used by plain-K path) |
| **Specialization** | `explanation_complexity_eq_behaviour` | `.Complexity` | Plain-K bounds for one canonical encoding |
| **Law** | `RegretModel.cannot_rule_out_half_maximal_regret` | `.Regret` | §4.1.2 style bridge; needs `HalfMaximalRegretBound` certificate |
| **Definition** | `OverrideModel.OverridesFor` | `.Override` | Definition 11 relativized to a compatible pair |
| **Boundary** | `Source.ReasonableForF.theorem_two_conditional` | `.SourceComplexity` | Informal Thm 2 **only if** Conjecture 9 predicate holds |

This file defines the core planner/reward API (`Planner`, `Explains`, Theorem 1
halves, degenerate pairs). Nested modules hold complexity, regret, and override
layers, and **this module does not import them** — it is a peer, not a facade,
so seven of the rows above need the import named beside them (`.Regret` is
`AISafetyAtlas.Preference.Regret`, and so on) or `AISafetyAtlas` for all of
them. The `Import` column says which; the `Declaration` column is the name, and
is independent of it.

## Statement intent (this file)

- **Objects.** Observable behaviour `B` and reward `R`. `Planner R B` is any
  function `R → B`. No rationality is assumed.
- **Quantifier order.** For every behaviour and every reward there exists a
  planner joining them (reward adversarial first).
- **Conclusion.** Observed behaviour alone does not constrain the reward
  component of a planner/reward pair.

## Explicit non-claims

- **Not** “value learning is impossible” — only that *behaviour alone* does not
  identify the pair; priors, norms, or extra channels are why learning can work.
- **Not** complete source coverage: registry ledger is **6/8** (Conjecture 9
  unproved; Proposition 10 blocked on resource-bounded complexity). All
  formalizations remain **RELATED**.
- **Not** the source's bounded reward-function type: `RewardFn S A` is
  real-valued without the paper's `[-1,1]` range invariant. The reproduced
  algebraic statements remain valid under this generalization.
- **Not** a nontrivial `c`-reasonable language existence proof; exhibited models
  may be degenerate.
- **Not** a claim about any particular algorithm, dataset, or deployed system.
- **Not** an AI-system bridge; `ai_bridge_status` remains human review.

Survey row: **BY-011**. Statement maps / residuals:
`docs/provenance/a1-a3-b1-b3-b7-statement-maps.md`,
`docs/provenance/a1-a3-b1-b3-b7-reverification.md`.
-/

namespace AISafetyAtlas.Preference

/--
A planner maps a reward object to an observable behaviour.

Deliberately unconstrained: a planner need not be rational, optimal, or even
sensitive to its argument. That permissiveness is the content of the source
result, not a weakness of the model — the point is that the hypothesis class of
planners is large enough to absorb any behaviour.
-/
public abbrev Planner (R B : Type*) : Type _ := R → B

/-- The pair `(p, r)` *explains* behaviour `b` when the planner applied to the
reward reproduces the observed behaviour exactly. -/
@[expose] public def Explains {R B : Type*} (p : Planner R B) (r : R) (b : B) : Prop :=
  p r = b

/-!
## Core degeneracy
-/

/--
**Every reward explains every behaviour, under some planner.**

The witness is the planner that ignores its reward argument. This is the formal
core of preference unidentifiability: fixing the observed behaviour eliminates
no reward whatsoever.
-/
public theorem exists_planner {R B : Type*} (b : B) (r : R) :
    ∃ p : Planner R B, Explains p r b :=
  ⟨fun _ => b, rfl⟩

/--
**The rewards consistent with an observation are all of them.**

Set-level restatement of `exists_planner`: the observation carries zero
information about the reward component.
-/
public theorem consistent_rewards_eq_univ {R B : Type*} (b : B) :
    {r : R | ∃ p : Planner R B, Explains p r b} = Set.univ :=
  Set.eq_univ_of_forall fun r => exists_planner b r

/--
**Anti-rational twin.**

If some planner realises behaviour `b` from reward `r`, then the planner that
first negates its argument realises the same behaviour from `-r`. So not even the
*sign* of the reward is identified by behaviour.

The planner here is arbitrary and unconstrained, so no maximisation is involved;
reading `p` as a maximiser and `fun r' => p (-r')` as a minimiser requires
optimality assumptions this module does not make.
-/
public theorem neg_twin {R B : Type*} [InvolutiveNeg R] (p : Planner R B) (r : R) :
    Explains (fun r' => p (-r')) (-r) (p r) := by
  simp [Explains]

/-!
## Instantiation at policies

The abstract statements above are instantiated at the reading intended by the
source: behaviour is a policy from states to actions, and a reward is a
real-valued function of state and action.
-/

/-- A policy: the observable state-to-action behaviour of an agent. -/
public abbrev Policy (S A : Type*) : Type _ := S → A

/-- A real-valued reward on state-action pairs. -/
public abbrev RewardFn (S A : Type*) : Type _ := S → A → ℝ

/--
**Policy form of preference unidentifiability (BY-011).**

For any observed policy and any candidate reward function there is a planner
producing that policy from that reward.
-/
public theorem policy_reward_unidentifiable {S A : Type*}
    (π : Policy S A) (R : RewardFn S A) :
    ∃ p : Planner (RewardFn S A) (Policy S A), Explains p R π :=
  exists_planner π R

/--
**Policy form of the anti-rational twin.**

Negating a reward function and pre-composing the planner with negation leaves
the realised policy unchanged.
-/
public theorem policy_neg_twin {S A : Type*}
    (p : Planner (RewardFn S A) (Policy S A)) (R : RewardFn S A) :
    Explains (fun R' => p (-R')) (-R) (p R) :=
  neg_twin p R

/-!
## Theorem 1, second half

The source's Theorem 1 has two halves. The first is `exists_planner`. The second
fixes the planner instead and varies the reward, and holds for any behaviour in
the planner's image.
-/

/--
**Theorem 1, second half.** For any planner and any behaviour in its image there
is a reward realising that behaviour.
-/
public theorem exists_reward {R B : Type*} (p : Planner R B) (b : B)
    (hb : b ∈ Set.range p) :
    ∃ r : R, Explains p r b := hb

/-!
## The degenerate pairs (source §5.1.1)

The source exhibits three pairs compatible with a policy `π`: the indifferent
planner with any reward, the greedy planner with the reward that rewards exactly
`π`'s action, and the anti-rational negation of the latter.
-/

/-- The indifferent planner: ignores its reward and always returns `π`. This is
the source's `p_π`, and the witness used by `exists_planner`. -/
@[expose] public def indifferentPlanner {R B : Type*} (b : B) : Planner R B :=
  fun _ => b

/-- The reward that pays exactly for following `π`. This is the source's `R_π`. -/
@[expose] public def rewardOf {S A : Type*} [DecidableEq A] (π : Policy S A) :
    RewardFn S A :=
  fun s a => if a = π s then 1 else 0

/-- An action maximising the reward at a state; the choice is arbitrary among
maximisers. -/
public noncomputable def greedyAction {S A : Type*} [Fintype A] [Nonempty A]
    (R : RewardFn S A) (s : S) : A :=
  (Finset.exists_max_image (Finset.univ : Finset A) (R s) ⟨Classical.arbitrary A, Finset.mem_univ _⟩).choose

/-- `greedyAction` earns its name: no action in the finite action type scores
above it under the same reward. The defining property a consumer needs, since
the definition itself goes through `Finset.exists_max_image` and `choose`. -/
public theorem greedyAction_max {S A : Type*} [Fintype A] [Nonempty A]
    (R : RewardFn S A) (s : S) (a : A) :
    R s a ≤ R s (greedyAction R s) :=
  (Finset.exists_max_image (Finset.univ : Finset A) (R s)
    ⟨Classical.arbitrary A, Finset.mem_univ _⟩).choose_spec.2 a (Finset.mem_univ a)

/-- The greedy planner: at each state take a reward-maximising action. This is
the source's `p_g`. -/
public noncomputable def greedyPlanner {S A : Type*} [Fintype A] [Nonempty A] :
    Planner (RewardFn S A) (Policy S A) :=
  fun R s => greedyAction R s

/-- **The greedy planner recovers `π` from `R_π`** — the source's `p_g(R_π) = π`. -/
public theorem greedy_rewardOf {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (π : Policy S A) :
    Explains greedyPlanner (rewardOf π) π := by
  simp only [Explains]
  funext s
  show greedyAction (rewardOf π) s = π s
  by_contra hne
  have hmax := greedyAction_max (rewardOf π) s (π s)
  have h1 : rewardOf π s (π s) = 1 := by simp [rewardOf]
  have h0 : rewardOf π s (greedyAction (rewardOf π) s) = 0 := by simp [rewardOf, hne]
  rw [h1, h0] at hmax
  exact absurd hmax (not_le.mpr zero_lt_one)

/--
**Definition 5.** The negative of a planner: `(-p)(R) = p(-R)`.

The source's anti-greedy planner is `-p_g`, and by this definition
`(-p_g)(R)(s) = argmin_a R(s,a)`.
-/
@[expose] public def negPlanner {S A : Type*}
    (p : Planner (RewardFn S A) (Policy S A)) : Planner (RewardFn S A) (Policy S A) :=
  fun R => p (-R)

/-- **Degenerate pair 1**: the indifferent planner with an arbitrary reward. -/
public theorem degenerate_indifferent {R B : Type*} (b : B) (r : R) :
    Explains (indifferentPlanner b) r b := rfl

/-- **Degenerate pair 2**: the greedy planner with the reward that pays for `π`. -/
public theorem degenerate_greedy {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (π : Policy S A) :
    Explains greedyPlanner (rewardOf π) π := greedy_rewardOf π

/-- **Degenerate pair 3**: the anti-rational negation of pair 2. The source's
`-p_g(-R_π) = p_g(R_π) = π`. -/
public theorem degenerate_antirational {S A : Type*} [Fintype A] [Nonempty A]
    [DecidableEq A] (π : Policy S A) :
    Explains (fun R' => greedyPlanner (-R')) (-rewardOf π) π := by
  have := neg_twin (greedyPlanner (S := S) (A := A)) (rewardOf π)
  rwa [greedy_rewardOf π] at this

/--
**Lemma 6.** The pairs `(p_π, 0)`, `(p_g, R_π)` and `(-p_g, -R_π)` are all
compatible with `π`.

Stated as the source states it, collecting the three separate compatibility
results above.
-/
public theorem lemma_six {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (π : Policy S A) :
    Explains (indifferentPlanner π) (0 : RewardFn S A) π ∧
    Explains greedyPlanner (rewardOf π) π ∧
    Explains (negPlanner greedyPlanner) (-rewardOf π) π :=
  ⟨degenerate_indifferent π 0, degenerate_greedy π, degenerate_antirational π⟩

end AISafetyAtlas.Preference
