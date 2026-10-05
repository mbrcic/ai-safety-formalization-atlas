module

public import AISafetyAtlas.Decision.Expect
public import AISafetyAtlas.Decision.MDP
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Discounted visit counts, and value as a linear functional of the reward

`AISafetyAtlas.Decision.DiscountedValue` computes a policy's value as the Banach
fixed point of its Bellman operator: a function from states to reals, one
equation per state. This module computes the same quantity the other way round.
A policy is a **point in Euclidean space** — its discounted visit counts — and a
reward function is a **linear functional** on that space.

The two readings answer different questions. The fixed point is what you iterate;
the embedding is what you do geometry on, and every result in Skalse, Howe,
Krasheninnikov and Krueger, *Defining and Characterizing Reward Hacking*, NeurIPS
2022, is geometry on it. Nothing here supersedes `DiscountedValue`; see
**What is not proved here** below for what relates them, which is nothing yet.

## Print's setup, §4.1

Skalse et al., published NeurIPS 2022 version, sha256
`634ffa7ccb0225296482ef2961a38ba175bd8c1b97b998556a6bcfa7ad560210`, read from
rendered page 4. An `MDP` is `(S, A, T, I, ℛ, γ)` with `I ∈ Δ(S)` an **initial
state distribution**; an `MDP \ ℛ` is the same tuple with the reward removed,
which is this repository's `MDP` together with `I` and `γ`. Print marginalizes
`ℛ(s, a, s')` over transitions to `ℛ(s, a)` and *"adopt[s] this view from here
on"*, which is the shape `r : State → Action → ℝ` already used throughout the
decision cluster.

Print's stationary policy is `π : S → Δ(A)` — a distribution over actions at
each state, not a choice of one. That is `State → PMF Action` here, and it is
wider than `vPi`, which is defined for deterministic policies
only.

> We define the **(discounted) visit counts** of a policy as
> `F^π(s, a) ≐ 𝔼_{τ∼π}[∑_{i=0}^∞ γ^i 𝟙(sᵢ = s, aᵢ = a)]`. Note that
> `J(π) = ∑_{s,a} ℛ(s, a) F^π(s, a)`, which we also write as `⟨ℛ, F^π⟩`.

`visitCount` is `F^π` and `J` is `⟨ℛ, F^π⟩`. **Print takes the expectation of a
sum and this takes the sum of expectations**: every term is non-negative, so the
exchange is Tonelli and the two are the same number. It is worth one sentence
because it is the only step between print's definition and this one.

`stateOcc` is the state-marginal `∑_a F^π(s, a)`, factored out because a
stationary policy makes `F^π(s, a) = (∑_{a'} F^π(s, a')) · π(a ∣ s)` — the
action is drawn from `π` at the state and from nothing else.

## A hypothesis print leaves implicit

Print says `γ ∈ [0, 1]`. At `γ = 1` the visit counts of a policy that never
leaves a state are infinite and `J` is not defined, so every statement here
carries `γ < 1`, matching `DiscountedValue`'s `{γ : ℝ≥0} (hγ : γ < 1)`. The
definitions themselves do not: a `tsum` of a non-summable family is zero, so the
hypothesis goes where it is used.

## What is not proved here

* **That this is `vPi` averaged over `I`.** It is, and the proof
  is not here: `vPi` is stated for deterministic policies and the bridge needs it
  for stochastic ones. Until that exists the tree has two value computations that
  no theorem connects, which `docs/agent/policy/lean-parsimony.md` allows only
  with the reason recorded — this is the reason, and section 26 of
  `docs/provenance/source-coverage-audit.md` carries the cost.
* **That `stateDist` is the state marginal of `AISafetyAtlas.Decision.MDP.run`.**
  `run` takes a single start state and a history-dependent policy; the stationary
  chain here is its specialization along `obs = id` at a policy that reads only
  the last observation. Also costed in section 26.
-/

namespace AISafetyAtlas.Decision

open scoped NNReal

universe u v

variable {State : Type u} {Action : Type v}

/-- A probability is at most one after `ENNReal.toReal`. -/
private theorem prob_le_one (p : PMF State) (s : State) : (p s).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one p s)

/-! ## The chain a stationary policy induces -/

/--
**The transition kernel of a stationary policy**: draw the action from `π` at the
current state, then the successor from the environment.
-/
@[expose] public noncomputable def stepKernel (M : MDP State Action)
    (π : State → PMF Action) (s : State) : PMF State :=
  (π s).bind (M.transition s)

/--
**Where the policy is after `n` steps**, starting from print's initial
distribution `I`.
-/
@[expose] public noncomputable def stateDist (M : MDP State Action)
    (π : State → PMF Action) (I : PMF State) : ℕ → PMF State
  | 0 => I
  | n + 1 => (stateDist M π I n).bind (stepKernel M π)

@[simp] public theorem stateDist_zero (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) : stateDist M π I 0 = I := rfl

@[simp] public theorem stateDist_succ (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) (n : ℕ) :
    stateDist M π I (n + 1) = (stateDist M π I n).bind (stepKernel M π) := rfl

/-! ## The visit counts -/

/--
**The discounted occupancy of a state**: how much discounted time the policy
spends there, summed over all of time.

This is `∑_a F^π(s, a)`. Print's `F^π` itself is `visitCount` below.
-/
@[expose] public noncomputable def stateOcc (M : MDP State Action)
    (π : State → PMF Action) (I : PMF State) (γ : ℝ≥0) (s : State) : ℝ :=
  ∑' n : ℕ, (γ : ℝ) ^ n * (stateDist M π I n s).toReal

/--
**Print's discounted visit counts `F^π(s, a)`.** The discounted time spent at
`s`, times the probability the policy takes `a` there.
-/
@[expose] public noncomputable def visitCount (M : MDP State Action)
    (π : State → PMF Action) (I : PMF State) (γ : ℝ≥0) (s : State) (a : Action) : ℝ :=
  stateOcc M π I γ s * (π s a).toReal

/--
**Print's second embedding `G`**: the policy read off directly as the vector of
its action probabilities, `G(π)[s, a] = π(a ∣ s)`.

Print uses it alongside `F` because the two are homeomorphic on an open set of
policies (its Lemma 1) — not proved here, and costed in section 26 of
`docs/provenance/source-coverage-audit.md`.
-/
@[expose] public noncomputable def actionEmbed (π : State → PMF Action)
    (s : State) (a : Action) : ℝ :=
  (π s a).toReal

/-- **The two embeddings differ by the state occupancy**, which is the whole
relationship between them at a stationary policy. -/
public theorem visitCount_eq_stateOcc_mul_actionEmbed (M : MDP State Action)
    (π : State → PMF Action) (I : PMF State) (γ : ℝ≥0) (s : State) (a : Action) :
    visitCount M π I γ s a = stateOcc M π I γ s * actionEmbed π s a := rfl

/-- The discounted occupancy series is summable below discount one, by
comparison with the geometric series. -/
public theorem summable_stateOcc (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) {γ : ℝ≥0} (hγ : γ < 1) (s : State) :
    Summable fun n : ℕ => (γ : ℝ) ^ n * (stateDist M π I n s).toReal := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg γ.coe_nonneg n) ENNReal.toReal_nonneg)
    (fun n => ?_) (summable_geometric_of_lt_one γ.coe_nonneg hγ')
  calc (γ : ℝ) ^ n * (stateDist M π I n s).toReal
      ≤ (γ : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (prob_le_one _ s) (pow_nonneg γ.coe_nonneg n)
    _ = (γ : ℝ) ^ n := mul_one _

/-- Discounted occupancy is non-negative. -/
public theorem stateOcc_nonneg (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) (γ : ℝ≥0) (s : State) : 0 ≤ stateOcc M π I γ s :=
  tsum_nonneg fun _ => mul_nonneg (pow_nonneg γ.coe_nonneg _) ENNReal.toReal_nonneg

/-- **No state is occupied for more than the whole discounted horizon.** -/
public theorem stateOcc_le (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) {γ : ℝ≥0} (hγ : γ < 1) (s : State) :
    stateOcc M π I γ s ≤ (1 - (γ : ℝ))⁻¹ := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  rw [← tsum_geometric_of_lt_one γ.coe_nonneg hγ']
  refine (summable_stateOcc M π I hγ s).tsum_le_tsum (fun n => ?_)
    (summable_geometric_of_lt_one γ.coe_nonneg hγ')
  calc (γ : ℝ) ^ n * (stateDist M π I n s).toReal
      ≤ (γ : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (prob_le_one _ s) (pow_nonneg γ.coe_nonneg n)
    _ = (γ : ℝ) ^ n := mul_one _

/-- Visit counts are non-negative. -/
public theorem visitCount_nonneg (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) (γ : ℝ≥0) (s : State) (a : Action) :
    0 ≤ visitCount M π I γ s a :=
  mul_nonneg (stateOcc_nonneg M π I γ s) ENNReal.toReal_nonneg

/--
**The whole discounted horizon is spent somewhere.** Total occupancy is
`(1 - γ)⁻¹` at every policy and every initial distribution — the policy decides
*where* the time goes, never *how much* there is.

This is what makes print's picture a picture: every policy's visit counts land
on one and the same scaled simplex, and a reward function is a linear functional
on it.
-/
public theorem sum_stateOcc_eq [Fintype State] (M : MDP State Action)
    (π : State → PMF Action) (I : PMF State) {γ : ℝ≥0} (hγ : γ < 1) :
    ∑ s, stateOcc M π I γ s = (1 - (γ : ℝ))⁻¹ := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  simp only [stateOcc]
  rw [← Summable.tsum_finsetSum fun s (_ : s ∈ Finset.univ) => summable_stateOcc M π I hγ s,
    ← tsum_geometric_of_lt_one γ.coe_nonneg hγ']
  refine tsum_congr fun n => ?_
  have hmass : ∑ s, (stateDist M π I n s).toReal = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional _)]
    exact tsum_prob _
  rw [← Finset.mul_sum, hmass, mul_one]

/-! ## Value as a linear functional of the reward -/

/--
**Print's `J_ℛ(π) = ⟨ℛ, F^π⟩`**: the reward paired with the policy's visit
counts.

The reward is an argument rather than a field, exactly as print's `MDP \ ℛ`
leaves it out of the environment, and that is what makes the pairing linear in
it.
-/
@[expose] public noncomputable def J [Fintype State] [Fintype Action]
    (M : MDP State Action) (I : PMF State) (γ : ℝ≥0)
    (R : State → Action → ℝ) (π : State → PMF Action) : ℝ :=
  ∑ s, ∑ a, R s a * visitCount M π I γ s a

/--
**Value is additive in the reward.** Two objectives pursued at once are their
sum, at every policy.
-/
public theorem J_add [Fintype State] [Fintype Action] (M : MDP State Action)
    (I : PMF State) (γ : ℝ≥0) (R₁ R₂ : State → Action → ℝ) (π : State → PMF Action) :
    J M I γ (fun s a => R₁ s a + R₂ s a) π = J M I γ R₁ π + J M I γ R₂ π := by
  simp only [J, add_mul, Finset.sum_add_distrib]

/-- **And homogeneous in it.** -/
public theorem J_smul [Fintype State] [Fintype Action] (M : MDP State Action)
    (I : PMF State) (γ : ℝ≥0) (c : ℝ) (R : State → Action → ℝ)
    (π : State → PMF Action) :
    J M I γ (fun s a => c * R s a) π = c * J M I γ R π := by
  simp only [J, Finset.mul_sum, mul_assoc]

/--
**So value is a linear functional of the reward** — print's whole geometric
picture in one statement. The policy enters only through its visit counts, and
the reward only through the pairing.
-/
public theorem J_linear [Fintype State] [Fintype Action] (M : MDP State Action)
    (I : PMF State) (γ : ℝ≥0) (c₁ c₂ : ℝ) (R₁ R₂ : State → Action → ℝ)
    (π : State → PMF Action) :
    J M I γ (fun s a => c₁ * R₁ s a + c₂ * R₂ s a) π
      = c₁ * J M I γ R₁ π + c₂ * J M I γ R₂ π := by
  rw [J_add M I γ (fun s a => c₁ * R₁ s a) (fun s a => c₂ * R₂ s a) π,
    J_smul M I γ c₁ R₁ π, J_smul M I γ c₂ R₂ π]

/-- **A constant reward pays the same to every policy** -- it is print's *trivial*
reward function, and the statement is that the whole discounted horizon is spent
somewhere. -/
public theorem J_const [Fintype State] [Fintype Action] (M : MDP State Action)
    (I : PMF State) (γ : ℝ≥0) (c : ℝ) (π : State → PMF Action) :
    J M I γ (fun _ _ => c) π = c * ∑ s, stateOcc M π I γ s := by
  have hsum : ∀ s : State, ∑ a, (π s a).toReal = 1 := fun s => by
    rw [← tsum_fintype (L := SummationFilter.unconditional _)]
    exact tsum_prob (π s)
  simp only [J, visitCount]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  calc ∑ a, c * (stateOcc M π I γ s * (π s a).toReal)
      = c * stateOcc M π I γ s * ∑ a, (π s a).toReal := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = c * stateOcc M π I γ s := by rw [hsum s, mul_one]

/--
**And so a constant reward pays every policy the same number.** Print's *trivial*
reward function, with the number computed.
-/
public theorem J_const_eq [Fintype State] [Fintype Action] (M : MDP State Action)
    (I : PMF State) {γ : ℝ≥0} (hγ : γ < 1) (c : ℝ) (π : State → PMF Action) :
    J M I γ (fun _ _ => c) π = c * (1 - (γ : ℝ))⁻¹ := by
  rw [J_const M I γ c π, sum_stateOcc_eq M π I hγ]

end AISafetyAtlas.Decision
