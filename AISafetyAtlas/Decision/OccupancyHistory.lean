module

public import AISafetyAtlas.Decision.Occupancy

/-!
# Discounted visit counts at non-stationary policies

`AISafetyAtlas.Decision.Occupancy` defines print's visit counts `F^π` and the
pairing `J_ℛ(π) = ⟨ℛ, F^π⟩` at a **stationary** policy `π : S → Δ(A)`. Print defines
them at every policy. Skalse, Howe, Krasheninnikov and Krueger, NeurIPS 2022, §4.1
(PDF p. 4): *"a non-stationary policy is a function `π : (S × A)^* × S → Δ(A)`"*, and
*"We define the (discounted) visit counts of a policy as
`F^π(s, a) = 𝔼_{τ∼π}[∑_{i=0}^∞ γ^i 𝟙(sᵢ = s, aᵢ = a)]`"*; §5.1 (PDF p. 6) then reads
`J₁` and `J₂` on the set `Π^N` of all non-stationary policies.

This module is that definition at print's non-stationary policies.

* **The policy** is `Policy State Action` of `AISafetyAtlas.Decision.MDP`, a map from
  observed histories to action distributions, with the state itself as the
  observation. A history there is the first state followed by the
  `(action, next state)` pairs, which carries exactly the information of print's
  `(S × A)^* × S`, in another order.
* **The trajectory** is `MDP.run`, which draws actions from the policy and successor
  states from the transition. `MDP.run` starts at one state; print's initial
  distribution `I` is bound in front of it.
* **The visit counts** are the sum over time of the discounted law of
  `(sₙ, aₙ)`. Print takes the expectation of a sum and this takes the sum of
  expectations; every term is non-negative, so the exchange is Tonelli, as in
  `Occupancy`.

`histVisitCount_ofStationary` ties the two layers together: at a policy that reads
only the current state, these visit counts are `AISafetyAtlas.Decision.visitCount`, so the
stationary layer is the special case and not a second computation.
-/

namespace AISafetyAtlas.Decision

open scoped NNReal

universe u v

variable {State : Type u} {Action : Type v}

/-- The current state of a history: its last observation. -/
@[expose] public def History.lastObs {Obs : Type u} {A : Type v} (h : History Obs A) : Obs :=
  (h.2.getLast?.map Prod.snd).getD h.1

/-- **The law of `(sₙ, aₙ)`** under a non-stationary policy `σ`, from print's
initial distribution `I`: run `n` steps, then draw the `n`-th action from the
policy at the history so far. -/
@[expose] public noncomputable def pairLaw (M : MDP State Action) (σ : Policy State Action)
    (I : PMF State) (n : ℕ) : PMF (State × Action) :=
  I.bind fun s₀ => (M.run id σ s₀ n).bind fun p => (σ p.2).map fun a => (p.1, a)

/-- **Print's discounted visit counts `F^π(s, a)` at a non-stationary policy.** -/
@[expose] public noncomputable def histVisitCount (M : MDP State Action)
    (σ : Policy State Action) (I : PMF State) (γ : ℝ≥0) (s : State) (a : Action) : ℝ :=
  ∑' n : ℕ, (γ : ℝ) ^ n * (pairLaw M σ I n (s, a)).toReal

/-- A probability is at most one after `ENNReal.toReal`. -/
private theorem toReal_le_one {α : Type*} (p : PMF α) (x : α) : (p x).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one p x)

/-- The visit-count series is summable below discount one. -/
public theorem summable_histVisitCount (M : MDP State Action) (σ : Policy State Action)
    (I : PMF State) {γ : ℝ≥0} (hγ : γ < 1) (s : State) (a : Action) :
    Summable fun n : ℕ => (γ : ℝ) ^ n * (pairLaw M σ I n (s, a)).toReal := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg γ.coe_nonneg n) ENNReal.toReal_nonneg)
    (fun n => ?_) (summable_geometric_of_lt_one γ.coe_nonneg hγ')
  calc (γ : ℝ) ^ n * (pairLaw M σ I n (s, a)).toReal
      ≤ (γ : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (toReal_le_one _ _) (pow_nonneg γ.coe_nonneg n)
    _ = (γ : ℝ) ^ n := mul_one _

/-- Visit counts are non-negative. -/
public theorem histVisitCount_nonneg (M : MDP State Action) (σ : Policy State Action)
    (I : PMF State) (γ : ℝ≥0) (s : State) (a : Action) :
    0 ≤ histVisitCount M σ I γ s a :=
  tsum_nonneg fun _ => mul_nonneg (pow_nonneg γ.coe_nonneg _) ENNReal.toReal_nonneg

/-- **The whole discounted horizon is spent somewhere**, at every non-stationary
policy: the visit counts sum to `(1 - γ)⁻¹`. -/
public theorem sum_histVisitCount_eq [Fintype State] [Fintype Action]
    (M : MDP State Action) (σ : Policy State Action) (I : PMF State) {γ : ℝ≥0}
    (hγ : γ < 1) :
    ∑ s, ∑ a, histVisitCount M σ I γ s a = (1 - (γ : ℝ))⁻¹ := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  simp only [histVisitCount]
  simp_rw [← Summable.tsum_finsetSum fun a (_ : a ∈ Finset.univ) =>
    summable_histVisitCount M σ I hγ _ a]
  rw [← Summable.tsum_finsetSum fun s (_ : s ∈ Finset.univ) =>
    summable_sum fun a (_ : a ∈ Finset.univ) => summable_histVisitCount M σ I hγ s a,
    ← tsum_geometric_of_lt_one γ.coe_nonneg hγ']
  refine tsum_congr fun n => ?_
  have hmass : ∑ s, ∑ a, (pairLaw M σ I n (s, a)).toReal = 1 := by
    rw [← Fintype.sum_prod_type' (fun s a => (pairLaw M σ I n (s, a)).toReal),
      ← tsum_fintype (L := SummationFilter.unconditional _)]
    exact tsum_prob _
  simp_rw [← Finset.mul_sum]
  rw [hmass, mul_one]

/-- **Print's `J_ℛ(π) = ⟨ℛ, F^π⟩` at a non-stationary policy.** -/
@[expose] public noncomputable def histJ [Fintype State] [Fintype Action]
    (M : MDP State Action) (I : PMF State) (γ : ℝ≥0)
    (R : State → Action → ℝ) (σ : Policy State Action) : ℝ :=
  ∑ s, ∑ a, R s a * histVisitCount M σ I γ s a

/-- **Value is a linear functional of the reward** at every non-stationary policy. -/
public theorem histJ_linear [Fintype State] [Fintype Action] (M : MDP State Action)
    (I : PMF State) (γ : ℝ≥0) (c₁ c₂ : ℝ) (R₁ R₂ : State → Action → ℝ)
    (σ : Policy State Action) :
    histJ M I γ (fun s a => c₁ * R₁ s a + c₂ * R₂ s a) σ
      = c₁ * histJ M I γ R₁ σ + c₂ * histJ M I γ R₂ σ := by
  simp only [histJ, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- **The expected reward at step `n`**, `𝔼[ℛ(sₙ, aₙ)]`, under a non-stationary
policy from `I`. -/
@[expose] public noncomputable def expectedReward [Fintype State] [Fintype Action]
    (M : MDP State Action) (σ : Policy State Action) (I : PMF State)
    (R : State → Action → ℝ) (n : ℕ) : ℝ :=
  ∑ s, ∑ a, R s a * (pairLaw M σ I n (s, a)).toReal

/--
**Print's "Note that `J(π) = ∑_{s,a} ℛ(s, a) F^π(s, a)`"** (§4.1, PDF p. 4), at every
non-stationary policy: the pairing `⟨ℛ, F^π⟩` is the discounted sum over time of the
expected rewards along the run, `∑ₙ γⁿ 𝔼[ℛ(sₙ, aₙ)]`. Print's `J(π) = 𝔼_τ[∑ᵢ γⁱ ℛ(sᵢ, aᵢ)]`
is the same number by the exchange of expectation and sum that its definition of
`F^π` already makes.
-/
public theorem histJ_eq_tsum_expectedReward [Fintype State] [Fintype Action]
    (M : MDP State Action) (I : PMF State) {γ : ℝ≥0} (hγ : γ < 1)
    (R : State → Action → ℝ) (σ : Policy State Action) :
    histJ M I γ R σ = ∑' n : ℕ, (γ : ℝ) ^ n * expectedReward M σ I R n := by
  have hs : ∀ s a, Summable fun n : ℕ =>
      R s a * ((γ : ℝ) ^ n * (pairLaw M σ I n (s, a)).toReal) :=
    fun s a => (summable_histVisitCount M σ I hγ s a).mul_left (R s a)
  simp only [histJ, histVisitCount, expectedReward, ← tsum_mul_left]
  simp_rw [← Summable.tsum_finsetSum fun a (_ : a ∈ Finset.univ) => hs _ a]
  rw [← Summable.tsum_finsetSum fun s (_ : s ∈ Finset.univ) =>
    summable_sum fun a (_ : a ∈ Finset.univ) => hs s a]
  refine tsum_congr fun n => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ## The stationary policies are the special case -/

/-- A stationary policy read as a non-stationary one: it looks only at the current
state. -/
@[expose] public def Policy.ofStationary (π : State → PMF Action) : Policy State Action :=
  fun h => π h.lastObs

/-- Along `MDP.run` with the state as observation, the current state of the history
is the state. -/
public theorem lastObs_of_mem_support_run (M : MDP State Action) (σ : Policy State Action)
    (s₀ : State) : ∀ (n : ℕ), ∀ p ∈ (M.run id σ s₀ n).support, p.2.lastObs = p.1
  | 0, p, hp => by
    rw [MDP.run, PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl
  | n + 1, p, hp => by
    simp only [MDP.run, PMF.support_bind, PMF.support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hp
    obtain ⟨prev, -, a, -, s, -, rfl⟩ := hp
    simp [History.lastObs]

/-- `bind` reads its continuation only on the support. -/
private theorem bind_congr_support {α β : Type*} (μ : PMF α) (f g : α → PMF β)
    (h : ∀ x ∈ μ.support, f x = g x) : μ.bind f = μ.bind g := by
  ext y
  simp only [PMF.bind_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ μ.support
  · rw [h x hx]
  · rw [PMF.mem_support_iff, not_not] at hx
    simp [hx]

/-- The law of the state after `n` steps, from `I`. -/
private noncomputable def stateLaw (M : MDP State Action) (σ : Policy State Action)
    (I : PMF State) (n : ℕ) : PMF State :=
  I.bind fun s₀ => (M.run id σ s₀ n).map Prod.fst

private theorem pairLaw_ofStationary (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) (n : ℕ) :
    pairLaw M (Policy.ofStationary π) I n
      = (stateLaw M (Policy.ofStationary π) I n).bind fun s => (π s).map fun a => (s, a) := by
  simp only [pairLaw, stateLaw, PMF.bind_bind, PMF.map]
  refine congrArg (I.bind) (funext fun s₀ => ?_)
  refine bind_congr_support _ _ _ fun p hp => ?_
  simp only [Policy.ofStationary, Function.comp_apply,
    lastObs_of_mem_support_run M _ s₀ n p hp, PMF.pure_bind]

private theorem stateLaw_ofStationary (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) : ∀ n, stateLaw M (Policy.ofStationary π) I n = stateDist M π I n
  | 0 => by simp [stateLaw, MDP.run, PMF.map, PMF.pure_bind, PMF.bind_pure]
  | n + 1 => by
    rw [stateDist_succ, ← stateLaw_ofStationary M π I n]
    simp only [stateLaw, MDP.run, PMF.map, PMF.bind_bind, PMF.pure_bind]
    refine congrArg (I.bind) (funext fun s₀ => ?_)
    refine bind_congr_support _ _ _ fun p hp => ?_
    simp only [Policy.ofStationary, Function.comp_apply,
      lastObs_of_mem_support_run M _ s₀ n p hp, PMF.bind_pure, PMF.pure_bind, stepKernel]

/-- **At a stationary policy the two layers agree**: the non-stationary visit counts
of the policy that reads only the current state are `AISafetyAtlas.Decision.visitCount`. -/
public theorem histVisitCount_ofStationary (M : MDP State Action) (π : State → PMF Action)
    (I : PMF State) (γ : ℝ≥0) (s : State) (a : Action) :
    histVisitCount M (Policy.ofStationary π) I γ s a = visitCount M π I γ s a := by
  have hpt : ∀ n, (pairLaw M (Policy.ofStationary π) I n (s, a)).toReal
      = (stateDist M π I n s).toReal * (π s a).toReal := by
    intro n
    rw [pairLaw_ofStationary, stateLaw_ofStationary, PMF.bind_apply,
      tsum_eq_single s, PMF.map_apply, tsum_eq_single a, ENNReal.toReal_mul]
    · simp
    · intro a' ha'
      simp [Ne.symm ha']
    · intro s' hs'
      have : (PMF.map (fun a => (s', a)) (π s')) (s, a) = 0 := by
        rw [PMF.map_apply]
        exact ENNReal.tsum_eq_zero.mpr fun a' => by simp [Ne.symm hs']
      simp [this]
  simp only [histVisitCount, visitCount, stateOcc, hpt, ← mul_assoc]
  exact tsum_mul_right

/-- **And so do the two pairings.** -/
public theorem histJ_ofStationary [Fintype State] [Fintype Action] (M : MDP State Action)
    (I : PMF State) (γ : ℝ≥0) (R : State → Action → ℝ) (π : State → PMF Action) :
    histJ M I γ R (Policy.ofStationary π) = J M I γ R π := by
  simp only [histJ, J, histVisitCount_ofStationary]

end AISafetyAtlas.Decision
