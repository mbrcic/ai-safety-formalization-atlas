import AISafetyAtlas.Examples.Wireheading.StochasticPolicy
import AISafetyAtlas.Wireheading.RewardGrid

/-!
# Everitt et al. Theorem 11, proof step 2, as printed is false; the repaired step holds

Tom Everitt, Victoria Krakovna, Laurent Orseau, Marcus Hutter and Shane Legg,
*Reinforcement Learning with a Corrupted Reward Channel*, arXiv:1705.08417v2
(long version, 19 Aug 2017), proof of Theorem 11, PDF p. 5 (audit row S09-R14):

    Both (Ṙ, C) and (Ṙ⁻, C⁻) induce the same observed reward function
    R̂(s) = … and therefore induce the same measure P^π_μ = P^π_{μ⁻} over
    histories (see Eq. (1)).

where `Ṙ⁻(s) = 1 − Ṙ(s)` and `C⁻_s(x) = C_s(1 − x)`, and Eq. (1), PDF p. 4, is

    When an agent π interacts with a CRMDP μ, the result can be described by a
    (possibly non-Markov) stochastic process P^π_μ over X = (s, a, ṙ, r̂),
    formally defined as:
    P^π_μ(h_n) = P^π_μ(s₀ ṙ₀ r̂₀ a₁ s₁ ṙ₁ r̂₁ … aₙ sₙ ṙₙ r̂ₙ)
      := ∏_{i=1}^{n} P(π(ĥ_{i−1}) = aᵢ) T(sᵢ | s_{i−1}, aᵢ) P(Ṙ(sᵢ) = ṙᵢ, R̂(sᵢ) = r̂ᵢ).   (1)

(Transcribed from the page images in
`docs/provenance/printed-statements/everitt-2017-corrupted-reward.yaml`, entries
`ek17-thm-11-proof-same-measure` and `ek17-eq-1`.) Theorem 11's setting: finite
`S` and `A`, rewards in a uniform discretisation `0 = r₁ < ⋯ < rₙ = 1` of `[0, 1]`,
policies possibly stochastic.

The process of Eq. (1) records the true reward `ṙᵢ`, and complementing flips it:
`Ṙ⁻(sᵢ) = 1 − Ṙ(sᵢ)`. So the two measures should disagree whenever a state whose
true reward is not `1/2` is reached with positive probability (not proved here in
general). This file proves one instance, in the library's
blind environment `blindEnv true` (true reward `0` at `true`, `1` at `false`;
observed reward `0` everywhere), with the dynamics `actIsState` (the action taken
is the next state), start state `false` and the deterministic policy that always
plays `false`. The one-step history `a₁ = false, s₁ = false, ṙ₁ = 1, r̂₁ = 0` has
probability `1` under `μ` and `0` under `μ⁻ = blindEnv false`. The rewards lie in
the grid `{0, 1}` (`n = 2`), which is closed under `x ↦ 1 − x`.

**Modelling choice: the law of Eq. (1).** The library has the law of the observed
history `(s, a, r̂)` (`mixedHistoryUpTo`) but no joint law with the true reward.
`fullHistoryLaw` is the minimal one: the observed-history law, with each step's
observation `(sᵢ, r̂ᵢ)` tagged by `Ṙ(sᵢ)`. Since `Ṙ` and `R̂` are deterministic, the
last factor of Eq. (1) is an indicator, so this pushforward has exactly the mass
Eq. (1) assigns. The policy still reads only the observed prefix `ĥ_{i−1}`,
because the library's run hands it `μ.channel`. The start observation is left
untagged. Eq. (1)'s product starts at `i = 1`, so print gives `ṙ₀` no factor, and
tagging it would make the two laws differ at `n = 0` on a coordinate print never
weighs. As modelled, the laws agree at `n = 0` and first split at the `i = 1`
factor `P(Ṙ(s₁) = ṙ₁, R̂(s₁) = r̂₁)`.

Why the repair is the necessary one and not a different theorem:

* it changes only the space the measure lives on: from histories over
  `(s, a, ṙ, r̂)` to observed histories over `(s, a, r̂)`, the marginal the policy
  reads. Eq. (1) itself writes the policy's argument as `ĥ_{i−1}`, the observed
  history;
* the proof uses step 2 only to get its equation (3), `G_t(μ, π, s₀) +
  G_t(μ⁻, π, s₀) = t`. For that it needs the visited states to have the same law,
  and the observed-history law carries them. The library proves (3) this way
  (`return_add_complement`, `mixedReturn_add_complement`);
* the repaired step is `mixedRun_complement`, proved for every kernel, every
  possibly stochastic policy and every horizon, over the whole interval-valued
  class (so without the grid hypothesis). `repaired_holds` states it.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/everitt-thm-11-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open AISafetyAtlas.Wireheading.CRMDP AISafetyAtlas.Wireheading.RewardGrid
  AISafetyAtlas.Examples.Wireheading

namespace EverittThmElevenLiteral

/-- One step of Eq. (1)'s process after the start: the action, then the state
reached with its true and observed reward, `(aᵢ, (sᵢ, ṙᵢ, r̂ᵢ))`. -/
abbrev FullStep (State Action : Type) : Type := Action × State × Reward × Reward

/-- A history of Eq. (1)'s process: the start observation `(s₀, r̂₀)`, then the
steps. -/
abbrev FullHistory (State Action : Type) : Type := Obs State × List (FullStep State Action)

/-- Tag each step's observation `(sᵢ, r̂ᵢ)` with the true reward `Ṙ(sᵢ)`. -/
def tagSteps {State Action : Type} (μ : Env State) (h : History State Action) :
    FullHistory State Action :=
  (h.1, h.2.map fun p => (p.1, p.2.1, μ.trueReward p.2.1, p.2.2))

/-- **Eq. (1)'s law after `n` steps**: the observed-history law, with each visited
state's true reward recorded. -/
noncomputable def fullHistoryLaw {State Action : Type} (M : AISafetyAtlas.Decision.MDP State Action)
    (μ : Env State) (σ : StochPolicy State Action) (s₀ : State) (n : ℕ) :
    PMF (FullHistory State Action) :=
  (mixedHistoryUpTo M μ σ s₀ n).map (tagSteps μ)

/-- Step 2 exactly as printed, in Theorem 11's setting (finite states and actions,
any transition kernel, true reward and corruption valued in the uniform grid of
`m + 2` points, possibly stochastic policy): an environment and its complement
induce the same Eq. (1) law over histories, from every start state and at every
length. -/
def LiteralPrint : Prop :=
  ∀ (State Action : Type) [Fintype State] [Fintype Action] (m : ℕ)
    (M : AISafetyAtlas.Decision.MDP State Action) (μ : Env State),
    (∀ s, ∃ i, μ.trueReward s = gridVal m i) →
    (∀ s i, ∃ j, μ.corruption s (gridVal m i) = gridVal m j) →
    ∀ (σ : StochPolicy State Action) (s₀ : State) (n : ℕ),
      fullHistoryLaw M μ.complement σ s₀ n = fullHistoryLaw M μ σ s₀ n

theorem zeroReward_eq_gridVal : zeroReward = gridVal 0 0 :=
  Subtype.ext (by simp [zeroReward, gridVal])

theorem oneReward_eq_gridVal : oneReward = gridVal 0 (Fin.last 1) :=
  Subtype.ext (by rw [gridVal_last]; rfl)

/-- `blindEnv true`'s true rewards lie in the grid `{0, 1}`. -/
theorem blindEnv_trueReward_grid (s : Bool) :
    ∃ i, (blindEnv true).trueReward s = gridVal 0 i := by
  cases s
  · exact ⟨Fin.last 1, oneReward_eq_gridVal⟩
  · exact ⟨0, zeroReward_eq_gridVal⟩

/-- And its channel maps the grid into the grid (it reports `0`). -/
theorem blindEnv_corruption_grid (s : Bool) (i : Fin 2) :
    ∃ j, (blindEnv true).corruption s (gridVal 0 i) = gridVal 0 j :=
  ⟨0, zeroReward_eq_gridVal⟩

/-- The policy that always plays `false`. -/
noncomputable def playFalse : StochPolicy Bool Bool := StochPolicy.ofDet fun _ => false

/-- The one-step Eq. (1) law in a blind environment under `playFalse`: a point
mass at `a₁ = false, s₁ = false`, `r̂₁ = 0`, with `ṙ₁` the environment's true
reward at `false`. -/
theorem fullHistoryLaw_blind (a₀ : Bool) :
    fullHistoryLaw (AISafetyAtlas.Decision.MDP.ofDet actIsState) (blindEnv a₀) playFalse
        false 1 =
      PMF.pure ((false, zeroReward),
        [(false, false, (blindEnv a₀).trueReward false, zeroReward)]) := by
  rw [fullHistoryLaw, mixedHistoryUpTo, playFalse, StochPolicy.ofDet,
    AISafetyAtlas.Decision.MDP.historyUpTo_ofDet, PMF.pure_map]
  rfl

/-- **The printed step is false.** In `blindEnv true` the one-step history
`a₁ = false, s₁ = false, ṙ₁ = 1, r̂₁ = 0` is certain; in its complement
`blindEnv false` the true reward at `false` is `0`, so the law is a point mass at
a different history. -/
theorem not_literalPrint : ¬ LiteralPrint := by
  intro h
  have := h Bool Bool 0 (AISafetyAtlas.Decision.MDP.ofDet actIsState) (blindEnv true)
    blindEnv_trueReward_grid blindEnv_corruption_grid playFalse false 1
  rw [← blindEnv_complement true, Bool.not_true, fullHistoryLaw_blind,
    fullHistoryLaw_blind] at this
  have hs := congrArg PMF.support this
  rw [PMF.support_pure, PMF.support_pure, Set.singleton_eq_singleton_iff] at hs
  simp [blindEnv, zeroReward, oneReward, Subtype.ext_iff] at hs

/-- **The repaired step holds**, as the library proves it: for every transition
kernel, environment, possibly stochastic policy, start state and horizon, an
environment and its complement induce the same law over the state and the
observed history `(s, a, r̂)`, which is everything the policy reads. No grid
hypothesis is needed. -/
theorem repaired_holds {State Action : Type} (M : AISafetyAtlas.Decision.MDP State Action)
    (μ : Env State) (σ : StochPolicy State Action) (s₀ : State) (n : ℕ) :
    mixedRun M μ.complement σ s₀ n = mixedRun M μ σ s₀ n ∧
      mixedHistoryUpTo M μ.complement σ s₀ n = mixedHistoryUpTo M μ σ s₀ n :=
  ⟨mixedRun_complement M μ σ s₀ n,
    AISafetyAtlas.Decision.MDP.historyUpTo_congr_obs M (Env.channel_complement μ) σ s₀ n⟩

/-- At the counterexample the repaired step holds too: the observed-history laws
of `blindEnv true` and `blindEnv false` agree. -/
theorem repaired_at_counterexample :
    mixedHistoryUpTo (AISafetyAtlas.Decision.MDP.ofDet actIsState) (blindEnv false)
        playFalse false 1 =
      mixedHistoryUpTo (AISafetyAtlas.Decision.MDP.ofDet actIsState) (blindEnv true)
        playFalse false 1 := by
  rw [show blindEnv false = (blindEnv true).complement from blindEnv_complement true]
  exact (repaired_holds _ _ _ _ _).2

end EverittThmElevenLiteral
