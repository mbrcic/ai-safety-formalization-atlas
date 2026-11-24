import AISafetyAtlas.Wireheading.RewardGrid

/-!
Everitt, Krakovna, Orseau, Hutter and Legg (2017), arXiv:1705.08417v2, eq. (3) in
the proof of Theorem 11, p. 5: "for any `μ, π, s₀, t`,
`G_t(μ, π, s₀) + G_t(μ⁻, π, s₀) = t`", where `G_t = E^π_μ[∑_{k=1}^t Ṙ(s_k)]`
(the derivation on the same page) and `μ⁻` replaces `Ṙ` by `1 - Ṙ` and `C_s` by
`x ↦ C_s(1 - x)`. Print's CRMDPs (Definition 7) have finite `S` and `A`, rewards in
a finite set, here Theorem 11's uniform discretisation of `[0, 1]`, a transition
function and possibly stochastic policies on observed histories (p. 4). Print's
instances are rendered with the atlas's grid class: `GridEnv m S` embedded by
`toEnv`, with `μ⁻` as `toEnv g.complement`, and `G_t` as `mixedReturnOver`. The
cited declaration is
`AISafetyAtlas.Wireheading.CRMDP.mixedReturn_add_complement` (arbitrary state and
action types, rewards anywhere in `[0, 1]`). The cited `stochReturn_add_complement`
and `return_add_complement` are its deterministic-policy and deterministic-
transition specializations; `lean_of_print_stoch` and `lean_of_print_det` reach
them through the library lemmas `mixedReturnOver_ofDet` and
`stochReturnOver_ofDet`.

The map fixes the horizon `t` and builds a print CRMDP with states
`Fin (t + 1) × Bool` (a clock and a coin), one action, the two-point grid
`{0, 1}`, true reward equal to the coin, and the constant observed reward `0`.
From a state with clock `c` it moves to clock `c + 1` and draws the coin by
drawing a state from the original state law at step `c + 1` and then a Bernoulli
coin with success probability the original true reward there. So the print
state law at step `k` is that coin, tagged with clock `k`. Its true-reward
expectation is the original stage expectation `E[Ṙ(s_k)]`, and its complemented
expectation is `∑ P(s) (1 - Ṙ(s))`. The latter equals the original stage
expectation in `μ⁻` once `μ⁻`'s state law is identified with `μ`'s:
`mixedStateAt_compl` re-derives the content of the cited
`mixedStateAt_complement` (the same-measure step, a separate print row) from the
uncited `Env.channel_complement`. Print's equation (3) at the image then gives
the Lean sum. The identity `∑ P(s) Ṙ(s) + ∑ P(s) (1 - Ṙ(s)) = 1` is not proved
here: print's conclusion supplies it.

Representation: as in the atlas's `RewardGrid`, a print policy is rendered as a
`StochPolicy` on histories labelled by all of `[0, 1]`; on a grid environment
only grid-labelled histories occur, so the extension off the grid is immaterial.

Checked: `lake env lean docs/provenance/transfers/185-complement-returns.lean`
-/

namespace Transfer185

open AISafetyAtlas AISafetyAtlas.Wireheading.CRMDP AISafetyAtlas.Wireheading.RewardGrid

universe u v

/-- Eq. (3) at print's instances: finite states and actions, Theorem 11's grid
of `m + 2` rewards, any transition, any possibly stochastic policy. -/
def PrintStatement : Prop :=
  ∀ (S A : Type) [Fintype S] [Fintype A] (m : ℕ) (M : Decision.MDP S A) (g : GridEnv m S)
    (σ : StochPolicy S A) (s₀ : S) (t : ℕ),
    mixedReturnOver M t s₀ (toEnv g) σ + mixedReturnOver M t s₀ (toEnv g.complement) σ = t

def LeanStatement : Prop :=
  ∀ {State : Type u} {Action : Type v} (M : Decision.MDP State Action) (t : ℕ) (s₀ : State)
    (μ : Env State) (σ : StochPolicy State Action),
    mixedReturnOver M t s₀ μ σ + mixedReturnOver M t s₀ μ.complement σ = (t : ℝ)

section

variable {State : Type u} {Action : Type v}
  (M : Decision.MDP State Action) (μ : Env State) (σ : StochPolicy State Action) (s₀ : State)

/-- A coin whose success probability is a reward. -/
noncomputable def bern (r : Reward) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then r.1 else 1 - r.1)) (by
    rw [Fintype.sum_bool, if_pos rfl, if_neg Bool.false_ne_true,
      ← ENNReal.ofReal_add r.2.1 (by linarith [r.2.2])]
    simp)

theorem bern_toReal (r : Reward) (b : Bool) :
    (bern r b).toReal = if b then r.1 else 1 - r.1 := by
  rw [bern, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  split_ifs <;> linarith [r.2.1, r.2.2]

/-- The coin at step `k`: a state from the `k`-th state law, then its reward coin. -/
noncomputable def coin (k : ℕ) : PMF Bool :=
  (mixedStateAt M μ σ s₀ k).bind fun s => bern (μ.trueReward s)

theorem coin_toReal (k : ℕ) (b : Bool) :
    (coin M μ σ s₀ k b).toReal = ∑' s, (mixedStateAt M μ σ s₀ k s).toReal *
      (if b then (μ.trueReward s : ℝ) else 1 - (μ.trueReward s : ℝ)) := by
  rw [coin, PMF.bind_apply, ENNReal.tsum_toReal_eq fun s =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp_rw [ENNReal.toReal_mul, bern_toReal]

/-- The clock reading `k` (taken mod `t + 1`; only `k ≤ t` is used). -/
def clk (t k : ℕ) : Fin (t + 1) := ⟨k % (t + 1), Nat.mod_lt _ (Nat.succ_pos t)⟩

/-- The image transition: advance the clock, draw the next coin. -/
noncomputable def phiM (t : ℕ) : Decision.MDP (Fin (t + 1) × Bool) Unit :=
  ⟨fun x _ => (coin M μ σ s₀ (x.1.val + 1)).bind fun b =>
    PMF.pure (clk t (x.1.val + 1), b)⟩

/-- The image environment: true reward the coin, observed reward `0`. -/
def phiG (t : ℕ) : GridEnv 0 (Fin (t + 1) × Bool) :=
  ⟨fun x => if x.2 then 1 else 0, fun _ _ => 0⟩

/-- The only policy over one action. -/
noncomputable def phiσ (t : ℕ) : StochPolicy (Fin (t + 1) × Bool) Unit := fun _ => PMF.pure ()

theorem stateAt_phiM (t : ℕ) (obs : Fin (t + 1) × Bool → Obs (Fin (t + 1) × Bool)) :
    ∀ k, k < t → (phiM M μ σ s₀ t).stateAt obs (phiσ t) (0, false) (k + 1) =
      (coin M μ σ s₀ (k + 1)).bind fun b => PMF.pure (clk t (k + 1), b) := by
  have hsucc : ∀ n, (phiM M μ σ s₀ t).stateAt obs (phiσ t) (0, false) (n + 1) =
      ((phiM M μ σ s₀ t).stateAt obs (phiσ t) (0, false) n).bind
        fun x => (phiM M μ σ s₀ t).transition x () := by
    intro n
    simp only [Decision.MDP.stateAt, Decision.MDP.run, PMF.bind_bind, PMF.pure_bind, phiσ,
      PMF.bind_pure]
  intro k hk
  induction k with
  | zero =>
    rw [hsucc]
    simp [Decision.MDP.stateAt, Decision.MDP.run, phiM]
  | succ k ih =>
    rw [hsucc, ih (by omega), PMF.bind_bind]
    simp only [PMF.pure_bind, phiM]
    have hv : (clk t (k + 1)).val = k + 1 := Nat.mod_eq_of_lt (by omega)
    simp only [hv, PMF.bind_const]

/-- The same-measure step, from the uncited `Env.channel_complement`. -/
theorem mixedStateAt_compl (n : ℕ) :
    mixedStateAt M μ.complement σ s₀ n = mixedStateAt M μ σ s₀ n := by
  unfold mixedStateAt
  rw [show μ.complement.channel = μ.channel from funext (Env.channel_complement μ)]

/-- Both image returns are the original returns, stage by stage. -/
theorem image_returns (t : ℕ) :
    mixedReturnOver (phiM M μ σ s₀ t) t (0, false) (toEnv (phiG t)) (phiσ t) =
        mixedReturnOver M t s₀ μ σ ∧
      mixedReturnOver (phiM M μ σ s₀ t) t (0, false) (toEnv (phiG t).complement) (phiσ t) =
        mixedReturnOver M t s₀ μ.complement σ := by
  constructor <;>
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [expectReward, mixedStateAt, stateAt_phiM M μ σ s₀ t _ k hk, Decision.expect_bind,
      Fintype.sum_bool, Decision.expect_pure, Decision.expect_pure, coin_toReal, coin_toReal,
      expectReward, Decision.expect]
    try rw [mixedStateAt_compl]
    simp [toEnv, phiG, GridEnv.complement, gridVal, gridRev, Env.complement,
      Env.rewardComplement]

/-- (H) holds vacuously: the Lean statement has no hypothesis, and the image is a
print instance by construction (finite states, one action, the grid `{0, 1}`). -/
theorem H (t : ℕ) : Nonempty (Fintype (Fin (t + 1) × Bool)) ∧ Nonempty (Fintype Unit) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- (C): print's eq. (3) at the image gives the Lean sum. -/
theorem C (t : ℕ)
    (h : mixedReturnOver (phiM M μ σ s₀ t) t (0, false) (toEnv (phiG t)) (phiσ t) +
      mixedReturnOver (phiM M μ σ s₀ t) t (0, false) (toEnv (phiG t).complement) (phiσ t) = t) :
    mixedReturnOver M t s₀ μ σ + mixedReturnOver M t s₀ μ.complement σ = (t : ℝ) := by
  rwa [(image_returns M μ σ s₀ t).1, (image_returns M μ σ s₀ t).2] at h

end

theorem lean_of_print : PrintStatement → LeanStatement.{u, v} := by
  intro hp State Action M t s₀ μ σ
  exact C M μ σ s₀ t (hp _ _ 0 (phiM M μ σ s₀ t) (phiG t) (phiσ t) (0, false) t)

theorem lean_of_print_stoch (hp : PrintStatement) {State : Type u} {Action : Type v}
    (M : Decision.MDP State Action) (t : ℕ) (s₀ : State) (μ : Env State)
    (π : Policy State Action) :
    stochReturnOver M t s₀ μ π + stochReturnOver M t s₀ μ.complement π = (t : ℝ) := by
  rw [← mixedReturnOver_ofDet, ← mixedReturnOver_ofDet]
  exact lean_of_print hp M t s₀ μ _

theorem lean_of_print_det (hp : PrintStatement) {State : Type u} {Action : Type v}
    (transition : State → Action → State) (t : ℕ) (s₀ : State) (μ : Env State)
    (π : Policy State Action) :
    returnOver transition t s₀ μ π + returnOver transition t s₀ μ.complement π = (t : ℝ) := by
  rw [← stochReturnOver_ofDet, ← stochReturnOver_ofDet]
  exact lean_of_print_stoch hp _ t s₀ μ π

/-- Every print instance is a Lean instance. -/
theorem print_of_lean : LeanStatement.{0, 0} → PrintStatement := by
  intro hl S A _ _ m M g σ s₀ t
  rw [mixedReturnOver_toEnv_complement]
  exact hl M t s₀ (toEnv g) σ

end Transfer185
