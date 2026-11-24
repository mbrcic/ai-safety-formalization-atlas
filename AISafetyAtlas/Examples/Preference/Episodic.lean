module

public import AISafetyAtlas.Preference.Episodic
public import AISafetyAtlas.Examples.Preference.Discounted

/-!
# The episodic regret and override results, on an infinite chain

The chain `0 → 1 → 2 → …` with two actions (`chainMDP`) and the reward
`payForTrue` paying `1` for action `true`. Always playing `true` earns `T`
over `T` steps, the bound, so it maximises; that inhabits the maximiser
hypotheses of equation (2) at every horizon.

Random termination: `coinEndMDP` on Bool (false running, true terminal) ends
each step with probability 1/2, so the episode's length is geometric and
unbounded. At a constant reward `k` per step the return up to termination is
2k (`coin_vPiTerm`), and no fixed horizon reaches it (`coin_vPiStopped_lt`).
Equation (2) is applied there at Ṙ = 1, R^a = 3.
-/

namespace AISafetyAtlas.Examples.Preference.Episodic

open AISafetyAtlas.Preference AISafetyAtlas.Decision AISafetyAtlas.Preference.Discounted
open AISafetyAtlas.Preference.Episodic AISafetyAtlas.Examples.Preference.Discounted

/-- **§4.1.2's half-maximal bound at an episodic MDP**, on an infinite state
space, at every horizon. -/
public theorem chain_episodic_half_maximal_regret (T : ℕ) (π : ℕ → Bool) :
    (⨆ π' : ℕ → Bool, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn ℕ Bool) (σ : ℕ → Bool) => vPiEpisodic chainMDP R.1 T σ 0)
        Set.univ π') / 2 ≤
      AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn ℕ Bool) (σ : ℕ → Bool) => vPiEpisodic chainMDP R.1 T σ 0)
        Set.univ π :=
  episodic_half_maximal_regret chainMDP T 0 π

/-- Always playing `true` maximises the `T`-step value of `payForTrue`. -/
public theorem chain_payForTrue_max_ep (T : ℕ) (π : ℕ → Bool) :
    vPiEpisodic chainMDP payForTrue T π 0 ≤
      vPiEpisodic chainMDP payForTrue T (fun _ => true) 0 := by
  rw [vPiEpisodic_const_reward chainMDP payForTrue (fun _ => true) 1 (fun _ => rfl) T]
  exact le_of_abs_le (abs_vPiEpisodic_le chainMDP payForTrue π
    (fun s => abs_payForTrue_le s (π s)) T 0)

/-- **Equation (2) at an episodic MDP**, at the forced policy maximising
`R^a = payForTrue`. -/
public theorem chain_beliefValueEp_overriding (T : ℕ) (πdot : ℕ → Bool) (ε : ℝ) :
    beliefValueEp chainMDP T 0 πdot ε payForTrue payForTrue (some fun _ => true) =
      ε * optValueEp chainMDP payForTrue T 0 +
        (1 - ε) * vPiEpisodic chainMDP payForTrue T (fun _ => true) 0 :=
  beliefValueEp_overriding chainMDP T 0 πdot ε payForTrue payForTrue _
    (chain_payForTrue_max_ep T)

/-- **Action `0` gives `V*_Ṙ` at an episodic MDP**, at the human policy
maximising `Ṙ = payForTrue`. -/
public theorem chain_beliefValueEp_noop (T : ℕ) (ε : ℝ) :
    beliefValueEp chainMDP T 0 (fun _ => true) ε payForTrue payForTrue none =
      optValueEp chainMDP payForTrue T 0 :=
  beliefValueEp_noop chainMDP T 0 _ ε payForTrue payForTrue (chain_payForTrue_max_ep T)

/-- Values on the augmented chain are values on the chain, at every horizon. -/
example (T : ℕ) (π : ℕ × Bool → Bool) (b : Bool) :
    vPiEpisodic (augmentMDP chainMDP) (liftReward payForTrue) T π (0, b) =
      vPiEpisodic chainMDP payForTrue T (fun s => π (s, b)) 0 :=
  vPiEpisodic_augmentMDP chainMDP _ T π 0 b

/-- Action `(1, π)` under the belief, for any forced policy. -/
example (T : ℕ) (πdot π : ℕ → Bool) (ε : ℝ) :
    beliefValueEp chainMDP T 0 πdot ε payForTrue payForTrue (some π) =
      ε * vPiEpisodic chainMDP payForTrue T π 0 +
        (1 - ε) * vPiEpisodic chainMDP payForTrue T π 0 :=
  beliefValueEp_some chainMDP T 0 πdot ε payForTrue payForTrue π

/-- `V*` at horizon `T` is attained by the maximising policy. -/
example (T : ℕ) :
    optValueEp chainMDP payForTrue T 0 = vPiEpisodic chainMDP payForTrue T (fun _ => true) 0 :=
  optValueEp_eq_of_max chainMDP payForTrue T 0 _ (chain_payForTrue_max_ep T)

/-! ## Random termination: a coin ends the episode -/

/-- **A coin ends the episode**: from any state the next state is true
(terminal) or false (running) with probability 1/2 each. -/
@[expose] public noncomputable def coinEndMDP : MDP Bool Unit where
  transition _ _ := PMF.ofFintype (fun _ => 2⁻¹) (by
    rw [Fintype.sum_bool]; exact ENNReal.inv_two_add_inv_two)

/-- The constant reward `k` per step. -/
@[expose] public def constReward (k : ℝ) : RewardFn Bool Unit := fun _ _ => k

/-- The expectation under the coin is the average of the two values. -/
public theorem expect_coin (s : Bool) (a : Unit) (f : Bool → ℝ) :
    expect (coinEndMDP.transition s a) f = f true / 2 + f false / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp [coinEndMDP, PMF.ofFintype_apply]
  ring

/-- **The stopped T-step value of the coin episode from the running state** is
2k (1 − 2^{-T}). -/
public theorem coin_vPiStopped (k : ℝ) (π : Bool → Unit) (T : ℕ) :
    vPiStopped coinEndMDP {true} (constReward k) T π false = 2 * k * (1 - (1 / 2) ^ T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [AISafetyAtlas.Decision.vPiStopped_succ_of_notMem _ _ _ _ (by simp), expect_coin, ih,
      AISafetyAtlas.Decision.vPiStopped_of_mem _ _ _ _ (Set.mem_singleton true)]
    simp only [constReward, pow_succ]
    ring

/-- **The return up to termination of the coin episode is 2k**: the stopped
values converge, so `AISafetyAtlas.Decision.vPiTerm` is a genuine limit. -/
public theorem coin_vPiTerm (k : ℝ) (π : Bool → Unit) :
    vPiTerm coinEndMDP {true} (constReward k) π false = 2 * k := by
  refine AISafetyAtlas.Decision.vPiTerm_eq_of_tendsto _ _ _ _ _ ?_
  simp only [coin_vPiStopped]
  have h : Filter.Tendsto (fun T : ℕ => (1 / 2 : ℝ) ^ T) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using (h.const_sub 1).const_mul (2 * k)

/-- **No fixed horizon gives the coin episode's return**: at a positive reward
every T-step stopped value falls short of it, since the episode outlasts any
horizon with positive probability. -/
public theorem coin_vPiStopped_lt {k : ℝ} (hk : 0 < k) (π : Bool → Unit) (T : ℕ) :
    vPiStopped coinEndMDP {true} (constReward k) T π false <
      vPiTerm coinEndMDP {true} (constReward k) π false := by
  rw [coin_vPiStopped, coin_vPiTerm]
  have : 0 < (1 / 2 : ℝ) ^ T := by positivity
  nlinarith

/-- With one action every policy maximises. -/
public theorem coin_max (R : RewardFn Bool Unit) (πa π : Bool → Unit) :
    vPiTerm coinEndMDP {true} R π false ≤ vPiTerm coinEndMDP {true} R πa false :=
  le_of_eq (congrArg (fun σ => vPiTerm coinEndMDP {true} R σ false) (Subsingleton.elim π πa))

/-- **Equation (2) under random termination, on the coin episode**: with
Ṙ = 1 and R^a = 3 per step, action (1, π^a) is worth 6ε + 2(1 − ε). -/
public theorem coin_beliefValueTerm_overriding (πdot πa : Bool → Unit) (ε : ℝ) :
    beliefValueTerm coinEndMDP {true} false πdot ε (constReward 1) (constReward 3) (some πa) =
      ε * 6 + (1 - ε) * 2 := by
  rw [AISafetyAtlas.Preference.Episodic.beliefValueTerm_overriding coinEndMDP {true} false πdot ε
      (constReward 1) (constReward 3) πa (fun π => coin_max _ πa π),
    AISafetyAtlas.Preference.Episodic.optValueTerm_eq_of_max coinEndMDP {true} (constReward 3)
      false πa (fun π => coin_max _ πa π),
    coin_vPiTerm, coin_vPiTerm]
  ring

/-- **Action 0 under random termination, on the coin episode**: worth
V^*_Ṙ = 2. -/
public theorem coin_beliefValueTerm_noop (πdot : Bool → Unit) (ε : ℝ) :
    beliefValueTerm coinEndMDP {true} false πdot ε (constReward 1) (constReward 3) none = 2 := by
  rw [AISafetyAtlas.Preference.Episodic.beliefValueTerm_noop coinEndMDP {true} false πdot ε
      (constReward 1) (constReward 3) (fun π => coin_max _ πdot π),
    AISafetyAtlas.Preference.Episodic.optValueTerm_eq_of_max coinEndMDP {true} (constReward 1)
      false πdot (fun π => coin_max _ πdot π),
    coin_vPiTerm]
  ring

/-- Action (1, π) and action 0 under the belief, on the coin episode. -/
example (πdot π : Bool → Unit) (ε : ℝ) :
    beliefValueTerm coinEndMDP {true} false πdot ε (constReward 1) (constReward 3) (some π) =
        ε * 6 + (1 - ε) * 2 ∧
      beliefValueTerm coinEndMDP {true} false πdot ε (constReward 1) (constReward 3) none =
        ε * 2 + (1 - ε) * 2 := by
  rw [AISafetyAtlas.Preference.Episodic.beliefValueTerm_some,
    AISafetyAtlas.Preference.Episodic.beliefValueTerm_none, coin_vPiTerm, coin_vPiTerm,
    coin_vPiTerm]
  constructor <;> ring

/-- The value of the override action on the augmented coin episode is the
forced policy's return up to termination on the coin episode. -/
example (πdot π : Bool → Unit) :
    augActionValueTerm coinEndMDP {true} false πdot (liftReward (constReward 3)) (some π) = 6 := by
  have hr : (fun s a => liftReward (constReward 3) (s, true) a) = constReward 3 := rfl
  rw [AISafetyAtlas.Preference.Episodic.augActionValueTerm, Option.getD_some, Option.isSome_some,
    AISafetyAtlas.Preference.Episodic.vPiTerm_augmentMDP, hr]
  simp only [mixPolicy, if_true]
  rw [coin_vPiTerm]
  norm_num

/-- Returns up to termination on the augmented coin episode are returns on the
coin episode, copy by copy, at every horizon and in the limit. -/
example (T : ℕ) (π : Bool × Bool → Unit) (b : Bool) :
    vPiStopped (augmentMDP coinEndMDP) (Prod.fst ⁻¹' {true}) (liftReward (constReward 1)) T π
        (false, b) = 2 * (1 - (1 / 2) ^ T) ∧
      vPiTerm (augmentMDP coinEndMDP) (Prod.fst ⁻¹' {true}) (liftReward (constReward 1)) π
        (false, b) = 2 := by
  have hr : (fun s a => liftReward (constReward 1) (s, b) a) = constReward 1 := rfl
  rw [AISafetyAtlas.Preference.Episodic.vPiStopped_augmentMDP,
    AISafetyAtlas.Preference.Episodic.vPiTerm_augmentMDP, hr]
  exact ⟨by simpa using coin_vPiStopped 1 _ T, by simpa using coin_vPiTerm 1 _⟩

/-- The stopped value is the episodic value of the stopped MDP at the masked
reward, and a terminal state is worth nothing. -/
example (T : ℕ) (π : Bool → Unit) :
    vPiEpisodic (stopMDP coinEndMDP {true}) (maskReward {true} (constReward 1)) T π false =
        2 * (1 - (1 / 2) ^ T) ∧
      vPiStopped coinEndMDP {true} (constReward 1) T π true = 0 := by
  rw [← AISafetyAtlas.Decision.vPiStopped_eq_vPiEpisodic]
  exact ⟨by simpa using coin_vPiStopped 1 π T,
    AISafetyAtlas.Decision.vPiStopped_of_mem _ _ _ _ (Set.mem_singleton true)⟩

/-- On the stopped coin MDP the terminal state earns nothing at any horizon, and
every stopped value starts at 0. -/
example (T : ℕ) (π : Bool → Unit) :
    vPiEpisodic (stopMDP coinEndMDP {true}) (maskReward {true} (constReward 1)) T π true = 0 ∧
      vPiStopped coinEndMDP {true} (constReward 1) 0 π false = 0 :=
  ⟨AISafetyAtlas.Decision.vPiEpisodic_stopMDP_of_mem _ _ _ _ (Set.mem_singleton true),
    AISafetyAtlas.Decision.vPiStopped_zero _ _ _ _ _⟩

/-- With nothing terminal the stopped value is the T-step value: on the chain,
T for always playing true. -/
example (T : ℕ) :
    vPiStopped chainMDP ∅ payForTrue T (fun _ => true) 0 = T := by
  rw [AISafetyAtlas.Decision.vPiStopped_empty,
    vPiEpisodic_const_reward chainMDP payForTrue (fun _ => true) 1 (fun _ => rfl) T]
  ring

/-- **The fixed horizon as random termination with a clock**, on the chain: the
clocked return up to time T is the T-step value, T for always playing
true, and the stopped values at horizon `n` are the min n T-step values. -/
example (T n : ℕ) :
    vPiTerm (clockMDP chainMDP) {x | T ≤ x.2} (fun x a => payForTrue x.1 a)
        (fun x => (fun _ => true : ℕ → Bool) x.1) (0, 0) = T ∧
      vPiStopped (clockMDP chainMDP) {x | T ≤ x.2} (fun x a => payForTrue x.1 a) n
        (fun x => (fun _ => true : ℕ → Bool) x.1) (0, 0) = min n T := by
  rw [AISafetyAtlas.Preference.Episodic.vPiTerm_clockMDP chainMDP payForTrue (fun _ => true) T 0,
    AISafetyAtlas.Preference.Episodic.vPiStopped_clockMDP chainMDP payForTrue (fun _ => true)
      T n 0 0,
    vPiEpisodic_const_reward chainMDP payForTrue (fun _ => true) 1 (fun _ => rfl),
    vPiEpisodic_const_reward chainMDP payForTrue (fun _ => true) 1 (fun _ => rfl)]
  simp

/-- **The clocked belief value is the fixed-horizon one**, at the override
action on the chain: ε T + (1 − ε) T. -/
example (T : ℕ) (πdot : ℕ → Bool) (ε : ℝ) :
    beliefValueTerm (clockMDP chainMDP) {x | T ≤ x.2} (0, 0) (fun x => πdot x.1) ε
        (fun x b => payForTrue x.1 b) (fun x b => payForTrue x.1 b)
        ((some fun _ => true : Option (ℕ → Bool)).map fun π x => π x.1) =
      ε * T + (1 - ε) * T := by
  rw [AISafetyAtlas.Preference.Episodic.beliefValueTerm_clockMDP,
    AISafetyAtlas.Preference.Episodic.beliefValueEp_some,
    vPiEpisodic_const_reward chainMDP payForTrue (fun _ => true) 1 (fun _ => rfl)]
  simp

/-- Action 0 at a fixed horizon, through `beliefValueEp_none`. -/
example (T : ℕ) (ε : ℝ) :
    beliefValueEp chainMDP T 0 (fun _ => true) ε payForTrue payForTrue none =
      ε * T + (1 - ε) * T := by
  rw [AISafetyAtlas.Preference.Episodic.beliefValueEp_none,
    vPiEpisodic_const_reward chainMDP payForTrue (fun _ => true) 1 (fun _ => rfl)]
  simp

end AISafetyAtlas.Examples.Preference.Episodic
