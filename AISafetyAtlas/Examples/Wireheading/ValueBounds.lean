module

public import AISafetyAtlas.Wireheading.ValueBounds
public import AISafetyAtlas.Wireheading.DelusionBox

/-! A one-program model witnesses the probability and value-bound hypotheses. -/

namespace AISafetyAtlas.Examples.Wireheading.ValueBounds

open AISafetyAtlas.Wireheading AgentEquations

/-- A deterministic unit observation has probability one. -/
public theorem unitBelief_subprobability :
    (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ())).IsSubprobability where
  nonneg := by intros; simp [DelusionBox.diracBelief]
  summable := by intros; exact Summable.of_finite
  total_le_one := by intros; simp [DelusionBox.diracBelief]

/-- The source's bounded-reward case inhabits the summability result. -/
public theorem unit_actionValue_summable (t n : ℕ) :
    Summable (fun o ↦
      (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ())).cond [] () o *
        value (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
          (DelusionBox.rlAgent (fun (_ : Unit) ↦ 1) 1) t n [((), o)]) :=
  actionValue_summable unitBelief_subprobability _ (by
    intro h
    simp only [DelusionBox.rlAgent, DelusionBox.lastReward]
    split <;> norm_num) t n [] ()

/-- The window horizon has finite support, so its absolute value is summable --
`rlAgent`'s horizon weight is `1` inside a window of `m` steps and `0` beyond
it. -/
public theorem unit_horizon_summable (t : ℕ) :
    Summable (fun k ↦ |(DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).horizon t k|) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_Icc 0 (t + 1))
  intro k hk
  simp only [Function.mem_support, ne_eq, abs_eq_zero] at hk
  by_contra hcon
  simp only [Set.mem_Icc, not_and, not_le] at hcon
  apply hk
  show (DelusionBox.windowHorizon 1 t k : ℝ) = 0
  rw [DelusionBox.windowHorizon, if_neg (by omega)]

/-- The reward is bounded by one in absolute value: it is either `0` (empty
history) or exactly `1`. -/
public theorem unit_utility_bounded (h : History Unit Unit) :
    |(DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).utility h| ≤ 1 := by
  show |DelusionBox.lastReward (fun (_ : Unit) ↦ (1:ℝ)) h| ≤ 1
  unfold DelusionBox.lastReward
  split <;> norm_num

/-- **Definition 9's infinite-horizon value equation, at the witness.** The
source's own bounded-reward, summable-horizon case. -/
public theorem unit_infiniteValue_eq (t : ℕ) (h : History Unit Unit) :
    infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h
      = (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).horizon t h.length *
          (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).utility h +
        ⨆ a, infiniteActionValue
          (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
          (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h a :=
  infiniteValue_eq unitBelief_subprobability (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1)
    unit_utility_bounded t (unit_horizon_summable t) h

/-- **The truncation error is bounded by the horizon's tail, at the witness.** -/
public theorem unit_value_error_le_tail (n : ℕ) (h : History Unit Unit) :
    |value (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) 0 n h -
      infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) 0 h| ≤
      ∑' i : ℕ, |(DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).horizon 0 (h.length + (n + i) + 1)| :=
  value_error_le_tail unitBelief_subprobability (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1)
    unit_utility_bounded 0 (unit_horizon_summable 0) n h

/-! ## Equation (1) at the infinite-horizon value -/

/-- **Print's recursion (3) with its max attained at the infinite-horizon argmax**,
at the bounded-reward, summable-horizon witness. -/
public theorem unit_infiniteValue_eq_infiniteBestAction (t : ℕ) (h : History Unit Unit) :
    infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h
      = (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).horizon t h.length *
          (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1).utility h +
        infiniteActionValue
          (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
          (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h
          (infiniteBestAction
            (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
            (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h
            (infAttains_of_fintype _ _ t h)) :=
  infiniteValue_eq_infiniteBestAction unitBelief_subprobability
    (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1)
    unit_utility_bounded t (unit_horizon_summable t) h (infAttains_of_fintype _ _ t h)

/-- A belief over two actions with a deterministic unit observation. -/
@[expose] public def boolBelief : Belief Bool Unit :=
  DelusionBox.diracBelief (fun _ _ ↦ ())

/-- An agent with zero horizon: every action ties, at every depth and in the limit. -/
@[expose] public def zeroAgent : Agent Bool Unit where
  utility := fun _ ↦ 0
  horizon := fun _ _ ↦ 0

/-- The infinite-horizon value of the zero-horizon agent is zero. -/
public theorem zeroAgent_infiniteValue (t : ℕ) (h : History Bool Unit) :
    infiniteValue boolBelief zeroAgent t h = 0 := by
  have hz : (fun n ↦ value boolBelief zeroAgent t n h) = fun _ ↦ 0 := funext fun n ↦
    value_eq_zero_of_horizon_vanishes boolBelief zeroAgent t 0 (fun _ _ ↦ rfl) n h (Nat.zero_le _)
  rw [infiniteValue, hz]
  exact tendsto_const_nhds.limUnder_eq

/-- Hence every infinite action value is zero. -/
public theorem zeroAgent_infiniteActionValue (t : ℕ) (h : History Bool Unit) (a : Bool) :
    infiniteActionValue boolBelief zeroAgent t h a = 0 := by
  simp [infiniteActionValue, zeroAgent_infiniteValue]

/-- **Footnote 4's tie rule at the infinite-horizon value**: both actions tie and
the lexicographic choice is `false`. -/
public theorem zeroAgent_infiniteLexBestAction (t : ℕ) (h : History Bool Unit) :
    infiniteLexBestAction boolBelief zeroAgent t h (infAttains_of_fintype _ _ t h) = false := by
  have hle := infiniteLexBestAction_le boolBelief zeroAgent t h (infAttains_of_fintype _ _ t h)
    (a := false) (fun b => by rw [zeroAgent_infiniteActionValue, zeroAgent_infiniteActionValue])
  exact le_bot_iff.mp hle

/-- The lexicographic infinite-horizon best action is maximal, at the witness. -/
public theorem zeroAgent_infiniteLexBestAction_max (t : ℕ) (h : History Bool Unit) (a : Bool) :
    infiniteActionValue boolBelief zeroAgent t h a ≤
      infiniteActionValue boolBelief zeroAgent t h
        (infiniteLexBestAction boolBelief zeroAgent t h (infAttains_of_fintype _ _ t h)) :=
  infiniteLexBestAction_max boolBelief zeroAgent t h (infAttains_of_fintype _ _ t h) a

/-- The infinite-horizon best action is maximal, at the witness. -/
public theorem zeroAgent_infiniteBestAction_max (t : ℕ) (h : History Bool Unit) (a : Bool) :
    infiniteActionValue boolBelief zeroAgent t h a ≤
      infiniteActionValue boolBelief zeroAgent t h
        (infiniteBestAction boolBelief zeroAgent t h (infAttains_of_fintype _ _ t h)) :=
  infiniteBestAction_max boolBelief zeroAgent t h (infAttains_of_fintype _ _ t h) a

/-- The non-learning variant's infinite action value collapses to one history. -/
public theorem zeroAgent_infiniteActionValue_diracBelief (t : ℕ) (h : History Bool Unit)
    (a : Bool) :
    infiniteActionValue boolBelief zeroAgent t h a =
      infiniteValue boolBelief zeroAgent t (h ++ [(a, ())]) :=
  DelusionBox.infiniteActionValue_diracBelief _ zeroAgent t h a


/-- **Equation (2) at depth `n` converges to the infinite-horizon action value**,
at the source's bounded-reward, summable-horizon witness. -/
public theorem unit_tendsto_actionValue (t : ℕ) (h : History Unit Unit) :
    Filter.Tendsto (fun n ↦ actionValue
        (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t n h ())
      Filter.atTop (nhds (infiniteActionValue
        (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) t h ())) :=
  tendsto_actionValue_infiniteActionValue unitBelief_subprobability _ unit_utility_bounded t
    (unit_horizon_summable t) h ()

/-- A point mass on `false` gives `true` no weight. -/
public theorem point_false_cond_true :
    (DelusionBox.diracBelief (fun (_ : History Unit Bool) (_ : Unit) ↦ false)).cond [] () true = 0 :=
  (DelusionBox.diracBelief_isSubprobability _).cond_eq_zero_of_eq_one
    (k := false) (by simp [DelusionBox.diracBelief]) (by decide)

/-! ## A dominated tail where the horizon is not summable

Print's Setting puts no summability condition on `w`. At `u ≡ 0` and the
constant-one horizon, print's expected sum is `0` at every history, but
`Summable |w t ·|` fails, so only the dominated-tail forms (here at `b ≡ 0`)
reach it. A utility decaying geometrically against the same horizon is reached at
`b k = (1/2)^k`. -/

/-- Zero utility under the constant-one horizon. -/
@[expose] public def flatAgent (Action : Type*) : Agent Action Unit where
  utility := fun _ ↦ 0
  horizon := fun _ _ ↦ 1

/-- Its horizon is not absolutely summable, so the `b ≡ 1` forms do not apply. -/
public theorem flatAgent_not_summable (Action : Type*) (t : ℕ) :
    ¬ Summable (fun k ↦ |(flatAgent Action).horizon t k|) := by
  simp [flatAgent, summable_const_iff]

/-- **Print's recursion (3) at the non-summable instance** (row 010's instance):
`u ≡ 0`, `w ≡ 1`, one action, one observation, `b ≡ 0`. -/
public theorem flatAgent_infiniteValue_eq (t : ℕ) (h : History Unit Unit) :
    infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        (flatAgent Unit) t h
      = (flatAgent Unit).horizon t h.length * (flatAgent Unit).utility h +
        ⨆ a, infiniteActionValue
          (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
          (flatAgent Unit) t h a :=
  infiniteValue_eq_of_dominated unitBelief_subprobability (flatAgent Unit) (b := fun _ ↦ 0)
    (fun _ ↦ by simp [flatAgent]) t (by simp) h

/-- **Print's recursion (3) with its max attained at equation (1)'s argmax, at the
non-summable instance** (row 028's instance): `u ≡ 0`, `w ≡ 1`, two actions. -/
public theorem flatAgent_infiniteValue_eq_infiniteBestAction (t : ℕ) (h : History Bool Unit) :
    infiniteValue boolBelief (flatAgent Bool) t h
      = (flatAgent Bool).horizon t h.length * (flatAgent Bool).utility h +
        infiniteActionValue boolBelief (flatAgent Bool) t h
          (infiniteBestAction boolBelief (flatAgent Bool) t h (infAttains_of_fintype _ _ t h)) :=
  infiniteValue_eq_infiniteBestAction_of_dominated (DelusionBox.diracBelief_isSubprobability _)
    (flatAgent Bool) (b := fun _ ↦ 0) (fun _ ↦ by simp [flatAgent]) t (by simp) h
    (infAttains_of_fintype _ _ t h)

/-- The finite values converge at the same instance. -/
public theorem flatAgent_tendsto_actionValue (t : ℕ) (h : History Bool Unit) (a : Bool) :
    Filter.Tendsto (fun n ↦ actionValue boolBelief (flatAgent Bool) t n h a) Filter.atTop
      (nhds (infiniteActionValue boolBelief (flatAgent Bool) t h a)) :=
  tendsto_actionValue_infiniteActionValue_of_dominated
    (DelusionBox.diracBelief_isSubprobability _) (flatAgent Bool) (b := fun _ ↦ 0)
    (fun _ ↦ by simp [flatAgent]) t (by simp) h a

/-- A utility decaying geometrically in the history length, under the constant-one
horizon. -/
@[expose] public noncomputable def halfAgent : Agent Unit Unit where
  utility := fun h ↦ (1 / 2 : ℝ) ^ h.length
  horizon := fun _ _ ↦ 1

private theorem halfAgent_hub (h : History Unit Unit) :
    |halfAgent.utility h| ≤ (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) h.length := by
  simp [halfAgent]

private theorem halfAgent_hw (t : ℕ) :
    Summable (fun k ↦ |halfAgent.horizon t k| * (1 / 2 : ℝ) ^ k) := by
  simpa [halfAgent] using summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)

/-- **Print's recursion (3) at a decaying utility and a non-summable horizon.** -/
public theorem halfAgent_infiniteValue_eq (t : ℕ) (h : History Unit Unit) :
    infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        halfAgent t h
      = halfAgent.horizon t h.length * halfAgent.utility h +
        ⨆ a, infiniteActionValue
          (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
          halfAgent t h a :=
  infiniteValue_eq_of_dominated unitBelief_subprobability halfAgent halfAgent_hub t
    (halfAgent_hw t) h

/-- The certified truncation error at the decaying utility. -/
public theorem halfAgent_value_error_le_tail (t n : ℕ) (h : History Unit Unit) :
    |value (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        halfAgent t n h -
      infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        halfAgent t h| ≤
      ∑' i : ℕ, |halfAgent.horizon t (h.length + (n + i) + 1)| *
        (1 / 2 : ℝ) ^ (h.length + (n + i) + 1) :=
  value_error_le_tail_of_dominated unitBelief_subprobability halfAgent
    (b := fun k ↦ (1 / 2 : ℝ) ^ k) (fun _ ↦ by positivity) halfAgent_hub t (halfAgent_hw t) n h

/-- The infinite value is bounded by the dominated tail at the decaying utility. -/
public theorem halfAgent_abs_infiniteValue_le (t : ℕ) (h : History Unit Unit) :
    |infiniteValue (DelusionBox.diracBelief (fun (_ : History Unit Unit) (_ : Unit) ↦ ()))
        halfAgent t h| ≤
      ∑' i : ℕ, |halfAgent.horizon t (h.length + i)| * (1 / 2 : ℝ) ^ (h.length + i) :=
  abs_infiniteValue_le_of_dominated unitBelief_subprobability halfAgent
    (b := fun k ↦ (1 / 2 : ℝ) ^ k) (fun _ ↦ by positivity) halfAgent_hub t (halfAgent_hw t) h

/-- The horizon of the decaying-utility agent is not absolutely summable. -/
public theorem halfAgent_not_summable (t : ℕ) :
    ¬ Summable (fun k ↦ |halfAgent.horizon t k|) := by
  simp [halfAgent, summable_const_iff]

/-! ## Print's tie rule at the infinite-horizon value without a well-founded order -/

/-- A belief over the actions `WithBot ℤ` (not well-founded,
`Examples.Wireheading.AgentEquations.withBotInt_not_wellFoundedLT`). -/
@[expose] public def withBotBelief : Belief (WithBot ℤ) Unit :=
  DelusionBox.diracBelief (fun _ _ ↦ ())

/-- Zero utility and zero horizon over the actions `WithBot ℤ`. -/
@[expose] public def zeroAgentZ : Agent (WithBot ℤ) Unit where
  utility := fun _ ↦ 0
  horizon := fun _ _ ↦ 0

/-- Every infinite action value is zero, so every action ties. -/
public theorem zeroAgentZ_infiniteActionValue (t : ℕ) (h : History (WithBot ℤ) Unit)
    (a : WithBot ℤ) : infiniteActionValue withBotBelief zeroAgentZ t h a = 0 := by
  have hv (h' : History (WithBot ℤ) Unit) : infiniteValue withBotBelief zeroAgentZ t h' = 0 := by
    have hz : (fun n ↦ value withBotBelief zeroAgentZ t n h') = fun _ ↦ 0 := funext fun n ↦
      value_eq_zero_of_horizon_vanishes withBotBelief zeroAgentZ t 0 (fun _ _ ↦ rfl) n h'
        (Nat.zero_le _)
    rw [infiniteValue, hz]
    exact tendsto_const_nhds.limUnder_eq
  simp [infiniteActionValue, hv]

/-- The tie set has the least element `⊥`: print's rule denotes. -/
public theorem zeroAgentZ_infLexAttains (t : ℕ) (h : History (WithBot ℤ) Unit) :
    InfLexAttains withBotBelief zeroAgentZ t h :=
  ⟨⊥, fun b ↦ by simp [zeroAgentZ_infiniteActionValue], fun _ _ ↦ bot_le⟩

/-- **Print's lexicographic choice on a non-well-founded action set** is `⊥`. -/
public theorem zeroAgentZ_infiniteLexBestActionOfLeast (t : ℕ) (h : History (WithBot ℤ) Unit) :
    infiniteLexBestActionOfLeast withBotBelief zeroAgentZ t h (zeroAgentZ_infLexAttains t h) =
      ⊥ :=
  le_bot_iff.mp (infiniteLexBestActionOfLeast_le _ _ _ _ _ (a := ⊥)
    (fun b ↦ by simp [zeroAgentZ_infiniteActionValue]))

/-- It is a maximiser there. -/
public theorem zeroAgentZ_infiniteLexBestActionOfLeast_max (t : ℕ)
    (h : History (WithBot ℤ) Unit) (a : WithBot ℤ) :
    infiniteActionValue withBotBelief zeroAgentZ t h a ≤
      infiniteActionValue withBotBelief zeroAgentZ t h
        (infiniteLexBestActionOfLeast withBotBelief zeroAgentZ t h
          (zeroAgentZ_infLexAttains t h)) :=
  infiniteLexBestActionOfLeast_max _ _ _ _ _ a

/-- On a finite action set the two lexicographic choices agree. -/
public theorem zeroAgent_infiniteLexBestActionOfLeast_eq (t : ℕ) (h : History Bool Unit) :
    infiniteLexBestActionOfLeast boolBelief zeroAgent t h
        (infLexAttains_of_infAttains (infAttains_of_fintype _ _ t h)) =
      infiniteLexBestAction boolBelief zeroAgent t h (infAttains_of_fintype _ _ t h) :=
  infiniteLexBestActionOfLeast_eq _ _ _ _ _ _

/-- A least maximiser is a maximiser, at the `WithBot ℤ` witness. -/
public theorem zeroAgentZ_infAttains (t : ℕ) (h : History (WithBot ℤ) Unit) :
    InfAttains withBotBelief zeroAgentZ t h :=
  (zeroAgentZ_infLexAttains t h).infAttains

/-! The summable-horizon forms, now corollaries of the dominated-tail family, at the
window agent. -/
example (t : ℕ) (h : History Unit Unit) :=
  AISafetyAtlas.Wireheading.AgentEquations.abs_infiniteValue_le unitBelief_subprobability _ unit_utility_bounded t
    (unit_horizon_summable t) h
example (t n : ℕ) (h : History Unit Unit) :=
  AISafetyAtlas.Wireheading.AgentEquations.abs_value_succ_sub_le unitBelief_subprobability
    (DelusionBox.rlAgent (Action := Unit) (fun (_ : Unit) ↦ (1:ℝ)) 1) unit_utility_bounded t n h
example (t : ℕ) (h : History Unit Unit) :=
  AISafetyAtlas.Wireheading.AgentEquations.infiniteActionValue_bddAbove unitBelief_subprobability _ unit_utility_bounded t
    (unit_horizon_summable t) h
example (t : ℕ) (h : History Unit Unit) :=
  AISafetyAtlas.Wireheading.AgentEquations.tendsto_value_infiniteValue unitBelief_subprobability _ unit_utility_bounded t
    (unit_horizon_summable t) h

end AISafetyAtlas.Examples.Wireheading.ValueBounds
