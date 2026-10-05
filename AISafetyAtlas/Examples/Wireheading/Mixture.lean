module

public import AISafetyAtlas.Wireheading.Mixture
public import AISafetyAtlas.Wireheading.DelusionBox

/-!
# Two environments, one bit, and the value of telling them apart

`AISafetyAtlas.Wireheading.Mixture` replaces the fixed-weight decomposition Ring
and Orseau's *Arguments* assume with a posterior one. This file inhabits it.

Two environments over one bit of observation: one echoes the action, the other
negates it. A policy committed to `true` is worth exactly the posterior average
of its value under each — `policyValue_mixture`, an equality — while the
optimal value is only at most that average, and strictly below it here, which is
the gap `Examples…not_mixesAt_one` exhibits on the other side.
-/

namespace AISafetyAtlas.Examples.Wireheading.Mixture

open AISafetyAtlas.Wireheading.AgentEquations
open AISafetyAtlas.Wireheading.Mixture
open AISafetyAtlas.Wireheading.DelusionBox

/-- An environment whose observation echoes the action. -/
@[expose] public def echoB : Belief Bool Bool where
  cond := fun _ a o => if o = a then 1 else 0

/-- An environment whose observation negates the action. -/
@[expose] public def flipB : Belief Bool Bool where
  cond := fun _ a o => if o = !a then 1 else 0

/-- Paid one exactly when the last observation is `true`. -/
@[expose] public def bitAgent : Agent Bool Bool where
  utility := fun h =>
    match h.getLast? with
    | none => 0
    | some q => if q.2 then 1 else 0
  horizon := fun _ _ => 1

/-- A policy committed to one action, whatever it has seen. -/
@[expose] public def alwaysTrue : History Bool Bool → Bool := fun _ => true

/-- The echoing environment is a probability. -/
public theorem echoB_isSubprobability : echoB.IsSubprobability where
  nonneg := by intro h a o; by_cases hoa : o = a <;> simp [echoB, hoa]
  summable := by intro _ _; exact Summable.of_finite
  total_le_one := by
    intro h a
    rw [tsum_fintype, Fintype.sum_bool]
    cases a <;> norm_num [echoB]

/-- So is the negating one. -/
public theorem flipB_isSubprobability : flipB.IsSubprobability where
  nonneg := by intro h a o; by_cases hoa : o = !a <;> simp [flipB, hoa]
  summable := by intro _ _; exact Summable.of_finite
  total_le_one := by
    intro h a
    rw [tsum_fintype, Fintype.sum_bool]
    cases a <;> norm_num [flipB]

/-- The agent's utility is bounded by one. -/
public theorem bitAgent_abs_utility_le_one (h : History Bool Bool) :
    |bitAgent.utility h| ≤ 1 := by
  simp only [bitAgent]
  split
  · norm_num
  · split_ifs <;> norm_num

/-- **History mass factors**, which is what makes the posterior update. -/
public theorem historyMass_append_echoB (h : History Bool Bool) (a o : Bool) :
    historyMass echoB (h ++ [(a, o)]) = historyMass echoB h * echoB.cond h a o :=
  historyMass_append_singleton echoB h a o

/-- And it is nonnegative. -/
public theorem historyMass_echoB_nonneg (h : History Bool Bool) :
    0 ≤ historyMass echoB h :=
  historyMass_nonneg echoB_isSubprobability.nonneg h

/-- The posterior is a weight. -/
public theorem posterior_mem_unit (h : History Bool Bool) :
    0 ≤ posterior (1 / 2) echoB flipB h ∧ posterior (1 / 2) echoB flipB h ≤ 1 :=
  ⟨posterior_nonneg (by norm_num) (by norm_num) echoB_isSubprobability.nonneg
      flipB_isSubprobability.nonneg h,
    posterior_le_one (by norm_num) (by norm_num) echoB_isSubprobability.nonneg
      flipB_isSubprobability.nonneg h⟩

/-- The mixture's conditional is what it is defined to be. -/
public theorem mixtureBelief_cond_at (h : History Bool Bool) (a o : Bool) :
    (mixtureBelief (1 / 2) echoB flipB).cond h a o
      = posterior (1 / 2) echoB flipB h * echoB.cond h a o
        + (1 - posterior (1 / 2) echoB flipB h) * flipB.cond h a o :=
  mixtureBelief_cond (1 / 2) echoB flipB h a o

/-- And it is nonnegative. -/
public theorem mixtureBelief_cond_nonneg_at (h : History Bool Bool) (a o : Bool) :
    0 ≤ (mixtureBelief (1 / 2) echoB flipB).cond h a o :=
  mixtureBelief_cond_nonneg (by norm_num) (by norm_num) echoB_isSubprobability.nonneg
    flipB_isSubprobability.nonneg h a o

/-- **Bayes' rule at this model**, both halves. -/
public theorem bayes_at (h : History Bool Bool) (a o : Bool) :
    (mixtureBelief (1 / 2) echoB flipB).cond h a o
        * posterior (1 / 2) echoB flipB (h ++ [(a, o)])
      = posterior (1 / 2) echoB flipB h * echoB.cond h a o :=
  mixtureBelief_cond_mul_posterior (by norm_num) (by norm_num)
    echoB_isSubprobability.nonneg flipB_isSubprobability.nonneg h a o

/-- The complementary half. -/
public theorem bayes_at_complement (h : History Bool Bool) (a o : Bool) :
    (mixtureBelief (1 / 2) echoB flipB).cond h a o
        * (1 - posterior (1 / 2) echoB flipB (h ++ [(a, o)]))
      = (1 - posterior (1 / 2) echoB flipB h) * flipB.cond h a o :=
  mixtureBelief_cond_mul_one_sub_posterior (by norm_num) (by norm_num)
    echoB_isSubprobability.nonneg flipB_isSubprobability.nonneg h a o

/-- Depth zero discards the tail. -/
public theorem policyValue_zero_at (t : ℕ) (h : History Bool Bool) :
    policyValue echoB bitAgent alwaysTrue t 0 h
      = bitAgent.horizon t h.length * bitAgent.utility h :=
  policyValue_zero echoB bitAgent alwaysTrue t h

/-- **The committed policy's value is exactly the posterior average.** -/
public theorem policyValue_mixture_at (t n : ℕ) (h : History Bool Bool) :
    policyValue (mixtureBelief (1 / 2) echoB flipB) bitAgent alwaysTrue t n h
      = posterior (1 / 2) echoB flipB h * policyValue echoB bitAgent alwaysTrue t n h
        + (1 - posterior (1 / 2) echoB flipB h)
          * policyValue flipB bitAgent alwaysTrue t n h :=
  policyValue_mixture (by norm_num) (by norm_num) echoB_isSubprobability.nonneg
    flipB_isSubprobability.nonneg bitAgent alwaysTrue t n h

/-- A committed policy never beats the optimum. -/
public theorem policyValue_le_value_at (t n : ℕ) (h : History Bool Bool) :
    policyValue echoB bitAgent alwaysTrue t n h ≤ value echoB bitAgent t n h :=
  policyValue_le_value echoB_isSubprobability bitAgent bitAgent_abs_utility_le_one
    alwaysTrue t n h

/-- **And the optimal value is at most the posterior average**, the direction
print's decomposition actually has. -/
public theorem value_mixture_le_at (t n : ℕ) (h : History Bool Bool) :
    value (mixtureBelief (1 / 2) echoB flipB) bitAgent t n h
      ≤ posterior (1 / 2) echoB flipB h * value echoB bitAgent t n h
        + (1 - posterior (1 / 2) echoB flipB h) * value flipB bitAgent t n h :=
  value_mixture_le (by norm_num) (by norm_num) echoB_isSubprobability
    flipB_isSubprobability bitAgent bitAgent_abs_utility_le_one t n h

/-!
## Print's decomposition fails above depth zero

`DelusionBox.mixesAt_zero` proves print's fixed-weight decomposition at remaining
depth zero, where the value does not depend on the belief at all. At depth
**one** the maximum in equation (3) has entered the recursion, and a maximum does
not commute with a convex combination.
-/

/-- The fixed-weight half mixture of the two, which is the uniform belief and is
exactly what `DelusionBox.mixesAt_zero` asks for. -/
@[expose] public noncomputable def halfBelief : Belief Bool Bool where
  cond := fun _ _ _ => 1 / 2

/-- It really is that fixed-weight mixture. -/
public theorem halfBelief_isMixture (h : History Bool Bool) (a o : Bool) :
    halfBelief.cond h a o
      = (1 / 2) * echoB.cond h a o + (1 - 1 / 2) * flipB.cond h a o := by
  cases a <;> cases o <;> norm_num [halfBelief, echoB, flipB]

/-- So the decomposition holds at depth zero. -/
public theorem mixesAt_zero_halfBelief (t : ℕ) (h : History Bool Bool) :
    MixesAt halfBelief echoB flipB bitAgent (1 / 2) t 0 h :=
  mixesAt_zero halfBelief echoB flipB bitAgent (1 / 2) t h halfBelief_isMixture

private theorem ciSup_bool (f : Bool → ℝ) : (⨆ b : Bool, f b) = max (f true) (f false) := by
  have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  refine le_antisymm (ciSup_le fun b => by cases b <;> simp) ?_
  exact max_le (le_ciSup hb true) (le_ciSup hb false)

/-- The last observation is what the utility reads. -/
private theorem utility_concat (h : History Bool Bool) (a o : Bool) :
    bitAgent.utility (h ++ [(a, o)]) = if o then 1 else 0 := by
  simp [bitAgent]

/-- At depth zero an action is worth the weight the belief puts on `true`. -/
public theorem actionValue_zero_eq (ρ : Belief Bool Bool) (t : ℕ)
    (h : History Bool Bool) (a : Bool) :
    actionValue ρ bitAgent t 0 h a = ρ.cond h a true := by
  rw [actionValue_eq_sum]
  simp [value, bitAgent]

/-- The echoing environment is worth one: it can make the observation `true`. -/
public theorem value_one_echo (t : ℕ) (h : History Bool Bool) :
    value echoB bitAgent t 1 h = bitAgent.utility h + 1 := by
  rw [value_succ, ciSup_bool]
  simp only [actionValue_zero_eq]
  norm_num [echoB, bitAgent]

/-- So is the negating one, by the opposite action. -/
public theorem value_one_flip (t : ℕ) (h : History Bool Bool) :
    value flipB bitAgent t 1 h = bitAgent.utility h + 1 := by
  rw [value_succ, ciSup_bool]
  simp only [actionValue_zero_eq]
  norm_num [flipB, bitAgent]

/-- The mixture is worth only a half: it cannot tell the two apart, so neither
action does better than a coin flip. -/
public theorem value_one_half (t : ℕ) (h : History Bool Bool) :
    value halfBelief bitAgent t 1 h = bitAgent.utility h + 1 / 2 := by
  rw [value_succ, ciSup_bool]
  simp only [actionValue_zero_eq]
  norm_num [halfBelief, bitAgent]

/--
**Print's decomposition is false above depth zero.**

At remaining depth one the two informed action values at `true` are `2` and `1`,
so print's average is `3/2`; the mixture's own action value is `1`. The gap is
the value of knowing which environment one is in, which the maximum inside
equation (3) collects and a fixed-weight average does not.
-/
public theorem not_mixesAt_one (t : ℕ) (h : History Bool Bool) :
    ¬ MixesAt halfBelief echoB flipB bitAgent (1 / 2) t 1 h := by
  intro hmix
  have hb := hmix true
  rw [actionValue_eq_sum, actionValue_eq_sum, actionValue_eq_sum] at hb
  simp only [Fintype.sum_bool, value_one_echo, value_one_flip, value_one_half,
    utility_concat] at hb
  norm_num [echoB, flipB, halfBelief] at hb

/-!
## Statement 1 without the decomposition

At the empty history both masses are one, so the posterior is the prior and
print's threshold is a condition on `p` itself. Everything else is print's own
arithmetic, and all of it holds here.
-/

/-- The committed policy is worth exactly one against the echoing environment,
which is print's "maximum attained in the box branch". -/
public theorem policyActionValue_echo_one (t : ℕ) :
    policyActionValue echoB bitAgent alwaysTrue t 0 [] = 1 := by
  rw [policyActionValue, tsum_fintype, Fintype.sum_bool]
  norm_num [echoB, alwaysTrue, policyValue, bitAgent]

/-- And nothing against the negating one, which is print's "at least zero". -/
public theorem policyActionValue_flip_zero (t : ℕ) :
    policyActionValue flipB bitAgent alwaysTrue t 0 [] = 0 := by
  rw [policyActionValue, tsum_fintype, Fintype.sum_bool]
  norm_num [flipB, alwaysTrue, policyValue, bitAgent]

/-- Refusing pays nothing in the box branch, print's `≤ r̄` at `r̄ = 0`. -/
public theorem actionValue_echo_false_zero (t : ℕ) :
    actionValue echoB bitAgent t 0 [] false = 0 := by
  rw [actionValue_zero_eq]; norm_num [echoB]

/-- And at most the maximum outside it. -/
public theorem actionValue_flip_false_le_one (t : ℕ) :
    actionValue flipB bitAgent t 0 [] false ≤ 1 := by
  rw [actionValue_zero_eq]; norm_num [flipB]

/-- At the empty history the posterior is the prior. -/
public theorem posterior_nil_echo (q : ℝ) : posterior q echoB flipB [] = q :=
  posterior_nil q echoB flipB

/--
**Statement 1's repaired antecedent is inhabited.** At prior `3/4`, `r̄ = 0` and
the policy committed to `true`, every hypothesis of
`DelusionBox.statement_one_of_posterior` holds, so the conclusion is print's
about a real pair of environments and not a vacuous implication.
-/
public theorem rl_uses_the_box_of_posterior (t : ℕ) :
    actionValue (mixtureBelief (3 / 4) echoB flipB) bitAgent t 0 [] false
      < actionValue (mixtureBelief (3 / 4) echoB flipB) bitAgent t 0 []
          (alwaysTrue []) := by
  have hpost : posterior (3 / 4 : ℝ) echoB flipB [] = 3 / 4 := posterior_nil_echo _
  refine statement_one_of_posterior echoB flipB (by norm_num) (by norm_num)
    echoB_isSubprobability flipB_isSubprobability bitAgent bitAgent_abs_utility_le_one
    t 0 [] alwaysTrue false 0 ?_ ?_ ?_ ?_ (by norm_num) ?_
  · rw [policyActionValue_echo_one]
  · rw [policyActionValue_flip_zero]
  · rw [actionValue_echo_false_zero]
  · exact actionValue_flip_false_le_one t
  · rw [hpost]; norm_num

/-!
## Statements 2 and 3, inhabited

Statement 3 is Statement 1 at `r̄ = 0` and runs on the same pair. Statement 2 is
not: print's second shape bounds the refusing action by `2^{-lᵃ}` in **both**
branches, and against the negating environment refusing is worth the maximum
here. So that one needs an environment in which refusing pays nothing either
way, which is what `constFalse` is.
-/

/-- An environment whose observation is `false` whatever the action, so nothing
the agent does pays. -/
@[expose] public def constFalse : Belief Bool Bool where
  cond := fun _ _ o => if o then 0 else 1

/-- It is a probability. -/
public theorem constFalse_isSubprobability : constFalse.IsSubprobability where
  nonneg := by intro h a o; cases o <;> norm_num [constFalse]
  summable := by intro _ _; exact Summable.of_finite
  total_le_one := by
    intro h a
    rw [tsum_fintype, Fintype.sum_bool]
    norm_num [constFalse]

/-- The committed policy is worth nothing against it. -/
public theorem policyActionValue_constFalse_zero (t : ℕ) :
    policyActionValue constFalse bitAgent alwaysTrue t 0 [] = 0 := by
  rw [policyActionValue, tsum_fintype, Fintype.sum_bool]
  norm_num [constFalse, alwaysTrue, policyValue, bitAgent]

/-- And so is refusing. -/
public theorem actionValue_constFalse_false_zero (t : ℕ) :
    actionValue constFalse bitAgent t 0 [] false = 0 := by
  rw [actionValue_zero_eq]; norm_num [constFalse]

/--
**Statement 2's repaired antecedent is inhabited**, at print's `\|o⁺\| = 1`,
`lᵃ = 2` and prior `3/4` — print's "easily satisfiable once `\|o⁺\| < lᵃ`".
-/
public theorem goal_uses_the_box_of_posterior (t : ℕ) :
    actionValue (mixtureBelief (3 / 4) echoB constFalse) bitAgent t 0 [] false
      < actionValue (mixtureBelief (3 / 4) echoB constFalse) bitAgent t 0 []
          (alwaysTrue []) := by
  refine statement_two_of_posterior echoB constFalse (by norm_num) (by norm_num)
    echoB_isSubprobability constFalse_isSubprobability bitAgent
    bitAgent_abs_utility_le_one t 0 [] alwaysTrue false 1 2 ?_ ?_ ?_ ?_ ?_
  · rw [policyActionValue_echo_one]; norm_num
  · rw [policyActionValue_constFalse_zero]
  · rw [actionValue_echo_false_zero]; norm_num
  · rw [actionValue_constFalse_false_zero]; norm_num
  · rw [posterior_nil]; norm_num

/-- **Statement 3's repaired antecedent is inhabited**, on the same pair as
Statement 1 and at the same prior. -/
public theorem pred_uses_the_box_of_posterior (t : ℕ) :
    actionValue (mixtureBelief (3 / 4) echoB flipB) bitAgent t 0 [] false
      < actionValue (mixtureBelief (3 / 4) echoB flipB) bitAgent t 0 []
          (alwaysTrue []) := by
  refine statement_three_of_posterior echoB flipB (by norm_num) (by norm_num)
    echoB_isSubprobability flipB_isSubprobability bitAgent
    bitAgent_abs_utility_le_one t 0 [] alwaysTrue false ?_ ?_ ?_ ?_ ?_
  · rw [policyActionValue_echo_one]
  · rw [policyActionValue_flip_zero]
  · rw [actionValue_echo_false_zero]
  · exact actionValue_flip_false_le_one t
  · rw [posterior_nil_echo]; norm_num

end AISafetyAtlas.Examples.Wireheading.Mixture
