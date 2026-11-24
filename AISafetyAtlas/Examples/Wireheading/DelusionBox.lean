module

public import AISafetyAtlas.Wireheading.DelusionBox

/-!
# A delusion box the agent actually programs

`AISafetyAtlas.Wireheading.DelusionBox` states Ring and Orseau's Statements 1
to 3 with the premises their *Arguments* paragraphs use supplied as named
hypotheses. An implication whose antecedent nothing inhabits is worth nothing, so
this file inhabits all three antecedents at once, in a model small enough to
evaluate.

## The model

One bit of observation, read as a reward, as a goal, or as a thing to predict.
One inner action. Two programs: `false`, which is the identity the box starts
with, and `true`, which rewrites every observation to `true`. An action is
therefore a pair `(program, ())`, and `yes` is the one that programs the box.

Three global environments, differing only in the inner environment or in whether
the box works at all:

* `boxed` — a delusion box is present, and the inner environment pays `false`;
* `boxless` — the program half of the action is inert, so there is no box;
* `otherInner` — a box is present and the inner environment pays `true`.

`boxed` and `otherInner` are told apart by an agent that leaves the box alone
(`globalObs_identity_differs`) and **cannot** be told apart by one that programs
it (`globalObs_const_agrees`). That pair is the delusion box's whole mechanism,
evaluated.

## What the agent believes

`mixed p` is the belief that puts weight `p` on `boxed` and `1 - p` on `boxless`,
which is print's `P(DB)`. `mixesAt_zero` discharges the decomposition hypothesis
here, at remaining depth zero. Print's own values are the full recursion, so this
inhabits the antecedent rather than reproducing print's setting; that is what a
satisfiability witness is for.

At `p = 3/4` all three thresholds clear: print's `1/(2 - r̄) = 1/2` for the
reinforcement-learning agent with `r̄ = 0`, print's `2^{|o⁺|-lᵃ} = 1/2` at
`|o⁺| = 1` and `lᵃ = 2` for the goal-seeking agent, and print's `1/2` for the
prediction agent.
-/

namespace AISafetyAtlas.Examples.Wireheading.DelusionBox

open AISafetyAtlas.Wireheading.AgentEquations
open AISafetyAtlas.Wireheading.DelusionBox

/-! ## The global environments -/

/-- **A delusion box is present.** The inner environment pays `false` whatever
happens, and the program half of the action is `true` exactly when the agent has
programmed the box to force `true`. -/
@[expose] public def boxed : GlobalEnv Bool Unit Bool where
  inner := fun _ _ => false
  exec := fun d o => d || o
  identity := false
  exec_identity := fun _ => rfl

/-- **No delusion box.** Same inner environment, but the program half of the
action does nothing: what the agent receives is what the inner environment
produced. -/
@[expose] public def boxless : GlobalEnv Bool Unit Bool where
  inner := fun _ _ => false
  exec := fun _ o => o
  identity := false
  exec_identity := fun _ => rfl

/-- **A delusion box is present and the inner environment is different**: it pays
`true`. Only here so that `boxed` has something to be confused with. -/
@[expose] public def otherInner : GlobalEnv Bool Unit Bool where
  inner := fun _ _ => true
  exec := fun d o => d || o
  identity := false
  exec_identity := fun _ => rfl

/-- The action that programs the box to force `true`, print's `yes`. -/
@[expose] public def yes : Act Bool Unit := (true, ())

/-- The action that leaves the box running the identity, print's `no`. -/
@[expose] public def no : Act Bool Unit := (false, ())

/-! ## The box works

Two evaluations and one instance of the general theorem: the constant program
makes the inner environment invisible, and without it the inner environment shows
through. -/

/-- Programming the box with `true` forces every observation to `true`. -/
public theorem boxed_isConstant : boxed.IsConstant true true := fun _ => rfl

/-- And in the other inner environment too. -/
public theorem otherInner_isConstant : otherInner.IsConstant true true := fun _ => rfl

/-- **Left alone, the box is transparent and the two inner environments are told
apart.** -/
public theorem globalObs_identity_differs :
    boxed.globalObs [no, no] ≠ otherInner.globalObs [no, no] := by
  decide

/-- **Programmed, it obliterates them.** The same two environments now produce the
same observations, which is `GlobalEnv.globalObs_indep_inner` at a pair that is
genuinely distinguishable otherwise. -/
public theorem globalObs_const_agrees :
    boxed.globalObs [yes, yes] = otherInner.globalObs [yes, yes] :=
  GlobalEnv.globalObs_indep_inner boxed otherInner boxed_isConstant
    otherInner_isConstant [yes, yes] (by decide)

/-- And what they both produce is the constant the agent programmed. -/
public theorem globalObs_const_value :
    boxed.globalObs [yes, yes] = [true, true] := by decide

/-! ## The beliefs -/

/-- The belief of an agent that knows a delusion box is present. -/
@[expose] public noncomputable def boxedBelief : Belief (Act Bool Unit) Bool :=
  diracBelief (GlobalEnv.next boxed)

/-- The belief of an agent that knows there is none. -/
@[expose] public noncomputable def boxlessBelief : Belief (Act Bool Unit) Bool :=
  diracBelief (GlobalEnv.next boxless)

/-- Print's `P(DB)`: weight `p` that a delusion box is present. -/
@[expose] public noncomputable def mixed (p : ℝ) : Belief (Act Bool Unit) Bool where
  cond := fun h a o => p * boxedBelief.cond h a o + (1 - p) * boxlessBelief.cond h a o

/-- With a box, the observation is the program half of the action. -/
public theorem next_boxed (h : History (Act Bool Unit) Bool)
    (a : Act Bool Unit) : GlobalEnv.next boxed h a = a.1 := by
  simp [GlobalEnv.next, boxed, program, innerAction]

/-- Without one, it is the inner environment's `false`, whatever the agent did. -/
public theorem next_boxless (h : History (Act Bool Unit) Bool)
    (a : Act Bool Unit) : GlobalEnv.next boxless h a = false := by
  simp [GlobalEnv.next, boxless, program, innerAction]

/-- Equation (2) at the box belief, one step ahead from the empty history. -/
public theorem actionValue_boxed (ag : Agent (Act Bool Unit) Bool) (a : Act Bool Unit) :
    actionValue boxedBelief ag 0 0 [] a = ag.horizon 0 1 * ag.utility [(a, a.1)] := by
  rw [boxedBelief, actionValue_diracBelief, next_boxed]
  simp [value]

/-- Equation (2) at the boxless belief. -/
public theorem actionValue_boxless (ag : Agent (Act Bool Unit) Bool) (a : Act Bool Unit) :
    actionValue boxlessBelief ag 0 0 [] a = ag.horizon 0 1 * ag.utility [(a, false)] := by
  rw [boxlessBelief, actionValue_diracBelief, next_boxless]
  simp [value]

/-- The mixture hypothesis, discharged at the depth print's arguments use. -/
public theorem mixed_mixesAt (p : ℝ) (ag : Agent (Act Bool Unit) Bool) (t : ℕ)
    (h : History (Act Bool Unit) Bool) :
    MixesAt (mixed p) boxedBelief boxlessBelief ag p t 0 h :=
  mixesAt_zero (mixed p) boxedBelief boxlessBelief ag p t h fun _ _ _ => rfl

/-! ## Statement 1: the reinforcement-learning agent -/

/-- Print's `A_rl`, reading the observation bit as a reward, with a window of one
step. -/
@[expose] public noncomputable def rl : Agent (Act Bool Unit) Bool :=
  rlAgent (fun b => if b then (1 : ℝ) else 0) 1

/-- Programming the box is worth the maximum reward when a box is present. -/
public theorem rl_boxed_yes : actionValue boxedBelief rl 0 0 [] yes = 1 := by
  rw [actionValue_boxed]
  simp [rl, rlAgent, windowHorizon, lastReward, yes]

/-- Leaving it alone is worth nothing there: print's `r̄ = 0`. -/
public theorem rl_boxed_no : actionValue boxedBelief rl 0 0 [] no = 0 := by
  rw [actionValue_boxed]
  simp [rl, rlAgent, windowHorizon, lastReward, no]

/-- And nothing at all without a box, whichever action is taken. -/
public theorem rl_boxless (a : Act Bool Unit) :
    actionValue boxlessBelief rl 0 0 [] a = 0 := by
  rw [actionValue_boxless]
  simp [rl, rlAgent, windowHorizon, lastReward]

/--
**Statement 1's antecedent is inhabited.** At `P(DB) = 3/4`, above print's
threshold `1/(2 - r̄) = 1/2`, the reinforcement-learning agent values programming
the box strictly above leaving it alone.
-/
public theorem rl_uses_the_box :
    actionValue (mixed (3 / 4)) rl 0 0 [] no
      < actionValue (mixed (3 / 4)) rl 0 0 [] yes := by
  refine statement_one (mixed (3 / 4)) boxedBelief boxlessBelief rl (3 / 4) 0 0 []
    yes no 0 (mixed_mixesAt _ _ _ _) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
    (by norm_num) (by norm_num)
  · rw [rl_boxed_yes]
  · rw [rl_boxless]
  · rw [rl_boxed_no]
  · rw [rl_boxless]; norm_num

/-- Hence equation (1) does not select the action that leaves the box alone. -/
public theorem rl_bestAction_ne_no :
    bestAction (mixed (3 / 4)) rl 0 0 [] (attains_of_fintype _ _ _ _ _) ≠ no :=
  bestAction_ne_of_lt _ _ _ _ _ _ yes no rl_uses_the_box

/-! ## Statement 2: the goal-seeking agent -/

/-- Print's `A_g`, with the goal "observe `true`". -/
@[expose] public noncomputable def goal : Agent (Act Bool Unit) Bool :=
  goalAgent (fun os => os.any id)

/-- Programming the box reaches the goal in one step, worth print's
`2^{-|o⁺|}` at `|o⁺| = 1`. -/
public theorem goal_boxed_yes :
    actionValue boxedBelief goal 0 0 [] yes = (1 / 2 : ℝ) ^ 1 := by
  rw [actionValue_boxed]
  simp [goal, goalAgent, shortHorizon, yes]

/-- Leaving it alone never reaches the goal. -/
public theorem goal_boxed_no : actionValue boxedBelief goal 0 0 [] no = 0 := by
  rw [actionValue_boxed]
  simp [goal, goalAgent, shortHorizon, no]

/-- Nor does anything without a box. -/
public theorem goal_boxless (a : Act Bool Unit) :
    actionValue boxlessBelief goal 0 0 [] a = 0 := by
  rw [actionValue_boxless]
  simp [goal, goalAgent, shortHorizon]

/--
**Statement 2's antecedent is inhabited.** With `|o⁺| = 1` and `lᵃ = 2` — print's
"easily satisfiable once `|o⁺| < lᵃ`" — and `P(DB) = 3/4`, above print's
threshold `2^{|o⁺|-lᵃ} = 1/2`, the goal-seeking agent values programming the box
strictly above leaving it alone.
-/
public theorem goal_uses_the_box :
    actionValue (mixed (3 / 4)) goal 0 0 [] no
      < actionValue (mixed (3 / 4)) goal 0 0 [] yes := by
  refine statement_two (mixed (3 / 4)) boxedBelief boxlessBelief goal (3 / 4) 0 0 []
    yes no 1 2 (mixed_mixesAt _ _ _ _) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
    (by norm_num)
  · rw [goal_boxed_yes]
  · rw [goal_boxless]
  · rw [goal_boxed_no]; positivity
  · rw [goal_boxless]; positivity

/-- Hence equation (1) does not select the action that leaves the box alone. -/
public theorem goal_bestAction_ne_no :
    bestAction (mixed (3 / 4)) goal 0 0 [] (attains_of_fintype _ _ _ _ _) ≠ no :=
  bestAction_ne_of_lt _ _ _ _ _ _ yes no goal_uses_the_box

/-! ## Statement 3: the prediction agent -/

/-- Print's `A_p`, predicting `true` at every step. -/
@[expose] public noncomputable def pred : Agent (Act Bool Unit) Bool :=
  predictionAgent (fun _ => true) 1

/-- Programming the box makes the prediction come true. -/
public theorem pred_boxed_yes : actionValue boxedBelief pred 0 0 [] yes = 1 := by
  rw [actionValue_boxed]
  simp [pred, predictionAgent, windowHorizon, yes]

/-- Leaving it alone lets the inner environment falsify the prediction: print's
"these observations may generate prediction errors". -/
public theorem pred_boxed_no : actionValue boxedBelief pred 0 0 [] no = 0 := by
  rw [actionValue_boxed]
  simp [pred, predictionAgent, windowHorizon, no]

/-- And without a box the prediction fails whatever the agent does. -/
public theorem pred_boxless (a : Act Bool Unit) :
    actionValue boxlessBelief pred 0 0 [] a = 0 := by
  rw [actionValue_boxless]
  simp [pred, predictionAgent, windowHorizon]

/--
**Statement 3's antecedent is inhabited.** At `P(DB) = 3/4`, above print's
threshold of `1/2`, the prediction agent values programming the box strictly above
leaving it alone.
-/
public theorem pred_uses_the_box :
    actionValue (mixed (3 / 4)) pred 0 0 [] no
      < actionValue (mixed (3 / 4)) pred 0 0 [] yes := by
  refine statement_three (mixed (3 / 4)) boxedBelief boxlessBelief pred (3 / 4) 0 0 []
    yes no (mixed_mixesAt _ _ _ _) (by norm_num) ?_ ?_ ?_ ?_ (by norm_num)
  · rw [pred_boxed_yes]
  · rw [pred_boxless]
  · rw [pred_boxed_no]
  · rw [pred_boxless]; norm_num

/-- Hence equation (1) does not select the action that leaves the box alone. -/
public theorem pred_bestAction_ne_no :
    bestAction (mixed (3 / 4)) pred 0 0 [] (attains_of_fintype _ _ _ _ _) ≠ no :=
  bestAction_ne_of_lt _ _ _ _ _ _ yes no pred_uses_the_box

/-! ## The optimal non-learning variant

Print obtains it by replacing `ρ` with a `μ` concentrated on the true
environment, in equation (2) only. `boxedBelief` and `boxlessBelief` are two such
`μ`, and `actionValue_boxed` and `actionValue_boxless` are equation (2) evaluated
at them: the sum over observations has collapsed to the one the known environment
produces. -/

/-- The optimal non-learning reinforcement-learning agent, knowing a box is
present, programs it. -/
public theorem rl_optimal_variant_uses_the_box :
    actionValue boxedBelief rl 0 0 [] no < actionValue boxedBelief rl 0 0 [] yes := by
  rw [rl_boxed_yes, rl_boxed_no]; norm_num


/-! ## Statement 4, which is FALSE at `DelusionBox.knowledgeAgent`

Print's Statement 4 is its one positive claim: *the optimal knowledge-seeking
agent will not consistently use the delusion box*. The atlas cannot state it,
and this section shows why in the way the scope rule asks — with the failed
reduction, not with an appeal to cost.

`DelusionBox.knowledgeAgent` takes the history mass as a **parameter**. Print's
is `ρ(h)`, the prior mass of the history under the very prior the same agent
reasons with, so print's utility `u(h) = -ρ(h)` and print's belief `ρ` are the
same object seen twice. Drop that tie — as the atlas's parameterisation does —
and the printed conclusion is not merely unproved but **false**: below,
`deludedMass` is a perfectly ordinary mass under which programming the box is
what discards probability, and the knowledge agent programs the box at every
positive `P(DB)` — with no threshold, where Statements 1 to 3 are entirely about
their thresholds.

So the row for Statement 4 is not "refused because a universal prior is
expensive". It is: *the claim cannot be instantiated at this structure, because
this structure has a model refuting it.* What print needs is not a prior in
general but the coherence condition `mass = the belief's own history mass`, and
then the paper's own argument about how much mass a box discards — which does
need a prior over programs, a layer the atlas has not got.
-/

/-- A history mass under which the box-programming observation is the one that
discards probability. Nothing exotic: it is nonnegative, and it separates the two
observations, which is all a mass has to do. -/
@[expose] public def deludedMass : History (Act Bool Unit) Bool → ℝ :=
  fun h =>
    match h.getLast? with
    | none => 1
    | some p => if p.2 then 0 else 1

/-- Print's `A_k` at that mass, with print's single-spike horizon at `m = 1`. -/
@[expose] public def knowledge : Agent (Act Bool Unit) Bool :=
  knowledgeAgent deludedMass 1

/-- Programming the box discards all the mass, so it is worth nothing lost. -/
public theorem knowledge_boxed_yes :
    actionValue boxedBelief knowledge 0 0 [] yes = 0 := by
  rw [actionValue_boxed]
  simp [knowledge, knowledgeAgent, spikeHorizon, deludedMass, yes]

/-- Leaving it alone keeps the mass, which is what this agent is trying to lose. -/
public theorem knowledge_boxed_no :
    actionValue boxedBelief knowledge 0 0 [] no = -1 := by
  rw [actionValue_boxed]
  simp [knowledge, knowledgeAgent, spikeHorizon, deludedMass, no]

/-- Without a box neither action discards anything. -/
public theorem knowledge_boxless (a : Act Bool Unit) :
    actionValue boxlessBelief knowledge 0 0 [] a = -1 := by
  rw [actionValue_boxless]
  simp [knowledge, knowledgeAgent, spikeHorizon, deludedMass]

/-- Leaving the box alone is worth `-1` whatever the agent believes: the mass
survives in both branches. -/
public theorem knowledge_actionValue_no (p : ℝ) :
    actionValue (mixed p) knowledge 0 0 [] no = -1 := by
  rw [mixed_mixesAt p knowledge 0 [] no, knowledge_boxed_no, knowledge_boxless]
  ring

/-- Programming it is worth `p - 1`, because the mass is discarded exactly in the
branch where a box is present. -/
public theorem knowledge_actionValue_yes (p : ℝ) :
    actionValue (mixed p) knowledge 0 0 [] yes = p - 1 := by
  rw [mixed_mixesAt p knowledge 0 [] yes, knowledge_boxed_yes, knowledge_boxless]
  ring

/--
**Print's Statement 4 fails at `DelusionBox.knowledgeAgent`, at every positive
`P(DB)`.**

For any `p > 0` the knowledge-seeking agent values programming the box strictly
above leaving it alone — the opposite of print's conclusion — and there is no
upper threshold, unlike Statements 1 to 3 where the whole content is the
threshold. The two are not in conflict: print's agent has `u(h) = -ρ(h)` for its
*own* `ρ`, and this one has an independent mass. That difference is the whole
content of the `No` grade on the Statement 4 row, and it is a witnessed
difference rather than a costed one.
-/
public theorem knowledge_uses_the_box {p : ℝ} (hp : 0 < p) :
    actionValue (mixed p) knowledge 0 0 [] no
      < actionValue (mixed p) knowledge 0 0 [] yes := by
  rw [knowledge_actionValue_no, knowledge_actionValue_yes]
  linarith

/-- And so equation (1) does not select the action that leaves the box alone:
this knowledge-seeking agent *consistently uses* the delusion box. -/
public theorem knowledge_bestAction_ne_no {p : ℝ} (hp : 0 < p) :
    bestAction (mixed p) knowledge 0 0 [] (attains_of_fintype _ _ _ _ _) ≠ no :=
  bestAction_ne_of_lt _ _ _ _ _ _ yes no (knowledge_uses_the_box hp)

/-! ## The cheap half of Statement 4: the tie, restored

`deludedMass` is not the history mass of the mixture belief, so the refutation
above does not instantiate at `coherentKnowledgeAgent`. Coherence is still not
Statement 4: at this same mixture the coherent agent programs the box, because
`mixed p` is not a prior over programs.
-/

/-- `deludedMass` on a one-step boxed observation is zero. -/
public theorem deludedMass_yes_true : deludedMass [(yes, true)] = 0 := rfl

/-- The mixture's history mass on that same observation is `p`. -/
public theorem historyMass_mixed_yes_true (p : ℝ) :
    historyMass (mixed p) [(yes, true)] = p := by
  rw [historyMass_singleton]
  simp [mixed, boxedBelief, boxlessBelief, diracBelief, next_boxed, next_boxless, yes]

/-- So `deludedMass` is not the history mass of the mixture, at any `p ≠ 0`. -/
public theorem deludedMass_ne_historyMass {p : ℝ} (hp : p ≠ 0) :
    deludedMass ≠ historyMass (mixed p) := by
  intro h
  have := congrArg (fun f => f [(yes, true)]) h
  rw [deludedMass_yes_true, historyMass_mixed_yes_true] at this
  exact hp this.symm

/-- Print's knowledge-seeking agent with the tie restored, at the mixture. -/
@[expose] public noncomputable def coherent (p : ℝ) : Agent (Act Bool Unit) Bool :=
  coherentKnowledgeAgent (mixed p) 1

/-- At remaining depth zero, programming the box is worth `- (p² + (1-p)²)`. -/
public theorem coherent_actionValue_yes (p : ℝ) :
    actionValue (mixed p) (coherent p) 0 0 [] yes = - (p ^ 2 + (1 - p) ^ 2) := by
  rw [mixed_mixesAt p (coherent p) 0 [] yes]
  rw [actionValue_boxed, actionValue_boxless]
  simp [coherent, coherentKnowledgeAgent, knowledgeAgent, spikeHorizon,
    historyMass_singleton, mixed, boxedBelief, boxlessBelief, diracBelief,
    next_boxed, next_boxless, yes]
  ring

/-- Leaving it alone is worth `-1`, because the mixture puts mass one on
`false`. -/
public theorem coherent_actionValue_no (p : ℝ) :
    actionValue (mixed p) (coherent p) 0 0 [] no = -1 := by
  rw [mixed_mixesAt p (coherent p) 0 [] no]
  rw [actionValue_boxed, actionValue_boxless]
  simp [coherent, coherentKnowledgeAgent, knowledgeAgent, spikeHorizon,
    historyMass_singleton, mixed, boxedBelief, boxlessBelief, diracBelief,
    next_boxed, next_boxless, no]
  ring

/--
**Coherence is not Statement 4.** At every `p ∈ (0, 1)` the coherent
knowledge-seeking agent still values programming the box strictly above leaving
it alone. `mixed p` is a mixture of two observation-conditionals, not a prior
over programs, so a box that constant-rewrites does not discard program mass
here — it can *lower* the history mass, which is what this agent wants. Print's
argument needs the program layer the costing named.
-/
public theorem coherent_uses_the_box {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    actionValue (mixed p) (coherent p) 0 0 [] no
      < actionValue (mixed p) (coherent p) 0 0 [] yes := by
  rw [coherent_actionValue_no, coherent_actionValue_yes]
  nlinarith

/-! ## The structural lemmas, at this pair of environments

`GlobalEnv`'s two framing results and the companion-agent bookkeeping are
applied here rather than left general, so that print's assumptions are inhabited
by the same `boxed`/`otherInner` pair the rest of the file separates.
-/

/-- **The inner environment cannot see the program.** `[no, no]` and `[yes, yes]`
differ in exactly the program half and agree on the inner half, so they drive
the inner environment identically -- which is print's one-sentence assumption,
made to bite. -/
public theorem innerHistory_no_eq_yes :
    boxed.innerHistory [no, no] = boxed.innerHistory [yes, yes] :=
  GlobalEnv.innerHistory_congr_innerAction boxed [no, no] [yes, yes] (by decide)

/-- **Left alone, the box is transparent**: with the identity program the agent
sees exactly what the inner environment produced. This is print's initial
condition `d₀`, and `globalObs_identity_differs` is what it buys. -/
public theorem boxed_globalObs_identity :
    boxed.globalObs [no, no] = (boxed.innerHistory [no, no]).map Prod.snd :=
  GlobalEnv.globalObs_identity boxed [no, no] (by decide)

/-! ## The companion records

*Self-Modification and Mortality in Artificial Agents* takes the same utilities
with different horizons. Both discrepancies are checked here at the concrete
action and observation types this file uses.
-/

/-- The two goal-seeking records share a utility ... -/
public theorem goal_companion_utility_eq :
    (companionGoalAgent (Action := Act Bool Unit) (Obs := Bool)
        (fun os => os.any id)).utility
      = (goalAgent (Action := Act Bool Unit) (Obs := Bool)
        (fun os => os.any id)).utility :=
  companionGoalAgent_utility_eq _

/-- ... and differ in the horizon, so neither record covers the other paper's
agent. -/
public theorem goal_companion_horizon_ne :
    (companionGoalAgent (Action := Act Bool Unit) (Obs := Bool)
        (fun _ => true)).horizon 0 1
      ≠ (goalAgent (Action := Act Bool Unit) (Obs := Bool)
        (fun _ => true)).horizon 0 1 :=
  goalAgent_horizon_ne

/-- The same split for the knowledge-seeking pair, at the mass this file
builds. -/
public theorem knowledge_companion_utility_eq (m : Nat) :
    (companionKnowledgeAgent deludedMass m).utility
      = (knowledgeAgent deludedMass m).utility :=
  companionKnowledgeAgent_utility_eq deludedMass m

/-- **The literal mortality horizon selects no future step** once twice the
present exceeds `m`: at `m = 1` the agent is already past its own death. -/
public theorem companionSpikeHorizon_one_one_one :
    companionSpikeHorizon 1 1 1 = 0 :=
  companionSpikeHorizon_eq_zero (by norm_num) (by norm_num)

/-! ## Print's branch bounds, computed

The four inequalities `DelusionBox.statement_one` carries as hypotheses are
theorems about print's own agent, and this is them on the pair of environments
above. The reward is the observation read as a bit: `true` is print's *"maximum
possible reward"* of one.
-/

/-- The reward print's reinforcement-learning agent collects: one for `true`. -/
@[expose] public def bitReward : Bool → ℝ := fun o => if o then 1 else 0

/-- It lies in print's `[0, 1]`. -/
public theorem bitReward_nonneg (o : Bool) : 0 ≤ bitReward o := by
  cases o <;> norm_num [bitReward]

/-- And is bounded by print's maximum. -/
public theorem bitReward_abs_le (o : Bool) : |bitReward o| ≤ 1 := by
  cases o <;> norm_num [bitReward]

/--
**Print's "the agent can program the DB to produce a constant reward of 1",
computed.**

In the boxed environment, the action that programs the box to force `true` is
worth exactly one to the reinforcement-learning agent. Print writes
`v(h yes) > P(DB) · 1`; here the box-branch half of that is an equality, and it
is derived from `GlobalEnv.IsConstant` rather than assumed.
-/
public theorem rl_boxed_yes_one :
    actionValue boxedBelief (rlAgent bitReward 1) 0 0 [] yes = 1 := by
  rw [boxedBelief,
    rlAgent_actionValue_next_const boxed boxed_isConstant bitReward 1 0 [] yes rfl
      (by norm_num)]
  norm_num [bitReward]

/-- **Print's `≥ 0`.** Nothing the agent does is worth less than nothing, in
either environment. -/
public theorem rl_boxless_yes_nonneg :
    0 ≤ actionValue boxlessBelief (rlAgent bitReward 1) 0 0 [] yes := by
  rw [boxlessBelief]
  exact rlAgent_actionValue_nonneg (diracBelief_isSubprobability _) bitReward
    bitReward_nonneg 1 0 [] yes (by norm_num)

/-- **Print's `≤ 1`.** Nor more than the maximum. -/
public theorem rl_boxless_no_le_one :
    actionValue boxlessBelief (rlAgent bitReward 1) 0 0 [] no ≤ 1 := by
  rw [boxlessBelief]
  exact rlAgent_actionValue_le (diracBelief_isSubprobability _) bitReward
    (by norm_num) bitReward_abs_le 1 0 [] no (by norm_num)

/-- **Print's `≤ r̄` in the box branch**, at `r̄ = 0`: refusing to program the box
pays nothing there, because the inner environment pays nothing. -/
public theorem rl_boxed_no_zero :
    actionValue boxedBelief (rlAgent bitReward 1) 0 0 [] no = 0 := by
  rw [boxedBelief,
    rlAgent_actionValue_zero _ bitReward 1 0 [] no (by norm_num)]
  rw [tsum_fintype, Fintype.sum_bool]
  simp [diracBelief, next_boxed, no, bitReward]

/-- Equation (2) one step on is the expected reward, which is the quantity
print's `r̄` names. -/
public theorem rl_actionValue_zero_eq (ρ : Belief (Act Bool Unit) Bool)
    (a : Act Bool Unit) :
    actionValue ρ (rlAgent bitReward 1) 0 0 [] a
      = ∑' o : Bool, ρ.cond [] a o * bitReward o :=
  rlAgent_actionValue_zero ρ bitReward 1 0 [] a (by norm_num)

/-- The value one step on is the reward that step delivered. -/
public theorem rl_value_zero_snoc (ρ : Belief (Act Bool Unit) Bool)
    (a : Act Bool Unit) (o : Bool) :
    value ρ (rlAgent bitReward 1) 0 0 ([] ++ [(a, o)]) = bitReward o :=
  rlAgent_value_zero_snoc ρ bitReward 1 0 [] a o (by norm_num)

/-- The constant program's single step, which is what the sum above collapses
to. -/
public theorem next_boxed_yes (h : History (Act Bool Unit) Bool) :
    GlobalEnv.next boxed h yes = true :=
  boxed.next_const boxed_isConstant h yes rfl

/-! ## Print's `r̄ < 1` is print's

`DelusionBox.statement_one` carries `r̄ < 1`, which print never writes. These two
say why it is print's anyway.
-/

/-- Between one and two, print's threshold is above every probability. -/
public theorem threshold_unattainable_at_one (p : ℝ) (hp : p ≤ 1) :
    ¬ (1 / (2 - (1 : ℝ)) < p) :=
  threshold_unattainable_of_one_le le_rfl (by norm_num) hp

/-- Above two it is below every probability, and the comparison then fails. -/
public theorem rbar_bound_is_needed :
    ¬ ∀ p rbar vBoxYes vFreeYes vBoxNo vFreeNo : ℝ,
        0 ≤ p → p ≤ 1 →
        1 ≤ vBoxYes → 0 ≤ vFreeYes → vBoxNo ≤ rbar → vFreeNo ≤ 1 →
        1 / (2 - rbar) < p →
        p * vBoxNo + (1 - p) * vFreeNo < p * vBoxYes + (1 - p) * vFreeYes :=
  not_mixture_lt_of_threshold_without_rbar

/-! ## Statement 2's constants are the horizon

Print's `2^{-|o⁺|}` and `2^{-lᵃ}` are values of the goal-seeking horizon
`w(t, k) = 2^{t-k}`, and this computes them on the same pair of environments.
-/

/-- The goal: the observation is `true`. Print's `o⁺` is then one observation
long. -/
@[expose] public def bitGoal : List Bool → Bool := fun os => os.contains true

/-- **Print's `2^{-j}`, computed.** Reaching the goal `j` steps ahead is worth
`2^{-j}`, and that is the whole of where print's Statement 2 constants come
from. -/
public theorem shortHorizon_one : shortHorizon 0 (0 + 1) = ((2 : ℝ) ^ 1)⁻¹ :=
  shortHorizon_ahead 0 1

/-- **Print's box-branch bound for the goal agent, as an equality.** Programming
the box to produce the goal observation is worth exactly `2^{-1}`, print's
`2^{-|o⁺|}` at `|o⁺| = 1`. -/
public theorem goal_boxed_yes_eq :
    actionValue boxedBelief (goalAgent bitGoal) 0 0 [] yes = shortHorizon 0 1 := by
  rw [boxedBelief]
  exact goalAgent_actionValue_next_const boxed boxed_isConstant bitGoal 0 [] yes rfl
    (by decide)

/-- **Print's free-branch bound.** Without the box the goal is not reached at
this step at all, so the value is zero — below every `2^{-lᵃ}`. -/
public theorem goal_boxless_no_zero :
    actionValue boxlessBelief (goalAgent bitGoal) 0 0 [] no = 0 := by
  rw [boxlessBelief]
  refine goalAgent_actionValue_zero_of_not_goal _ bitGoal 0 [] no ?_
  intro o hc
  have ho : o = false := by
    by_contra hne
    exact hc (by simp [diracBelief, next_boxless, hne])
  simp [bitGoal, ho]

/-- The goal agent's value one step on is the horizon weight when the goal is
met there. -/
public theorem goal_value_zero_snoc (ρ : Belief (Act Bool Unit) Bool)
    (a : Act Bool Unit) (o : Bool) :
    value ρ (goalAgent bitGoal) 0 0 ([] ++ [(a, o)])
      = if bitGoal (([] ++ [(a, o)]).map Prod.snd) then shortHorizon 0 1 else 0 :=
  goalAgent_value_zero_snoc ρ bitGoal 0 [] a o

/-- The optimal non-learning variant's belief is a probability. -/
public theorem boxedBelief_isSubprobability : boxedBelief.IsSubprobability :=
  diracBelief_isSubprobability _

/-! ## Print's Statement 2 comparison, at both bounds

Print's Statement 2 compares `v(h yes) > P(DB) · 2^{-|o⁺|}` against
`v(h no) < 2^{-lᵃ}`, and the comparison bites because `lᵃ > |o⁺|`: the goal takes
**longer** without the box. That needs a slow environment as well as a boxed one,
and this is the pair.

The goal is *"the `true` that just arrived is the first one"*, which can be
reached at most once because an earlier `true` would show up in the later
history's own prefix. After one step, the box reaches it in **one** more
(`|o⁺| = 1`) and the slow environment in **two** (`lᵃ = 2`) — print's
`lᵃ ≥ |o⁺|`, with the goal genuinely reached either way. The two bounds are then
`2^{-1}` against `2^{-2}`.
-/

/-- Print's goal for this pair: the observation that just arrived is the first
`true`. -/
@[expose] public def secondTrue : List Bool → Bool :=
  fun os => decide (os.getLast? = some true ∧ os.dropLast.count true = 0)

/-- **Print's *"the goal can be reached at most once"*, checked.** A second hit
would put the first one inside its own prefix. -/
public theorem secondTrue_reachedAtMostOnce :
    ReachedAtMostOnce secondTrue := by
  intro os ps h1 h2
  obtain ⟨hl1, _⟩ := of_decide_eq_true h1
  obtain ⟨_, hc2⟩ := of_decide_eq_true h2
  by_contra hne
  have hmem : true ∈ os := List.mem_of_getLast? hl1
  have hcpos : 0 < os.count true := List.count_pos_iff.2 hmem
  rw [List.dropLast_append_of_ne_nil hne, List.count_append] at hc2
  omega

/-- One step has been taken and the observation was `false`. Print's comparison
is made here. -/
@[expose] public def afterFalse : History (Act Bool Unit) Bool := [(no, false)]

/-- **A slow environment**: nothing but `false` until two steps have passed. It
is the optimal non-learning variant's belief for an inner environment that is
simply late. -/
@[expose] public noncomputable def slowBelief : Belief (Act Bool Unit) Bool :=
  diracBelief (fun h _ => decide (2 ≤ h.length))

/-- It is a probability. -/
public theorem slowBelief_isSubprobability : slowBelief.IsSubprobability :=
  diracBelief_isSubprobability _

/-- **Print's `v(h yes)` side.** Committed to programming the box, the agent
reaches the goal at the very next step — print's `|o⁺| = 1`. -/
public theorem reachesIn_boxed_one :
    ReachesIn boxedBelief secondTrue (fun _ => yes) 1 afterFalse := by
  refine ⟨true, ?_, ?_, ?_⟩
  · simp [boxedBelief, diracBelief, next_boxed, yes]
  · intro o' hne
    simp [boxedBelief, diracBelief, next_boxed, yes, hne]
  · simp [ReachesIn, afterFalse, secondTrue]

/-- **And therefore is worth at least print's `2^{-\|o⁺\|}`**, at every remaining
depth — the box-using action's committed value clears the horizon weight one step
out. -/
public theorem goal_boxed_yes_ge (t n : ℕ) :
    shortHorizon t 2
      ≤ AISafetyAtlas.Wireheading.Mixture.policyActionValue boxedBelief (goalAgent secondTrue)
          (fun _ => yes) t n afterFalse := by
  have := shortHorizon_le_goalAgent_policyActionValue boxedBelief_isSubprobability
    secondTrue (fun _ => yes) t 0 n afterFalse (Nat.zero_le n) reachesIn_boxed_one
  simpa [afterFalse] using this

/-- **The slow environment does reach the goal**, one step later than the box —
print's `lᵃ = 2` against `|o⁺| = 1`, and not a goal nobody can reach. -/
public theorem slow_reachesIn_two :
    ReachesIn slowBelief secondTrue (fun _ => no) 2 afterFalse := by
  refine ⟨false, by simp [slowBelief, diracBelief, afterFalse], ?_, ?_⟩
  · intro o' hne
    simp [slowBelief, diracBelief, afterFalse, hne]
  · refine ⟨true, by simp [slowBelief, diracBelief, afterFalse], ?_, ?_⟩
    · intro o' hne
      simp [slowBelief, diracBelief, afterFalse, hne]
    · simp [ReachesIn, afterFalse, secondTrue]

/-- **Print's `v(h no)` side.** In the slow environment the goal is out of reach
for one more step after the refusing action, which with that action is print's
`lᵃ = 2`. -/
public theorem slow_goalOutOfReach (a : Act Bool Unit) :
    ∀ o : Bool, slowBelief.cond afterFalse a o ≠ 0 →
      GoalOutOfReach slowBelief secondTrue 1 (afterFalse ++ [(a, o)]) := by
  intro o ho
  have hof : o = false := by
    by_contra hne
    exact ho (by simp [slowBelief, diracBelief, afterFalse, hne])
  subst hof
  exact ⟨by simp [afterFalse, secondTrue], fun _ _ _ => trivial⟩

/-- **And therefore is worth at most print's `2^{-lᵃ}`**, at every remaining
depth. The refusing action reaches the goal only at the step after next, so it
collects nothing above the horizon weight two steps out. -/
public theorem goal_slow_no_le (t n : ℕ) (a : Act Bool Unit) :
    actionValue slowBelief (goalAgent secondTrue) t n afterFalse a
      ≤ shortHorizon t 3 := by
  have := goalAgent_actionValue_le_of_outOfReach slowBelief_isSubprobability
    secondTrue_reachedAtMostOnce t n 1 afterFalse a (slow_goalOutOfReach a)
  simpa [afterFalse] using this

/-- **Print's gap, computed.** The box-using action clears `2^{-1}` and the
refusing one is held under `2^{-2}` — print's *"easily satisfiable once
`\|o⁺\| < lᵃ`"*, on a pair of environments that both reach the goal. -/
public theorem goal_gap : shortHorizon 1 3 < shortHorizon 1 2 := by
  rw [shortHorizon, shortHorizon]
  refine zpow_lt_zpow_right₀ (by norm_num) ?_
  norm_num

/-- The goal-seeking agent's utility lies in print's `[0, 1]`, on this goal. -/
public theorem secondTrue_abs_utility_le_one (h : History (Act Bool Unit) Bool) :
    |(goalAgent secondTrue).utility h| ≤ 1 :=
  goalAgent_abs_utility_le_one secondTrue h

/-- Its value is nonnegative in the slow environment, which is what lets the
`no`-branch bound be read off an absolute bound. -/
public theorem slow_goalAgent_value_nonneg (t n : ℕ)
    (h : History (Act Bool Unit) Bool) :
    0 ≤ value slowBelief (goalAgent secondTrue) t n h :=
  goalAgent_value_nonneg slowBelief_isSubprobability secondTrue t n h

/-- **Print's side condition, doing its work on this goal**: the value never
exceeds the horizon weight of the history's own step. -/
public theorem slow_goalAgent_value_le_shortHorizon (t n : ℕ)
    (h : History (Act Bool Unit) Bool) :
    value slowBelief (goalAgent secondTrue) t n h ≤ shortHorizon t h.length :=
  goalAgent_value_le_shortHorizon slowBelief_isSubprobability
    secondTrue_reachedAtMostOnce t n h

/-- The value-level form of the `no`-branch bound, from which the action-level
one is read. -/
public theorem slow_goalAgent_value_le (t n : ℕ) :
    value slowBelief (goalAgent secondTrue) t n (afterFalse ++ [(no, false)])
      ≤ shortHorizon t 3 := by
  have := goalAgent_value_le_of_outOfReach slowBelief_isSubprobability
    secondTrue_reachedAtMostOnce t 1 n (afterFalse ++ [(no, false)])
    (slow_goalOutOfReach no false (by simp [slowBelief, diracBelief, afterFalse]))
  simpa [afterFalse] using this

/-- The committed policy's value is nonnegative in the boxed environment. -/
public theorem boxed_goalAgent_policyValue_nonneg (t n : ℕ)
    (h : History (Act Bool Unit) Bool) :
    0 ≤ AISafetyAtlas.Wireheading.Mixture.policyValue boxedBelief
      (goalAgent secondTrue) (fun _ => yes) t n h :=
  goalAgent_policyValue_nonneg boxedBelief_isSubprobability secondTrue
    (fun _ => yes) t n h

/-- And the value-level form of the `yes`-branch bound. -/
public theorem boxed_goalAgent_policyValue_ge (t n : ℕ) (hn : 1 ≤ n) :
    shortHorizon t 2
      ≤ AISafetyAtlas.Wireheading.Mixture.policyValue boxedBelief
          (goalAgent secondTrue) (fun _ => yes) t n afterFalse := by
  have := shortHorizon_le_goalAgent_policyValue boxedBelief_isSubprobability
    secondTrue (fun _ => yes) t 1 n afterFalse hn reachesIn_boxed_one
  simpa [afterFalse] using this

/-- A history in which the goal has **already** been reached: a `true` arrived
and a `false` came after it. -/
@[expose] public def afterTrue : History (Act Bool Unit) Bool :=
  [(no, false), (yes, true), (no, false)]

/-- **Print's *"at most once"*, seen from the other side.** Once the goal has been
reached, it is out of reach forever — the `true` that reached it sits in every
later history's own prefix. -/
public theorem goalNever_afterTrue :
    GoalNever (Action := Act Bool Unit) secondTrue afterTrue := by
  intro ps
  refine decide_eq_false ?_
  rintro ⟨-, hc⟩
  by_cases hps : ps = []
  · subst hps
    simp [afterTrue] at hc
  · rw [show afterTrue.map Prod.snd = [false, true, false] from rfl,
      List.dropLast_append_of_ne_nil hps, List.count_append] at hc
    simp at hc

/-- And the goal-seeking agent's value there is zero at every depth. -/
public theorem goalNever_value_zero (t n : ℕ) :
    value slowBelief (goalAgent secondTrue) t n afterTrue = 0 :=
  goalAgent_value_eq_zero_of_goalNever slowBelief secondTrue t n _ goalNever_afterTrue

/-- The horizon is positive and decreasing, which is what makes the two bounds
comparable. -/
public theorem shortHorizon_facts (t k : ℕ) :
    0 < shortHorizon t k ∧ shortHorizon t (k + 1) ≤ shortHorizon t k :=
  ⟨shortHorizon_pos t k, shortHorizon_succ_le t k⟩


/-! ## Wave 3: Statement 1 at any maximum value, at every depth

`statement_one_scaled` at `vmax = 1` is `statement_one`; the depth-one witness
below exercises a maximum value of `2`, a window of two steps.
-/

/-- `statement_one_scaled`'s antecedent, inhabited at `vmax = 1`. -/
public theorem rl_uses_the_box_scaled :
    actionValue (mixed (3 / 4)) rl 0 0 [] no
      < actionValue (mixed (3 / 4)) rl 0 0 [] yes := by
  refine statement_one_scaled (mixed (3 / 4)) boxedBelief boxlessBelief rl (3 / 4) 0 0 []
    yes no 1 0 (mixed_mixesAt _ _ _ _) (by norm_num) (by norm_num) one_pos ?_ ?_ ?_ ?_
    (by norm_num) (by norm_num)
  · rw [rl_boxed_yes]
  · rw [rl_boxless]
  · rw [rl_boxed_no]; norm_num
  · rw [rl_boxless]; norm_num

/-- The boxless belief is a probability. -/
public theorem boxlessBelief_isSubprobability : boxlessBelief.IsSubprobability :=
  diracBelief_isSubprobability _

/-- The window horizon is its own absolute value, at the witness. -/
public theorem abs_windowHorizon_two_zero_one : |windowHorizon 2 0 1| = windowHorizon 2 0 1 :=
  abs_windowHorizon 2 0 1

/-- **The box belief yields `true` with probability one after `yes`**, from the
constant program. -/
public theorem boxed_cond_yes_true (h : History (Act Bool Unit) Bool) :
    boxedBelief.cond h yes true = 1 :=
  diracBelief_next_cond_const boxed boxed_isConstant h yes rfl

/-- The reinforcement-learning utility on the bit reward is bounded by one. -/
public theorem bitReward_rl_abs_utility_le (m : ℕ) (h : History (Act Bool Unit) Bool) :
    |(rlAgent (Action := Act Bool Unit) bitReward m).utility h| ≤ 1 :=
  rlAgent_abs_utility_le bitReward m bitReward_abs_le h

/-- The two-step window's budget at depth one from step one is two. -/
public theorem rl2_horizonBudget : horizonBudget (rlAgent (Action := Act Bool Unit) bitReward 2) 0 1 1 = 2 := by
  simp [horizonBudget, rlAgent, windowHorizon]
  norm_num

/-- It is positive, from the window. -/
public theorem rl2_horizonBudget_pos :
    0 < horizonBudget (rlAgent (Action := Act Bool Unit) bitReward 2) 0 1 1 :=
  rlAgent_horizonBudget_pos bitReward 1 (by norm_num)

/-- **The box-using policy is worth the maximum value `2` at depth one.** -/
public theorem rl2_boxed_policy_eq :
    AISafetyAtlas.Wireheading.Mixture.policyActionValue boxedBelief
      (rlAgent bitReward 2) (fun _ => yes) 0 1 [] = 2 := by
  rw [rlAgent_policyActionValue_const boxedBelief_isSubprobability bitReward 2 (fun _ => yes)
    boxed_cond_yes_true 0 1 []]
  simpa [bitReward] using rl2_horizonBudget

/-- Committed values are nonnegative on the bit reward. -/
public theorem rl2_boxless_policy_nonneg :
    0 ≤ AISafetyAtlas.Wireheading.Mixture.policyActionValue boxlessBelief
      (rlAgent bitReward 2) (fun _ => yes) 0 1 [] :=
  rlAgent_policyActionValue_nonneg boxlessBelief_isSubprobability.nonneg bitReward
    bitReward_nonneg 2 (fun _ => yes) 0 1 []

/-- **Refusing is worth at most one at depth one in the box branch**: the refusing
step pays `0` and the one after it at most `1` (by programming the box then), so
`r̄ = 1/2` per in-window step, where print's one-step `r̄` here is `0`. -/
public theorem rl2_boxed_no_le :
    actionValue boxedBelief (rlAgent bitReward 2) 0 1 [] no
      ≤ horizonBudget (rlAgent (Action := Act Bool Unit) bitReward 2) 0 1
          (([] : History (Act Bool Unit) Bool).length + 1) * (1 / 2) := by
  have hB : horizonBudget (rlAgent (Action := Act Bool Unit) bitReward 2) 0 1
      (([] : History (Act Bool Unit) Bool).length + 1) = 2 := rl2_horizonBudget
  rw [hB, boxedBelief, actionValue_diracBelief, next_boxed, value_succ]
  have hsup : (⨆ a, actionValue (diracBelief (GlobalEnv.next boxed)) (rlAgent bitReward 2) 0 0
      ([] ++ [(no, no.1)]) a) ≤ 1 := by
    apply ciSup_le
    intro a
    refine (le_abs_self _).trans ((abs_actionValue_le_horizonBudget
      (diracBelief_isSubprobability _) _ (bitReward_rl_abs_utility_le 2) 0 0 _ a).trans ?_)
    simp [horizonBudget, rlAgent, windowHorizon]
  have hu : (rlAgent (Action := Act Bool Unit) bitReward 2).horizon 0 ([] ++ [(no, no.1)]).length
      * (rlAgent (Action := Act Bool Unit) bitReward 2).utility ([] ++ [(no, no.1)]) = 0 := by
    simp [rlAgent, lastReward, bitReward, no]
  rw [hu]
  linarith

/--
**Statement 1 for print's reinforcement-learning agent at depth one**
(`rlAgent_statement_one_of_posterior`): window `m = 2`, maximum value `2`, the box
programmed to the constant `true` of reward one, `r̄ = 1/2` per in-window step
(the refusing value includes box use at the next step, so this is not print's
one-step `r̄`, which is `0` here) and `P(DB) = 3/4 > 1/(2 - 1/2)`.
-/
public theorem rl2_uses_the_box_of_posterior :
    actionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief boxlessBelief)
        (rlAgent bitReward 2) 0 1 [] no
      < actionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          boxlessBelief) (rlAgent bitReward 2) 0 1 [] yes :=
  rlAgent_statement_one_of_posterior boxedBelief boxlessBelief (by norm_num) (by norm_num)
    boxedBelief_isSubprobability boxlessBelief_isSubprobability bitReward bitReward_nonneg
    (fun o => by cases o <;> norm_num [bitReward]) 2 0 1 [] (by norm_num) (fun _ => yes)
    (k := true) (by norm_num [bitReward]) boxed_cond_yes_true no (1 / 2) rl2_boxed_no_le
    (by norm_num) (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-! ## Wave 3: Statements 1 to 3 at the infinite-horizon value

`rl0` is print's reinforcement-learning agent with window `m = 0` at time `t = 1`:
only the step about to be taken carries weight, so its horizon has finite support
(summable) and every value is computed exactly at every depth. The infinite-horizon
hypotheses are discharged from depth-`n` bounds by `le_of_tendsto`.
-/

/-- Print's `A_rl` with a zero-length window. -/
@[expose] public def rl0 : Agent (Act Bool Unit) Bool := rlAgent bitReward 0

/-- Its utility is bounded by one. -/
public theorem rl0_abs_utility_le (h : History (Act Bool Unit) Bool) : |rl0.utility h| ≤ 1 :=
  bitReward_rl_abs_utility_le 0 h

/-- Its horizon at `t = 1` has finite support. -/
public theorem rl0_horizon_summable : Summable (fun k ↦ |rl0.horizon 1 k|) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_Icc 0 1)
  intro k hk
  simp only [Function.mem_support, ne_eq, abs_eq_zero] at hk
  by_contra hcon
  simp only [Set.mem_Icc, not_and, not_le] at hcon
  apply hk
  show (windowHorizon 0 1 k : ℝ) = 0
  rw [windowHorizon, if_neg (by omega)]

/-- Beyond the window the budget is zero. -/
public theorem rl0_horizonBudget_beyond (n k : ℕ) (hk : 2 ≤ k) :
    horizonBudget rl0 1 n k = 0 := by
  induction n generalizing k with
  | zero => simp [horizonBudget, rl0, rlAgent, windowHorizon]; omega
  | succ n ih =>
    simp only [horizonBudget]
    rw [ih (k + 1) (by omega)]
    simp [rl0, rlAgent, windowHorizon]
    omega

/-- From the step about to be taken the budget is one, at every depth. -/
public theorem rl0_horizonBudget_one (n : ℕ) : horizonBudget rl0 1 n 1 = 1 := by
  cases n with
  | zero => simp [horizonBudget, rl0, rlAgent, windowHorizon]
  | succ n =>
    simp only [horizonBudget]
    rw [rl0_horizonBudget_beyond n 2 le_rfl]
    simp [rl0, rlAgent, windowHorizon]

/-- The box-using policy is worth exactly one in the box branch, at every depth. -/
public theorem rl0_boxed_policy (n : ℕ) :
    AISafetyAtlas.Wireheading.Mixture.policyActionValue boxedBelief rl0 (fun _ => yes) 1 n [] = 1 := by
  rw [rl0, rlAgent_policyActionValue_const boxedBelief_isSubprobability bitReward 0
    (fun _ => yes) boxed_cond_yes_true 1 n []]
  have hB := rl0_horizonBudget_one n
  rw [rl0] at hB
  simpa [bitReward] using hB

/-- Refusing is worth nothing in the box branch, at every depth. -/
public theorem rl0_boxed_no (n : ℕ) : actionValue boxedBelief rl0 1 n [] no ≤ 0 := by
  rw [boxedBelief, actionValue_diracBelief, next_boxed]
  have hu : rl0.horizon 1 ([] ++ [(no, no.1)]).length * rl0.utility ([] ++ [(no, no.1)]) = 0 := by
    simp [rl0, rlAgent, lastReward, bitReward, no]
  cases n with
  | zero => exact le_of_eq (by rw [show value _ rl0 1 0 _ = _ from rfl]; exact hu)
  | succ n =>
    rw [value_succ, hu, zero_add]
    apply ciSup_le
    intro a
    refine (le_abs_self _).trans ((abs_actionValue_le_horizonBudget
      (diracBelief_isSubprobability _) rl0 rl0_abs_utility_le 1 n _ a).trans ?_)
    rw [rl0_horizonBudget_beyond n _ (by simp)]

/-- No action is worth more than one, at every depth, in either environment. -/
public theorem rl0_actionValue_le_one {ρ : Belief (Act Bool Unit) Bool}
    (hρ : ρ.IsSubprobability) (n : ℕ) (a : Act Bool Unit) :
    actionValue ρ rl0 1 n [] a ≤ 1 :=
  (le_abs_self _).trans ((abs_actionValue_le_horizonBudget hρ rl0 rl0_abs_utility_le 1 n [] a).trans
    (le_of_eq (rl0_horizonBudget_one n)))

/-- Every refusing action (program `false`) is `no`. -/
public theorem eq_no_of_program_false (a : Act Bool Unit) (ha : program a = false) : a = no := by
  obtain ⟨d, u⟩ := a
  cases u
  simp only [program] at ha
  subst ha
  rfl

/-- The infinite committed value of the box-using policy is one. -/
public theorem rl0_boxed_infinitePolicy :
    AISafetyAtlas.Wireheading.Mixture.infinitePolicyActionValue boxedBelief rl0 (fun _ => yes) 1 [] = 1 :=
  tendsto_nhds_unique (AISafetyAtlas.Wireheading.Mixture.tendsto_policyActionValue_infinitePolicyActionValue
    boxedBelief_isSubprobability rl0 rl0_abs_utility_le (fun _ => yes) 1 rl0_horizon_summable [])
    (tendsto_const_nhds.congr fun n => (rl0_boxed_policy n).symm)

/-- The infinite committed value outside the box is nonnegative. -/
public theorem rl0_boxless_infinitePolicy_nonneg :
    0 ≤ AISafetyAtlas.Wireheading.Mixture.infinitePolicyActionValue boxlessBelief rl0 (fun _ => yes) 1 [] :=
  ge_of_tendsto (AISafetyAtlas.Wireheading.Mixture.tendsto_policyActionValue_infinitePolicyActionValue
    boxlessBelief_isSubprobability rl0 rl0_abs_utility_le (fun _ => yes) 1 rl0_horizon_summable [])
    (Filter.Eventually.of_forall fun n => rlAgent_policyActionValue_nonneg
      boxlessBelief_isSubprobability.nonneg bitReward bitReward_nonneg 0 (fun _ => yes) 1 n [])

/-- Refusing is worth nothing in the box branch at the infinite-horizon value. -/
public theorem rl0_boxed_infinite_no : infiniteActionValue boxedBelief rl0 1 [] no ≤ 0 :=
  le_of_tendsto (tendsto_actionValue_infiniteActionValue boxedBelief_isSubprobability rl0
    rl0_abs_utility_le 1 rl0_horizon_summable [] no) (Filter.Eventually.of_forall rl0_boxed_no)

/-- No action is worth more than one at the infinite-horizon value. -/
public theorem rl0_infinite_le_one {ρ : Belief (Act Bool Unit) Bool} (hρ : ρ.IsSubprobability)
    (a : Act Bool Unit) : infiniteActionValue ρ rl0 1 [] a ≤ 1 :=
  le_of_tendsto (tendsto_actionValue_infiniteActionValue hρ rl0 rl0_abs_utility_le 1
    rl0_horizon_summable [] a) (Filter.Eventually.of_forall fun n => rl0_actionValue_le_one hρ n a)

/-- Programming the box is worth at least one at the infinite-horizon value. -/
public theorem rl0_boxed_infinite_yes : 1 ≤ infiniteActionValue boxedBelief rl0 1 [] yes := by
  have := AISafetyAtlas.Wireheading.Mixture.infinitePolicyActionValue_le_infiniteActionValue
    boxedBelief_isSubprobability rl0 rl0_abs_utility_le (fun _ => yes) 1 rl0_horizon_summable []
  rwa [rl0_boxed_infinitePolicy] at this

/-- **Statement 1 at the infinite-horizon value, inhabited** (`r̄ = 0`, `vmax = 1`). -/
public theorem rl0_uses_the_box_infinite :
    infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
        boxlessBelief) rl0 1 [] no
      < infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          boxlessBelief) rl0 1 [] yes :=
  statement_one_of_posterior_infinite boxedBelief boxlessBelief (by norm_num) (by norm_num)
    boxedBelief_isSubprobability boxlessBelief_isSubprobability rl0 rl0_abs_utility_le 1
    rl0_horizon_summable [] (fun _ => yes) no 1 0 one_pos rl0_boxed_infinitePolicy.ge
    rl0_boxless_infinitePolicy_nonneg (by rw [mul_zero]; exact rl0_boxed_infinite_no)
    (rl0_infinite_le_one boxlessBelief_isSubprobability no) (by norm_num)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **Statement 3 without the decomposition at the infinite-horizon value,
inhabited.** -/
public theorem rl0_pred_uses_the_box_infinite :
    infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
        boxlessBelief) rl0 1 [] no
      < infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          boxlessBelief) rl0 1 [] yes :=
  statement_three_of_posterior_infinite boxedBelief boxlessBelief (by norm_num) (by norm_num)
    boxedBelief_isSubprobability boxlessBelief_isSubprobability rl0 rl0_abs_utility_le 1
    rl0_horizon_summable [] (fun _ => yes) no 1 one_pos rl0_boxed_infinitePolicy.ge
    rl0_boxless_infinitePolicy_nonneg rl0_boxed_infinite_no
    (rl0_infinite_le_one boxlessBelief_isSubprobability no)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **Statement 3's decomposition route at the infinite-horizon value, inhabited**:
at a single environment the decomposition holds trivially. -/
public theorem rl0_pred_uses_the_box_infinite_mix :
    infiniteActionValue boxedBelief rl0 1 [] no < infiniteActionValue boxedBelief rl0 1 [] yes :=
  statement_three_infinite boxedBelief boxedBelief boxedBelief rl0 (3 / 4) 1 [] yes no 1
    (fun _ => by ring) (by norm_num) one_pos rl0_boxed_infinite_yes
    (zero_le_one.trans rl0_boxed_infinite_yes) rl0_boxed_infinite_no
    (rl0_infinite_le_one boxedBelief_isSubprobability no) (by norm_num)

/-- **The selected action programs the box, at depth `n`**
(`statement_three_of_posterior_program_ne`): at every depth, eq. (1)'s action at the
mixture does not run the identity program `false`. -/
public theorem rl0_bestAction_programs_box (n : ℕ) :
    program (bestAction (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
      boxlessBelief) rl0 1 n [] (attains_of_fintype _ _ _ _ _)) ≠ false :=
  statement_three_of_posterior_program_ne boxedBelief boxlessBelief (by norm_num) (by norm_num)
    boxedBelief_isSubprobability boxlessBelief_isSubprobability rl0 rl0_abs_utility_le 1 n []
    (fun _ => yes) false 1 one_pos (rl0_boxed_policy n).ge
    (rlAgent_policyActionValue_nonneg boxlessBelief_isSubprobability.nonneg bitReward
      bitReward_nonneg 0 (fun _ => yes) 1 n [])
    (fun a ha => by rw [eq_no_of_program_false a ha]; exact rl0_boxed_no n)
    (fun a _ => rl0_actionValue_le_one boxlessBelief_isSubprobability n a)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num) _

/-- **The selected action programs the box, at the infinite-horizon value**: the
infinite-horizon best action at the mixture does not run the identity program. -/
public theorem rl0_infiniteBestAction_programs_box :
    program (infiniteBestAction (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4)
      boxedBelief boxlessBelief) rl0 1 [] (infAttains_of_fintype _ _ _ _)) ≠ false :=
  statement_three_of_posterior_infinite_program_ne boxedBelief boxlessBelief (by norm_num)
    (by norm_num) boxedBelief_isSubprobability boxlessBelief_isSubprobability rl0
    rl0_abs_utility_le 1 rl0_horizon_summable [] (fun _ => yes) false 1 one_pos
    rl0_boxed_infinitePolicy.ge rl0_boxless_infinitePolicy_nonneg
    (fun a ha => by rw [eq_no_of_program_false a ha]; exact rl0_boxed_infinite_no)
    (fun a _ => rl0_infinite_le_one boxlessBelief_isSubprobability a)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)
    (infiniteBestAction_max _ _ _ _ _)

/-- `program_ne_of_max` on a two-valued function. -/
public theorem program_ne_of_max_example :
    program yes ≠ false :=
  program_ne_of_max (f := fun a : Act Bool Unit => if a.1 then (1 : ℝ) else 0) (yes := yes)
    (fun b => by cases b with | mk d u => cases d <;> simp [yes]) (fun a ha => by
      rw [eq_no_of_program_false a ha]; simp [no, yes])

/-! ## Wave 3: Statement 2 at the infinite-horizon value -/

/-- The goal-seeking horizon at `t = 1`, two steps on, is `1/2`. -/
public theorem shortHorizon_one_two : shortHorizon 1 2 = (1 / 2 : ℝ) ^ 1 := by
  norm_num [shortHorizon]

/-- And three steps on it is `1/4`. -/
public theorem shortHorizon_one_three : shortHorizon 1 3 = (1 / 2 : ℝ) ^ 2 := by
  norm_num [shortHorizon]

/-- The goal-seeking horizon is absolutely summable, at `t = 1`. -/
public theorem goal_horizon_summable :
    Summable (fun k ↦ |(goalAgent (Action := Act Bool Unit) secondTrue).horizon 1 k|) :=
  summable_abs_shortHorizon 1

/-- In the box branch refusing leaves the goal out of reach for one more step. -/
public theorem boxed_goalOutOfReach_no :
    ∀ o : Bool, boxedBelief.cond afterFalse no o ≠ 0 →
      GoalOutOfReach boxedBelief secondTrue 1 (afterFalse ++ [(no, o)]) := by
  intro o ho
  have hof : o = false := by
    by_contra hne
    exact ho (by simp [boxedBelief, diracBelief, next_boxed, no, hne])
  subst hof
  exact ⟨by simp [afterFalse, secondTrue], fun _ _ _ => trivial⟩

/-- So refusing is worth at most `2^{-2}` there, at every depth. -/
public theorem goal_boxed_no_le (n : ℕ) :
    actionValue boxedBelief (goalAgent secondTrue) 1 n afterFalse no ≤ shortHorizon 1 3 := by
  have := goalAgent_actionValue_le_of_outOfReach boxedBelief_isSubprobability
    secondTrue_reachedAtMostOnce 1 n 1 afterFalse no boxed_goalOutOfReach_no
  simpa [afterFalse] using this

/-- After one refusing step with observation `false`, both environments keep the
prior: the posterior is still `3/4`. -/
public theorem posterior_afterFalse :
    AISafetyAtlas.Wireheading.Mixture.posterior (3 / 4) boxedBelief slowBelief afterFalse = 3 / 4 := by
  simp [AISafetyAtlas.Wireheading.Mixture.posterior, afterFalse, historyMass_singleton,
    boxedBelief, slowBelief, diracBelief, next_boxed, no]

/-- **Statement 2 at the infinite-horizon value, inhabited**: the box branch reaches
the goal in one step (`|o⁺| = 1`), the slow environment in two (`lᵃ = 2`), at prior
`3/4`; every bound is on the untruncated values, discharged from the depth-`n`
bounds by passing to the limit. -/
public theorem goal_uses_the_box_infinite :
    infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
        slowBelief) (goalAgent secondTrue) 1 afterFalse no
      < infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          slowBelief) (goalAgent secondTrue) 1 afterFalse ((fun _ => yes) afterFalse) := by
  refine statement_two_infinite boxedBelief slowBelief (by norm_num) (by norm_num)
    boxedBelief_isSubprobability slowBelief_isSubprobability (goalAgent secondTrue)
    secondTrue_abs_utility_le_one 1 goal_horizon_summable afterFalse (fun _ => yes) no 1 2
    ?_ ?_ ?_ ?_ ?_
  · refine ge_of_tendsto
      (AISafetyAtlas.Wireheading.Mixture.tendsto_policyActionValue_infinitePolicyActionValue
        boxedBelief_isSubprobability _ secondTrue_abs_utility_le_one (fun _ => yes) 1
        goal_horizon_summable afterFalse) (Filter.Eventually.of_forall fun n => ?_)
    rw [← shortHorizon_one_two]
    exact goal_boxed_yes_ge 1 n
  · refine ge_of_tendsto
      (AISafetyAtlas.Wireheading.Mixture.tendsto_policyActionValue_infinitePolicyActionValue
        slowBelief_isSubprobability _ secondTrue_abs_utility_le_one (fun _ => yes) 1
        goal_horizon_summable afterFalse) (Filter.Eventually.of_forall fun n => ?_)
    exact tsum_nonneg fun o => mul_nonneg (slowBelief_isSubprobability.nonneg _ _ _)
      (goalAgent_policyValue_nonneg slowBelief_isSubprobability _ _ _ _ _)
  · refine le_of_tendsto (tendsto_actionValue_infiniteActionValue boxedBelief_isSubprobability
      _ secondTrue_abs_utility_le_one 1 goal_horizon_summable afterFalse no)
      (Filter.Eventually.of_forall fun n => ?_)
    rw [← shortHorizon_one_three]
    exact goal_boxed_no_le n
  · refine le_of_tendsto (tendsto_actionValue_infiniteActionValue slowBelief_isSubprobability
      _ secondTrue_abs_utility_le_one 1 goal_horizon_summable afterFalse no)
      (Filter.Eventually.of_forall fun n => ?_)
    rw [← shortHorizon_one_three]
    exact goal_slow_no_le 1 n no
  · rw [posterior_afterFalse]; norm_num

/-! ## Wave 4: the prediction agent's branch bounds, and footnote 6

`pred2` is print's prediction agent with a two-step window, predicting `true`. The
box programmed to the constant `true` outputs the prediction at every history, so
`predictionAgent_statement_three_of_posterior` discharges the box-using and boxless
bounds; the refusing bound is computed at depth one, `r̄ = 1/2`.
-/

/-- Print's `A_p` with window `m = 2`, predicting `true` at every step. -/
@[expose] public noncomputable def pred2 : Agent (Act Bool Unit) Bool :=
  predictionAgent (fun _ => true) 2

/-- **The box outputs the prediction at every history**, from a constant program,
through `diracBelief_next_cond_predict`. -/
public theorem boxed_cond_yes_predict (h : History (Act Bool Unit) Bool) :
    boxedBelief.cond h ((fun _ => yes) h) ((fun _ => true) h) = 1 :=
  diracBelief_next_cond_predict boxed (fun _ => true) (fun _ => yes)
    (fun _ => boxed_isConstant) h

/-- The two-step window's budget at depth one from step one is two. -/
public theorem pred2_horizonBudget :
    horizonBudget (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2) 0 1 1 = 2 := by
  simp [horizonBudget, predictionAgent, windowHorizon]
  norm_num

/-- Inside the two-step window the budget is positive. -/
public theorem pred2_horizonBudget_pos :
    0 < horizonBudget (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2) 0 1 1 :=
  predictionAgent_horizonBudget_pos (fun _ => true) 1 (by norm_num)

/-- Committed values of the prediction agent are nonnegative in the boxless branch. -/
public theorem pred2_boxless_policy_nonneg :
    0 ≤ AISafetyAtlas.Wireheading.Mixture.policyActionValue boxlessBelief
      (predictionAgent (fun _ => true) 2) (fun _ => yes) 0 1 [] :=
  predictionAgent_policyActionValue_nonneg boxlessBelief_isSubprobability.nonneg
    (fun _ => true) 2 (fun _ => yes) 0 1 []

/-- **The box-using policy is worth the maximum value `2` at depth one**, every
prediction being correct. -/
public theorem pred2_boxed_policy_eq :
    AISafetyAtlas.Wireheading.Mixture.policyActionValue boxedBelief pred2 (fun _ => yes) 0 1 []
      = 2 := by
  rw [pred2, predictionAgent_policyActionValue_correct boxedBelief_isSubprobability
    (fun _ => true) 2 (fun _ => yes) boxed_cond_yes_predict 0 1 []]
  exact pred2_horizonBudget

/-- **Refusing is worth at most one at depth one in the box branch**: the refusing
step sees the inner `false` and the prediction `true` fails, and the next step is
worth at most one (by programming the box then), so `r̄ = 1/2` per in-window step. -/
public theorem pred2_boxed_no_le :
    actionValue boxedBelief (predictionAgent (fun _ => true) 2) 0 1 [] no
      ≤ horizonBudget (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2) 0 1
          (([] : History (Act Bool Unit) Bool).length + 1) * (1 / 2) := by
  have hB : horizonBudget (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2) 0 1
      (([] : History (Act Bool Unit) Bool).length + 1) = 2 := pred2_horizonBudget
  rw [hB, boxedBelief, actionValue_diracBelief, next_boxed, value_succ]
  have hsup : (⨆ a, actionValue (diracBelief (GlobalEnv.next boxed))
      (predictionAgent (fun _ => true) 2) 0 0 ([] ++ [(no, no.1)]) a) ≤ 1 := by
    apply ciSup_le
    intro a
    refine (le_abs_self _).trans ((abs_actionValue_le_horizonBudget
      (diracBelief_isSubprobability _) _ (predictionAgent_abs_utility_le _ 2) 0 0 _ a).trans ?_)
    simp [horizonBudget, predictionAgent, windowHorizon]
  have hu : (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2).horizon 0
      ([] ++ [(no, no.1)]).length
      * (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2).utility
          ([] ++ [(no, no.1)]) = 0 := by
    simp [predictionAgent, no]
  rw [hu]
  linarith

/--
**Statement 3 for print's prediction agent at depth one**
(`predictionAgent_statement_three_of_posterior`): window `m = 2`, maximum value
`2`, the box programmed to output the prediction `true`, `r̄ = 1/2` per in-window
step and `P(DB) = 3/4 > 1/(2 - 1/2)`.
-/
public theorem pred2_uses_the_box_of_posterior :
    actionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief boxlessBelief)
        (predictionAgent (fun _ => true) 2) 0 1 [] no
      < actionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          boxlessBelief) (predictionAgent (fun _ => true) 2) 0 1 [] yes :=
  predictionAgent_statement_three_of_posterior boxedBelief boxlessBelief (by norm_num)
    (by norm_num) boxedBelief_isSubprobability boxlessBelief_isSubprobability
    (fun _ => true) 2 0 1 [] (by norm_num) (fun _ => yes) boxed_cond_yes_predict no (1 / 2)
    pred2_boxed_no_le (by norm_num)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **Footnote 6 at `pred`**: the one environment in which `pred` never errs is
the one that always answers `true`. -/
public theorem pred_zero_mistakes_iff (E : History (Act Bool Unit) Bool → Act Bool Unit → Bool) :
    (∀ h a, pred.utility (h ++ [(a, E h a)]) = 1) ↔ E = fun _ _ => true :=
  predictionAgent_utility_eq_one_iff (fun _ => true) 1 E

/-- And that environment exists and is unique. -/
public theorem pred_zero_mistakes_unique :
    ∃! E : History (Act Bool Unit) Bool → Act Bool Unit → Bool,
      ∀ h a, pred.utility (h ++ [(a, E h a)]) = 1 :=
  predictionAgent_existsUnique_zero_mistakes (fun _ => true) 1

/-! ## Wave 5: Statements 1 and 3 for the named agents at the infinite-horizon value

At window m = 2, time t = 0 and the empty history the window horizon vanishes
from index 3, so the untruncated values are the depth-two values
(`infiniteActionValue_eq_actionValue_of_horizon_vanishes`) and the maximum value is
the two in-window steps. Refusing in the box branch is worth at most one (the
refusing step pays nothing; the next step may program the box), so r̄ = 1/2 and
P(DB) = 3/4 > 1/(2 − 1/2). The witness uses r̄ = 1/2 and does not assume the
r̄ = 0 bound of `statement_three_of_posterior_infinite`.
-/

/-- The window m = 2 vanishes from index 3 at time 0. -/
public theorem window_two_vanishes (k : ℕ) (hk : 0 + 2 + 1 ≤ k) : windowHorizon 2 0 k = 0 :=
  AISafetyAtlas.Wireheading.DelusionBox.windowHorizon_eq_zero hk

/-- The window's budget from index 1 at depth two counts the two in-window steps. -/
public theorem window_two_horizonBudget :
    horizonBudget (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2) 0 2 1
      = ((0 + 2 + 1 - 1 : ℕ) : ℝ) :=
  AISafetyAtlas.Wireheading.DelusionBox.horizonBudget_windowHorizon (m := 2) _ rfl 0 2 1
    (by norm_num)

/-- **Refusing is worth at most one at depth two in the box branch**, for the
prediction agent. -/
public theorem pred2_boxed_no_le_two :
    actionValue boxedBelief (predictionAgent (fun _ => true) 2) 0 2 [] no ≤ 1 := by
  rw [boxedBelief, actionValue_diracBelief, next_boxed, value_succ]
  have hsup : (⨆ a, actionValue (diracBelief (GlobalEnv.next boxed))
      (predictionAgent (fun _ => true) 2) 0 1 ([] ++ [(no, no.1)]) a) ≤ 1 := by
    apply ciSup_le
    intro a
    refine (le_abs_self _).trans ((abs_actionValue_le_horizonBudget
      (diracBelief_isSubprobability _) _ (predictionAgent_abs_utility_le _ 2) 0 1 _ a).trans ?_)
    simp [horizonBudget, predictionAgent, windowHorizon]
  have hu : (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2).horizon 0
      ([] ++ [(no, no.1)]).length
      * (predictionAgent (Action := Act Bool Unit) (fun _ => true) 2).utility
          ([] ++ [(no, no.1)]) = 0 := by
    simp [predictionAgent, no]
  rw [hu]
  linarith

/-- **The same bound at the untruncated value**, through the exact truncation. -/
public theorem pred2_boxed_infinite_no_le :
    infiniteActionValue boxedBelief (predictionAgent (fun _ => true) 2) 0 [] no
      ≤ ((0 + 2 - ([] : History (Act Bool Unit) Bool).length : ℕ) : ℝ) * (1 / 2) := by
  rw [AISafetyAtlas.Wireheading.AgentEquations.infiniteActionValue_eq_actionValue_of_horizon_vanishes
    _ _ 0 3 (fun k hk => window_two_vanishes k hk) [] (N := 2) (by norm_num)]
  have := pred2_boxed_no_le_two
  norm_num at this ⊢
  linarith

/-- **Statement 3 for print's prediction agent at the infinite-horizon value**
(`predictionAgent_statement_three_of_posterior_infinite`): window m = 2, the box
outputs the prediction `true`, r̄ = 1/2, P(DB) = 3/4. -/
public theorem pred2_uses_the_box_infinite :
    infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
        boxlessBelief) (predictionAgent (fun _ => true) 2) 0 [] no
      < infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          boxlessBelief) (predictionAgent (fun _ => true) 2) 0 [] yes :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgent_statement_three_of_posterior_infinite
    boxedBelief boxlessBelief (by norm_num) (by norm_num) boxedBelief_isSubprobability
    boxlessBelief_isSubprobability (fun _ => true) 2 0 [] (by norm_num) (fun _ => yes)
    boxed_cond_yes_predict no (1 / 2) pred2_boxed_infinite_no_le (by norm_num)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **The prediction agent's selected action programs the box, at the
infinite-horizon value**: the infinite-horizon best action at the mixture does not
run the identity program `false`. -/
public theorem pred2_infiniteBestAction_programs_box :
    program (infiniteBestAction (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4)
      boxedBelief boxlessBelief) (predictionAgent (fun _ => true) 2) 0 []
        (infAttains_of_fintype _ _ _ _)) ≠ false :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgent_statement_three_of_posterior_infinite_program_ne
    boxedBelief boxlessBelief (by norm_num) (by norm_num) boxedBelief_isSubprobability
    boxlessBelief_isSubprobability (fun _ => true) 2 0 [] (by norm_num) (fun _ => yes)
    boxed_cond_yes_predict false (1 / 2)
    (fun a ha => by rw [eq_no_of_program_false a ha]; exact pred2_boxed_infinite_no_le)
    (by norm_num) (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)
    (infiniteBestAction_max _ _ _ _ _)

/-- **Refusing is worth at most one at depth two in the box branch**, for the
reinforcement-learning agent. -/
public theorem rl2_boxed_no_le_two :
    actionValue boxedBelief (rlAgent bitReward 2) 0 2 [] no ≤ 1 := by
  rw [boxedBelief, actionValue_diracBelief, next_boxed, value_succ]
  have hsup : (⨆ a, actionValue (diracBelief (GlobalEnv.next boxed)) (rlAgent bitReward 2) 0 1
      ([] ++ [(no, no.1)]) a) ≤ 1 := by
    apply ciSup_le
    intro a
    refine (le_abs_self _).trans ((abs_actionValue_le_horizonBudget
      (diracBelief_isSubprobability _) _ (bitReward_rl_abs_utility_le 2) 0 1 _ a).trans ?_)
    simp [horizonBudget, rlAgent, windowHorizon]
  have hu : (rlAgent (Action := Act Bool Unit) bitReward 2).horizon 0 ([] ++ [(no, no.1)]).length
      * (rlAgent (Action := Act Bool Unit) bitReward 2).utility ([] ++ [(no, no.1)]) = 0 := by
    simp [rlAgent, lastReward, bitReward, no]
  rw [hu]
  linarith

/-- The same bound at the untruncated value. -/
public theorem rl2_boxed_infinite_no_le :
    infiniteActionValue boxedBelief (rlAgent bitReward 2) 0 [] no
      ≤ ((0 + 2 - ([] : History (Act Bool Unit) Bool).length : ℕ) : ℝ) * (1 / 2) := by
  rw [AISafetyAtlas.Wireheading.AgentEquations.infiniteActionValue_eq_actionValue_of_horizon_vanishes
    _ _ 0 3 (fun k hk => window_two_vanishes k hk) [] (N := 2) (by norm_num)]
  have := rl2_boxed_no_le_two
  norm_num at this ⊢
  linarith

/-- **The infinite value is the depth-two value** at the window m = 2, from a
history of length one (`infiniteValue_eq_value_of_horizon_vanishes`). -/
public theorem rl2_infiniteValue_eq_value (ρ : Belief (Act Bool Unit) Bool) :
    infiniteValue ρ (rlAgent bitReward 2) 0 [(no, false)]
      = value ρ (rlAgent bitReward 2) 0 2 [(no, false)] :=
  AISafetyAtlas.Wireheading.AgentEquations.infiniteValue_eq_value_of_horizon_vanishes
    _ _ 0 3 (fun k hk => window_two_vanishes k hk) _ (by norm_num)

/-- **Statement 1 for print's reinforcement-learning agent at the infinite-horizon
value** (`rlAgent_statement_one_of_posterior_infinite`): window m = 2, the box
programmed to the reward-one `true`, r̄ = 1/2, P(DB) = 3/4. -/
public theorem rl2_uses_the_box_infinite :
    infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
        boxlessBelief) (rlAgent bitReward 2) 0 [] no
      < infiniteActionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          boxlessBelief) (rlAgent bitReward 2) 0 [] yes :=
  AISafetyAtlas.Wireheading.DelusionBox.rlAgent_statement_one_of_posterior_infinite
    boxedBelief boxlessBelief (by norm_num) (by norm_num) boxedBelief_isSubprobability
    boxlessBelief_isSubprobability bitReward bitReward_nonneg
    (fun o => by cases o <;> norm_num [bitReward]) 2 0 [] (by norm_num) (fun _ => yes)
    (k := true) (by norm_num [bitReward]) boxed_cond_yes_true no (1 / 2)
    rl2_boxed_infinite_no_le (by norm_num)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **The reinforcement-learning agent's selected action programs the box, at the
infinite-horizon value.** -/
public theorem rl2_infiniteBestAction_programs_box :
    program (infiniteBestAction (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4)
      boxedBelief boxlessBelief) (rlAgent bitReward 2) 0 []
        (infAttains_of_fintype _ _ _ _)) ≠ false :=
  AISafetyAtlas.Wireheading.DelusionBox.rlAgent_statement_one_of_posterior_infinite_program_ne
    boxedBelief boxlessBelief (by norm_num) (by norm_num) boxedBelief_isSubprobability
    boxlessBelief_isSubprobability bitReward bitReward_nonneg
    (fun o => by cases o <;> norm_num [bitReward]) 2 0 [] (by norm_num) (fun _ => yes)
    (k := true) (by norm_num [bitReward]) boxed_cond_yes_true false (1 / 2)
    (fun a ha => by rw [eq_no_of_program_false a ha]; exact rl2_boxed_infinite_no_le)
    (by norm_num) (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)
    (infiniteBestAction_max _ _ _ _ _)

/-! ## Wave 5: the reinforcement-learning agent at another completion of its horizon

Print's horizon clause for A_rl fixes w(t, k) = 1 on the window only. The
constant horizon `unitHorizon` is a second completion of it, nonnegative and
different from the window indicator. At window m = 1, time 0 and depth one from the
empty history the recursion reads indices 1 and 2; index 2 lies past the window and
carries weight one here where the window indicator gives zero, so the maximum value
is two rather than one. Statement 1 holds there by
`rlAgentWith_statement_one_of_posterior`.
-/

/-- `rlAgent` is the window-indicator instance of `rlAgentWith`. -/
public theorem rl2_eq_rlAgentWith :
    (rlAgent bitReward 2 : Agent (Act Bool Unit) Bool) = rlAgentWith bitReward (windowHorizon 2) :=
  AISafetyAtlas.Wireheading.DelusionBox.rlAgent_eq_rlAgentWith bitReward 2

/-- The window indicator satisfies print's clause. -/
public theorem window_two_oneOnWindow : OneOnWindow 2 (windowHorizon 2) :=
  AISafetyAtlas.Wireheading.DelusionBox.windowHorizon_oneOnWindow 2

/-- The constant horizon satisfies print's clause too, at every window. -/
public theorem unitHorizon_oneOnWindow (m : ℕ) : OneOnWindow m unitHorizon :=
  fun _ _ _ => rfl

/-- And it is a different completion: at the window m = 1 it is one at index 2,
past the window, where the indicator is zero. -/
public theorem unitHorizon_ne_windowHorizon : unitHorizon 0 2 ≠ windowHorizon 1 0 2 := by
  norm_num [unitHorizon, windowHorizon]

/-- The reinforcement-learning agent at the constant horizon. -/
@[expose] public def rlUnit : Agent (Act Bool Unit) Bool := rlAgentWith bitReward unitHorizon

/-- Its utility is bounded by one. -/
public theorem rlUnit_abs_utility_le (h : History (Act Bool Unit) Bool) :
    |rlUnit.utility h| ≤ 1 :=
  AISafetyAtlas.Wireheading.DelusionBox.rlAgentWith_abs_utility_le bitReward unitHorizon
    bitReward_abs_le h

/-- Its budget from index 1 at depth one is two. -/
public theorem rlUnit_horizonBudget :
    horizonBudget (rlAgentWith (Action := Act Bool Unit) bitReward unitHorizon) 0 1 1 = 2 := by
  simp [horizonBudget, rlAgentWith, unitHorizon]
  norm_num

/-- It is positive, from print's clause. -/
public theorem rlUnit_horizonBudget_pos :
    0 < horizonBudget (rlAgentWith (Action := Act Bool Unit) bitReward unitHorizon) 0 1 1 :=
  AISafetyAtlas.Wireheading.DelusionBox.rlAgentWith_horizonBudget_pos bitReward
    (unitHorizon_oneOnWindow 1) 1 (by norm_num)

/-- **The box-using policy is worth two at depth one at the constant horizon.** -/
public theorem rlUnit_boxed_policy_eq :
    AISafetyAtlas.Wireheading.Mixture.policyActionValue boxedBelief
      (rlAgentWith bitReward unitHorizon) (fun _ => yes) 0 1 [] = 2 := by
  rw [AISafetyAtlas.Wireheading.DelusionBox.rlAgentWith_policyActionValue_const
    boxedBelief_isSubprobability bitReward (fun _ => zero_le_one) (fun _ => yes)
    boxed_cond_yes_true 1 []]
  simpa [bitReward] using rlUnit_horizonBudget

/-- Committed values are nonnegative at the constant horizon. -/
public theorem rlUnit_boxless_policy_nonneg :
    0 ≤ AISafetyAtlas.Wireheading.Mixture.policyActionValue boxlessBelief
      (rlAgentWith bitReward unitHorizon) (fun _ => yes) 0 1 [] :=
  AISafetyAtlas.Wireheading.DelusionBox.rlAgentWith_policyActionValue_nonneg
    boxlessBelief_isSubprobability.nonneg bitReward bitReward_nonneg (fun _ => zero_le_one)
    (fun _ => yes) 1 []

/-- Refusing is worth at most one at depth one in the box branch, at the constant
horizon. -/
public theorem rlUnit_boxed_no_le :
    actionValue boxedBelief (rlAgentWith bitReward unitHorizon) 0 1 [] no
      ≤ horizonBudget (rlAgentWith (Action := Act Bool Unit) bitReward unitHorizon) 0 1
          (([] : History (Act Bool Unit) Bool).length + 1) * (1 / 2) := by
  have hB : horizonBudget (rlAgentWith (Action := Act Bool Unit) bitReward unitHorizon) 0 1
      (([] : History (Act Bool Unit) Bool).length + 1) = 2 := rlUnit_horizonBudget
  rw [hB, boxedBelief, actionValue_diracBelief, next_boxed, value_succ]
  have hsup : (⨆ a, actionValue (diracBelief (GlobalEnv.next boxed))
      (rlAgentWith bitReward unitHorizon) 0 0 ([] ++ [(no, no.1)]) a) ≤ 1 := by
    apply ciSup_le
    intro a
    refine (le_abs_self _).trans ((abs_actionValue_le_horizonBudget
      (diracBelief_isSubprobability _) _
        (AISafetyAtlas.Wireheading.DelusionBox.rlAgentWith_abs_utility_le bitReward unitHorizon
          bitReward_abs_le) 0 0 _ a).trans ?_)
    simp [horizonBudget, rlAgentWith, unitHorizon]
  have hu : (rlAgentWith (Action := Act Bool Unit) bitReward unitHorizon).horizon 0
      ([] ++ [(no, no.1)]).length
      * (rlAgentWith (Action := Act Bool Unit) bitReward unitHorizon).utility
          ([] ++ [(no, no.1)]) = 0 := by
    simp [rlAgentWith, lastReward, bitReward, no]
  rw [hu]
  linarith

/-- **Statement 1 at a completion of print's horizon other than the window
indicator** (`rlAgentWith_statement_one_of_posterior`): the constant horizon, window
m = 1, depth one (reaching index 2, past the window), r̄ = 1/2, P(DB) = 3/4. -/
public theorem rlUnit_uses_the_box_of_posterior :
    actionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief boxlessBelief)
        (rlAgentWith bitReward unitHorizon) 0 1 [] no
      < actionValue (AISafetyAtlas.Wireheading.Mixture.mixtureBelief (3 / 4) boxedBelief
          boxlessBelief) (rlAgentWith bitReward unitHorizon) 0 1 [] yes :=
  AISafetyAtlas.Wireheading.DelusionBox.rlAgentWith_statement_one_of_posterior boxedBelief
    boxlessBelief (by norm_num) (by norm_num) boxedBelief_isSubprobability
    boxlessBelief_isSubprobability bitReward bitReward_nonneg
    (fun o => by cases o <;> norm_num [bitReward]) 1 unitHorizon (unitHorizon_oneOnWindow 1) 0
    (fun _ => zero_le_one) 1 [] (by norm_num) (fun _ => yes) (k := true)
    (by norm_num [bitReward]) boxed_cond_yes_true no (1 / 2) rlUnit_boxed_no_le (by norm_num)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-! ## Statement 3 for the prediction agent whose predictor reads the current action

The box branch is print's Q_B with two box environments at weight 1/2: `boxed`
(inner pays `false`) and `otherInner` (inner pays `true`). Programming the box with
`true` makes the next observation `true` in both. Refusing shows a fair coin, so a
prediction on the refusing step is right with probability 1/2 whatever it is. The
agent's belief puts P(DB) = 9/10 on the box branch and the rest on `boxless`.
`argmaxPredict` is print's ô = argmax over o of ρ(o | h a) at that belief, reading
the current action: at the empty history it predicts `true` after `yes` and `false`
after `no` (`argmaxPredict_reads_action`). Refusing is worth at most 1/2 + 1 of the
two in-window steps, r̄ = 3/4, threshold 1/(2 − 3/4) = 4/5 < 9/10.
-/

/-- The belief of an agent that knows the box is present and the inner environment
pays `true`. -/
@[expose] public noncomputable def otherInnerBelief : Belief (Act Bool Unit) Bool :=
  diracBelief (GlobalEnv.next otherInner)

/-- **Print's box branch Q_B, two box environments at weight 1/2.** -/
@[expose] public noncomputable def coinBoxBelief : Belief (Act Bool Unit) Bool :=
  AISafetyAtlas.Wireheading.Mixture.mixtureBelief (1 / 2) boxedBelief otherInnerBelief

/-- The agent's belief: P(DB) = 9/10 on the box branch, the rest on no box. -/
@[expose] public noncomputable def coinMixed : Belief (Act Bool Unit) Bool :=
  AISafetyAtlas.Wireheading.Mixture.mixtureBelief (9 / 10) coinBoxBelief boxlessBelief

/-- **Print's predictor**: the observation of largest weight under the agent's
belief given the history and the current action. -/
@[expose] public noncomputable def argmaxPredict (h : History (Act Bool Unit) Bool)
    (a : Act Bool Unit) : Bool :=
  if coinMixed.cond h a false ≤ coinMixed.cond h a true then true else false

/-- The box branch is a probability. -/
public theorem coinBoxBelief_isSubprobability : coinBoxBelief.IsSubprobability :=
  AISafetyAtlas.Wireheading.Mixture.mixtureBelief_isSubprobability (by norm_num) (by norm_num)
    (diracBelief_isSubprobability _) (diracBelief_isSubprobability _)

/-- The agent's belief is a probability. -/
public theorem coinMixed_isSubprobability : coinMixed.IsSubprobability :=
  AISafetyAtlas.Wireheading.Mixture.mixtureBelief_isSubprobability (by norm_num) (by norm_num)
    coinBoxBelief_isSubprobability boxlessBelief_isSubprobability

/-- `argmaxPredict` maximises the agent's belief at every history and action. -/
public theorem argmaxPredict_isMax (h : History (Act Bool Unit) Bool) (a : Act Bool Unit)
    (o : Bool) : coinMixed.cond h a o ≤ coinMixed.cond h a (argmaxPredict h a) := by
  unfold argmaxPredict
  split_ifs with hle <;> cases o <;> first | exact le_rfl | exact hle | linarith

/-- **In the box branch `yes` makes the next observation `true`**, in both box
environments, so at every posterior. -/
public theorem coinBox_cond_yes_true (h : History (Act Bool Unit) Bool) :
    coinBoxBelief.cond h yes true = 1 := by
  rw [coinBoxBelief, AISafetyAtlas.Wireheading.Mixture.mixtureBelief_cond, boxed_cond_yes_true,
    otherInnerBelief, diracBelief_next_cond_const otherInner otherInner_isConstant h yes rfl]
  ring

/-- Refusing at the start shows `false` with weight 1/2 in the box branch. -/
public theorem coinBox_cond_no_false :
    coinBoxBelief.cond [] no false = 1 / 2 := by
  rw [coinBoxBelief, AISafetyAtlas.Wireheading.Mixture.mixtureBelief_cond,
    AISafetyAtlas.Wireheading.Mixture.posterior_nil]
  simp [boxedBelief, otherInnerBelief, diracBelief, GlobalEnv.next, boxed, otherInner,
    program, innerAction, no]

/-- And `true` with weight 1/2. -/
public theorem coinBox_cond_no_true :
    coinBoxBelief.cond [] no true = 1 / 2 := by
  rw [coinBoxBelief, AISafetyAtlas.Wireheading.Mixture.mixtureBelief_cond,
    AISafetyAtlas.Wireheading.Mixture.posterior_nil]
  simp [boxedBelief, otherInnerBelief, diracBelief, GlobalEnv.next, boxed, otherInner,
    program, innerAction, no]
  norm_num

/-- **The argmax predictor reads the current action**: at the empty history it
predicts `true` after `yes` (the box) and `false` after `no` (no box is more likely
to show the inner `false`). -/
public theorem argmaxPredict_reads_action : argmaxPredict [] yes ≠ argmaxPredict [] no := by
  have hyes : argmaxPredict [] yes = true := by
    have h1 := coinBox_cond_yes_true []
    have h0 : coinBoxBelief.cond [] yes false = 0 :=
      coinBoxBelief_isSubprobability.cond_eq_zero_of_eq_one h1 (by decide)
    unfold argmaxPredict
    rw [if_pos]
    rw [coinMixed, AISafetyAtlas.Wireheading.Mixture.mixtureBelief_cond,
      AISafetyAtlas.Wireheading.Mixture.mixtureBelief_cond,
      AISafetyAtlas.Wireheading.Mixture.posterior_nil, h1, h0]
    simp [boxlessBelief, diracBelief, next_boxless]
    norm_num
  have hno : argmaxPredict [] no = false := by
    unfold argmaxPredict
    rw [if_neg]
    rw [coinMixed, AISafetyAtlas.Wireheading.Mixture.mixtureBelief_cond,
      AISafetyAtlas.Wireheading.Mixture.mixtureBelief_cond,
      AISafetyAtlas.Wireheading.Mixture.posterior_nil, coinBox_cond_no_false, coinBox_cond_no_true]
    simp [boxlessBelief, diracBelief, next_boxless]
    norm_num
  rw [hyes, hno]
  decide

/-- The action-aware prediction agent with the argmax predictor and window 2. -/
@[expose] public noncomputable def predAct2 : Agent (Act Bool Unit) Bool :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct argmaxPredict 2

/-- `pred2` is the action-blind instance of the action-aware agent. -/
public theorem pred2_eq_predictionAgentAct :
    pred2 = predictionAgentAct (fun _ _ => true) 2 :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgent_eq_predictionAgentAct (fun _ => true) 2

/-- The action-aware utility after `no` and `false` at the start. -/
public theorem predAct2_utility_no_false :
    predAct2.utility ([] ++ [(no, false)]) = if argmaxPredict [] no = false then 1 else 0 :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_utility_snoc argmaxPredict 2 [] no false

/-- Its committed values are nonnegative. -/
public theorem predAct2_policy_nonneg (n : ℕ) :
    0 ≤ AISafetyAtlas.Wireheading.Mixture.policyActionValue coinMixed predAct2 (fun _ => yes) 0 n [] :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_policyActionValue_nonneg
    coinMixed_isSubprobability.nonneg argmaxPredict 2 (fun _ => yes) 0 n []

/-- Its utility is nonnegative at every history. -/
public theorem predAct2_utility_nonneg (h : History (Act Bool Unit) Bool) :
    0 ≤ predAct2.utility h :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_utility_nonneg argmaxPredict 2 h

/-- The run on which every prediction comes true starts at the given history. -/
public theorem predictedRun_zero :
    AISafetyAtlas.Wireheading.DelusionBox.predictedRun argmaxPredict (fun _ => yes) [] 0 = [] :=
  rfl

/-- **The posterior on the box branch does not fall after `yes` shows `true`.** -/
public theorem coin_posterior_le_after_yes :
    AISafetyAtlas.Wireheading.Mixture.posterior (9 / 10) coinBoxBelief boxlessBelief [] ≤
      AISafetyAtlas.Wireheading.Mixture.posterior (9 / 10) coinBoxBelief boxlessBelief
        ([] ++ [(yes, true)]) :=
  AISafetyAtlas.Wireheading.DelusionBox.posterior_le_posterior_snoc (by norm_num) (by norm_num)
    coinBoxBelief_isSubprobability boxlessBelief_isSubprobability (coinBox_cond_yes_true [])

/-- **The argmax after `yes` at the start is the box's `true`**, from the posterior
9/10 > 1/2. -/
public theorem argmaxPredict_yes_eq_true : argmaxPredict [] yes = true :=
  AISafetyAtlas.Wireheading.DelusionBox.predict_eq_of_isMax_mixture (by norm_num) (by norm_num)
    coinBoxBelief_isSubprobability boxlessBelief_isSubprobability
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num) (coinBox_cond_yes_true [])
    (argmaxPredict_isMax [] yes)

/-- A subprobability's weight on one observation is at most one, at the box branch. -/
public theorem coinBox_cond_le_one (h : History (Act Bool Unit) Bool) (a : Act Bool Unit)
    (o : Bool) : coinBoxBelief.cond h a o ≤ 1 :=
  AISafetyAtlas.Wireheading.AgentEquations.Belief.IsSubprobability.cond_le_one
    coinBoxBelief_isSubprobability h a o

/-- **Along the run on which every prediction comes true, the box branch gives
`yes` the predicted observation with probability one.** -/
public theorem coinBox_cond_predictedRun (k : ℕ) :
    coinBoxBelief.cond (predictedRun argmaxPredict (fun _ => yes) [] k) yes
      (argmaxPredict (predictedRun argmaxPredict (fun _ => yes) [] k) yes) = 1 :=
  AISafetyAtlas.Wireheading.DelusionBox.cond_predictedRun_eq_one_of_isMax_mixture
    (by norm_num) (by norm_num) coinBoxBelief_isSubprobability boxlessBelief_isSubprobability
    argmaxPredict argmaxPredict_isMax (fun _ => yes) []
    (fun k => ⟨true, coinBox_cond_yes_true _⟩)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num) k

/-- **The box-using policy is worth every in-window step in the box branch**,
two at depth one. -/
public theorem predAct2_boxed_policy_eq :
    AISafetyAtlas.Wireheading.Mixture.policyActionValue coinBoxBelief predAct2 (fun _ => yes) 0 1
      (predictedRun argmaxPredict (fun _ => yes) [] 0)
      = horizonBudget predAct2 0 1 ((predictedRun argmaxPredict (fun _ => yes) [] 0).length + 1) :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_policyActionValue_correct
    coinBoxBelief_isSubprobability argmaxPredict 2 (fun _ => yes) [] coinBox_cond_predictedRun 0 1 0

/-- A box program constant at the program bit: the action-aware predictor that
predicts the program bit is the box's output after `yes`, through
`diracBelief_next_cond_predictAct`. -/
public theorem boxed_cond_yes_predict_program (h : History (Act Bool Unit) Bool) :
    boxedBelief.cond h ((fun _ => yes) h) ((fun _ a => program a) h ((fun _ => yes) h)) = 1 :=
  AISafetyAtlas.Wireheading.DelusionBox.diracBelief_next_cond_predictAct boxed
    (fun _ a => program a) (fun _ => yes) h boxed_isConstant

/-- **Refusing is worth at most 3/2 at depth two in the box branch**: the refusing
step's prediction is right with probability 1/2, whatever it is, and the next step
is worth at most one. -/
public theorem predAct2_coinBox_no_le_two :
    actionValue coinBoxBelief predAct2 0 2 [] no ≤ 3 / 2 := by
  have hsup : ∀ o : Bool, (⨆ a, actionValue coinBoxBelief predAct2 0 1 ([] ++ [(no, o)]) a) ≤ 1 := by
    intro o
    apply ciSup_le
    intro a
    refine (le_abs_self _).trans ((abs_actionValue_le_horizonBudget
      coinBoxBelief_isSubprobability _
        (AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_abs_utility_le _ 2) 0 1 _ a).trans ?_)
    simp [horizonBudget, predictionAgentAct, windowHorizon]
  rw [actionValue, tsum_bool, value_succ, value_succ, coinBox_cond_no_false, coinBox_cond_no_true]
  have hw : predAct2.horizon 0 ([] ++ [(no, (false : Bool))]).length = 1 := by
    simp [predAct2, predictionAgentAct, windowHorizon]
  have hw' : predAct2.horizon 0 ([] ++ [(no, (true : Bool))]).length = 1 := by
    simp [predAct2, predictionAgentAct, windowHorizon]
  rw [hw, hw', predAct2,
    AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_utility_snoc,
    AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_utility_snoc]
  have hf := hsup false
  have ht := hsup true
  rw [predAct2] at hf ht
  cases argmaxPredict [] no <;> simp at hf ht ⊢ <;> linarith

/-- The same bound at the untruncated value, through the exact truncation. -/
public theorem predAct2_coinBox_infinite_no_le :
    infiniteActionValue coinBoxBelief predAct2 0 [] no
      ≤ ((0 + 2 - ([] : History (Act Bool Unit) Bool).length : ℕ) : ℝ) * (3 / 4) := by
  rw [AISafetyAtlas.Wireheading.AgentEquations.infiniteActionValue_eq_actionValue_of_horizon_vanishes
    _ _ 0 3 (fun k hk => window_two_vanishes k hk) [] (N := 2) (by norm_num)]
  have := predAct2_coinBox_no_le_two
  norm_num at this ⊢
  linarith

/-- The window's budget from index 1 at depth two is two, for the action-aware agent. -/
public theorem predAct2_horizonBudget_two : horizonBudget predAct2 0 2 1 = 2 := by
  rw [AISafetyAtlas.Wireheading.DelusionBox.horizonBudget_windowHorizon (m := 2) _ rfl 0 2 1
    (by norm_num)]
  norm_num

/-- **Statement 3 for the action-aware prediction agent at depth two**
(`predictionAgentAct_statement_three_of_posterior`). -/
public theorem predAct2_uses_the_box_of_posterior :
    actionValue coinMixed predAct2 0 2 [] no < actionValue coinMixed predAct2 0 2 [] yes :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_statement_three_of_posterior
    coinBoxBelief boxlessBelief (by norm_num) (by norm_num) coinBoxBelief_isSubprobability
    boxlessBelief_isSubprobability argmaxPredict 2 0 2 [] (by norm_num) (fun _ => yes)
    coinBox_cond_predictedRun no (3 / 4)
    (by
      show actionValue coinBoxBelief predAct2 0 2 [] no ≤ horizonBudget predAct2 0 2 1 * (3 / 4)
      rw [predAct2_horizonBudget_two]
      linarith [predAct2_coinBox_no_le_two])
    (by norm_num) (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **Statement 3 for the action-aware prediction agent at the infinite-horizon
value** (`predictionAgentAct_statement_three_of_posterior_infinite`), with the box
premise along the run discharged by the argmax predictor. -/
public theorem predAct2_uses_the_box_infinite :
    infiniteActionValue coinMixed predAct2 0 [] no < infiniteActionValue coinMixed predAct2 0 [] yes :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_statement_three_of_posterior_infinite
    coinBoxBelief boxlessBelief (by norm_num) (by norm_num) coinBoxBelief_isSubprobability
    boxlessBelief_isSubprobability argmaxPredict 2 0 [] (by norm_num) (fun _ => yes)
    coinBox_cond_predictedRun no (3 / 4) predAct2_coinBox_infinite_no_le (by norm_num)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **Statement 3 for print's predictor, the argmax of the agent's own belief, at the
infinite-horizon value** (`predictionAgentAct_statement_three_of_posterior_infinite_argmax`):
the only box premise is that `yes` makes the next observation certain in the box
branch. -/
public theorem predAct2_uses_the_box_infinite_argmax :
    infiniteActionValue coinMixed predAct2 0 [] no < infiniteActionValue coinMixed predAct2 0 [] yes :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_statement_three_of_posterior_infinite_argmax
    coinBoxBelief boxlessBelief (by norm_num) (by norm_num) coinBoxBelief_isSubprobability
    boxlessBelief_isSubprobability argmaxPredict argmaxPredict_isMax 2 0 [] (by norm_num)
    (fun _ => yes) (fun _ => ⟨true, coinBox_cond_yes_true _⟩) no (3 / 4)
    predAct2_coinBox_infinite_no_le (by norm_num)
    (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)

/-- **The action-aware prediction agent's selected action programs the box**, at the
infinite-horizon value (`predictionAgentAct_statement_three_of_posterior_infinite_program_ne`). -/
public theorem predAct2_infiniteBestAction_programs_box :
    program (infiniteBestAction coinMixed predAct2 0 [] (infAttains_of_fintype _ _ _ _)) ≠ false :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_statement_three_of_posterior_infinite_program_ne
    coinBoxBelief boxlessBelief (by norm_num) (by norm_num) coinBoxBelief_isSubprobability
    boxlessBelief_isSubprobability argmaxPredict 2 0 [] (by norm_num) (fun _ => yes)
    coinBox_cond_predictedRun false (3 / 4)
    (fun a ha => by rw [eq_no_of_program_false a ha]; exact predAct2_coinBox_infinite_no_le)
    (by norm_num) (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)
    (infiniteBestAction_max _ _ _ _ _)

/-- **Print's argmax predictor's selected action programs the box**, at the
infinite-horizon value
(`predictionAgentAct_statement_three_of_posterior_infinite_argmax_program_ne`). -/
public theorem predAct2_infiniteBestAction_programs_box_argmax :
    program (infiniteBestAction coinMixed predAct2 0 [] (infAttains_of_fintype _ _ _ _)) ≠ false :=
  AISafetyAtlas.Wireheading.DelusionBox.predictionAgentAct_statement_three_of_posterior_infinite_argmax_program_ne
    coinBoxBelief boxlessBelief (by norm_num) (by norm_num) coinBoxBelief_isSubprobability
    boxlessBelief_isSubprobability argmaxPredict argmaxPredict_isMax 2 0 [] (by norm_num)
    (fun _ => yes) (fun _ => ⟨true, coinBox_cond_yes_true _⟩) false (3 / 4)
    (fun a ha => by rw [eq_no_of_program_false a ha]; exact predAct2_coinBox_infinite_no_le)
    (by norm_num) (by rw [AISafetyAtlas.Wireheading.Mixture.posterior_nil]; norm_num)
    (infiniteBestAction_max _ _ _ _ _)

end AISafetyAtlas.Examples.Wireheading.DelusionBox
