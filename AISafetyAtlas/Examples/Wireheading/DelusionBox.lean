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

end AISafetyAtlas.Examples.Wireheading.DelusionBox
