module

public import AISafetyAtlas.Wireheading.AgentEquations
public import AISafetyAtlas.Wireheading.Mixture
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Ring and Orseau's delusion box, and their Statements 1 to 3

Ring and Orseau, *Delusion, Survival, and Intelligent Agents*, AGI 2011, §3.
`AISafetyAtlas.Wireheading.AgentEquations` writes down §2's equations (1) to (3);
this module writes down the object the paper is named for, the four agents §2
describes, and the three statements §3 argues.

**Which text.** The Springer chapter (LNAI 6830, pp. 11–20) is closed. What has
been read is the author deposit on HAL, `hal-01000226v1`, sha256
`a207ab73c87896e0663e4998906aa4c4bcef6d93a43d8e29ebc3cdb81e32ea6d`, in the
project's literature directory, manifest `SOURCES-2026-09-09-wireheading.md`.
Pagination differs from the chapter and no claim is made about the chapter.

## §3 as printed, and as rendered

Print: the global environment splits into an *inner environment* and a *delusion
box*. The inner environment's output `oᵉ_t` passes through the box before the
agent sees it, the box is a function on observations, and **the code of that
function is part of the agent's action**: an action is a pair `⟨d_t, aᵉ_t⟩` of a
program for the box and an action for the inner environment. Print assumes the
inner environment cannot read the program, and that the box initially runs the
identity.

`GlobalEnv` is that, field for field. `Act` is print's pair. `trace` runs an
action sequence and produces both histories at once — the inner environment's, in
its own observations, and the agent's, in the observations the box let through.

Three theorems say the definition has the content print uses it for:

* `innerHistory_congr_innerAction` — the inner environment cannot see the
  program, which print assumes in one sentence;
* `globalObs_identity` — with the identity program the agent sees exactly the
  inner environment, print's `d₀`;
* `globalObs_const_of_isConstant` and `globalObs_indep_inner` — a program that
  rewrites every observation to one value makes the agent's observations
  independent of the inner environment entirely. This is print's "obliterating
  observations", and it is what every one of Statements 1 to 3 leans on.

## What print does not state, and what is assumed here

**Print's Statements are argued, not proved.** Each is followed by a paragraph
headed *Arguments* which bounds two quantities and compares them. The bounds
need premises print never writes down, so the theorems below carry them as named
explicit hypotheses and the coverage audit grades the rows **Narrower**. The
three that matter:

1. **The two-hypothesis decomposition.** Print treats `v(h yes)` and `v(h no)` as
   `P(DB)`-weighted averages of the value under "there is a box" and the value
   under "there is not". Equations (2) and (3) do not supply that: the value
   under a mixed belief is not the mixture of the values under the components,
   because equation (3) maximises over actions *inside* the recursion. `MixesAt`
   is that decomposition, named. It is **not** vacuous: `mixesAt_zero` proves it
   at remaining depth zero, and every witness below inhabits it there. **Print's
   own values are not at depth zero** — its `v` is the full recursion — and
   above depth zero the decomposition is **false**, not merely unproved:
   `Examples…not_mixesAt_one` exhibits two one-bit environments whose informed
   values average to `3/2` where the mixture's own value is `1`. What print
   needs instead is in `AISafetyAtlas.Wireheading.Mixture`: at a *posterior*
   weight a **committed policy's** value is exactly the average
   (`Mixture.policyValue_mixture`) while the **optimal** value is only at most it
   (`Mixture.value_mixture_le`). Print uses an equality on both branches of its
   comparison, and only one of the two directions is the one each branch needs.
2. **The ranges of the branch values.** Print writes `1` for the best attainable
   value and `r̄` for the value without the box, and never says that a value lies
   in `[0, 1]` or that programming the box attains the maximum. Each theorem
   takes those as four separate inequalities on the two actions, so nothing is
   folded into a definition.
3. **That a box-using action exists.** Print's `yes` is an action of the agent;
   here it is a quantified argument, and the witness supplies one.

**What cannot be instantiated, and why that is not the same as refused.** Print's
Statement 4 — the knowledge-seeking agent will *not* consistently use the box —
is **false at `knowledgeAgent`**. Print's utility is `u(h) = -ρ(h)` for the same
`ρ` the agent reasons with; here the mass is a parameter, and
`AISafetyAtlas.Examples.Wireheading.DelusionBox.knowledge_uses_the_box` exhibits
an ordinary mass under which the agent programs the box at every positive
`P(DB)`, at an arbitrary `p > 0` and with no threshold. So the statement is not deferred for the cost of a universal prior; it
is unstatable at this agent, and the witness says exactly which tie has been cut.
The cheap half is now built: `historyMass` is the product of successive
conditionals and `coherentKnowledgeAgent` is `knowledgeAgent` at that mass.
Print's Statement 4 is still not proved — `Examples.DelusionBox.coherent_uses_the_box`
shows the coherent agent at the mixture belief still programs the box — because
the argument about discarded mass needs a type of programs and a prior over it.

Also **not** here: AIXI, Solomonoff induction, incomputability, any convergence
of a learning agent to its optimal variant, §4's self-modification setting and
Statements 5 to 7, and any infinite-horizon limit. `Belief` remains an arbitrary
real-valued conditional weight, not a probability; the mixing parameter `p` is
print's `P(DB)` and is constrained only by `0 ≤ p ≤ 1` where a theorem needs it.

Survey rows: §3, §2's four agents and their optimal non-learning variants, and
Statements 1 to 3, in section 11 of `docs/provenance/source-coverage-audit.md`.
No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.DelusionBox

open AISafetyAtlas.Wireheading.AgentEquations

/-! ## §3, the delusion box -/

/--
**An action in the global environment**, print's `a_t = ⟨d_t, aᵉ_t⟩`: a program
to be executed by the delusion box at this step, and an action for the inner
environment to interpret.

A pair rather than a two-field structure so that finiteness of the two halves
gives finiteness of the action set, which equation (1) needs.
-/
public abbrev Act (Program InnerAction : Type*) : Type _ := Program × InnerAction

/-- The program half of an action, print's `d_t`. -/
@[expose] public def program {Program InnerAction : Type*}
    (a : Act Program InnerAction) : Program := a.1

/-- The inner-environment half of an action, print's `aᵉ_t`. -/
@[expose] public def innerAction {Program InnerAction : Type*}
    (a : Act Program InnerAction) : InnerAction := a.2

/--
**The delusion box**, print's §3.

The global environment is an inner environment together with a box that rewrites
the inner environment's observations before the agent sees them.

* `inner` is print's `E`. It maps the inner environment's own history — its
  actions and its own observations — and the next inner action to the next inner
  observation `oᵉ`. It takes **only inner actions**, which is print's assumption
  that "the inner environment cannot access this program"; that the assumption
  bites is `innerHistory_congr_innerAction`.
* `exec` is print's `d : O → O`, indexed by the program that specifies it. Print
  writes both `d : O → O` and `o_t = d(a_t, oᵉ_t)`; the second is the first
  applied to the program carried inside the action, and that is what `exec` is.
* `identity` and `exec_identity` are print's initial condition, "initially, the
  delusion box executes the identity function `d₀(oᵉ_t) = o_t`".

There is no probability here and none in print's §3: the box is a deterministic
rewriting, and the agent's uncertainty about whether one is present is carried by
its belief, not by the environment.
-/
public structure GlobalEnv (Program InnerAction Obs : Type*) where
  /-- The inner environment, print's `E`: its own history and the next inner
  action determine the next inner observation `oᵉ`. -/
  inner : List (InnerAction × Obs) → InnerAction → Obs
  /-- The delusion box, print's `d`: a program rewrites an inner observation into
  the observation the agent receives. -/
  exec : Program → Obs → Obs
  /-- The program print's box runs before the agent reprograms it. -/
  identity : Program
  /-- And it is the identity, print's `d₀(oᵉ_t) = o_t`. -/
  exec_identity : ∀ o, exec identity o = o

namespace GlobalEnv

variable {P Ae O : Type*}

/-- One step of the global environment: the inner environment produces `oᵉ` from
its own history, the box rewrites it, and both histories are extended. -/
@[expose] public def step (G : GlobalEnv P Ae O)
    (st : List (Ae × O) × List (Act P Ae × O)) (a : Act P Ae) :
    List (Ae × O) × List (Act P Ae × O) :=
  (st.1 ++ [(innerAction a, G.inner st.1 (innerAction a))],
    st.2 ++ [(a, G.exec (program a) (G.inner st.1 (innerAction a)))])

/-- Running an action sequence: the inner environment's history and the agent's
history, produced together because each step of one feeds the other. -/
@[expose] public def trace (G : GlobalEnv P Ae O) (as : List (Act P Ae)) :
    List (Ae × O) × List (Act P Ae × O) :=
  as.foldl G.step ([], [])

/-- The inner environment's own history, in its own observations `oᵉ`. -/
@[expose] public def innerHistory (G : GlobalEnv P Ae O) (as : List (Act P Ae)) :
    List (Ae × O) :=
  (G.trace as).1

/-- The agent's history: the actions it took and the observations the box let
through. -/
@[expose] public def globalHistory (G : GlobalEnv P Ae O) (as : List (Act P Ae)) :
    List (Act P Ae × O) :=
  (G.trace as).2

/-- The inner environment's run, reading only inner actions. -/
@[expose] public def innerRun (G : GlobalEnv P Ae O) :
    List (Ae × O) → List Ae → List (Ae × O)
  | ih, [] => ih
  | ih, a :: rest => G.innerRun (ih ++ [(a, G.inner ih a)]) rest

/-- The inner half of the trace is the inner environment's own run on the inner
actions, from any starting pair of histories. -/
public theorem trace_fst_foldl (G : GlobalEnv P Ae O) :
    ∀ (as : List (Act P Ae)) (st : List (Ae × O) × List (Act P Ae × O)),
      (as.foldl G.step st).1 = G.innerRun st.1 (as.map innerAction) := by
  intro as
  induction as with
  | nil => intro st; rfl
  | cons a rest ih =>
      intro st
      rw [List.foldl_cons, ih (G.step st a)]
      rfl

/--
**The inner environment cannot see the program.**

Print assumes this in one sentence — "we assume that the inner environment cannot
access this program" — and here it is a consequence of `inner` taking an inner
action rather than a whole action: two action sequences with the same inner
halves drive the inner environment identically, whatever their programs.
-/
public theorem innerHistory_congr_innerAction (G : GlobalEnv P Ae O)
    (as bs : List (Act P Ae)) (h : as.map innerAction = bs.map innerAction) :
    G.innerHistory as = G.innerHistory bs := by
  rw [innerHistory, innerHistory, trace, trace, trace_fst_foldl, trace_fst_foldl, h]

/-- The agent's observations after an action sequence. -/
@[expose] public def globalObs (G : GlobalEnv P Ae O) (as : List (Act P Ae)) : List O :=
  (G.globalHistory as).map Prod.snd

/-- A program is **constant at `k`** when it rewrites every inner observation to
`k`. This is what print means by programming the box "to produce a constant
reward of 1", and by programming it "to output a predictable sequence". -/
@[expose] public def IsConstant (G : GlobalEnv P Ae O) (d : P) (k : O) : Prop :=
  ∀ o, G.exec d o = k

/-- The agent's observations, from any starting pair of histories. -/
public theorem trace_snd_const (G : GlobalEnv P Ae O) {d : P} {k : O}
    (hd : G.IsConstant d k) :
    ∀ (as : List (Act P Ae)) (st : List (Ae × O) × List (Act P Ae × O)),
      (∀ a ∈ as, program a = d) →
      ((as.foldl G.step st).2).map Prod.snd
        = (st.2).map Prod.snd ++ as.map (fun _ => k) := by
  intro as
  induction as with
  | nil => intro st _; simp
  | cons a rest ih =>
      intro st hall
      rw [List.foldl_cons,
        ih (G.step st a) (fun b hb => hall b (List.mem_cons_of_mem a hb))]
      have hprog : program a = d := hall a List.mem_cons_self
      simp [step, hprog, hd _]

/--
**A constant program obliterates the inner environment.**

Every observation the agent receives is `k`, whatever the inner environment
produced. This is the mechanism all three of print's Statements use, and it is
the reason the agent's own uncertainty about the inner environment stops
mattering once it has programmed the box.
-/
public theorem globalObs_const_of_isConstant (G : GlobalEnv P Ae O) {d : P} {k : O}
    (hd : G.IsConstant d k) (as : List (Act P Ae)) (hall : ∀ a ∈ as, program a = d) :
    G.globalObs as = as.map (fun _ => k) := by
  rw [globalObs, globalHistory, trace, trace_snd_const G hd as ([], []) hall]
  simp

/--
**Hence two global environments with the same box are indistinguishable under a
constant program**, however different their inner environments.

Print's Statement 3 says the prediction agent programs the box "obliterating
observations from `q_b`, since these observations may generate prediction
errors". This is that sentence: the true inner environment has stopped reaching
the agent at all.
-/
public theorem globalObs_indep_inner (G G' : GlobalEnv P Ae O) {d : P} {k : O}
    (hd : G.IsConstant d k) (hd' : G'.IsConstant d k)
    (as : List (Act P Ae)) (hall : ∀ a ∈ as, program a = d) :
    G.globalObs as = G'.globalObs as := by
  rw [globalObs_const_of_isConstant G hd as hall,
    globalObs_const_of_isConstant G' hd' as hall]

/--
**With the identity program the box is transparent.**

Print's initial condition: before the agent reprograms it, the box passes the
inner environment's observations through unchanged, so the agent sees exactly
what the inner environment produced.
-/
public theorem globalObs_identity (G : GlobalEnv P Ae O) (as : List (Act P Ae))
    (hall : ∀ a ∈ as, program a = G.identity) :
    G.globalObs as = (G.innerHistory as).map Prod.snd := by
  rw [globalObs, globalHistory, innerHistory, trace]
  suffices h : ∀ (bs : List (Act P Ae)) (st : List (Ae × O) × List (Act P Ae × O)),
      (∀ a ∈ bs, program a = G.identity) →
      (st.2).map Prod.snd = (st.1).map Prod.snd →
      ((bs.foldl G.step st).2).map Prod.snd = ((bs.foldl G.step st).1).map Prod.snd by
    exact h as ([], []) hall rfl
  intro bs
  induction bs with
  | nil => intro st _ hst; exact hst
  | cons a rest ih =>
      intro st hall hst
      refine ih (G.step st a) (fun b hb => hall b (List.mem_cons_of_mem a hb)) ?_
      have hprog : program a = G.identity := hall a List.mem_cons_self
      simp [step, hprog, G.exec_identity, hst]

/--
**The global environment is an environment like any other**, which is print's
Fig. 1(a) caption: the next observation the agent receives is a function of the
history it has seen and the action it takes.

`AgentEquations` reads a history as a list of action-observation pairs, and the
actions in it are exactly the action sequence the global environment consumes.
-/
@[expose] public def next (G : GlobalEnv P Ae O)
    (h : AgentEquations.History (Act P Ae) O) (a : Act P Ae) : O :=
  G.exec (program a) (G.inner (G.innerHistory (h.map Prod.fst)) (innerAction a))

/--
**Print's mechanism, one step at a time.** An action carrying a program the box
runs constantly at `k` produces `k`, whatever the inner environment did and
whatever the history was.

`globalObs_const_of_isConstant` is this along a whole action sequence; this is
the single step the agent's equation (2) sums over, and it is what turns print's
*"the agent can program the DB to produce a constant reward of 1"* into a
computation rather than an assumption.
-/
public theorem next_const (G : GlobalEnv P Ae O) {d : P} {k : O}
    (hd : G.IsConstant d k) (h : AgentEquations.History (Act P Ae) O)
    (a : Act P Ae) (ha : program a = d) :
    G.next h a = k := by
  rw [next, ha, hd]

end GlobalEnv

/-! ## §2, the four agents and their optimal non-learning variants -/

variable {Action Obs : Type*}

/-- Print's reinforcement-learning and prediction horizon, `w(t, k) = 1` if
`k - t ≤ m` and `0` otherwise.

Print's `k - t ≤ m` is written here as `k ≤ t + m`, which is the same condition
over the integers and avoids truncated subtraction; print's `k` is a future step,
so `k < t` does not arise. -/
@[expose] public def windowHorizon (m : ℕ) : ℕ → ℕ → ℝ :=
  fun t k => if k ≤ t + m then 1 else 0

/-- Print's knowledge-seeking horizon, `w(t, k) = 1` if `k - t = m` and `0`
otherwise: one distant step and nothing else. -/
@[expose] public def spikeHorizon (m : ℕ) : ℕ → ℕ → ℝ :=
  fun t k => if k = t + m then 1 else 0

/-- Print's goal-seeking horizon, `w(t, k) = 2^{t-k}`, favouring short histories.

The exponent is an integer difference, not a truncated natural one, so this is
print's weight at every pair `(t, k)` and not only at `k ≥ t`. -/
@[expose] public noncomputable def shortHorizon : ℕ → ℕ → ℝ :=
  fun t k => (2 : ℝ) ^ ((t : ℤ) - (k : ℤ))

/-- The reward the last observation of a history carries, `0` on the empty
history. Print's `r_{|h|}`, once an observation is read as carrying a reward. -/
@[expose] public def lastReward (reward : Obs → ℝ)
    (h : AgentEquations.History Action Obs) : ℝ :=
  match h.getLast? with
  | none => 0
  | some p => reward p.2

/-- **Print's reinforcement-learning agent.** Its utility is the reward the
environment gave at the last step; its horizon weight is one inside a window of
`m` steps.

Print writes the observation as a pair `⟨õ_t, r_t⟩` of other information and a
reward. Here the reward is read off the observation by a function, which is the
same factorization without fixing how the observation is coded. -/
@[expose] public def rlAgent (reward : Obs → ℝ) (m : ℕ) : Agent Action Obs where
  utility := lastReward reward
  horizon := windowHorizon m

/-- **Print's reinforcement-learning agent at any horizon.** Print's horizon clause
for A_rl (Ring and Orseau, AGI 2011, §2, PDF p. 4) is *"w(t, k) = 1 if k − t ≤ m"*
and states no value off the window; `rlAgent` completes it by zero
(`windowHorizon`), the binary horizon of the companion paper. This is the same
utility, the last reward, at an arbitrary horizon w. Print's clause is
`OneOnWindow`; `rlAgent_eq_rlAgentWith` and `windowHorizon_oneOnWindow` make
`rlAgent` its window-indicator instance. -/
@[expose] public def rlAgentWith (reward : Obs → ℝ) (w : ℕ → ℕ → ℝ) : Agent Action Obs where
  utility := lastReward reward
  horizon := w

/-- Print's horizon clause for A_rl: weight one at every future step inside the
window of m steps (k ≤ t + m, print's k − t ≤ m), and nothing said outside
it. -/
@[expose] public def OneOnWindow (m : ℕ) (w : ℕ → ℕ → ℝ) : Prop :=
  ∀ t k, k ≤ t + m → w t k = 1

/-- The window indicator satisfies print's clause: it is one completion of it. -/
public theorem windowHorizon_oneOnWindow (m : ℕ) : OneOnWindow m (windowHorizon m) :=
  fun t k hk => by simp [windowHorizon, hk]

/-- `rlAgent` is `rlAgentWith` at the window indicator. -/
public theorem rlAgent_eq_rlAgentWith (reward : Obs → ℝ) (m : ℕ) :
    (rlAgent reward m : Agent Action Obs) = rlAgentWith reward (windowHorizon m) := rfl

/-- **Print's goal-seeking agent.** Its utility is one when the goal is achieved
at the current step and zero otherwise, and the goal is a predicate on the
observations only, print's `g(o₁, …, o_{|h|})`. Its horizon favours short
histories.

Print also records that the goal can be reached at most once, so the utilities
along a trajectory sum to at most one. That is a condition on `g`, not part of
this definition, and nothing below uses it. -/
@[expose] public noncomputable def goalAgent (g : List Obs → Bool) : Agent Action Obs where
  utility := fun h => if g (h.map Prod.snd) then 1 else 0
  horizon := shortHorizon

/-- Print's **companion** goal-seeking horizon, the constant `w(t, k) = 1`.

*Self-Modification and Mortality in Artificial Agents* takes the same
goal-seeking utility and a different horizon, and says so in one sentence on its
page 4: *"The goal can be reached at most once, so `Σ_{t=0}^∞ u(h_t) ≤ 1`. For
this utility function, the horizon function is not necessary, does not need to
be summable, and can be set to 1: `w(t, k) = 1`."*

So the two papers' goal-seeking agents differ in exactly one field, and this is
the second one's. -/
@[expose] public def unitHorizon : ℕ → ℕ → ℝ := fun _ _ => 1

/-- **The companion paper's goal-seeking agent.**

The same utility as `goalAgent` — one when the goal predicate holds of the
observations so far — at the constant horizon its own page 4 sets, rather than
`shortHorizon`, which is the horizon of *Delusion, Survival, and Intelligent
Agents*.

It is a separate record rather than a parameter because the audit grades the two
papers separately and each names its own agent; `goalAgent_horizon_ne` records
that the distinction is not cosmetic.

Print's side condition that the goal is reached at most once, so the utilities
along a trajectory sum to at most one, is a condition on `g` and is not imposed
here — which widens this record rather than narrowing it, and is why nothing
below may assume the sum is bounded. -/
@[expose] public def companionGoalAgent (g : List Obs → Bool) : Agent Action Obs where
  utility := fun h => if g (h.map Prod.snd) then 1 else 0
  horizon := unitHorizon

/-- The two goal-seeking agents share a utility and differ in the horizon, so
neither record covers the other paper's agent. -/
public theorem companionGoalAgent_utility_eq (g : List Obs → Bool) :
    (companionGoalAgent (Action := Action) (Obs := Obs) g).utility =
      (goalAgent (Action := Action) (Obs := Obs) g).utility := rfl

/-- The horizons genuinely differ: at `t = 0`, `k = 1` the constant horizon is
`1` and `shortHorizon` is `1/2`. -/
public theorem goalAgent_horizon_ne :
    (companionGoalAgent (Action := Action) (Obs := Obs) (fun _ => true)).horizon 0 1 ≠
      (goalAgent (Action := Action) (Obs := Obs) (fun _ => true)).horizon 0 1 := by
  show unitHorizon 0 1 ≠ shortHorizon 0 1
  unfold unitHorizon shortHorizon
  norm_num

/-- **Print's prediction-seeking agent.** Its utility is one when the agent
correctly predicted the observation it just received.

Print takes the prediction to be Solomonoff induction's — the observation
maximising the prior weight given the history, print's ρ(o | h a) with h ending
in the action just taken. Here it is an arbitrary function of the history before
the current action–observation pair, so it cannot read the current action: this
widens print in the predictor's form and narrows it in what the predictor sees,
since print's own action-conditioned predictor is not a value of the predictor
parameter.
`predictionAgentAct` takes a predictor that reads the current action, and this
agent is its action-blind instance (`predictionAgent_eq_predictionAgentAct`). -/
@[expose] public def predictionAgent [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ) : Agent Action Obs where
  utility := fun h =>
    match h.getLast? with
    | none => 0
    | some p => if predict h.dropLast = p.2 then 1 else 0
  horizon := windowHorizon m

/-- The prediction agent's utility after an observation arrives: one exactly when
the prediction made on the history before it was that observation, so a utility
of zero at a nonempty history is a prediction mistake (Orseau and Ring, AGI 2011,
§2.1, `A^ρ_p`). The utility reads only the history and the predictor, never the
agent's belief. -/
public theorem predictionAgent_utility_snoc [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ)
    (h : AgentEquations.History Action Obs) (a : Action) (o : Obs) :
    (predictionAgent predict m).utility (h ++ [(a, o)]) = if predict h = o then 1 else 0 := by
  simp [predictionAgent]

/-- **The only environment in which the prediction makes no mistake** (Orseau and
Ring, *Self-Modification and Mortality in Artificial Agents*, AGI 2011, footnote 6,
PDF p. 4: *"there is only one environment in which the prediction makes 0
mistake"*). For a deterministic environment `E`, answering each history and action
with an observation, the prediction agent's utility is one after every step at
every history exactly when `E` answers every history with the prediction made on
it. -/
public theorem predictionAgent_utility_eq_one_iff [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ)
    (E : AgentEquations.History Action Obs → Action → Obs) :
    (∀ h a, (predictionAgent predict m).utility (h ++ [(a, E h a)]) = 1) ↔
      E = fun h _ => predict h := by
  constructor
  · intro hE
    funext h a
    have := hE h a
    rw [predictionAgent_utility_snoc] at this
    split_ifs at this with hp
    · exact hp.symm
    · norm_num at this
  · rintro rfl h a
    rw [predictionAgent_utility_snoc]
    simp

/-- Footnote 6 as uniqueness: exactly one deterministic environment gives the
prediction agent utility one after every step (Orseau and Ring, AGI 2011,
footnote 6, PDF p. 4). -/
public theorem predictionAgent_existsUnique_zero_mistakes [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ) :
    ∃! E : AgentEquations.History Action Obs → Action → Obs,
      ∀ h a, (predictionAgent predict m).utility (h ++ [(a, E h a)]) = 1 :=
  ⟨fun h _ => predict h, (predictionAgent_utility_eq_one_iff predict m _).mpr rfl,
    fun _ hE => (predictionAgent_utility_eq_one_iff predict m _).mp hE⟩

/-- **Print's knowledge-seeking agent.** Its utility is the negated prior mass of
the history, so it acts to make as many environments inconsistent as possible,
and its horizon is a single distant step.

Defined because §2 defines it. **Print's Statement 4 is false at it**: the mass
is a parameter here and print's is `ρ(h)` for the agent's own `ρ`, so the two
are not the same agent.
`AISafetyAtlas.Examples.Wireheading.DelusionBox.knowledge_uses_the_box` is the
witness. `coherentKnowledgeAgent` restores the tie at the observation layer;
print's argument about discarded *program* mass is still absent.
-/
@[expose] public def knowledgeAgent (mass : AgentEquations.History Action Obs → ℝ)
    (m : ℕ) : Agent Action Obs where
  utility := fun h => -mass h
  horizon := spikeHorizon m

/-- The mortality author's version, p.4, prints `k + t = m`, not `k - t = m`.
This definition transcribes that version without adjudicating the discrepancy. -/
@[expose] public def companionSpikeHorizon (m : ℕ) : ℕ → ℕ → ℝ :=
  fun t k ↦ if k + t = m then 1 else 0

/-- The mortality paper's knowledge agent, with its literal horizon. The mass
parameter remains separate from a program prior, as in `knowledgeAgent`. -/
@[expose] public def companionKnowledgeAgent
    (mass : AgentEquations.History Action Obs → ℝ) (m : ℕ) : Agent Action Obs where
  utility := fun h ↦ -mass h
  horizon := companionSpikeHorizon m

/-- The two author versions agree on utility, independently of their horizons. -/
public theorem companionKnowledgeAgent_utility_eq
    (mass : AgentEquations.History Action Obs → ℝ) (m : ℕ) :
    (companionKnowledgeAgent mass m).utility = (knowledgeAgent mass m).utility := rfl

/-- The horizon discrepancy is observable at a future step, not just before the present. -/
public theorem knowledgeAgent_horizon_ne (mass : AgentEquations.History Action Obs → ℝ) :
    (companionKnowledgeAgent mass 2).horizon 1 1 ≠ (knowledgeAgent mass 2).horizon 1 1 := by
  norm_num [companionKnowledgeAgent, companionSpikeHorizon, knowledgeAgent, spikeHorizon]

/-- The literal mortality horizon selects no future step once twice the present exceeds `m`. -/
public theorem companionSpikeHorizon_eq_zero {m t k : ℕ} (ht : m < t + t) (hk : t ≤ k) :
    companionSpikeHorizon m t k = 0 := by
  simp [companionSpikeHorizon, show k + t ≠ m by omega]

/--
**Print's knowledge-seeking agent, with the tie restored.** Utility is the
negated history mass of the *same* belief the agent reasons with, which is
print's `u(h) = -ρ(h)`.

This is the cheap half of recovering Statement 4. The expensive half — a type
of programs and a prior over it, so that a delusion box discards mass by
making observations uninformative — is not here. Coherence alone does not
prove Statement 4: `Examples.DelusionBox.coherent_uses_the_box` shows the
coherent agent at the mixture belief still programs the box.
-/
@[expose] public def coherentKnowledgeAgent (ρ : Belief Action Obs) (m : ℕ) :
    Agent Action Obs :=
  knowledgeAgent (historyMass ρ) m

/--
**The optimal non-learning variant's belief**, print's `μ` with
`μ(q) = 1 ⟺ q = q_μ`.

Print obtains the variant by "replacing `ρ` by `μ` in (only) equation (2)", so
the variant differs from the learning agent in the belief and in nothing else:
same utility, same horizon. A `μ` concentrated on one environment is a belief
that puts weight one on the observation that environment produces.
-/
@[expose] public def diracBelief [DecidableEq Obs]
    (E : AgentEquations.History Action Obs → Action → Obs) : Belief Action Obs where
  cond := fun h a o => if o = E h a then 1 else 0

-- No finiteness on the action type: the source bounds `𝒜` nowhere, and since
-- 2026-09-13 neither does this section.  `mixesAt_zero` keeps `[Fintype Obs]`
-- explicitly, which is a different axis.

/--
**Equation (2) at the optimal non-learning variant's belief.**

The weighted sum over observations collapses to the single observation the known
environment produces, which is the sense in which the non-learning variant has
"full knowledge of the environment".
-/
public theorem actionValue_diracBelief [DecidableEq Obs]
    (E : AgentEquations.History Action Obs → Action → Obs) (ag : Agent Action Obs)
    (t n : ℕ) (h : AgentEquations.History Action Obs) (a : Action) :
    actionValue (diracBelief E) ag t n h a
      = value (diracBelief E) ag t n (h ++ [(a, E h a)]) := by
  rw [actionValue,
    tsum_eq_single (E h a) (fun o hne => by simp [diracBelief, hne])]
  simp [diracBelief]

/-- **Equation (2) at the optimal non-learning variant's belief, at the
infinite-horizon value.** The same collapse as `actionValue_diracBelief`, for
`infiniteActionValue`: the non-learning variant's action value is the
infinite value of the one history the known environment produces (Ring and
Orseau, AGI 2011, §2, optimal variants). -/
public theorem infiniteActionValue_diracBelief [DecidableEq Obs]
    (E : AgentEquations.History Action Obs → Action → Obs) (ag : Agent Action Obs)
    (t : ℕ) (h : AgentEquations.History Action Obs) (a : Action) :
    infiniteActionValue (diracBelief E) ag t h a
      = infiniteValue (diracBelief E) ag t (h ++ [(a, E h a)]) := by
  rw [infiniteActionValue,
    tsum_eq_single (E h a) (fun o hne => by simp [diracBelief, hne])]
  simp [diracBelief]

/-- **The optimal non-learning variant's belief is a probability.** It puts
weight one on the observation the known environment produces and nothing
anywhere else, so every bound stated at `Belief.IsSubprobability` applies to it.
-/
public theorem diracBelief_isSubprobability [DecidableEq Obs]
    (E : AgentEquations.History Action Obs → Action → Obs) :
    (diracBelief E).IsSubprobability where
  nonneg := by
    intro h a o
    by_cases ho : o = E h a <;> simp [diracBelief, ho]
  summable := fun h a => (hasSum_ite_eq (E h a) (1 : ℝ)).summable
  total_le_one := fun h a => le_of_eq (hasSum_ite_eq (E h a) (1 : ℝ)).tsum_eq

/-! ### Print's four branch bounds, derived

`statement_one` carries four inequalities on the two actions' values as
hypotheses, and its docstring says they are the premises print's *Arguments*
paragraph uses without stating. Three of the four are theorems about print's own
reinforcement-learning agent, and the fourth is print's own definition.

Print compares `v(h yes)` and `v(h no)` at the step the box is programmed — its
`r̄` is *"the expected reward when not using the DB"*, an expectation one step on
— so these are stated at remaining depth zero, which is where the witnesses in
`AISafetyAtlas.Examples.Wireheading.Mixture` already live.

* *"The agent can program the DB to produce a constant reward of 1"* is
  `rlAgent_actionValue_next_const`, at a global environment whose box runs a
  program constant at an observation of reward one. Print writes `>`; this is an
  equality.
* `0 ≤ ·` and `· ≤ 1` are `rlAgent_actionValue_nonneg` and
  `rlAgent_actionValue_le`, from `Belief.IsSubprobability` and a bounded reward
  — print's own `u : ℋ → [0,1]`.
* `v(h no) ≤ r̄` in the box branch is **print's definition of `r̄`** and nothing
  derives it: print says what `r̄` is, so the hypothesis is discharged by taking
  `r̄` to be that action value. `rlAgent_actionValue_le` covers it whenever a
  reward bound is what supplies `r̄`.
-/

/-- The reinforcement-learning agent's value one step on is the reward that step
delivered, whenever the step falls inside its window. -/
public theorem rlAgent_value_zero_snoc (ρ : Belief Action Obs) (reward : Obs → ℝ)
    (m t : ℕ) (h : AgentEquations.History Action Obs) (a : Action) (o : Obs)
    (hwin : h.length + 1 ≤ t + m) :
    value ρ (rlAgent reward m) t 0 (h ++ [(a, o)]) = reward o := by
  simp [value, rlAgent, windowHorizon, lastReward, hwin]

/-- **Equation (2) for the reinforcement-learning agent at remaining depth zero**
is the expected reward of the next step, which is the quantity print's `r̄`
names. -/
public theorem rlAgent_actionValue_zero (ρ : Belief Action Obs) (reward : Obs → ℝ)
    (m t : ℕ) (h : AgentEquations.History Action Obs) (a : Action)
    (hwin : h.length + 1 ≤ t + m) :
    actionValue ρ (rlAgent reward m) t 0 h a = ∑' o, ρ.cond h a o * reward o := by
  rw [actionValue]
  exact tsum_congr fun o => by rw [rlAgent_value_zero_snoc ρ reward m t h a o hwin]

/-- **Print's `≥ 0`.** A nonnegative reward makes every action value
nonnegative, which is the bound print's `v(h yes) > P(DB) · 1` uses when it
drops the `¬DB` term. -/
public theorem rlAgent_actionValue_nonneg {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (reward : Obs → ℝ) (hr : ∀ o, 0 ≤ reward o)
    (m t : ℕ) (h : AgentEquations.History Action Obs) (a : Action)
    (hwin : h.length + 1 ≤ t + m) :
    0 ≤ actionValue ρ (rlAgent reward m) t 0 h a := by
  rw [rlAgent_actionValue_zero ρ reward m t h a hwin]
  exact tsum_nonneg fun o => mul_nonneg (hρ.nonneg h a o) (hr o)

/-- **Print's `≤ 1`, and its `≤ r̄`.** A uniformly bounded reward bounds every
action value by the same constant. At `c = 1` this is print's *"the maximum
possible reward"*; at a `c` that bounds the reward available without the box it
is print's `r̄`. -/
public theorem rlAgent_actionValue_le {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (reward : Obs → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hr : ∀ o, |reward o| ≤ c)
    (m t : ℕ) (h : AgentEquations.History Action Obs) (a : Action)
    (hwin : h.length + 1 ≤ t + m) :
    actionValue ρ (rlAgent reward m) t 0 h a ≤ c := by
  rw [rlAgent_actionValue_zero ρ reward m t h a hwin]
  exact (le_abs_self _).trans (hρ.abs_tsum_mul_le h a hc hr)

/--
**Print's "the agent can program the DB to produce a constant reward of 1",
proved at print's own equation (2).**

At the belief a global environment induces, the reinforcement-learning agent's
value for an action carrying a box program constant at `k` is exactly the reward
of `k` — whatever the inner environment is and whatever the history was, by
`GlobalEnv.next_const`. Taking `k` to be an observation of reward one gives
print's box-branch bound as an **equality**, where print writes an inequality.
-/
public theorem rlAgent_actionValue_next_const {P Ae O : Type*} [DecidableEq O]
    (G : GlobalEnv P Ae O) {d : P} {k : O} (hd : G.IsConstant d k)
    (reward : O → ℝ) (m t : ℕ)
    (h : AgentEquations.History (Act P Ae) O) (a : Act P Ae) (ha : program a = d)
    (hwin : h.length + 1 ≤ t + m) :
    actionValue (diracBelief G.next) (rlAgent reward m) t 0 h a = reward k := by
  rw [actionValue_diracBelief, G.next_const hd h a ha,
    rlAgent_value_zero_snoc _ reward m t h a k hwin]

/-! ## Statements 1 to 3

Each is print's comparison of two actions, with the premises print's argument
uses supplied as named hypotheses. -/

/--
**The two-hypothesis decomposition print's arguments assume and never state.**

Print writes `v(h yes) > P(DB) · 1` and
`v(h no) < P(DB) · r̄ + P(¬DB) · 1`, treating the value of an action as the
`P(DB)`-weighted average of its value if the environment contains a delusion box
and its value if it does not.

Equations (2) and (3) do not give that. The value of a history under a mixed
belief is not the mixture of the values under the two component beliefs, because
equation (3) takes a maximum over actions *inside* the recursion and a maximum
does not commute with a mixture. Print's footnote 5 is where the assumption
hides: the agent "is assumed to have already explored its environment", so it is
being treated as if it knew which hypothesis held and were averaging over the
two.

So the decomposition is a hypothesis here, at the action values equation (1)
compares. `mixesAt_zero` proves it is satisfiable, at remaining depth zero. That
is a *lower* bound on where print stands, not a reconstruction of it: print's
`v` is the full recursion, so print is applying the decomposition at every depth,
and only the depth-zero case is a theorem — and, by `Examples…not_mixesAt_one`,
the only case that is true.
-/
@[expose] public def MixesAt (ρ ρbox ρfree : Belief Action Obs) (ag : Agent Action Obs)
    (p : ℝ) (t n : ℕ) (h : AgentEquations.History Action Obs) : Prop :=
  ∀ a : Action,
    actionValue ρ ag t n h a
      = p * actionValue ρbox ag t n h a + (1 - p) * actionValue ρfree ag t n h a

/--
**The decomposition holds at remaining depth zero.**

At depth zero equation (3)'s maximum has not yet entered the recursion, so the
value of a one-step extension does not depend on the belief at all and
equation (2)'s sum is linear in it. A belief that is a `p`-mixture of two others
therefore mixes their action values exactly.

This is what stops `MixesAt` from being an antecedent nothing inhabits, and it
bounds the narrowing exactly: the decomposition is available at depth zero and
**false** above it, which `Examples…not_mixesAt_one` proves rather than leaves
open. Print applies it to its full recursive value, so print is assuming
something that does not hold; `AISafetyAtlas.Wireheading.Mixture` carries the two
laws that do.
-/
public theorem mixesAt_zero [Fintype Obs] (ρ ρbox ρfree : Belief Action Obs)
    (ag : Agent Action Obs)
    (p : ℝ) (t : ℕ) (h : AgentEquations.History Action Obs)
    (hmix : ∀ h' a o, ρ.cond h' a o = p * ρbox.cond h' a o + (1 - p) * ρfree.cond h' a o) :
    MixesAt ρ ρbox ρfree ag p t 0 h := by
  intro a
  simp only [actionValue_eq_sum, value, hmix, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun o _ => by ring

/--
**Statement 1's comparison, as arithmetic.**

Print's bounds are: the box-using action is worth at least the maximum if a box
is present and at least nothing if not; the other action is worth at most `r̄` if
a box is present and at most the maximum if not. Print then requires
`P(DB) > 1/(2 - r̄)`, which at an arbitrary maximum `vmax` is
`vmax < p · (2·vmax - r̄)`.

The six hypotheses are print's argument written out. None of them is derivable
from the agent definitions, which is why they are here rather than there.
-/
public theorem mixture_lt_of_threshold
    {p vmax rbar vBoxYes vFreeYes vBoxNo vFreeNo : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hyesBox : vmax ≤ vBoxYes) (hyesFree : 0 ≤ vFreeYes)
    (hnoBox : vBoxNo ≤ rbar) (hnoFree : vFreeNo ≤ vmax)
    (hthresh : vmax < p * (2 * vmax - rbar)) :
    p * vBoxNo + (1 - p) * vFreeNo < p * vBoxYes + (1 - p) * vFreeYes := by
  have h1 : p * vBoxNo ≤ p * rbar := mul_le_mul_of_nonneg_left hnoBox hp0
  have h1' : p * vmax ≤ p * vBoxYes := mul_le_mul_of_nonneg_left hyesBox hp0
  have hp1' : (0 : ℝ) ≤ 1 - p := by linarith
  have h2 : (1 - p) * vFreeNo ≤ (1 - p) * vmax :=
    mul_le_mul_of_nonneg_left hnoFree hp1'
  have h2' : (0 : ℝ) ≤ (1 - p) * vFreeYes := mul_nonneg hp1' hyesFree
  nlinarith [hthresh, h1, h1', h2, h2']

/--
**Statement 2's comparison, as arithmetic.**

Print's goal-seeking bounds have a different shape: the box-using action is worth
at least `P(DB) · 2^{-|o⁺|}`, and the other action is worth at most `2^{-lᵃ}`
*in both branches* rather than `r̄` in one and the maximum in the other. So the
threshold is a gap between two numbers rather than a two-sided average.
-/
public theorem mixture_lt_of_gap
    {p B C vBoxYes vFreeYes vBoxNo vFreeNo : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hyesBox : B ≤ vBoxYes) (hyesFree : 0 ≤ vFreeYes)
    (hnoBox : vBoxNo ≤ C) (hnoFree : vFreeNo ≤ C)
    (hthresh : C < p * B) :
    p * vBoxNo + (1 - p) * vFreeNo < p * vBoxYes + (1 - p) * vFreeYes := by
  have hp1' : (0 : ℝ) ≤ 1 - p := by linarith
  have h1 : p * vBoxNo ≤ p * C := mul_le_mul_of_nonneg_left hnoBox hp0
  have h2 : (1 - p) * vFreeNo ≤ (1 - p) * C := mul_le_mul_of_nonneg_left hnoFree hp1'
  have h1' : p * B ≤ p * vBoxYes := mul_le_mul_of_nonneg_left hyesBox hp0
  have h2' : (0 : ℝ) ≤ (1 - p) * vFreeYes := mul_nonneg hp1' hyesFree
  nlinarith [hthresh, h1, h2, h1', h2']

/-- The threshold `P(DB) > 1/(2 - r̄)` scaled to a maximum value `vmax`: the box
branch's maximum is `vmax` and the refusing action's box-branch value is at most
`vmax · r̄`. -/
private theorem scaled_threshold {p vmax rbar : ℝ} (hvmax : 0 < vmax) (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < p) : vmax < p * (2 * vmax - vmax * rbar) := by
  have hpos : (0 : ℝ) < 2 - rbar := by linarith
  have hd := (div_lt_iff₀ hpos).mp hthresh
  have : vmax * 1 < vmax * (p * (2 - rbar)) := mul_lt_mul_of_pos_left hd hvmax
  nlinarith [this]

/--
**Statement 1 at any maximum value** (Ring and Orseau, AGI 2011, Statement 1 and
its *Arguments*, PDF pp. 5–6). Print normalises the maximum possible reward to
`1`, which is the maximum *value* only at a one-step horizon. With print's window
horizon `w(t, k) = 1` for `k - t ≤ m` and the full recursion, the box branch is
worth the in-window step count times the constant reward, so the bounds are in a
maximum `vmax` (`vmax ≤ v(h yes)` in the box branch, `v(h no) ≤ vmax` without
it) and the refusing action's box-branch value is at most `vmax · r̄`.
`statement_one` is this at `vmax = 1`.

**What `r̄` is here.** `r̄` is the refusing action's box-branch value divided by
`vmax`, i.e. averaged over the in-window steps, and that value includes the
optimal continuation, which may use the box at later steps. It is print's
one-step *"expected reward when not using the DB"* only at remaining depth zero.
Above it, a refusing first step followed by box use gives `r̄ ≥ (N - 1)/N` for `N`
in-window steps, so the threshold `1/(2 - r̄)` rises towards `1` with depth;
print's threshold at print's own `r̄` is not claimed at depth `n ≥ 1`.
-/
public theorem statement_one_scaled
    (ρ ρbox ρfree : Belief Action Obs) (ag : Agent Action Obs)
    (p : ℝ) (t n : ℕ) (h : AgentEquations.History Action Obs)
    (yes no : Action) (vmax rbar : ℝ)
    (hmix : MixesAt ρ ρbox ρfree ag p t n h)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ actionValue ρbox ag t n h yes)
    (hyesFree : 0 ≤ actionValue ρfree ag t n h yes)
    (hnoBox : actionValue ρbox ag t n h no ≤ vmax * rbar)
    (hnoFree : actionValue ρfree ag t n h no ≤ vmax)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < p) :
    actionValue ρ ag t n h no < actionValue ρ ag t n h yes := by
  rw [hmix no, hmix yes]
  exact mixture_lt_of_threshold hp0 hp1 hyesBox hyesFree hnoBox hnoFree
    (scaled_threshold hvmax hrbar hthresh)

/--
**Statement 1.** *The reinforcement-learning agent will use the delusion box to
maximize its utility.*

Print's conclusion is that the box-using action beats the other one once
`P(DB) > 1/(2 - r̄)`, and `bestAction_ne_of_lt` below turns that into the
statement about equation (1).

**Narrower than print, and here is the whole of it.** Print quantifies over its
agent and its universal prior and asserts the conclusion outright; the
hypotheses `hmix`, `hyesBox`, `hyesFree`, `hnoBox` and `hnoFree` are the premises
its *Arguments* paragraph uses without stating, and `hrbar` is the implicit
assumption that not using the box is worse than the maximum, without which the
printed threshold is not attainable by any probability. Nothing has been folded
into `rlAgent`: the agent is a parameter here, and the theorem is about whatever
values the two actions happen to have.
-/
public theorem statement_one
    (ρ ρbox ρfree : Belief Action Obs) (ag : Agent Action Obs)
    (p : ℝ) (t n : ℕ) (h : AgentEquations.History Action Obs)
    (yes no : Action) (rbar : ℝ)
    (hmix : MixesAt ρ ρbox ρfree ag p t n h)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hyesBox : 1 ≤ actionValue ρbox ag t n h yes)
    (hyesFree : 0 ≤ actionValue ρfree ag t n h yes)
    (hnoBox : actionValue ρbox ag t n h no ≤ rbar)
    (hnoFree : actionValue ρfree ag t n h no ≤ 1)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < p) :
    actionValue ρ ag t n h no < actionValue ρ ag t n h yes :=
  statement_one_scaled ρ ρbox ρfree ag p t n h yes no 1 rbar hmix hp0 hp1 one_pos
    hyesBox hyesFree (by rwa [one_mul]) hnoFree hrbar hthresh

/-! ### Statement 2's constants are the horizon, not the prior

Print's *Arguments* for Statement 2 read: *"Let `o⁺_t` be the shortest string of
observations that can satisfy the goal after history `h`. If `v(h yes)` is the
expected value of programming the DB to produce `o⁺_t`, then
`v(h yes) > P(DB) · 2^{−|o⁺_t|}`. Without the DB, the agent achieves the goal by
producing a string of actions of length `l^a_t ≥ |o⁺_t|`, and so
`v(h no) < P(DB) · 2^{−l^a_t} + (1 − P(DB)) · 2^{−l^a_t} = 2^{−l^a_t}`."*

**Both constants are values of the goal-seeking horizon `w(t, k) = 2^{t−k}`, and
the universal prior enters nowhere in that paragraph.** Section 11 of
`docs/provenance/source-coverage-audit.md` said they were *"computed from its
universal prior and its goal predicate"*, and the prior half of that was wrong:
`2^{−j}` is `shortHorizon t (t + j)`, the discount for reaching the goal `j`
steps later. What the goal predicate supplies is *which* step that is.
-/

/-- The goal-seeking horizon is strictly positive. -/
public theorem shortHorizon_pos (t k : ℕ) : 0 < shortHorizon t k :=
  zpow_pos (by norm_num) _

/-- And it decreases as the step moves further out, which is what makes print's
goal agent prefer short histories. -/
public theorem shortHorizon_succ_le (t k : ℕ) :
    shortHorizon t (k + 1) ≤ shortHorizon t k := by
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  push_cast
  linarith

/-- The goal-seeking agent's utility lies in print's `[0, 1]`. -/
public theorem goalAgent_abs_utility_le_one (g : List Obs → Bool)
    (h : AgentEquations.History Action Obs) : |(goalAgent g).utility h| ≤ 1 := by
  by_cases hg : g (h.map Prod.snd) <;> simp [goalAgent, hg]

/-- **Print's `2^{−j}` is the goal-seeking horizon `j` steps ahead**, and
nothing else. -/
public theorem shortHorizon_ahead (t j : ℕ) :
    shortHorizon t (t + j) = ((2 : ℝ) ^ j)⁻¹ := by
  simp [shortHorizon, zpow_natCast]

/-- The goal-seeking agent's value one step on is the horizon weight at that
step when the goal is met there, and zero when it is not. -/
public theorem goalAgent_value_zero_snoc (ρ : Belief Action Obs)
    (g : List Obs → Bool) (t : ℕ) (h : AgentEquations.History Action Obs)
    (a : Action) (o : Obs) :
    value ρ (goalAgent g) t 0 (h ++ [(a, o)])
      = if g ((h ++ [(a, o)]).map Prod.snd) then shortHorizon t (h.length + 1)
        else 0 := by
  simp [value, goalAgent]

/--
**Print's box-branch bound for the goal-seeking agent, as an equality.**

Programming the box with a constant program whose observation satisfies the goal
is worth exactly the horizon weight of the step it is reached at, which is
print's `2^{−|o⁺|}` at `|o⁺| = 1`. As with the reinforcement-learning agent,
print writes an inequality and the construction gives an equality.
-/
public theorem goalAgent_actionValue_next_const {P Ae O : Type*} [DecidableEq O]
    (G : GlobalEnv P Ae O) {d : P} {k : O} (hd : G.IsConstant d k)
    (g : List O → Bool) (t : ℕ)
    (h : AgentEquations.History (Act P Ae) O) (a : Act P Ae) (ha : program a = d)
    (hgoal : g ((h ++ [(a, k)]).map Prod.snd) = true) :
    actionValue (diracBelief G.next) (goalAgent g) t 0 h a
      = shortHorizon t (h.length + 1) := by
  rw [actionValue_diracBelief, G.next_const hd h a ha,
    goalAgent_value_zero_snoc _ g t h a k, if_pos hgoal]

/--
**Print's free-branch bound for the goal-seeking agent.**

Where the goal cannot be met at the next step the value is zero, which is below
every `2^{−lᵃ}`. Print's `l^a_t ≥ |o⁺_t|` is the statement that the goal takes
longer without the box; at the step print's comparison is made, "longer" means
"not now".

The goal has to fail only at the observations the belief gives weight to, which
is what the delusion box makes true: outside the box branch the inner
environment produces what it produces, and the agent cannot make it satisfy the
goal in one step.
-/
public theorem goalAgent_actionValue_zero_of_not_goal (ρ : Belief Action Obs)
    (g : List Obs → Bool) (t : ℕ) (h : AgentEquations.History Action Obs)
    (a : Action)
    (hg : ∀ o, ρ.cond h a o ≠ 0 → g ((h ++ [(a, o)]).map Prod.snd) = false) :
    actionValue ρ (goalAgent g) t 0 h a = 0 := by
  rw [actionValue]
  have hz : ∀ o, ρ.cond h a o * value ρ (goalAgent g) t 0 (h ++ [(a, o)]) = 0 := by
    intro o
    by_cases hc : ρ.cond h a o = 0
    · rw [hc]; ring
    · rw [goalAgent_value_zero_snoc ρ g t h a o, if_neg (by rw [hg o hc]; simp)]
      ring
  simp [hz]

/-! ### Print's `v(h no) < 2^{-lᵃ}` at every depth

The bounds above are at remaining depth zero, and for Statement 1 that is print's
own reading: its `r̄` is *"the expected reward when not using the DB"*, a reward
and not a sum of rewards. **Statement 2 is different.** Print's `2^{-lᵃ}` is the
horizon weight of a step `lᵃ` **later** — *"the agent achieves the goal by
producing a string of actions of length `lᵃ ≥ |o⁺|`"* — so its refusing-action
bound says the goal is reachable without the box and merely *slower*. At depth
zero that content never enters, because the value is simply zero.

This section is that bound at every depth, and it is the first thing in the atlas
to use print's own side condition on the goal predicate: *"the goal can be
reached at most once, so `Σ_t u(h_t) ≤ 1`"*. Without it a later goal hit adds to
the value and no single `2^{-lᵃ}` bounds it — the weights `2^{t-k}` sum to twice
the first one.
-/

/--
**Print's side condition on the goal predicate**: the goal is reached at most
once along a trajectory. Print states it as `Σ_t u(h_t) ≤ 1` and never uses it;
`goalAgent_value_le_shortHorizon` is what it is for.
-/
@[expose] public def ReachedAtMostOnce (g : List Obs → Bool) : Prop :=
  ∀ os ps : List Obs, g os = true → g (os ++ ps) = true → ps = []

/-- The goal fails at a history and at every extension of it. -/
@[expose] public def GoalNever (g : List Obs → Bool)
    (h : AgentEquations.History Action Obs) : Prop :=
  ∀ ps : List Obs, g (h.map Prod.snd ++ ps) = false

/--
**Print's `lᵃ`**: the goal is out of reach for `l` steps **against this belief**.

Print's `lᵃ` is the length of the action string that reaches the goal *without*
the delusion box, and it exceeds `|o⁺|` because the environment is slower, not
because the goal is longer. So the condition has to be relative to the belief:
no continuation the belief gives weight to satisfies the goal sooner.
-/
@[expose] public def GoalOutOfReach (ρ : Belief Action Obs) (g : List Obs → Bool) :
    ℕ → AgentEquations.History Action Obs → Prop
  | 0, _ => True
  | l + 1, h => g (h.map Prod.snd) = false ∧
      ∀ (a : Action) (o : Obs), ρ.cond h a o ≠ 0 → GoalOutOfReach ρ g l (h ++ [(a, o)])

private theorem goalNever_snoc {g : List Obs → Bool}
    {h : AgentEquations.History Action Obs} (hn : GoalNever g h)
    (a : Action) (o : Obs) : GoalNever g (h ++ [(a, o)]) := by
  intro ps
  have := hn (o :: ps)
  simpa [List.map_append] using this

/-- Once the goal is out of reach forever, the goal-seeking agent's value is zero
at every depth: every utility along every continuation is zero. -/
public theorem goalAgent_value_eq_zero_of_goalNever [Nonempty Action]
    (ρ : Belief Action Obs) (g : List Obs → Bool) (t : ℕ) :
    ∀ (n : ℕ) (h : AgentEquations.History Action Obs), GoalNever g h →
      value ρ (goalAgent g) t n h = 0 := by
  intro n
  induction n with
  | zero =>
      intro h hn
      have h0 : g (h.map Prod.snd) = false := by simpa using hn []
      simp [value, goalAgent, h0]
  | succ n ih =>
      intro h hn
      have h0 : g (h.map Prod.snd) = false := by simpa using hn []
      have hzero : ∀ a : Action, actionValue ρ (goalAgent g) t n h a = 0 := by
        intro a
        rw [actionValue]
        have hterms : ∀ o : Obs,
            ρ.cond h a o * value ρ (goalAgent g) t n (h ++ [(a, o)]) = 0 := by
          intro o
          rw [ih _ (goalNever_snoc hn a o)]
          ring
        simp [hterms]
      have hs : (⨆ a : Action, actionValue ρ (goalAgent g) t n h a) = 0 := by
        simp only [hzero]
        exact ciSup_const
      rw [value_succ, hs]
      simp [goalAgent, h0]

/-- The goal-seeking agent's value is nonnegative: its utilities are and its
horizon weights are. -/
public theorem goalAgent_value_nonneg [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (g : List Obs → Bool) (t : ℕ) :
    ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      0 ≤ value ρ (goalAgent g) t n h := by
  intro n
  induction n with
  | zero =>
      intro h
      by_cases hg : g (h.map Prod.snd)
      · simp [value, goalAgent, hg, (shortHorizon_pos t h.length).le]
      · simp [value, goalAgent, hg]
  | succ n ih =>
      intro h
      have hterm : 0 ≤ (goalAgent (Action := Action) g).horizon t h.length
          * (goalAgent (Action := Action) g).utility h := by
        by_cases hg : g (h.map Prod.snd)
        · simp [goalAgent, hg, (shortHorizon_pos t h.length).le]
        · simp [goalAgent, hg]
      have hav : ∀ a : Action, 0 ≤ actionValue ρ (goalAgent g) t n h a := by
        intro a
        rw [actionValue]
        exact tsum_nonneg fun o => mul_nonneg (hρ.nonneg h a o) (ih _)
      have hbdd := actionValue_bddAbove hρ (goalAgent g)
        (goalAgent_abs_utility_le_one g) t n h
      have hsup : 0 ≤ ⨆ a : Action, actionValue ρ (goalAgent g) t n h a :=
        (hav (Classical.arbitrary Action)).trans (le_ciSup hbdd _)
      rw [value_succ]
      linarith

/-- A bound on the goal-seeking value at every observation the belief gives
weight to is a bound on the action value. -/
private theorem goalAgent_actionValue_le_of_branch [Nonempty Action]
    {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (g : List Obs → Bool) (t n : ℕ)
    (h : AgentEquations.History Action Obs) (a : Action) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ o : Obs, ρ.cond h a o ≠ 0 →
      value ρ (goalAgent g) t n (h ++ [(a, o)]) ≤ B) :
    actionValue ρ (goalAgent g) t n h a ≤ B := by
  classical
  have hsum1 := actionValue_summable hρ (goalAgent g)
    (goalAgent_abs_utility_le_one g) t n h a
  have hsum2 : Summable (fun o : Obs => ρ.cond h a o * B) :=
    Summable.mul_right B (hρ.summable h a)
  have hle : ∀ o : Obs,
      ρ.cond h a o * value ρ (goalAgent g) t n (h ++ [(a, o)]) ≤ ρ.cond h a o * B := by
    intro o
    by_cases hc : ρ.cond h a o = 0
    · simp [hc]
    · exact mul_le_mul_of_nonneg_left (hb o hc) (hρ.nonneg h a o)
  rw [actionValue]
  refine (Summable.tsum_le_tsum hle hsum1 hsum2).trans ?_
  rw [tsum_mul_right]
  have htot := hρ.total_le_one h a
  have hnn : (0 : ℝ) ≤ ∑' o : Obs, ρ.cond h a o :=
    tsum_nonneg (g := ρ.cond h a) (hρ.nonneg h a)
  nlinarith [htot, hnn]

/--
**Print's side condition, doing the work it was stated for.**

With the goal reachable at most once, the goal-seeking agent's value at a history
is at most the horizon weight of that history's own step. Without the condition
the bound is false by a factor of two, because `Σ_{k ≥ j} 2^{t-k} = 2^{t-j+1}`.
-/
public theorem goalAgent_value_le_shortHorizon [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) {g : List Obs → Bool}
    (hg : ReachedAtMostOnce g) (t : ℕ) :
    ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      value ρ (goalAgent g) t n h ≤ shortHorizon t h.length := by
  intro n
  induction n with
  | zero =>
      intro h
      by_cases hgh : g (h.map Prod.snd)
      · simp [value, goalAgent, hgh]
      · simp [value, goalAgent, hgh, (shortHorizon_pos t h.length).le]
  | succ n ih =>
      intro h
      by_cases hgh : g (h.map Prod.snd) = true
      · have hnever : ∀ (a : Action) (o : Obs), GoalNever g (h ++ [(a, o)]) := by
          intro a o ps
          rcases Bool.eq_false_or_eq_true (g (h.map Prod.snd ++ (o :: ps))) with hb | hb
          · exact absurd (hg _ (o :: ps) hgh hb) (by simp)
          · simpa [List.map_append] using hb
        have hzero : ∀ a : Action, actionValue ρ (goalAgent g) t n h a = 0 := by
          intro a
          rw [actionValue]
          have hterms : ∀ o : Obs,
              ρ.cond h a o * value ρ (goalAgent g) t n (h ++ [(a, o)]) = 0 := by
            intro o
            rw [goalAgent_value_eq_zero_of_goalNever ρ g t n _ (hnever a o)]
            ring
          simp [hterms]
        have hs : (⨆ a : Action, actionValue ρ (goalAgent g) t n h a) = 0 := by
          simp only [hzero]
          exact ciSup_const
        rw [value_succ, hs]
        simp [goalAgent, hgh]
      · have hgh' : g (h.map Prod.snd) = false := by simpa using hgh
        have hav : ∀ a : Action,
            actionValue ρ (goalAgent g) t n h a ≤ shortHorizon t (h.length + 1) := by
          intro a
          refine goalAgent_actionValue_le_of_branch hρ g t n h a
            (shortHorizon_pos t (h.length + 1)).le (fun o _ => ?_)
          simpa using ih (h ++ [(a, o)])
        have hsup : (⨆ a : Action, actionValue ρ (goalAgent g) t n h a)
            ≤ shortHorizon t (h.length + 1) := ciSup_le hav
        have hmono := shortHorizon_succ_le t h.length
        have hterm : (goalAgent (Action := Action) g).horizon t h.length
            * (goalAgent (Action := Action) g).utility h = 0 := by
          simp [goalAgent, hgh']
        rw [value_succ, hterm]
        linarith

/--
**Print's `v(h no) < 2^{-lᵃ}`, at every depth.**

If no continuation the belief gives weight to reaches the goal in fewer than `l`
more steps, the goal-seeking agent's value is at most the horizon weight `l`
steps out — print's `2^{-lᵃ}` once the current step is print's `t`. This is the
bound print's Statement 2 argument uses, and it needs print's own *"reached at
most once"*, which `goalAgent_value_le_shortHorizon` carries.
-/
public theorem goalAgent_value_le_of_outOfReach [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) {g : List Obs → Bool}
    (hg : ReachedAtMostOnce g) (t : ℕ) :
    ∀ (l n : ℕ) (h : AgentEquations.History Action Obs), GoalOutOfReach ρ g l h →
      value ρ (goalAgent g) t n h ≤ shortHorizon t (h.length + l) := by
  intro l
  induction l with
  | zero =>
      intro n h _
      simpa using goalAgent_value_le_shortHorizon hρ hg t n h
  | succ l ih =>
      intro n h hnb
      obtain ⟨hgh, hext⟩ := hnb
      cases n with
      | zero =>
          have hz : value ρ (goalAgent g) t 0 h = 0 := by simp [value, goalAgent, hgh]
          rw [hz]
          exact (shortHorizon_pos t (h.length + (l + 1))).le
      | succ n =>
          have hav : ∀ a : Action, actionValue ρ (goalAgent g) t n h a
              ≤ shortHorizon t (h.length + (l + 1)) := by
            intro a
            refine goalAgent_actionValue_le_of_branch hρ g t n h a
              (shortHorizon_pos t (h.length + (l + 1))).le (fun o hc => ?_)
            have := ih n (h ++ [(a, o)]) (hext a o hc)
            simpa [Nat.add_right_comm, Nat.add_assoc] using this
          have hterm : (goalAgent (Action := Action) g).horizon t h.length
              * (goalAgent (Action := Action) g).utility h = 0 := by
            simp [goalAgent, hgh]
          rw [value_succ, hterm, zero_add]
          exact ciSup_le hav

/--
**Print's `v(h no)` bound at equation (2).**

The refusing action's value is at most the horizon weight `l` steps beyond the
step it takes, whenever no continuation of it reaches the goal sooner. With the
current step print's `t`, this is print's `2^{-lᵃ}`, and `shortHorizon_ahead`
reads the constant off.
-/
public theorem goalAgent_actionValue_le_of_outOfReach [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) {g : List Obs → Bool}
    (hg : ReachedAtMostOnce g) (t n l : ℕ)
    (h : AgentEquations.History Action Obs) (a : Action)
    (hnb : ∀ o : Obs, ρ.cond h a o ≠ 0 → GoalOutOfReach ρ g l (h ++ [(a, o)])) :
    actionValue ρ (goalAgent g) t n h a ≤ shortHorizon t (h.length + 1 + l) := by
  refine goalAgent_actionValue_le_of_branch hρ g t n h a
    (shortHorizon_pos t (h.length + 1 + l)).le (fun o hc => ?_)
  have := goalAgent_value_le_of_outOfReach hρ hg t l n (h ++ [(a, o)]) (hnb o hc)
  simpa using this

/-! ### Print's `v(h yes) > P(DB) · 2^{-|o⁺|}` at every `|o⁺|`

The `no` branch above bounds the refusing action from above. Print's other half
bounds the box-using action from **below**: *"if `v(h yes)` is the expected value
of programming the DB to produce `o⁺_t`, then `v(h yes) > P(DB) · 2^{−|o⁺_t|}`"*.

`goalAgent_actionValue_next_const` is that at `|o⁺| = 1`, where one constant
program suffices. For a longer `o⁺` the agent programs the box afresh at each
step, and what carries the bound is a **committed policy** — the same object
Statement 1's repair needed, and for the same reason: no maximum may intervene
between the steps, or the value is only bounded above.
-/

/--
**The policy reaches the goal in `j` steps.** At each step the belief is certain
of the observation the policy's action brings about — which is what programming
the box gives — and after `j` of them the goal predicate holds.

Print's *"programming the DB to produce `o⁺_t`"* is this at `j = |o⁺_t|`: the
box is reprogrammed at each step, so the observations are prescribed one by one
rather than by a single constant program.
-/
@[expose] public def ReachesIn (ρ : Belief Action Obs) (g : List Obs → Bool)
    (π : AgentEquations.History Action Obs → Action) :
    ℕ → AgentEquations.History Action Obs → Prop
  | 0, h => g (h.map Prod.snd) = true
  | j + 1, h => ∃ o : Obs, ρ.cond h (π h) o = 1 ∧
      (∀ o' : Obs, o' ≠ o → ρ.cond h (π h) o' = 0) ∧
      ReachesIn ρ g π j (h ++ [(π h, o)])

/-- A committed policy's value for the goal-seeking agent is nonnegative. -/
public theorem goalAgent_policyValue_nonneg {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (g : List Obs → Bool)
    (π : AgentEquations.History Action Obs → Action) (t : ℕ) :
    ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      0 ≤ Mixture.policyValue ρ (goalAgent g) π t n h := by
  intro n
  induction n with
  | zero =>
      intro h
      by_cases hgh : g (h.map Prod.snd) = true
      · simp [Mixture.policyValue, goalAgent, hgh, (shortHorizon_pos t h.length).le]
      · have hgh' : g (h.map Prod.snd) = false := by simpa using hgh
        simp [Mixture.policyValue, goalAgent, hgh']
  | succ n ih =>
      intro h
      have hterm : 0 ≤ (goalAgent (Action := Action) g).horizon t h.length
          * (goalAgent (Action := Action) g).utility h := by
        by_cases hgh : g (h.map Prod.snd) = true
        · simp [goalAgent, hgh, (shortHorizon_pos t h.length).le]
        · have hgh' : g (h.map Prod.snd) = false := by simpa using hgh
          simp [goalAgent, hgh']
      have hsum : 0 ≤ Mixture.policyActionValue ρ (goalAgent g) π t n h := by
        rw [Mixture.policyActionValue]
        exact tsum_nonneg fun o => mul_nonneg (hρ.nonneg h (π h) o) (ih _)
      rw [Mixture.policyValue_succ]
      linarith

/--
**Print's `v(h yes) ≥ 2^{-|o⁺|}`, at every `|o⁺|`.**

A committed policy that reaches the goal in `j` steps is worth at least the
horizon weight of the step it reaches it at. The maximum of equation (3) never
enters, which is exactly why a committed policy is the object that carries a
lower bound where the optimal value does not.
-/
public theorem shortHorizon_le_goalAgent_policyValue {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (g : List Obs → Bool)
    (π : AgentEquations.History Action Obs → Action) (t : ℕ) :
    ∀ (j n : ℕ) (h : AgentEquations.History Action Obs), j ≤ n → ReachesIn ρ g π j h →
      shortHorizon t (h.length + j) ≤ Mixture.policyValue ρ (goalAgent g) π t n h := by
  intro j
  induction j with
  | zero =>
      intro n h _ hr
      have hgh : g (h.map Prod.snd) = true := hr
      cases n with
      | zero => simp [Mixture.policyValue, goalAgent, hgh]
      | succ n =>
          have hsum : 0 ≤ Mixture.policyActionValue ρ (goalAgent g) π t n h := by
            rw [Mixture.policyActionValue]
            exact tsum_nonneg fun o =>
              mul_nonneg (hρ.nonneg h (π h) o) (goalAgent_policyValue_nonneg hρ g π t n _)
          rw [Mixture.policyValue_succ]
          have hterm : (goalAgent (Action := Action) g).horizon t h.length
              * (goalAgent (Action := Action) g).utility h = shortHorizon t h.length := by
            simp [goalAgent, hgh]
          rw [hterm]
          simpa using hsum
  | succ j ih =>
      intro n h hjn hr
      obtain ⟨o, ho1, ho0, hrest⟩ := hr
      cases n with
      | zero => exact absurd hjn (by omega)
      | succ n =>
          have hjn' : j ≤ n := by omega
          have hterm : 0 ≤ (goalAgent (Action := Action) g).horizon t h.length
              * (goalAgent (Action := Action) g).utility h := by
            by_cases hgh : g (h.map Prod.snd) = true
            · simp [goalAgent, hgh, (shortHorizon_pos t h.length).le]
            · have hgh' : g (h.map Prod.snd) = false := by simpa using hgh
              simp [goalAgent, hgh']
          have hcollapse : Mixture.policyActionValue ρ (goalAgent g) π t n h
              = Mixture.policyValue ρ (goalAgent g) π t n (h ++ [(π h, o)]) := by
            rw [Mixture.policyActionValue,
              tsum_eq_single o (fun o' hne => by rw [ho0 o' hne]; ring), ho1, one_mul]
          have hstep := ih n (h ++ [(π h, o)]) hjn' hrest
          rw [Mixture.policyValue_succ, hcollapse]
          have hlen : (h ++ [(π h, o)]).length + j = h.length + (j + 1) := by
            simp [Nat.add_right_comm, Nat.add_assoc]
          rw [hlen] at hstep
          linarith

/--
**Print's `v(h yes)` bound at equation (2).**

The box-using action's committed value is at least the horizon weight of the step
the goal is reached at, which is print's `2^{-|o⁺|}` once the current step is
print's `t`.
-/
public theorem shortHorizon_le_goalAgent_policyActionValue {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (g : List Obs → Bool)
    (π : AgentEquations.History Action Obs → Action) (t j n : ℕ)
    (h : AgentEquations.History Action Obs) (hjn : j ≤ n)
    (hr : ReachesIn ρ g π (j + 1) h) :
    shortHorizon t (h.length + 1 + j) ≤ Mixture.policyActionValue ρ (goalAgent g) π t n h := by
  obtain ⟨o, ho1, ho0, hrest⟩ := hr
  have hcollapse : Mixture.policyActionValue ρ (goalAgent g) π t n h
      = Mixture.policyValue ρ (goalAgent g) π t n (h ++ [(π h, o)]) := by
    rw [Mixture.policyActionValue,
      tsum_eq_single o (fun o' hne => by rw [ho0 o' hne]; ring), ho1, one_mul]
  have hstep := shortHorizon_le_goalAgent_policyValue hρ g π t j n (h ++ [(π h, o)]) hjn hrest
  simpa [hcollapse, Nat.add_right_comm, Nat.add_assoc] using hstep

/-! ### `r̄ < 1` is print's presupposition, not a hypothesis added here

`statement_one` carries `hrbar : rbar < 1`, and print states no such condition.
It is nevertheless print's, twice over.

Between `1` and `2` the printed threshold is **unattainable**: `1/(2 − r̄) ≥ 1`,
so no probability clears it and print's Statement says nothing about such an
`r̄`. Above `2` the threshold goes **negative**, every probability clears it, and
the comparison is then **false** — so the condition is not a convenience. Print's
`r̄` is *"the expected reward when not using the DB"*, which under print's own
`u : ℋ → [0,1]` is at most one; `r̄ < 1` is that bound with the degenerate case
excluded, and the degenerate case is exactly where the threshold stops biting.
-/

/-- **Between one and two the printed threshold is unattainable.** No probability
exceeds `1/(2 − r̄)` there, so print's Statement 1 is vacuous at such an `r̄`
rather than false. -/
public theorem threshold_unattainable_of_one_le {rbar p : ℝ}
    (h1 : 1 ≤ rbar) (h2 : rbar < 2) (hp : p ≤ 1) :
    ¬ (1 / (2 - rbar) < p) := by
  intro hlt
  have hpos : (0 : ℝ) < 2 - rbar := by linarith
  have hge : (1 : ℝ) ≤ 1 / (2 - rbar) := by
    rw [le_div_iff₀ hpos]; linarith
  linarith

/-- **Above two the comparison is false**, and not merely unproved. At `r̄ = 3`
the threshold is `-1`, which every probability clears, and the refusing action
is worth four times the box-using one while all of print's other bounds hold.
So dropping `r̄ < 1` from `mixture_lt_of_threshold` breaks it. -/
public theorem not_mixture_lt_of_threshold_without_rbar :
    ¬ ∀ p rbar vBoxYes vFreeYes vBoxNo vFreeNo : ℝ,
        0 ≤ p → p ≤ 1 →
        1 ≤ vBoxYes → 0 ≤ vFreeYes → vBoxNo ≤ rbar → vFreeNo ≤ 1 →
        1 / (2 - rbar) < p →
        p * vBoxNo + (1 - p) * vFreeNo < p * vBoxYes + (1 - p) * vFreeYes := by
  intro hall
  have h := hall (1 / 2) 3 1 0 3 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h

/--
**Statement 1 without the decomposition, at every observation type and any
maximum value** (Ring and Orseau, AGI 2011, Statement 1, PDF p. 5, and its
*Arguments*, PDF pp. 5–6). `statement_one_of_posterior` with `[Fintype Obs]`
dropped (print's eq. (2) sums over `o ∈ 𝒪` with no finiteness; source card S11)
and with print's maximum reward `1` generalised to a maximum value `vmax`, as in
`statement_one_scaled`: the box-using policy is worth at least `vmax` in the box
branch, the refusing action at most `vmax · r̄` there and at most `vmax` outside
it, with the threshold `P(DB) > 1/(2 - r̄)`. `r̄` is read as in
`statement_one_scaled`: the refusing action's box-branch value per in-window step,
continuation included, which is print's one-step `r̄` only at depth zero.
`rlAgent_statement_one_of_posterior` discharges the three `vmax` bounds for
print's reinforcement-learning agent at every depth inside its window.
-/
public theorem statement_one_of_posterior_scaled
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (vmax rbar : ℝ)
    (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ Mixture.policyActionValue ρbox ag π t n h)
    (hyesFree : 0 ≤ Mixture.policyActionValue ρfree ag π t n h)
    (hnoBox : actionValue ρbox ag t n h no ≤ vmax * rbar)
    (hnoFree : actionValue ρfree ag t n h no ≤ vmax)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hq0 := Mixture.posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hq1 := Mixture.posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hno := Mixture.actionValue_mixture_le_tsum hp0 hp1 hboxS hfreeS ag hu t n h no
  have hyes :
      Mixture.posterior p ρbox ρfree h * Mixture.policyActionValue ρbox ag π t n h
        + (1 - Mixture.posterior p ρbox ρfree h)
          * Mixture.policyActionValue ρfree ag π t n h
      ≤ actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) := by
    rw [← Mixture.policyActionValue_mixture_tsum hp0 hp1 hboxS hfreeS ag hu π t n h]
    exact Mixture.policyActionValue_le_actionValue_tsum
      (Mixture.mixtureBelief_isSubprobability hp0 hp1 hboxS hfreeS) ag hu π t n h
  have hmid := mixture_lt_of_threshold hq0 hq1 hyesBox hyesFree hnoBox hnoFree
    (scaled_threshold hvmax hrbar hthresh)
  linarith

/--
**Statement 1 without the decomposition, because the decomposition is false.**

`statement_one` above takes print's `P(DB)`-weighted average as a hypothesis,
and `Examples…not_mixesAt_one` shows that hypothesis fails above remaining depth
zero. This is print's conclusion without it.

Three things change, and each is forced rather than chosen.

* The belief is a genuine Bayesian mixture, `Mixture.mixtureBelief`, and the
  weight is `Mixture.posterior` at the history where the comparison is made. A
  fixed weight is not a mixture of two environments but a third that never
  learns. Print's `P(DB)` is a credence, so the posterior is the faithful
  reading of it even though print never indexes it by history.
* The two branches are bounded in **opposite directions**, because those are the
  directions available. The `no` branch is bounded above by
  `Mixture.actionValue_mixture_le`, which is all the optimal value gives. The
  `yes` branch is bounded **below** through a committed policy, by
  `Mixture.policyActionValue_mixture`, whose mixing is an equality precisely
  because no maximum intervenes. Print used one equality for both.
* Print's unstated premise that a box-using action exists is discharged rather
  than assumed: the action compared against is the one `π` takes, and the
  hypotheses are about that policy's value.
-/
public theorem statement_one_of_posterior [Fintype Obs] [Nonempty Action]
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (rbar : ℝ)
    (hyesBox : 1 ≤ Mixture.policyActionValue ρbox ag π t n h)
    (hyesFree : 0 ≤ Mixture.policyActionValue ρfree ag π t n h)
    (hnoBox : actionValue ρbox ag t n h no ≤ rbar)
    (hnoFree : actionValue ρfree ag t n h no ≤ 1)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) :=
  statement_one_of_posterior_scaled ρbox ρfree hp0 hp1 hboxS hfreeS ag hu t n h π no 1 rbar
    one_pos hyesBox hyesFree (by rwa [one_mul]) hnoFree hrbar hthresh

/--
**Statement 2.** *The goal-seeking agent will also use the delusion box.*

Print's threshold is `P(DB) > 2^{|o⁺|-lᵃ}`, where `o⁺` is the shortest
observation string satisfying the goal and `lᵃ` the length of the action string
that reaches the goal without the box; print adds that this "is easily
satisfiable once `|o⁺| < lᵃ`". Written with `k` for `|o⁺|` and `l` for `lᵃ`, the
threshold is `(1/2)^l < p · (1/2)^k`.

**Narrower than print** in the same three ways `statement_one` is, plus one more:
print's `2^{-|o⁺|}` and `2^{-lᵃ}` are values it computes from its universal prior
and its goal predicate, and here they are hypotheses about the two actions'
values. Nothing here derives them.
-/
public theorem statement_two
    (ρ ρbox ρfree : Belief Action Obs) (ag : Agent Action Obs)
    (p : ℝ) (t n : ℕ) (h : AgentEquations.History Action Obs)
    (yes no : Action) (k l : ℕ)
    (hmix : MixesAt ρ ρbox ρfree ag p t n h)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hyesBox : (1 / 2 : ℝ) ^ k ≤ actionValue ρbox ag t n h yes)
    (hyesFree : 0 ≤ actionValue ρfree ag t n h yes)
    (hnoBox : actionValue ρbox ag t n h no ≤ (1 / 2 : ℝ) ^ l)
    (hnoFree : actionValue ρfree ag t n h no ≤ (1 / 2 : ℝ) ^ l)
    (hthresh : (1 / 2 : ℝ) ^ l < p * (1 / 2 : ℝ) ^ k) :
    actionValue ρ ag t n h no < actionValue ρ ag t n h yes := by
  rw [hmix no, hmix yes]
  exact mixture_lt_of_gap hp0 hp1 hyesBox hyesFree hnoBox hnoFree hthresh

/--
**Statement 2 without the decomposition, at every observation type** (Ring and
Orseau, AGI 2011, Statement 2, PDF p. 6): `statement_two_of_posterior` with
`[Fintype Obs]` dropped, as print's eq. (2) has no finiteness (source card S11).
-/
public theorem statement_two_of_posterior_tsum
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (k l : ℕ)
    (hyesBox : (1 / 2 : ℝ) ^ k ≤ Mixture.policyActionValue ρbox ag π t n h)
    (hyesFree : 0 ≤ Mixture.policyActionValue ρfree ag π t n h)
    (hnoBox : actionValue ρbox ag t n h no ≤ (1 / 2 : ℝ) ^ l)
    (hnoFree : actionValue ρfree ag t n h no ≤ (1 / 2 : ℝ) ^ l)
    (hthresh : (1 / 2 : ℝ) ^ l
      < Mixture.posterior p ρbox ρfree h * (1 / 2 : ℝ) ^ k) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hq0 := Mixture.posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hq1 := Mixture.posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hno := Mixture.actionValue_mixture_le_tsum hp0 hp1 hboxS hfreeS ag hu t n h no
  have hyes :
      Mixture.posterior p ρbox ρfree h * Mixture.policyActionValue ρbox ag π t n h
        + (1 - Mixture.posterior p ρbox ρfree h)
          * Mixture.policyActionValue ρfree ag π t n h
      ≤ actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) := by
    rw [← Mixture.policyActionValue_mixture_tsum hp0 hp1 hboxS hfreeS ag hu π t n h]
    exact Mixture.policyActionValue_le_actionValue_tsum
      (Mixture.mixtureBelief_isSubprobability hp0 hp1 hboxS hfreeS) ag hu π t n h
  have hmid := mixture_lt_of_gap hq0 hq1 hyesBox hyesFree hnoBox hnoFree hthresh
  linarith

/--
**Statement 2 without the decomposition**, by the same repair as Statement 1 and
against print's own second comparison shape: `2^{-lᵃ}` bounds the refusing action
in **both** branches, where Statement 1 has `r̄` in one and the maximum in the
other, which is why `mixture_lt_of_gap` is a separate lemma.
-/
public theorem statement_two_of_posterior [Fintype Obs] [Nonempty Action]
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (k l : ℕ)
    (hyesBox : (1 / 2 : ℝ) ^ k ≤ Mixture.policyActionValue ρbox ag π t n h)
    (hyesFree : 0 ≤ Mixture.policyActionValue ρfree ag π t n h)
    (hnoBox : actionValue ρbox ag t n h no ≤ (1 / 2 : ℝ) ^ l)
    (hnoFree : actionValue ρfree ag t n h no ≤ (1 / 2 : ℝ) ^ l)
    (hthresh : (1 / 2 : ℝ) ^ l
      < Mixture.posterior p ρbox ρfree h * (1 / 2 : ℝ) ^ k) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) :=
  statement_two_of_posterior_tsum ρbox ρfree hp0 hp1 hboxS hfreeS ag hu t n h π no k l
    hyesBox hyesFree hnoBox hnoFree hthresh

/--
**Statement 3 without the decomposition**, which is Statement 1's repair at
`r̄ = 0` exactly as `statement_three` is `statement_one` at `r̄ = 0`: print's
prediction bound gives the refusing action no value in the branch where a box is
present, because there the true inner environment is the one being deluded away.
-/
public theorem statement_three_of_posterior [Fintype Obs] [Nonempty Action]
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action)
    (hyesBox : 1 ≤ Mixture.policyActionValue ρbox ag π t n h)
    (hyesFree : 0 ≤ Mixture.policyActionValue ρfree ag π t n h)
    (hnoBox : actionValue ρbox ag t n h no ≤ 0)
    (hnoFree : actionValue ρfree ag t n h no ≤ 1)
    (hthresh : 1 / 2 < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) :=
  statement_one_of_posterior ρbox ρfree hp0 hp1 hboxS hfreeS ag hu t n h π no 0
    hyesBox hyesFree hnoBox hnoFree (by norm_num) (by simpa using hthresh)

/--
**Statement 3 without the decomposition, at every observation type and any
maximum value** (Ring and Orseau, AGI 2011, Statement 3, PDF p. 6):
`statement_one_of_posterior_scaled` at `r̄ = 0`, as `statement_three_of_posterior`
is `statement_one_of_posterior` at `r̄ = 0`. No `[Fintype Obs]`.
-/
public theorem statement_three_of_posterior_scaled
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (vmax : ℝ)
    (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ Mixture.policyActionValue ρbox ag π t n h)
    (hyesFree : 0 ≤ Mixture.policyActionValue ρfree ag π t n h)
    (hnoBox : actionValue ρbox ag t n h no ≤ 0)
    (hnoFree : actionValue ρfree ag t n h no ≤ vmax)
    (hthresh : 1 / 2 < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) ag t n h (π h) :=
  statement_one_of_posterior_scaled ρbox ρfree hp0 hp1 hboxS hfreeS ag hu t n h π no vmax 0
    hvmax hyesBox hyesFree (by rwa [mul_zero]) hnoFree (by norm_num)
    (by norm_num; linarith)

/-! ### Statement 1's bounds for the reinforcement-learning agent at every depth

Print's *Arguments* for Statement 1 (PDF pp. 5–6): *"The agent can program the DB
to produce a constant reward of 1"*, made for `A_rl` with the window horizon
`w(t, k) = 1` if `k - t ≤ m` and the full recursion. At remaining depth `n` inside
the window the box branch is then worth the constant reward times the in-window
step count, which is the absolute horizon budget, and no action is worth more
(`abs_actionValue_le_horizonBudget`). So `vmax` is that budget, and the depth-zero
lemmas above are its `n = 0` case.

The delusion-box premise is stated on the belief, *"the box-using action yields
the constant observation `k` with probability one"*, which every mixture of
delusion-box environments whose box runs the constant program satisfies
(`diracBelief_next_cond_const` for one deterministic global environment).
-/

/-- Print's window horizon takes the values `0` and `1`, so it is its own absolute
value. -/
public theorem abs_windowHorizon (m t k : ℕ) : |windowHorizon m t k| = windowHorizon m t k := by
  unfold windowHorizon
  split_ifs <;> norm_num

/-- A reward in print's `[0, 1]` (or `[-1, 1]`) bounds the reinforcement-learning
utility. -/
public theorem rlAgent_abs_utility_le (reward : Obs → ℝ) (m : ℕ)
    (hr : ∀ o, |reward o| ≤ 1) (h : AgentEquations.History Action Obs) :
    |(rlAgent (Action := Action) reward m).utility h| ≤ 1 := by
  change |lastReward reward h| ≤ 1
  unfold lastReward
  split
  · norm_num
  · exact hr _

/-- Inside the window the absolute horizon budget is positive. -/
public theorem rlAgent_horizonBudget_pos (reward : Obs → ℝ) {m t : ℕ} (n : ℕ) {k : ℕ}
    (hk : k ≤ t + m) : 0 < horizonBudget (rlAgent (Action := Action) reward m) t n k := by
  have h1 : |(rlAgent (Action := Action) reward m).horizon t k| = 1 := by
    simp [rlAgent, windowHorizon, hk]
  cases n with
  | zero => simp only [horizonBudget]; rw [h1]; norm_num
  | succ n =>
    simp only [horizonBudget]
    rw [h1]
    linarith [horizonBudget_nonneg (rlAgent (Action := Action) reward m) t n (k + 1)]

/-- **Print's "the agent can program the DB to produce a constant reward", at every
depth.** If the belief gives the policy's action the observation `k` with
probability one at every history, the reinforcement-learning agent's committed
action value at remaining depth `n` is the reward of `k` times the absolute
horizon budget of the next `n + 1` steps, i.e. times the in-window step count. -/
public theorem rlAgent_policyActionValue_const {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (reward : Obs → ℝ) (m : ℕ)
    (π : AgentEquations.History Action Obs → Action) {k : Obs}
    (hk : ∀ h', ρ.cond h' (π h') k = 1) (t : ℕ) :
    ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      Mixture.policyActionValue ρ (rlAgent reward m) π t n h
        = reward k * horizonBudget (rlAgent (Action := Action) reward m) t n (h.length + 1) := by
  have collapse : ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      Mixture.policyActionValue ρ (rlAgent reward m) π t n h
        = Mixture.policyValue ρ (rlAgent reward m) π t n (h ++ [(π h, k)]) := by
    intro n h
    rw [Mixture.policyActionValue, tsum_eq_single k (fun o ho => by
      rw [hρ.cond_eq_zero_of_eq_one (hk h) ho, zero_mul]), hk h, one_mul]
  intro n
  induction n with
  | zero =>
    intro h
    rw [collapse, Mixture.policyValue_zero]
    simp only [horizonBudget]
    simp [rlAgent, lastReward, abs_windowHorizon, mul_comm]
  | succ n ih =>
    intro h
    rw [collapse, Mixture.policyValue_succ, ih]
    simp only [horizonBudget]
    simp [rlAgent, lastReward, abs_windowHorizon]
    ring

/-- A nonnegative reward makes every committed action value of the
reinforcement-learning agent nonnegative, at every depth. -/
public theorem rlAgent_policyActionValue_nonneg {ρ : Belief Action Obs}
    (hρ : ∀ h a o, 0 ≤ ρ.cond h a o) (reward : Obs → ℝ) (hr : ∀ o, 0 ≤ reward o) (m : ℕ)
    (π : AgentEquations.History Action Obs → Action) (t n : ℕ)
    (h : AgentEquations.History Action Obs) :
    0 ≤ Mixture.policyActionValue ρ (rlAgent reward m) π t n h := by
  refine Mixture.policyActionValue_nonneg hρ _ π t (fun h' => ?_) n h
  have hw : 0 ≤ windowHorizon m t h'.length := by unfold windowHorizon; split_ifs <;> norm_num
  have hl : 0 ≤ lastReward reward h' := by
    unfold lastReward
    split
    · norm_num
    · exact hr _
  exact mul_nonneg hw hl

/-- One deterministic global environment whose box runs a constant program
satisfies the delusion-box premise of `rlAgent_policyActionValue_const`. -/
public theorem diracBelief_next_cond_const {P Ae O : Type*} [DecidableEq O]
    (G : GlobalEnv P Ae O) {d : P} {k : O} (hd : G.IsConstant d k)
    (h : AgentEquations.History (Act P Ae) O) (a : Act P Ae) (ha : program a = d) :
    (diracBelief G.next).cond h a k = 1 := by
  simp [diracBelief, G.next_const hd h a ha]

/--
**Statement 1 for print's reinforcement-learning agent at every depth inside its
window** (Ring and Orseau, AGI 2011, Statement 1, PDF p. 5, *Arguments* PDF
pp. 5–6), at every observation type. The maximum value is
`vmax = horizonBudget (rlAgent reward m) t n (|h| + 1)`, the number of in-window
steps among the next `n + 1`. Three of print's four branch bounds are theorems
here: the box-using policy is worth exactly `vmax` in the box branch (the box
yields an observation `k` of reward `1`), it is worth at least `0` outside it
(rewards in `[0, 1]`), and no action is worth more than `vmax` outside it. The
fourth, `v(h no) ≤ vmax · r̄` in the box branch, stays a hypothesis. **It is not
print's `r̄` above depth zero**: the refusing action's box-branch value includes
the optimal continuation, which may program the box at later steps, so the
effective `r̄` is at least `(N - 1)/N` for `N` in-window steps even when the inner
environment pays nothing, and the threshold `1/(2 - r̄)` rises towards `1` with
depth (the depth-one witness needs `r̄ = 1/2` where print's one-step `r̄` is `0`).
Print's threshold at print's own `r̄` is claimed at depth zero only.
-/
public theorem rlAgent_statement_one_of_posterior {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (reward : Obs → ℝ) (hr0 : ∀ o, 0 ≤ reward o) (hr1 : ∀ o, reward o ≤ 1)
    (m t n : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action) {k : Obs} (hk1 : reward k = 1)
    (hbox : ∀ h', ρbox.cond h' (π h') k = 1) (no : Action) (rbar : ℝ)
    (hnoBox : actionValue ρbox (rlAgent reward m) t n h no
      ≤ horizonBudget (rlAgent (Action := Action) reward m) t n (h.length + 1) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgent reward m) t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgent reward m) t n h (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hr : ∀ o, |reward o| ≤ 1 := fun o => abs_le.mpr ⟨by linarith [hr0 o], hr1 o⟩
  have hu := rlAgent_abs_utility_le (Action := Action) reward m hr
  refine statement_one_of_posterior_scaled ρbox ρfree hp0 hp1 hboxS hfreeS _ hu t n h π no
    _ rbar (rlAgent_horizonBudget_pos reward n hwin) ?_ ?_ hnoBox ?_ hrbar hthresh
  · rw [rlAgent_policyActionValue_const hboxS reward m π hbox t n h, hk1, one_mul]
  · exact rlAgent_policyActionValue_nonneg hfreeS.nonneg reward hr0 m π t n h
  · exact (le_abs_self _).trans (abs_actionValue_le_horizonBudget hfreeS _ hu t n h no)

/-! ### Statement 1's bounds for the reinforcement-learning agent at any nonnegative horizon

The lemmas above at rlAgentWith reward w, for any horizon w equal to one on the
window (`OneOnWindow`, print's clause) and nonnegative at the time index used. The
nonnegativity is what the proofs use: the box-using value is the horizon sum and
the bound on every action is the absolute horizon sum, which agree when w ≥ 0.
At w = windowHorizon m these are the `rlAgent` lemmas (`rlAgent_eq_rlAgentWith`).
-/

/-- A reward in print's range [0, 1] (or in [-1, 1]) bounds the reinforcement-learning
utility at any horizon. -/
public theorem rlAgentWith_abs_utility_le (reward : Obs → ℝ) (w : ℕ → ℕ → ℝ)
    (hr : ∀ o, |reward o| ≤ 1) (h : AgentEquations.History Action Obs) :
    |(rlAgentWith (Action := Action) reward w).utility h| ≤ 1 := by
  change |lastReward reward h| ≤ 1
  unfold lastReward
  split
  · norm_num
  · exact hr _

/-- Inside the window the absolute horizon budget is positive, at any horizon
satisfying print's clause. -/
public theorem rlAgentWith_horizonBudget_pos (reward : Obs → ℝ) {m : ℕ} {w : ℕ → ℕ → ℝ}
    (hw : OneOnWindow m w) {t : ℕ} (n : ℕ) {k : ℕ} (hk : k ≤ t + m) :
    0 < horizonBudget (rlAgentWith (Action := Action) reward w) t n k := by
  have h1 : |(rlAgentWith (Action := Action) reward w).horizon t k| = 1 := by
    simp [rlAgentWith, hw t k hk]
  cases n with
  | zero => simp only [horizonBudget]; rw [h1]; norm_num
  | succ n =>
    simp only [horizonBudget]
    rw [h1]
    linarith [horizonBudget_nonneg (rlAgentWith (Action := Action) reward w) t n (k + 1)]

/-- **"The agent can program the DB to produce a constant reward", at any
nonnegative horizon.** If the belief gives the policy's action the observation k
with probability one at every history, the committed action value at remaining
depth n is the reward of k times the absolute horizon budget of the next
n + 1 steps. -/
public theorem rlAgentWith_policyActionValue_const {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (reward : Obs → ℝ) {w : ℕ → ℕ → ℝ} {t : ℕ}
    (hw0 : ∀ k, 0 ≤ w t k) (π : AgentEquations.History Action Obs → Action) {k : Obs}
    (hk : ∀ h', ρ.cond h' (π h') k = 1) :
    ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      Mixture.policyActionValue ρ (rlAgentWith reward w) π t n h
        = reward k * horizonBudget (rlAgentWith (Action := Action) reward w) t n
            (h.length + 1) := by
  have habs : ∀ j, |w t j| = w t j := fun j => abs_of_nonneg (hw0 j)
  have collapse : ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      Mixture.policyActionValue ρ (rlAgentWith reward w) π t n h
        = Mixture.policyValue ρ (rlAgentWith reward w) π t n (h ++ [(π h, k)]) := by
    intro n h
    rw [Mixture.policyActionValue, tsum_eq_single k (fun o ho => by
      rw [hρ.cond_eq_zero_of_eq_one (hk h) ho, zero_mul]), hk h, one_mul]
  intro n
  induction n with
  | zero =>
    intro h
    rw [collapse, Mixture.policyValue_zero]
    simp only [horizonBudget]
    simp [rlAgentWith, lastReward, habs, mul_comm]
  | succ n ih =>
    intro h
    rw [collapse, Mixture.policyValue_succ, ih]
    simp only [horizonBudget]
    simp [rlAgentWith, lastReward, habs]
    ring

/-- A nonnegative reward and a nonnegative horizon make every committed action
value of the reinforcement-learning agent nonnegative, at every depth. -/
public theorem rlAgentWith_policyActionValue_nonneg {ρ : Belief Action Obs}
    (hρ : ∀ h a o, 0 ≤ ρ.cond h a o) (reward : Obs → ℝ) (hr : ∀ o, 0 ≤ reward o)
    {w : ℕ → ℕ → ℝ} {t : ℕ} (hw0 : ∀ k, 0 ≤ w t k)
    (π : AgentEquations.History Action Obs → Action) (n : ℕ)
    (h : AgentEquations.History Action Obs) :
    0 ≤ Mixture.policyActionValue ρ (rlAgentWith reward w) π t n h := by
  refine Mixture.policyActionValue_nonneg hρ _ π t (fun h' => ?_) n h
  have hl : 0 ≤ lastReward reward h' := by
    unfold lastReward
    split
    · norm_num
    · exact hr _
  exact mul_nonneg (hw0 _) hl

/--
**Statement 1 for print's reinforcement-learning agent at any nonnegative horizon
equal to one on its window** (Ring and Orseau, AGI 2011, Statement 1, PDF p. 5,
*Arguments* PDF pp. 5–6; the horizon clause of A_rl, PDF p. 4, which states no
value off the window). `rlAgent_statement_one_of_posterior` with the window
indicator replaced by any horizon w satisfying print's clause OneOnWindow m w
and nonnegative at time t. The maximum value is the absolute horizon budget of
the next n + 1 steps; the refusing bound v(h no) ≤ vmax · r̄ stays a hypothesis,
read as in `rlAgent_statement_one_of_posterior`.
-/
public theorem rlAgentWith_statement_one_of_posterior {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (reward : Obs → ℝ) (hr0 : ∀ o, 0 ≤ reward o) (hr1 : ∀ o, reward o ≤ 1)
    (m : ℕ) (w : ℕ → ℕ → ℝ) (hw : OneOnWindow m w) (t : ℕ) (hw0 : ∀ k, 0 ≤ w t k)
    (n : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action) {k : Obs} (hk1 : reward k = 1)
    (hbox : ∀ h', ρbox.cond h' (π h') k = 1) (no : Action) (rbar : ℝ)
    (hnoBox : actionValue ρbox (rlAgentWith reward w) t n h no
      ≤ horizonBudget (rlAgentWith (Action := Action) reward w) t n (h.length + 1) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgentWith reward w) t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgentWith reward w) t n h
          (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hr : ∀ o, |reward o| ≤ 1 := fun o => abs_le.mpr ⟨by linarith [hr0 o], hr1 o⟩
  have hu := rlAgentWith_abs_utility_le (Action := Action) reward w hr
  refine statement_one_of_posterior_scaled ρbox ρfree hp0 hp1 hboxS hfreeS _ hu t n h π no
    _ rbar (rlAgentWith_horizonBudget_pos reward hw n hwin) ?_ ?_ hnoBox ?_ hrbar hthresh
  · rw [rlAgentWith_policyActionValue_const hboxS reward hw0 π hbox n h, hk1, one_mul]
  · exact rlAgentWith_policyActionValue_nonneg hfreeS.nonneg reward hr0 hw0 π n h
  · exact (le_abs_self _).trans (abs_actionValue_le_horizonBudget hfreeS _ hu t n h no)

/-! ### Statement 3's bounds for the prediction agent at every depth

Print's *Arguments* for Statement 3 (Ring and Orseau, AGI 2011, PDF p. 6): the
prediction agent *"will immediately program the DB to output a predictable
sequence"*. Its utility is one exactly when the prediction was correct
(`predictionAgent_utility_snoc`) and its horizon is the window, so a box that
outputs, at every step, the observation the agent predicts makes every in-window
prediction correct and the box branch is worth the absolute horizon budget, which
no action exceeds. These are the analogues of the reinforcement-learning lemmas
above.
-/

/-- The prediction agent's utility is `0` or `1`, so it is nonnegative. -/
public theorem predictionAgent_utility_nonneg [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ)
    (h : AgentEquations.History Action Obs) :
    0 ≤ (predictionAgent predict m).utility h := by
  simp only [predictionAgent]
  split
  · norm_num
  · split_ifs <;> norm_num

/-- The prediction agent's utility is `0` or `1`, so it is bounded by one. -/
public theorem predictionAgent_abs_utility_le [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ)
    (h : AgentEquations.History Action Obs) :
    |(predictionAgent predict m).utility h| ≤ 1 := by
  simp only [predictionAgent]
  split
  · norm_num
  · split_ifs <;> norm_num

/-- Inside the window the prediction agent's absolute horizon budget is
positive. -/
public theorem predictionAgent_horizonBudget_pos [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) {m t : ℕ} (n : ℕ) {k : ℕ}
    (hk : k ≤ t + m) : 0 < horizonBudget (predictionAgent predict m) t n k := by
  have h1 : |(predictionAgent predict m).horizon t k| = 1 := by
    simp [predictionAgent, windowHorizon, hk]
  cases n with
  | zero => simp only [horizonBudget]; rw [h1]; norm_num
  | succ n =>
    simp only [horizonBudget]
    rw [h1]
    linarith [horizonBudget_nonneg (predictionAgent predict m) t n (k + 1)]

/-- **Print's "program the DB to output a predictable sequence", at every depth.**
If the belief gives the policy's action the observation the agent predicts with
probability one at every history, every prediction is correct and the prediction
agent's committed action value at remaining depth `n` is the absolute horizon
budget of the next `n + 1` steps, i.e. the in-window step count. -/
public theorem predictionAgent_policyActionValue_correct [DecidableEq Obs]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ)
    (π : AgentEquations.History Action Obs → Action)
    (hk : ∀ h', ρ.cond h' (π h') (predict h') = 1) (t : ℕ) :
    ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      Mixture.policyActionValue ρ (predictionAgent predict m) π t n h
        = horizonBudget (predictionAgent predict m) t n (h.length + 1) := by
  have collapse : ∀ (n : ℕ) (h : AgentEquations.History Action Obs),
      Mixture.policyActionValue ρ (predictionAgent predict m) π t n h
        = Mixture.policyValue ρ (predictionAgent predict m) π t n
            (h ++ [(π h, predict h)]) := by
    intro n h
    rw [Mixture.policyActionValue, tsum_eq_single (predict h) (fun o ho => by
      rw [hρ.cond_eq_zero_of_eq_one (hk h) ho, zero_mul]), hk h, one_mul]
  intro n
  induction n with
  | zero =>
    intro h
    rw [collapse, Mixture.policyValue_zero, predictionAgent_utility_snoc]
    simp only [horizonBudget]
    simp [predictionAgent, abs_windowHorizon]
  | succ n ih =>
    intro h
    rw [collapse, Mixture.policyValue_succ, ih, predictionAgent_utility_snoc]
    simp only [horizonBudget]
    simp [predictionAgent, abs_windowHorizon]

/-- Every committed action value of the prediction agent is nonnegative, at every
depth. -/
public theorem predictionAgent_policyActionValue_nonneg [DecidableEq Obs]
    {ρ : Belief Action Obs} (hρ : ∀ h a o, 0 ≤ ρ.cond h a o)
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ)
    (π : AgentEquations.History Action Obs → Action) (t n : ℕ)
    (h : AgentEquations.History Action Obs) :
    0 ≤ Mixture.policyActionValue ρ (predictionAgent predict m) π t n h := by
  refine Mixture.policyActionValue_nonneg hρ _ π t (fun h' => ?_) n h
  have hw : 0 ≤ windowHorizon m t h'.length := by unfold windowHorizon; split_ifs <;> norm_num
  exact mul_nonneg hw (predictionAgent_utility_nonneg predict m h')

/-- One deterministic global environment satisfies the box premise of
`predictionAgent_policyActionValue_correct` when the policy's action at every
history carries a box program constant at the observation predicted there. -/
public theorem diracBelief_next_cond_predict {P Ae O : Type*} [DecidableEq O]
    (G : GlobalEnv P Ae O) (predict : AgentEquations.History (Act P Ae) O → O)
    (π : AgentEquations.History (Act P Ae) O → Act P Ae)
    (hG : ∀ h, G.IsConstant (program (π h)) (predict h))
    (h : AgentEquations.History (Act P Ae) O) :
    (diracBelief G.next).cond h (π h) (predict h) = 1 :=
  diracBelief_next_cond_const G (hG h) h (π h) rfl

/--
**Statement 3 for print's prediction agent at every depth inside its window**
(Ring and Orseau, AGI 2011, Statement 3, PDF p. 6, *Arguments* PDF p. 6:
*"it will immediately program the DB to output a predictable sequence"*), at every
observation type and for an arbitrary predictor. The maximum value is
`vmax = horizonBudget (predictionAgent predict m) t n (|h| + 1)`, the number of
in-window steps among the next `n + 1`. Three of the four branch bounds of
`statement_one_of_posterior_scaled` are theorems here: the box-using policy is
worth exactly `vmax` in the box branch (the box outputs the predicted observation
with probability one, so every prediction is correct), it is worth at least `0`
outside it (utility in `{0, 1}`), and no action is worth more than `vmax` outside
it. The fourth, the refusing action's box-branch bound `v(h no) ≤ vmax · r̄` with
`r̄ < 1` and threshold `1/(2 - r̄)`, stays a hypothesis: print's *"since these
observations may generate prediction errors"*. As for
`rlAgent_statement_one_of_posterior`, `r̄` is the refusing action's box-branch
value per in-window step **including the optimal continuation**, which may program
the box at later steps, so it is not a one-step quantity. The `r̄ = 0` of
`statement_three_of_posterior` fails wherever another in-window step follows the
refusing one: at window `m = 1` and depth `n = 1`, refusing now and programming the
box at the next step earns one correct prediction.
-/
public theorem predictionAgent_statement_three_of_posterior [DecidableEq Obs] {p : ℝ}
    (ρbox ρfree : Belief Action Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Obs)
    (m t n : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action)
    (hbox : ∀ h', ρbox.cond h' (π h') (predict h') = 1) (no : Action) (rbar : ℝ)
    (hnoBox : actionValue ρbox (predictionAgent predict m) t n h no
      ≤ horizonBudget (predictionAgent predict m) t n (h.length + 1) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgent predict m) t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgent predict m) t n h
          (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hu := predictionAgent_abs_utility_le predict m
  refine statement_one_of_posterior_scaled ρbox ρfree hp0 hp1 hboxS hfreeS _ hu t n h π no
    _ rbar (predictionAgent_horizonBudget_pos predict n hwin) ?_ ?_ hnoBox ?_ hrbar hthresh
  · rw [predictionAgent_policyActionValue_correct hboxS predict m π hbox t n h]
  · exact predictionAgent_policyActionValue_nonneg hfreeS.nonneg predict m π t n h
  · exact (le_abs_self _).trans (abs_actionValue_le_horizonBudget hfreeS _ hu t n h no)

/-! ### Statements 1 to 3 at the infinite-horizon value

Ring and Orseau's recursion (3) has no terminal condition (source card S11), so
print's comparison is between untruncated values: `infiniteActionValue`, which
`ValueBounds.infiniteValue_eq` ties to print's recursion at
`Belief.IsSubprobability`, `|u| ≤ 1` and an absolutely summable horizon. The
branch bounds are stated on the infinite objects, which is wider than bounding
every depth: a bound at every depth gives the bound on the limit (`le_of_tendsto`),
not conversely. The strict comparison survives the limit because the one strict
step is arithmetic on the limit numbers.

**Horizon summability.** Print states none (source card S11). The horizons of
print's named agents are summable: the window horizon has finite support and the
goal-seeking `shortHorizon` is geometric (`summable_abs_shortHorizon`).
Conditionally summable signed horizons are outside these statements.
-/

/-- Print's goal-seeking horizon `w(t, k) = 2^{t-k}` is absolutely summable in
`k`: it is `2^t · (1/2)^k`. -/
public theorem summable_abs_shortHorizon (t : ℕ) : Summable (fun k ↦ |shortHorizon t k|) := by
  have heq : (fun k : ℕ ↦ |shortHorizon t k|) = fun k ↦ (2 : ℝ) ^ t * (1 / 2 : ℝ) ^ k := by
    funext k
    rw [abs_of_pos (shortHorizon_pos t k), shortHorizon, zpow_sub₀ (by norm_num),
      zpow_natCast, zpow_natCast, one_div, inv_pow, div_eq_mul_inv]
  rw [heq]
  exact summable_geometric_two.mul_left _

/-- **Statement 1 without the decomposition, at the infinite-horizon value**: the
limit form of `statement_one_of_posterior_scaled`, with the branch bounds on the
untruncated values. -/
public theorem statement_one_of_posterior_infinite
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (vmax rbar : ℝ)
    (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ Mixture.infinitePolicyActionValue ρbox ag π t h)
    (hyesFree : 0 ≤ Mixture.infinitePolicyActionValue ρfree ag π t h)
    (hnoBox : infiniteActionValue ρbox ag t h no ≤ vmax * rbar)
    (hnoFree : infiniteActionValue ρfree ag t h no ≤ vmax)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h no
      < infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hq0 := Mixture.posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hq1 := Mixture.posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hno := Mixture.infiniteActionValue_mixture_le hp0 hp1 hboxS hfreeS ag hu t hw h no
  have hyes :
      Mixture.posterior p ρbox ρfree h * Mixture.infinitePolicyActionValue ρbox ag π t h
        + (1 - Mixture.posterior p ρbox ρfree h)
          * Mixture.infinitePolicyActionValue ρfree ag π t h
      ≤ infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h (π h) := by
    rw [← Mixture.infinitePolicyActionValue_mixture hp0 hp1 hboxS hfreeS ag hu π t hw h]
    exact Mixture.infinitePolicyActionValue_le_infiniteActionValue
      (Mixture.mixtureBelief_isSubprobability hp0 hp1 hboxS hfreeS) ag hu π t hw h
  have hmid := mixture_lt_of_threshold hq0 hq1 hyesBox hyesFree hnoBox hnoFree
    (scaled_threshold hvmax hrbar hthresh)
  linarith

/-- **Statement 2 at the infinite-horizon value** (Ring and Orseau, AGI 2011,
Statement 2, PDF p. 6): the goal-seeking comparison between untruncated values,
with print's `2^{-|o⁺|}` and `2^{-lᵃ}` bounding the infinite committed and optimal
action values. For the goal-seeking agent the horizon condition is
`summable_abs_shortHorizon`. No `[Fintype Obs]`. -/
public theorem statement_two_infinite
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (k l : ℕ)
    (hyesBox : (1 / 2 : ℝ) ^ k ≤ Mixture.infinitePolicyActionValue ρbox ag π t h)
    (hyesFree : 0 ≤ Mixture.infinitePolicyActionValue ρfree ag π t h)
    (hnoBox : infiniteActionValue ρbox ag t h no ≤ (1 / 2 : ℝ) ^ l)
    (hnoFree : infiniteActionValue ρfree ag t h no ≤ (1 / 2 : ℝ) ^ l)
    (hthresh : (1 / 2 : ℝ) ^ l
      < Mixture.posterior p ρbox ρfree h * (1 / 2 : ℝ) ^ k) :
    infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h no
      < infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hq0 := Mixture.posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hq1 := Mixture.posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hno := Mixture.infiniteActionValue_mixture_le hp0 hp1 hboxS hfreeS ag hu t hw h no
  have hyes :
      Mixture.posterior p ρbox ρfree h * Mixture.infinitePolicyActionValue ρbox ag π t h
        + (1 - Mixture.posterior p ρbox ρfree h)
          * Mixture.infinitePolicyActionValue ρfree ag π t h
      ≤ infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h (π h) := by
    rw [← Mixture.infinitePolicyActionValue_mixture hp0 hp1 hboxS hfreeS ag hu π t hw h]
    exact Mixture.infinitePolicyActionValue_le_infiniteActionValue
      (Mixture.mixtureBelief_isSubprobability hp0 hp1 hboxS hfreeS) ag hu π t hw h
  have hmid := mixture_lt_of_gap hq0 hq1 hyesBox hyesFree hnoBox hnoFree hthresh
  linarith

/-- **Statement 3 without the decomposition, at the infinite-horizon value** (Ring
and Orseau, AGI 2011, Statement 3, PDF p. 6): `statement_one_of_posterior_infinite`
at `r̄ = 0`. -/
public theorem statement_three_of_posterior_infinite
    {p : ℝ} (ρbox ρfree : Belief Action Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : AgentEquations.History Action Obs)
    (π : AgentEquations.History Action Obs → Action) (no : Action) (vmax : ℝ)
    (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ Mixture.infinitePolicyActionValue ρbox ag π t h)
    (hyesFree : 0 ≤ Mixture.infinitePolicyActionValue ρfree ag π t h)
    (hnoBox : infiniteActionValue ρbox ag t h no ≤ 0)
    (hnoFree : infiniteActionValue ρfree ag t h no ≤ vmax)
    (hthresh : 1 / 2 < Mixture.posterior p ρbox ρfree h) :
    infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h no
      < infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h (π h) :=
  statement_one_of_posterior_infinite ρbox ρfree hp0 hp1 hboxS hfreeS ag hu t hw h π no vmax 0
    hvmax hyesBox hyesFree (by rwa [mul_zero]) hnoFree (by norm_num) (by norm_num; linarith)

/-- **Statement 3's decomposition route at the infinite-horizon value**: the
arithmetic of `statement_three` over untruncated values, with print's fixed-weight
decomposition taken at the infinite action values and print's maximum `1`
generalised to `vmax`. The decomposition is a hypothesis exactly as `MixesAt` is;
`statement_three_of_posterior_infinite` is the route that does not need it. -/
public theorem statement_three_infinite
    (ρ ρbox ρfree : Belief Action Obs) (ag : Agent Action Obs) (p : ℝ) (t : ℕ)
    (h : AgentEquations.History Action Obs) (yes no : Action) (vmax : ℝ)
    (hmix : ∀ a, infiniteActionValue ρ ag t h a
      = p * infiniteActionValue ρbox ag t h a + (1 - p) * infiniteActionValue ρfree ag t h a)
    (hp1 : p ≤ 1) (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ infiniteActionValue ρbox ag t h yes)
    (hyesFree : 0 ≤ infiniteActionValue ρfree ag t h yes)
    (hnoBox : infiniteActionValue ρbox ag t h no ≤ 0)
    (hnoFree : infiniteActionValue ρfree ag t h no ≤ vmax)
    (hthresh : 1 / 2 < p) :
    infiniteActionValue ρ ag t h no < infiniteActionValue ρ ag t h yes := by
  rw [hmix no, hmix yes]
  exact mixture_lt_of_threshold (by linarith) hp1 hyesBox hyesFree
    (hnoBox.trans_eq (mul_zero vmax).symm) hnoFree
    (scaled_threshold hvmax (by norm_num) (by norm_num; linarith))

/-! ### "Will use the delusion box": the selected action programs the box

Print's Statement 3 (PDF p. 6) says the agent *uses* the box: the action eq. (1)
selects, `a_t = ⟨d_t, aᵉ_t⟩`, has `d_t` other than the identity program `d₀`
(PDF p. 5). Beating one refusing action is not that when the inner action set has
more than one element; the statements below take the refusing bounds for **every**
action whose program is `d₀` and conclude about the program of any maximiser, so
they cover `bestAction`, `infiniteBestAction` and the lexicographic
`infiniteLexBestAction` alike (`bestAction_ne_of_lt` is the one-action form).
-/

/-- Any maximiser avoids a class of actions each strictly beaten by one action. -/
public theorem program_ne_of_max {P Ae : Type*} {f : Act P Ae → ℝ} {d₀ : P}
    {yes a : Act P Ae} (hmax : ∀ b, f b ≤ f a)
    (hlt : ∀ no, program no = d₀ → f no < f yes) : program a ≠ d₀ :=
  fun ha => absurd (hmax yes) (not_le.mpr (hlt a ha))

/-- **Statement 3, the selected action programs the box**, at depth `n` without
the decomposition and at every observation type: eq. (1)'s `bestAction` at the
mixture does not run the identity program `d₀`, once every identity-program action
satisfies the refusing bounds. -/
public theorem statement_three_of_posterior_program_ne {P Ae : Type*}
    {p : ℝ} (ρbox ρfree : Belief (Act P Ae) Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent (Act P Ae) Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : AgentEquations.History (Act P Ae) Obs)
    (π : AgentEquations.History (Act P Ae) Obs → Act P Ae) (d₀ : P) (vmax : ℝ)
    (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ Mixture.policyActionValue ρbox ag π t n h)
    (hyesFree : 0 ≤ Mixture.policyActionValue ρfree ag π t n h)
    (hnoBox : ∀ no, program no = d₀ → actionValue ρbox ag t n h no ≤ 0)
    (hnoFree : ∀ no, program no = d₀ → actionValue ρfree ag t n h no ≤ vmax)
    (hthresh : 1 / 2 < Mixture.posterior p ρbox ρfree h)
    (hat : AgentEquations.Attains (Mixture.mixtureBelief p ρbox ρfree) ag t n h) :
    program (bestAction (Mixture.mixtureBelief p ρbox ρfree) ag t n h hat) ≠ d₀ :=
  program_ne_of_max (bestAction_max _ ag t n h hat) fun no hno =>
    statement_three_of_posterior_scaled ρbox ρfree hp0 hp1 hboxS hfreeS ag hu t n h π no vmax
      hvmax hyesBox hyesFree (hnoBox no hno) (hnoFree no hno) hthresh

/-- **Statement 3 at the infinite-horizon value, the selected action programs the
box**: every maximiser of the untruncated action value at the mixture — in
particular `infiniteBestAction` and print's lexicographic `infiniteLexBestAction`,
by their `_max` lemmas — runs a program other than the identity `d₀`. -/
public theorem statement_three_of_posterior_infinite_program_ne {P Ae : Type*}
    {p : ℝ} (ρbox ρfree : Belief (Act P Ae) Obs)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent (Act P Ae) Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : AgentEquations.History (Act P Ae) Obs)
    (π : AgentEquations.History (Act P Ae) Obs → Act P Ae) (d₀ : P) (vmax : ℝ)
    (hvmax : 0 < vmax)
    (hyesBox : vmax ≤ Mixture.infinitePolicyActionValue ρbox ag π t h)
    (hyesFree : 0 ≤ Mixture.infinitePolicyActionValue ρfree ag π t h)
    (hnoBox : ∀ no, program no = d₀ → infiniteActionValue ρbox ag t h no ≤ 0)
    (hnoFree : ∀ no, program no = d₀ → infiniteActionValue ρfree ag t h no ≤ vmax)
    (hthresh : 1 / 2 < Mixture.posterior p ρbox ρfree h) {a : Act P Ae}
    (hmax : ∀ b, infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h b
      ≤ infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) ag t h a) :
    program a ≠ d₀ :=
  program_ne_of_max hmax fun no hno =>
    statement_three_of_posterior_infinite ρbox ρfree hp0 hp1 hboxS hfreeS ag hu t hw h π no
      vmax hvmax hyesBox hyesFree (hnoBox no hno) (hnoFree no hno) hthresh

/-! ### Statements 1 and 3 for the named agents at the infinite-horizon value

Print's window horizon vanishes past t + m, so the untruncated value is the value
at any depth that reaches past the window
(`infiniteActionValue_eq_actionValue_of_horizon_vanishes`): the depth-n theorems
`rlAgent_statement_one_of_posterior` and
`predictionAgent_statement_three_of_posterior`, read at depth t + m, are
comparisons of print's untruncated values. The maximum value is then the number of
in-window steps after h, t + m − |h| (`horizonBudget_windowHorizon`). The
refusing bound v(h no) ≤ (t + m − |h|) · r̄ is a hypothesis on the infinite value,
with r̄ < 1 and threshold P(DB) > 1/(2 − r̄): footnote 5's *"P(DB) is as high as
needed"* (PDF p. 5) supplies the posterior, and r̄ < 1 is print's *"since these
observations may generate prediction errors"*. r̄ includes the optimal
continuation, which may program the box at a later in-window step, so it is not a
one-step quantity (see `predictionAgent_statement_three_of_posterior`).
-/

/-- The window horizon is zero past the window. -/
public theorem windowHorizon_eq_zero {m t k : ℕ} (hk : t + m + 1 ≤ k) :
    windowHorizon m t k = 0 := by
  unfold windowHorizon
  rw [if_neg (by omega)]

/-- **The window's absolute horizon budget counts the in-window steps**: from index
k, at any depth reaching the window's last index t + m, it is the number of
indices in [k, t + m]. -/
public theorem horizonBudget_windowHorizon (ag : Agent Action Obs) {m : ℕ}
    (hag : ag.horizon = windowHorizon m) (t : ℕ) :
    ∀ (n k : ℕ), t + m ≤ k + n → horizonBudget ag t n k = ((t + m + 1 - k : ℕ) : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    simp only [horizonBudget, hag, abs_windowHorizon]
    unfold windowHorizon
    split_ifs with h1
    · rw [show t + m + 1 - k = 1 by omega]; norm_num
    · rw [show t + m + 1 - k = 0 by omega]; norm_num
  | succ n ih =>
    intro k hk
    simp only [horizonBudget]
    rw [ih (k + 1) (by omega), hag, abs_windowHorizon]
    unfold windowHorizon
    split_ifs with h1
    · rw [show t + m + 1 - k = (t + m + 1 - (k + 1)) + 1 by omega]; push_cast; ring
    · rw [show t + m + 1 - k = 0 by omega, show t + m + 1 - (k + 1) = 0 by omega]; norm_num

/-- At depth t + m from |h| + 1 the window's budget is the in-window step count
t + m − |h|. -/
private theorem horizonBudget_windowHorizon_depth (ag : Agent Action Obs) {m : ℕ}
    (hag : ag.horizon = windowHorizon m) (t : ℕ) (h : AgentEquations.History Action Obs) :
    horizonBudget ag t (t + m) (h.length + 1) = ((t + m - h.length : ℕ) : ℝ) := by
  rw [horizonBudget_windowHorizon ag hag t (t + m) (h.length + 1) (by omega)]
  congr 1
  omega

/--
**Statement 3 for print's prediction agent at the infinite-horizon value**
(Ring and Orseau, AGI 2011, Statement 3, PDF p. 6, *Arguments* PDF p. 6, under
footnote 5, PDF p. 5): the limit form of
`predictionAgent_statement_three_of_posterior`, at every observation type and for an
arbitrary predictor. Three of the four branch bounds are theorems (the box that
outputs the prediction is worth every in-window step, t + m − |h|; every value is
nonnegative; no action exceeds the step count); the refusing box-branch bound
v(h no) ≤ (t + m − |h|) · r̄ with r̄ < 1 stays a hypothesis, at the untruncated
value.
-/
public theorem predictionAgent_statement_three_of_posterior_infinite [DecidableEq Obs] {p : ℝ}
    (ρbox ρfree : Belief Action Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Obs)
    (m t : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action)
    (hbox : ∀ h', ρbox.cond h' (π h') (predict h') = 1) (no : Action) (rbar : ℝ)
    (hnoBox : infiniteActionValue ρbox (predictionAgent predict m) t h no
      ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgent predict m) t h no
      < infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgent predict m) t h
          (π h) := by
  have hz : ∀ k, t + m + 1 ≤ k → (predictionAgent (Action := Action) predict m).horizon t k = 0 :=
    fun k hk => windowHorizon_eq_zero hk
  have hN : t + m + 1 ≤ h.length + 1 + (t + m) := by omega
  rw [infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN,
    infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN]
  rw [infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN,
    ← horizonBudget_windowHorizon_depth (predictionAgent (Action := Action) predict m) rfl t h]
    at hnoBox
  exact predictionAgent_statement_three_of_posterior ρbox ρfree hp0 hp1 hboxS hfreeS predict
    m t (t + m) h hwin π hbox no rbar hnoBox hrbar hthresh

/--
**Statement 1 for print's reinforcement-learning agent at the infinite-horizon
value** (Ring and Orseau, AGI 2011, Statement 1, PDF p. 5, *Arguments* PDF pp. 5–6,
under footnote 5, PDF p. 5): the limit form of `rlAgent_statement_one_of_posterior`,
at every observation type. The box programmed to a reward-one observation is worth
every in-window step, t + m − |h|; the refusing box-branch bound stays a
hypothesis, at the untruncated value.
-/
public theorem rlAgent_statement_one_of_posterior_infinite {p : ℝ}
    (ρbox ρfree : Belief Action Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (reward : Obs → ℝ) (hr0 : ∀ o, 0 ≤ reward o) (hr1 : ∀ o, reward o ≤ 1)
    (m t : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action) {k : Obs} (hk1 : reward k = 1)
    (hbox : ∀ h', ρbox.cond h' (π h') k = 1) (no : Action) (rbar : ℝ)
    (hnoBox : infiniteActionValue ρbox (rlAgent reward m) t h no
      ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgent reward m) t h no
      < infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgent reward m) t h
          (π h) := by
  have hz : ∀ k, t + m + 1 ≤ k → (rlAgent (Action := Action) reward m).horizon t k = 0 :=
    fun k hk => windowHorizon_eq_zero hk
  have hN : t + m + 1 ≤ h.length + 1 + (t + m) := by omega
  rw [infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN,
    infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN]
  rw [infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN,
    ← horizonBudget_windowHorizon_depth (rlAgent (Action := Action) reward m) rfl t h]
    at hnoBox
  exact rlAgent_statement_one_of_posterior ρbox ρfree hp0 hp1 hboxS hfreeS reward hr0 hr1
    m t (t + m) h hwin π hk1 hbox no rbar hnoBox hrbar hthresh

/-- **Statement 3 for print's prediction agent at the infinite-horizon value, the
selected action programs the box**: once every action running the identity program
d₀ satisfies the refusing bound, every maximiser of the untruncated action value at
the mixture (`infiniteBestAction`, and print's lexicographic `infiniteLexBestAction`,
by their `infiniteBestAction_max` and `infiniteLexBestAction_max`) runs a program other than d₀. -/
public theorem predictionAgent_statement_three_of_posterior_infinite_program_ne
    {P Ae : Type*} [DecidableEq Obs] {p : ℝ}
    (ρbox ρfree : Belief (Act P Ae) Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History (Act P Ae) Obs → Obs)
    (m t : ℕ) (h : AgentEquations.History (Act P Ae) Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History (Act P Ae) Obs → Act P Ae)
    (hbox : ∀ h', ρbox.cond h' (π h') (predict h') = 1) (d₀ : P) (rbar : ℝ)
    (hnoBox : ∀ no, program no = d₀ →
      infiniteActionValue ρbox (predictionAgent predict m) t h no
        ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) {a : Act P Ae}
    (hmax : ∀ b, infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree)
        (predictionAgent predict m) t h b
      ≤ infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree)
        (predictionAgent predict m) t h a) :
    program a ≠ d₀ :=
  program_ne_of_max hmax fun no hno =>
    predictionAgent_statement_three_of_posterior_infinite ρbox ρfree hp0 hp1 hboxS hfreeS
      predict m t h hwin π hbox no rbar (hnoBox no hno) hrbar hthresh

/-- **Statement 1 for print's reinforcement-learning agent at the infinite-horizon
value, the selected action programs the box**: every maximiser of the untruncated
action value at the mixture runs a program other than the identity d₀, once every
identity-program action satisfies the refusing bound. -/
public theorem rlAgent_statement_one_of_posterior_infinite_program_ne {P Ae : Type*} {p : ℝ}
    (ρbox ρfree : Belief (Act P Ae) Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (reward : Obs → ℝ) (hr0 : ∀ o, 0 ≤ reward o) (hr1 : ∀ o, reward o ≤ 1)
    (m t : ℕ) (h : AgentEquations.History (Act P Ae) Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History (Act P Ae) Obs → Act P Ae) {k : Obs} (hk1 : reward k = 1)
    (hbox : ∀ h', ρbox.cond h' (π h') k = 1) (d₀ : P) (rbar : ℝ)
    (hnoBox : ∀ no, program no = d₀ →
      infiniteActionValue ρbox (rlAgent reward m) t h no
        ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) {a : Act P Ae}
    (hmax : ∀ b, infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgent reward m) t h b
      ≤ infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (rlAgent reward m) t h a) :
    program a ≠ d₀ :=
  program_ne_of_max hmax fun no hno =>
    rlAgent_statement_one_of_posterior_infinite ρbox ρfree hp0 hp1 hboxS hfreeS reward hr0 hr1
      m t h hwin π hk1 hbox no rbar (hnoBox no hno) hrbar hthresh

/-! ### The prediction agent with a predictor that reads the current action

Ring and Orseau, AGI 2011, §2: the prediction agent's prediction is
ô_t = argmax over o of ρ(o | h), with the history convention
h = (o₁, a₁, …, o_t, a_t), which ends in the action just taken, and eq. (2)'s
ρ(o | h a). So print's predictor conditions on the current action, which carries
the box program d_t. `predictionAgent` reads only the history before the current
action–observation pair. `predictionAgentAct` takes a predictor of type
History → Action → Obs, applied to the history before the pair and to the action
of the pair; `predictionAgent` is its action-blind instance
(`predictionAgent_eq_predictionAgentAct`).

For an action-aware predictor the box premise of Statement 3 is a condition on the
predictor and the box-using policy together: the box branch must give the policy's
action the observation predicted for that very action. It is needed only along the
run on which every prediction comes true (`predictedRun`). For print's predictor,
an argmax of the agent's own mixture belief, it follows from the posterior: above
one half at h, the argmax is the observation the box branch makes certain
(`predict_eq_of_isMax_mixture`), and along the run the posterior does not decrease
(`posterior_le_posterior_snoc`), so
`predictionAgentAct_statement_three_of_posterior_infinite_argmax` carries
Statement 3 with no box premise beyond "the box-using action makes the next
observation certain in the box branch".
-/

/-- **Print's prediction agent with an action-aware predictor.** Its utility is one
when the observation just received is the one predicted from the history before
it **and the action just taken**, print's ô_t = argmax over o of ρ(o | h a) with h
ending in the current action (Ring and Orseau, AGI 2011, §2). Horizon: the window,
as for `predictionAgent`. -/
@[expose] public def predictionAgentAct [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Action → Obs) (m : ℕ) :
    Agent Action Obs where
  utility := fun h =>
    match h.getLast? with
    | none => 0
    | some p => if predict h.dropLast p.1 = p.2 then 1 else 0
  horizon := windowHorizon m

/-- `predictionAgent` is the action-blind instance of `predictionAgentAct`: the
predictor that ignores the current action. -/
public theorem predictionAgent_eq_predictionAgentAct [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Obs) (m : ℕ) :
    predictionAgent predict m = predictionAgentAct (fun h _ => predict h) m := rfl

/-- The action-aware prediction agent's utility after an action and an
observation: one exactly when the prediction for that action, made on the history
before it, was that observation. -/
public theorem predictionAgentAct_utility_snoc [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Action → Obs) (m : ℕ)
    (h : AgentEquations.History Action Obs) (a : Action) (o : Obs) :
    (predictionAgentAct predict m).utility (h ++ [(a, o)]) =
      if predict h a = o then 1 else 0 := by
  simp [predictionAgentAct]

/-- The action-aware prediction agent's utility is 0 or 1, so it is
nonnegative. -/
public theorem predictionAgentAct_utility_nonneg [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Action → Obs) (m : ℕ)
    (h : AgentEquations.History Action Obs) :
    0 ≤ (predictionAgentAct predict m).utility h := by
  simp only [predictionAgentAct]
  split
  · norm_num
  · split_ifs <;> norm_num

/-- The action-aware prediction agent's utility is 0 or 1, so it is bounded by
one. -/
public theorem predictionAgentAct_abs_utility_le [DecidableEq Obs]
    (predict : AgentEquations.History Action Obs → Action → Obs) (m : ℕ)
    (h : AgentEquations.History Action Obs) :
    |(predictionAgentAct predict m).utility h| ≤ 1 := by
  simp only [predictionAgentAct]
  split
  · norm_num
  · split_ifs <;> norm_num

/-- **The run on which every prediction comes true**: from h, the policy π acts and
the observation is the one predicted for π's action. -/
@[expose] public def predictedRun
    (predict : AgentEquations.History Action Obs → Action → Obs)
    (π : AgentEquations.History Action Obs → Action) (h : AgentEquations.History Action Obs) :
    ℕ → AgentEquations.History Action Obs
  | 0 => h
  | k + 1 => predictedRun predict π h k ++
      [(π (predictedRun predict π h k), predict (predictedRun predict π h k)
        (π (predictedRun predict π h k)))]

/-- **Print's "program the DB to output a predictable sequence", for an
action-aware predictor.** If along the run on which every prediction comes true the
belief gives the policy's action the observation predicted for it with probability
one, every committed action value along that run is the absolute horizon budget of
the next n + 1 steps. The premise is needed on that run only, not at every
history. -/
public theorem predictionAgentAct_policyActionValue_correct [DecidableEq Obs]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Action → Obs) (m : ℕ)
    (π : AgentEquations.History Action Obs → Action) (h : AgentEquations.History Action Obs)
    (hk : ∀ k, ρ.cond (predictedRun predict π h k) (π (predictedRun predict π h k))
      (predict (predictedRun predict π h k) (π (predictedRun predict π h k))) = 1) (t : ℕ) :
    ∀ (n k : ℕ),
      Mixture.policyActionValue ρ (predictionAgentAct predict m) π t n (predictedRun predict π h k)
        = horizonBudget (predictionAgentAct predict m) t n
            ((predictedRun predict π h k).length + 1) := by
  have collapse : ∀ (n k : ℕ),
      Mixture.policyActionValue ρ (predictionAgentAct predict m) π t n
          (predictedRun predict π h k)
        = Mixture.policyValue ρ (predictionAgentAct predict m) π t n
            (predictedRun predict π h (k + 1)) := by
    intro n k
    rw [Mixture.policyActionValue, tsum_eq_single _ (fun o ho => by
      rw [hρ.cond_eq_zero_of_eq_one (hk k) ho, zero_mul]), hk k, one_mul]
    rfl
  have hlen : ∀ k, (predictedRun predict π h (k + 1)).length =
      (predictedRun predict π h k).length + 1 := fun k => by simp [predictedRun]
  have hu : ∀ k, (predictionAgentAct predict m).utility (predictedRun predict π h (k + 1)) = 1 :=
    fun k => by simp only [predictedRun]; rw [predictionAgentAct_utility_snoc]; simp
  intro n
  induction n with
  | zero =>
    intro k
    rw [collapse, Mixture.policyValue_zero, hu, hlen]
    simp only [horizonBudget]
    simp [predictionAgentAct, abs_windowHorizon]
  | succ n ih =>
    intro k
    rw [collapse, Mixture.policyValue_succ, ih, hu, hlen]
    simp only [horizonBudget]
    simp [predictionAgentAct, abs_windowHorizon]

/-- Every committed action value of the action-aware prediction agent is
nonnegative, at every depth. -/
public theorem predictionAgentAct_policyActionValue_nonneg [DecidableEq Obs]
    {ρ : Belief Action Obs} (hρ : ∀ h a o, 0 ≤ ρ.cond h a o)
    (predict : AgentEquations.History Action Obs → Action → Obs) (m : ℕ)
    (π : AgentEquations.History Action Obs → Action) (t n : ℕ)
    (h : AgentEquations.History Action Obs) :
    0 ≤ Mixture.policyActionValue ρ (predictionAgentAct predict m) π t n h := by
  refine Mixture.policyActionValue_nonneg hρ _ π t (fun h' => ?_) n h
  have hw : 0 ≤ windowHorizon m t h'.length := by unfold windowHorizon; split_ifs <;> norm_num
  exact mul_nonneg hw (predictionAgentAct_utility_nonneg predict m h')

/-- A deterministic global environment satisfies the box premise of
`predictionAgentAct_policyActionValue_correct` at a history when the policy's
action there carries a box program constant at the observation predicted for that
action. -/
public theorem diracBelief_next_cond_predictAct {P Ae O : Type*} [DecidableEq O]
    (G : GlobalEnv P Ae O) (predict : AgentEquations.History (Act P Ae) O → Act P Ae → O)
    (π : AgentEquations.History (Act P Ae) O → Act P Ae)
    (h : AgentEquations.History (Act P Ae) O)
    (hG : G.IsConstant (program (π h)) (predict h (π h))) :
    (diracBelief G.next).cond h (π h) (predict h (π h)) = 1 :=
  diracBelief_next_cond_const G hG h (π h) rfl

/--
**Statement 3 for the action-aware prediction agent at every depth inside its
window** (Ring and Orseau, AGI 2011, Statement 3, PDF p. 6): the form of
`predictionAgent_statement_three_of_posterior` for a predictor that reads the
current action, print's ô_t = argmax over o of ρ(o | h a). The box premise is
needed only along `predictedRun`. The refusing box-branch bound with r̄ < 1 stays a
hypothesis, as there.
-/
public theorem predictionAgentAct_statement_three_of_posterior [DecidableEq Obs] {p : ℝ}
    (ρbox ρfree : Belief Action Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Action → Obs)
    (m t n : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action)
    (hbox : ∀ k, ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k))
      (predict (predictedRun predict π h k) (π (predictedRun predict π h k))) = 1)
    (no : Action) (rbar : ℝ)
    (hnoBox : actionValue ρbox (predictionAgentAct predict m) t n h no
      ≤ horizonBudget (predictionAgentAct predict m) t n (h.length + 1) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    actionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgentAct predict m) t n h no
      < actionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgentAct predict m) t n h
          (π h) := by
  have : Nonempty Action := ⟨no⟩
  have hu := predictionAgentAct_abs_utility_le predict m
  have hpos : 0 < horizonBudget (predictionAgentAct predict m) t n (h.length + 1) := by
    have h1 : |(predictionAgentAct predict m).horizon t (h.length + 1)| = 1 := by
      simp [predictionAgentAct, windowHorizon, hwin]
    cases n with
    | zero => simp only [horizonBudget]; rw [h1]; norm_num
    | succ n =>
      simp only [horizonBudget]
      rw [h1]
      linarith [horizonBudget_nonneg (predictionAgentAct predict m) t n (h.length + 1 + 1)]
  refine statement_one_of_posterior_scaled ρbox ρfree hp0 hp1 hboxS hfreeS _ hu t n h π no
    _ rbar hpos ?_ ?_ hnoBox ?_ hrbar hthresh
  · rw [show h = predictedRun predict π h 0 from rfl,
      predictionAgentAct_policyActionValue_correct hboxS predict m π h hbox t n 0]
  · exact predictionAgentAct_policyActionValue_nonneg hfreeS.nonneg predict m π t n h
  · exact (le_abs_self _).trans (abs_actionValue_le_horizonBudget hfreeS _ hu t n h no)

/--
**Statement 3 for the action-aware prediction agent at the infinite-horizon value**
(Ring and Orseau, AGI 2011, Statement 3, PDF p. 6, under footnote 5, PDF p. 5): the
form of `predictionAgent_statement_three_of_posterior_infinite` for a predictor
that reads the current action. The box-using policy, whose predictions all come
true along `predictedRun` in the box branch, is worth every in-window step,
t + m − |h|; the refusing box-branch bound stays a hypothesis at the untruncated
value.
-/
public theorem predictionAgentAct_statement_three_of_posterior_infinite [DecidableEq Obs]
    {p : ℝ} (ρbox ρfree : Belief Action Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Action → Obs)
    (m t : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action)
    (hbox : ∀ k, ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k))
      (predict (predictedRun predict π h k) (π (predictedRun predict π h k))) = 1)
    (no : Action) (rbar : ℝ)
    (hnoBox : infiniteActionValue ρbox (predictionAgentAct predict m) t h no
      ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgentAct predict m) t h no
      < infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgentAct predict m) t h
          (π h) := by
  have hz : ∀ k, t + m + 1 ≤ k →
      (predictionAgentAct (Action := Action) predict m).horizon t k = 0 :=
    fun k hk => windowHorizon_eq_zero hk
  have hN : t + m + 1 ≤ h.length + 1 + (t + m) := by omega
  rw [infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN,
    infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN]
  rw [infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN,
    ← horizonBudget_windowHorizon_depth (predictionAgentAct (Action := Action) predict m) rfl t h]
    at hnoBox
  exact predictionAgentAct_statement_three_of_posterior ρbox ρfree hp0 hp1 hboxS hfreeS predict
    m t (t + m) h hwin π hbox no rbar hnoBox hrbar hthresh

/-- **Statement 3 for the action-aware prediction agent at the infinite-horizon
value, the selected action programs the box**: once every action running the
identity program d₀ satisfies the refusing bound, every maximiser of the
untruncated action value at the mixture runs a program other than d₀. -/
public theorem predictionAgentAct_statement_three_of_posterior_infinite_program_ne
    {P Ae : Type*} [DecidableEq Obs] {p : ℝ}
    (ρbox ρfree : Belief (Act P Ae) Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History (Act P Ae) Obs → Act P Ae → Obs)
    (m t : ℕ) (h : AgentEquations.History (Act P Ae) Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History (Act P Ae) Obs → Act P Ae)
    (hbox : ∀ k, ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k))
      (predict (predictedRun predict π h k) (π (predictedRun predict π h k))) = 1)
    (d₀ : P) (rbar : ℝ)
    (hnoBox : ∀ no, program no = d₀ →
      infiniteActionValue ρbox (predictionAgentAct predict m) t h no
        ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) {a : Act P Ae}
    (hmax : ∀ b, infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree)
        (predictionAgentAct predict m) t h b
      ≤ infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree)
        (predictionAgentAct predict m) t h a) :
    program a ≠ d₀ :=
  program_ne_of_max hmax fun no hno =>
    predictionAgentAct_statement_three_of_posterior_infinite ρbox ρfree hp0 hp1 hboxS hfreeS
      predict m t h hwin π hbox no rbar (hnoBox no hno) hrbar hthresh

/-! #### Print's predictor: the argmax of the agent's own belief -/

/-- **The argmax of the mixture is the observation the box makes certain**, once
the posterior on the box exceeds one half: at weight one on c in the box branch,
the mixture puts at least the posterior on c and at most one minus the posterior
on any other observation. This is print's prediction ô = argmax over o of
ρ(o | h a) (Ring and Orseau, AGI 2011, §2) at the agent's own belief, the mixture
`Mixture.mixtureBelief`. -/
public theorem predict_eq_of_isMax_mixture {p : ℝ} {ρbox ρfree : Belief Action Obs}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    {h : AgentEquations.History Action Obs} {a : Action} {c o' : Obs}
    (hpost : 1 / 2 < Mixture.posterior p ρbox ρfree h) (hc : ρbox.cond h a c = 1)
    (hmax : ∀ o, (Mixture.mixtureBelief p ρbox ρfree).cond h a o
      ≤ (Mixture.mixtureBelief p ρbox ρfree).cond h a o') :
    o' = c := by
  by_contra hne
  have hq1 := Mixture.posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have h0 : ρbox.cond h a o' = 0 := hboxS.cond_eq_zero_of_eq_one hc hne
  have hle := hmax c
  rw [Mixture.mixtureBelief_cond, Mixture.mixtureBelief_cond, hc, h0] at hle
  have hf1 := hfreeS.cond_le_one h a o'
  have hf0 := hfreeS.nonneg h a c
  nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hf0, mul_le_mul_of_nonneg_left hf1 (sub_nonneg.mpr hq1)]

/-- **The posterior on the box does not decrease after an observation the box
branch makes certain**: the box branch's likelihood is one, the mixture's at most
one (Bayes' rule, `Mixture.mixtureBelief_cond_mul_posterior`). -/
public theorem posterior_le_posterior_snoc {p : ℝ} {ρbox ρfree : Belief Action Obs}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    {h : AgentEquations.History Action Obs} {a : Action} {c : Obs}
    (hc : ρbox.cond h a c = 1) :
    Mixture.posterior p ρbox ρfree h ≤ Mixture.posterior p ρbox ρfree (h ++ [(a, c)]) := by
  have hbayes := Mixture.mixtureBelief_cond_mul_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h a c
  rw [hc, mul_one] at hbayes
  have hq0 := Mixture.posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hq1 := Mixture.posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
  have hq0' := Mixture.posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg (h ++ [(a, c)])
  have hmix1 : (Mixture.mixtureBelief p ρbox ρfree).cond h a c ≤ 1 := by
    rw [Mixture.mixtureBelief_cond, hc]
    nlinarith [hfreeS.cond_le_one h a c]
  have hmix0 := Mixture.mixtureBelief_cond_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h a c
  nlinarith

/-- **Along the run on which every prediction comes true, an argmax predictor
predicts what the box makes certain**: if the posterior exceeds one half at h, the
predictor is an argmax of the mixture at every history and action, and along the
run the box branch makes the policy's next observation certain, then the box branch
gives the policy's action the predicted observation with probability one at every
step of the run, which is the box premise of
`predictionAgentAct_statement_three_of_posterior_infinite`. -/
public theorem cond_predictedRun_eq_one_of_isMax_mixture {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Action → Obs)
    (hargmax : ∀ h' a o, (Mixture.mixtureBelief p ρbox ρfree).cond h' a o
      ≤ (Mixture.mixtureBelief p ρbox ρfree).cond h' a (predict h' a))
    (π : AgentEquations.History Action Obs → Action) (h : AgentEquations.History Action Obs)
    (hcert : ∀ k, ∃ c, ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k)) c = 1)
    (hpost : 1 / 2 < Mixture.posterior p ρbox ρfree h) :
    ∀ k, ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k))
      (predict (predictedRun predict π h k) (π (predictedRun predict π h k))) = 1 := by
  have step : ∀ k, 1 / 2 < Mixture.posterior p ρbox ρfree (predictedRun predict π h k) →
      ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k))
        (predict (predictedRun predict π h k) (π (predictedRun predict π h k))) = 1 := by
    intro k hk
    obtain ⟨c, hc⟩ := hcert k
    rw [predict_eq_of_isMax_mixture hp0 hp1 hboxS hfreeS hk hc (hargmax _ _)]
    exact hc
  have hall : ∀ k, 1 / 2 < Mixture.posterior p ρbox ρfree (predictedRun predict π h k) := by
    intro k
    induction k with
    | zero => exact hpost
    | succ k ih =>
      exact ih.trans_le (posterior_le_posterior_snoc hp0 hp1 hboxS hfreeS (step k ih))
  exact fun k => step k (hall k)

/-- The untruncated action value of an agent with nonnegative weighted utilities
is nonnegative, at a nonnegative belief and a horizon that vanishes past an index. -/
private theorem value_nonneg_of_weighted {ρ : Belief Action Obs} (hρ : ∀ h a o, 0 ≤ ρ.cond h a o)
    (ag : Agent Action Obs) (t : ℕ) (hw : ∀ h, 0 ≤ ag.horizon t h.length * ag.utility h) :
    ∀ n h, 0 ≤ value ρ ag t n h := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro h
    rw [value_succ]
    exact add_nonneg (hw h) (Real.iSup_nonneg fun a =>
      tsum_nonneg fun o => mul_nonneg (hρ h a o) (ih _))

/--
**Statement 3 for print's prediction agent, its predictor the argmax of its own
belief, at the infinite-horizon value** (Ring and Orseau, AGI 2011, Statement 3,
PDF p. 6, *Arguments*: *"it will immediately program the DB to output a
predictable sequence"*; under footnote 5, PDF p. 5). The predictor is print's
ô = argmax over o of ρ(o | h a) at the agent's belief, the mixture, reading the
current action. The box premise is no longer a hypothesis on the predictor: it is
enough that the box-using action makes the next observation certain in the box
branch along the run (print's box executing a constant program), because the
posterior threshold puts the posterior above one half and an argmax predictor
then predicts the certain observation (`cond_predictedRun_eq_one_of_isMax_mixture`).
The refusing box-branch bound with r̄ < 1 stays a hypothesis.
-/
public theorem predictionAgentAct_statement_three_of_posterior_infinite_argmax
    [DecidableEq Obs] {p : ℝ} (ρbox ρfree : Belief Action Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History Action Obs → Action → Obs)
    (hargmax : ∀ h' a o, (Mixture.mixtureBelief p ρbox ρfree).cond h' a o
      ≤ (Mixture.mixtureBelief p ρbox ρfree).cond h' a (predict h' a))
    (m t : ℕ) (h : AgentEquations.History Action Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History Action Obs → Action)
    (hcert : ∀ k, ∃ c, ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k)) c = 1)
    (no : Action) (rbar : ℝ)
    (hnoBox : infiniteActionValue ρbox (predictionAgentAct predict m) t h no
      ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) :
    infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgentAct predict m) t h no
      < infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree) (predictionAgentAct predict m) t h
          (π h) := by
  have hz : ∀ k, t + m + 1 ≤ k →
      (predictionAgentAct (Action := Action) predict m).horizon t k = 0 :=
    fun k hk => windowHorizon_eq_zero hk
  have hN : t + m + 1 ≤ h.length + 1 + (t + m) := by omega
  have hv0 : 0 ≤ infiniteActionValue ρbox (predictionAgentAct predict m) t h no := by
    rw [infiniteActionValue_eq_actionValue_of_horizon_vanishes _ _ t _ hz h hN]
    refine tsum_nonneg fun o => mul_nonneg (hboxS.nonneg _ _ _) ?_
    refine value_nonneg_of_weighted hboxS.nonneg _ t (fun h' => ?_) _ _
    have hw : 0 ≤ windowHorizon m t h'.length := by unfold windowHorizon; split_ifs <;> norm_num
    exact mul_nonneg hw (predictionAgentAct_utility_nonneg predict m h')
  have hcount : (0 : ℝ) < ((t + m - h.length : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < t + m - h.length by omega)
  have hr0 : 0 ≤ rbar := by
    by_contra hneg
    have : ((t + m - h.length : ℕ) : ℝ) * rbar < 0 := mul_neg_of_pos_of_neg hcount (by linarith)
    linarith
  have hpost : 1 / 2 < Mixture.posterior p ρbox ρfree h := by
    refine lt_of_le_of_lt ?_ hthresh
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  exact predictionAgentAct_statement_three_of_posterior_infinite ρbox ρfree hp0 hp1 hboxS hfreeS
    predict m t h hwin π
    (cond_predictedRun_eq_one_of_isMax_mixture hp0 hp1 hboxS hfreeS predict hargmax π h hcert hpost)
    no rbar hnoBox hrbar hthresh

/-- **Statement 3 for print's prediction agent with the argmax predictor, the
selected action programs the box**, at the infinite-horizon value: every maximiser
of the untruncated action value at the mixture runs a program other than the
identity d₀, once every identity-program action satisfies the refusing bound. -/
public theorem predictionAgentAct_statement_three_of_posterior_infinite_argmax_program_ne
    {P Ae : Type*} [DecidableEq Obs] {p : ℝ}
    (ρbox ρfree : Belief (Act P Ae) Obs) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (predict : AgentEquations.History (Act P Ae) Obs → Act P Ae → Obs)
    (hargmax : ∀ h' a o, (Mixture.mixtureBelief p ρbox ρfree).cond h' a o
      ≤ (Mixture.mixtureBelief p ρbox ρfree).cond h' a (predict h' a))
    (m t : ℕ) (h : AgentEquations.History (Act P Ae) Obs) (hwin : h.length + 1 ≤ t + m)
    (π : AgentEquations.History (Act P Ae) Obs → Act P Ae)
    (hcert : ∀ k, ∃ c, ρbox.cond (predictedRun predict π h k) (π (predictedRun predict π h k)) c = 1)
    (d₀ : P) (rbar : ℝ)
    (hnoBox : ∀ no, program no = d₀ →
      infiniteActionValue ρbox (predictionAgentAct predict m) t h no
        ≤ ((t + m - h.length : ℕ) : ℝ) * rbar)
    (hrbar : rbar < 1)
    (hthresh : 1 / (2 - rbar) < Mixture.posterior p ρbox ρfree h) {a : Act P Ae}
    (hmax : ∀ b, infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree)
        (predictionAgentAct predict m) t h b
      ≤ infiniteActionValue (Mixture.mixtureBelief p ρbox ρfree)
        (predictionAgentAct predict m) t h a) :
    program a ≠ d₀ :=
  program_ne_of_max hmax fun no hno =>
    predictionAgentAct_statement_three_of_posterior_infinite_argmax ρbox ρfree hp0 hp1 hboxS
      hfreeS predict hargmax m t h hwin π hcert no rbar (hnoBox no hno) hrbar hthresh

/--
**Statement 3.** *The prediction agent will use the delusion box.*

Print's argument is that once the agent believes the environment contains a
delusion box — "i.e. `Q_B > Q_h/2`", which is `P(DB) > 1/2` — it programs the box
to output a predictable sequence, obliterating the observations that could
generate prediction errors. `GlobalEnv.globalObs_indep_inner` is the
obliteration; this is the comparison.

The threshold `1/2` is `statement_one`'s threshold at `r̄ = 0`, and that is not a
coincidence: print's prediction bound gives the non-box action *no* value in the
branch where a box is present, because there the true inner environment is the
one being deluded away.

**Narrower than print** in the same ways, and in one more: print's step from
"`ρ(q_b) < ρ(Q_B)`, so it takes fewer errors to converge to `Q_B`" to "the agent
believes `P(DB) > 1/2`" is a claim about a universal prior and a convergence
rate. It is not formalized; `p` is simply given.
-/
public theorem statement_three
    (ρ ρbox ρfree : Belief Action Obs) (ag : Agent Action Obs)
    (p : ℝ) (t n : ℕ) (h : AgentEquations.History Action Obs)
    (yes no : Action)
    (hmix : MixesAt ρ ρbox ρfree ag p t n h)
    (hp1 : p ≤ 1)
    (hyesBox : 1 ≤ actionValue ρbox ag t n h yes)
    (hyesFree : 0 ≤ actionValue ρfree ag t n h yes)
    (hnoBox : actionValue ρbox ag t n h no ≤ 0)
    (hnoFree : actionValue ρfree ag t n h no ≤ 1)
    (hthresh : 1 / 2 < p) :
    actionValue ρ ag t n h no < actionValue ρ ag t n h yes :=
  statement_one ρ ρbox ρfree ag p t n h yes no 0 hmix (by linarith) hp1
    hyesBox hyesFree hnoBox hnoFree (by norm_num) (by norm_num; linarith)

/--
**Equation (1) does not select the beaten action.**

Print's Statements say the agent "will use the delusion box"; equation (1) selects
an action attaining the maximum action value, so an action strictly beaten by
another is not the one selected. This is the bridge from the comparisons above to
the agent's behaviour, and it is as much as a strict comparison of two actions
can give: it does not say which box-using action is chosen, only that the beaten
one is not.
-/
public theorem bestAction_ne_of_lt (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t n : ℕ) (h : AgentEquations.History Action Obs)
    (hat : AgentEquations.Attains ρ ag t n h) (yes no : Action)
    (hlt : actionValue ρ ag t n h no < actionValue ρ ag t n h yes) :
    bestAction ρ ag t n h hat ≠ no := by
  intro hEq
  have hmax := bestAction_max ρ ag t n h hat yes
  rw [hEq] at hmax
  exact absurd hmax (not_le.mpr hlt)

end AISafetyAtlas.Wireheading.DelusionBox
