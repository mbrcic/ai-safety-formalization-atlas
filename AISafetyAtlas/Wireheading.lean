module

public import AISafetyAtlas.Wireheading.Corruption
public import AISafetyAtlas.Wireheading.AgentEquations
public import AISafetyAtlas.Wireheading.AgentHistory
public import AISafetyAtlas.Wireheading.CRMDP
public import AISafetyAtlas.Wireheading.StochasticCRMDP
public import AISafetyAtlas.Wireheading.StochasticPolicy
public import AISafetyAtlas.Wireheading.RewardGrid
public import AISafetyAtlas.Wireheading.ObservationLimits
public import AISafetyAtlas.Wireheading.GoalPreservation
public import AISafetyAtlas.Wireheading.GoalPreservationCarrier
public import AISafetyAtlas.Wireheading.GoalPreservationSource
public import AISafetyAtlas.Wireheading.GoalPreservationRun
public import AISafetyAtlas.Wireheading.Objective
public import AISafetyAtlas.Wireheading.DelusionBox
public import AISafetyAtlas.Wireheading.SelfMod
public import AISafetyAtlas.Wireheading.ValueBounds
public import AISafetyAtlas.Wireheading.Mixture
public import AISafetyAtlas.Wireheading.ProgramPrior
public import AISafetyAtlas.Wireheading.ValueLearning

/-!
# Wireheading and self-modification — public facade

Results on **corruptible reward / evaluation channels**, finite-horizon
objective structure, and **on-policy goal preservation** under self-modification.
Import this module (or `AISafetyAtlas`) for the surface below.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `Corruption.ComplementedClass.everitt_theorem_eleven` | Half-maximal worst-case regret from complement closure |
| **Specialization** | `CRMDP.Model.everitt_theorem_eleven` | Same bound with states, corruption, observed channel (BY-039 canonical) |
| **Specialization** | `CRMDP.StochModel.everitt_theorem_eleven` | The same bound when the transition is a distribution over successor states and returns are expectations |
| **Specialization** | `CRMDP.MixedModel.everitt_theorem_eleven` | The same bound at print's own quantifier over the policy: the agent may randomise over actions too |
| **Witness** | `Examples.…witness_theorem_eleven` | A corrupt-reward MDP whose worst-case regret is exactly one, so the bound reads `1/2 ≤ ·` rather than `0/2 ≤ 0` |
| **Witness** | `Examples.…coinPolicy_worstCaseRegret` | A fair coin's worst-case regret is exactly `1/2` against a worst policy's `1`, so print's factor of two is attained, and by a policy that is not a point mass |
| **Law** | `CRMDP.stochReturn_add_complement` | Equation (3) between **expectations**: expected true returns of an environment and its complement sum to the horizon |
| **Law** | `CRMDP.mixedReturn_add_complement` | Equation (3) when the agent randomises as well: the whole content of the policy widening |
| **Law** | `CRMDP.stochStateAt_complement` | A complement is invisible to the whole trajectory distribution, not only to a single observation |
| **Law** | `CRMDP.mixedRun_complement` | And still invisible when the action is drawn rather than determined |
| **Theorem** | `RewardGrid.everitt_theorem_eleven_gridClass` | The same bound over the source's own uniform reward grid, with all three extrema derived from finiteness rather than assumed |
| **Law** | `CRMDP.Env.observed_complement` | Environment and complement look the same on the channel |
| **Law** | `CRMDP.Env.channel_complement` | The same fact in the form the carrier's run consumes: an environment and its complement present the same observation map |
| **Law** | `CRMDP.return_add_complement` | True returns sum to the horizon (eq. 3 style) |
| **Boundary** | `ObservationLimits.not_knowable_trueReturn_of_complement_mem` | A complement pair inside a class defeats every history-to-return decoder |
| **Corollary** | `ObservationLimits.not_knowable_trueReturn` | The unrestricted class, at any positive horizon |
| **Law** | `GoalPreservationSource.Model.selected_matches_initial` | Finite-percept Thm 16 induction step without naming surjectivity |
| **Law** | `GoalPreservationSource.Model.safe_modification` | One-step on-policy continuation matches initial value |
| **Theorem** | `GoalPreservationRun.Model.equation_thirteen` | Everitt et al. Theorem 16 equation (13) at every step of every percept sequence, with no naming surjectivity |
| **Specialization** | `AgentEquations.value_eq_of_agree_on_window` | Ring–Orseau finite value depends only on window `(u,w)` |
| **Definition** | `DelusionBox.GlobalEnv` | Ring–Orseau §3: the global environment splits into an inner environment and a box whose program is part of the agent's action |
| **Law** | `DelusionBox.GlobalEnv.globalObs_indep_inner` | A constant program obliterates the inner environment: two global environments an untouched box tells apart become indistinguishable |
| **Law** | `DelusionBox.GlobalEnv.innerHistory_congr_innerAction` | The inner environment cannot see the program, which print assumes in one sentence |
| **Definition** | `SelfMod.Exec` | Orseau–Ring §3: a code whose executor produces the next compound action |
| **Law** | `SelfMod.smValue` | Finite-depth value through that code: the continuation is valued at the next code, not by maximising again |
| **Theorem** | `DelusionBox.statement_one` | Ring–Orseau Statement 1, at print's threshold `1/(2-r̄)`, with the premises print's *Arguments* paragraph leaves implicit as named hypotheses — each of them discharged from print's construction by `rlAgent_actionValue_next_const`, `rlAgent_actionValue_nonneg`, `rlAgent_actionValue_le` and `threshold_unattainable_of_one_le` |
| **Theorem** | `DelusionBox.statement_two` | Statement 2, at print's threshold `2^{|o⁺|-lᵃ}` |
| **Theorem** | `DelusionBox.statement_three` | Statement 3, at print's threshold `1/2` |
| **Law** | `DelusionBox.mixesAt_zero` | The two-hypothesis decomposition all three arguments assume, proved at the one-step depth they use — so the hypothesis is not one nothing inhabits |
| **Witness** | `Examples.…rl_uses_the_box` | All three antecedents inhabited in one evaluable model, with `P(DB) = 3/4` |
| **Helper** | `Objective.value_eq_of_agree_on_window` | Finite-horizon locality on trajectories |
| **Helper** | `Objective.value_congr` | Record congruence only — not a paper theorem |
| **Law** | `ValueLearning.Beliefs.isEEP_of_isCP` | Everitt–Hutter Lemma 13: a consistency-preserving action is expected-ethics preserving |
| **Law** | `ValueLearning.Beliefs.vrlValue_of_isCP` | Everitt–Hutter Theorem 14: the CP-VRL value function drops the reward evidence |
| **Contrast** | `ValueLearning.Beliefs.vrlValue_eq_rlValue_of_isCP` | Under the CP constraint the VRL value is the RL value (Lemma 27's computation) |

Simpler / secondary: deterministic `GoalPreservation` (uses strong
`names_surjective`); keep as a specialization. `GoalPreservationSource` is the
source-aligned finite-percept induction step, not the full source theorem;
`GoalPreservationRun` iterates that step to the printed conclusion, replacing
`names_surjective` with the two printed hypotheses it stands in for — equation
(7) and the optimality of the initial policy — and deriving
`initial_dominates` rather than assuming it.

## Explicit non-claims

- **Not** EXACT Everitt et al. Theorem 11, and what stands between is no longer a
  missing axis but a missing **join**. Graded **RELATED**. Print's statement is
  four things at once — rewards over a uniform grid, the three extrema derived
  from finiteness rather than assumed, a transition that is a Markov kernel, and
  a quantifier over *possibly stochastic* policies — and each is now closed by
  some rendering. `AISafetyAtlas.Wireheading.RewardGrid` closes the first two:
  `RewardGrid.everitt_theorem_eleven_gridClass` runs over the source's own finite
  uniform grid and assumes no extremum.
  `AISafetyAtlas.Wireheading.StochasticCRMDP` closes the third: `CRMDP.StochModel`
  has a distribution-valued transition and expected returns, which at print's own
  finite state set (Definition 7) is print's stochastic kernel exactly.
  `AISafetyAtlas.Wireheading.StochasticPolicy` closes the fourth: `CRMDP.MixedModel`
  reads a policy as a distribution over actions and
  `CRMDP.MixedModel.everitt_theorem_eleven` proves the bound at print's own
  quantifier over it. **No single rendering closes all four**, and that is what
  keeps the grade RELATED. What is missing is named rather than carried out, and
  it is **two** steps, not one: first the grid extrema over a
  `AISafetyAtlas.Decision.MDP`, and only then affinity for mixed policies. The
  affine-functional argument in the header of
  `AISafetyAtlas.Wireheading.RewardGrid` is the second of those. Calling it *the*
  obstruction overstates it -- the parts already proved do not route through it.
- The renderings trade faithfulness against generality and none dominates.
  `RewardGrid` is the most faithful — print's reward grid, extrema derived — and
  is deterministic in the dynamics and in the policy both. `StochModel` is
  general on the dynamics, `MixedModel` on the dynamics and the policy, and each
  of those takes its extrema as fields. They are chained rather than merely
  analogous: `CRMDP.Model.toStoch_returnValue` and
  `CRMDP.StochModel.toMixed_returnValue` say the three statements of Theorem 11
  are about the same numbers.
- **Not** AIXI, and not all of Ring–Orseau. `AgentEquations` is a finite-horizon
  packaging of the displayed equations under an arbitrary weight, and
  `DelusionBox` adds §3's box, §2's four agents and Statements 1 to 3. What is
  absent is §4's self-modification setting with Statements 5 to 7, and
  **Statement 4** — the paper's positive claim, that the knowledge-seeking agent
  will not consistently use the box. The cheap half of recovering it is built:
  `historyMass` is the product of successive conditionals and
  `coherentKnowledgeAgent` is print's `u(h) = -ρ(h)` at that mass. The
  conclusion is not proved. `knowledge_uses_the_box` still refutes it at the
  untied `knowledgeAgent`; `coherent_uses_the_box` shows the coherent agent at
  the mixture belief still programs the box, so coherence is not Statement 4.
  Print's argument about discarded program mass needs more than
  `ProgramPrior.Model` supplies. **Statements 1 to 3 were graded `Partial` and
  Narrower until 2026-09-20 and are now `Yes` and Wider**: their printed
  arguments need premises print never states, and those premises are now derived
  from print's own construction rather than assumed. Statement 2's two constants
  are horizon weights of steps *later*, so its bounds hold at every depth —
  `goalAgent_actionValue_le_of_outOfReach` above and
  `shortHorizon_le_goalAgent_policyActionValue` below — and proving the first
  consumed print's own *"the goal can be reached at most once"*, a side condition
  this paper states and never uses. The two-hypothesis
  decomposition was **refuted** and replaced by a posterior and a committed
  policy; the four branch bounds are theorems about print's agent, with
  `rlAgent_actionValue_next_const` carrying *"the agent can program the DB to
  produce a constant reward of 1"*; and `r̄ < 1` is forced by print's threshold,
  not assumed. The agent is still a parameter of each Statement theorem and
  nothing was folded into `rlAgent`.
- **Not** utility modification; GoalPreservationSource is policy self-mod only,
  and does not derive the full optimal-policy-existence result (the technical
  report's Appendix A Theorem 20, which the source's own proof of Theorem 12
  invokes). Its finite percept weights are normalized and full-support. Its
  domination hypothesis is no longer a cluster-level assumption:
  `GoalPreservationRun.Model.contValue_le_initial` derives it from equation (7)
  and the initial policy's optimality, and `GoalPreservationRun.Model.toSource`
  hands `GoalPreservationSource` an interface with it already discharged.
- **Not** multiprincipal / shared-evaluator infrastructure by itself — that is
  a possible consumer of these cores, not what this facade currently is.
- **Not** an AI-system bridge without separate review.
- **Not** a sequential VRL agent: `ValueLearning` is the source's single-step
  decision problem, over a finite utility class, and asserts nothing about
  whether a useful prior consistent with the reward channel can be specified —
  which the source itself records as open.

- **Not** a novelty claim for `ObservationLimits`: the impossibility is the
  source's and `CRMDP` already formalizes both of its steps. That module adds the
  factorization reading through `Knowledge`, a certificate, and the import edge.
  It is class-relative, says nothing about approximate or prior-conditional
  estimation, and quantifies over environments rather than over agents.

Survey / landscape: BY-039 (RELATED), `LAND-WIRE-OBJ-001`, `LAND-GOAL-001`,
`LAND-CRMDP-KNOW-001`, `LAND-VRL-001`.
Residuals: `docs/provenance/a1-a3-b1-b3-b7-reverification.md`.
-/
