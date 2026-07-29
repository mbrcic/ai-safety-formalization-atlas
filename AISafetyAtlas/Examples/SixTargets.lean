module

import AISafetyAtlas
import Mathlib.Tactic.NormNum

/-!
# Concrete compile checks for the A1–A3/B1–B3 increment

These examples are deliberately tiny. Their role is to show that the abstract
interfaces have concrete inhabitants and that the principal theorems can be
instantiated; they make no additional public claims.
-/

namespace AISafetyAtlas.Examples.SixTargets

open AISafetyAtlas.Compositional.Hyperproperties

/-- The empty hyperproperty is `0`-safety: the empty observation refutes it. -/
def voidHyperproperty : Hyperproperty Bool := ∅

theorem voidHyperproperty_is_zero_safety :
    IsKSafety (fun p t : Bool => p = t) 0 voidHyperproperty := by
  intro S _
  refine ⟨∅, by simp, ?_, ?_⟩
  · simp [Realizes]
  · simp [IsBadObservation, voidHyperproperty]

example (S : TraceSystem Bool) :
    S ∈ voidHyperproperty ↔
      ∀ batch ∈ FiniteSelfComposition 0 S,
        SelfCompositionSafe (fun p t : Bool => p = t)
          0 voidHyperproperty batch :=
  k_safety_iff_finite_self_composition
    (fun p t : Bool => p = t) 0 voidHyperproperty
    voidHyperproperty_is_zero_safety S

/-- Theorem 2 in the source's synchronized-product form, over a nonempty
system. -/
example (S : TraceSystem Bool) (hS : S.Nonempty) :
    S ∈ voidHyperproperty ↔
      ∀ tup ∈ productSelfComposition 0 S,
        SelfCompositionSafe (fun p t : Bool => p = t)
          0 voidHyperproperty (toBatch tup) :=
  k_safety_iff_product_self_composition
    (fun p t : Bool => p = t) 0 voidHyperproperty
    voidHyperproperty_is_zero_safety hS

/-- The boundary padding cannot cross: with `k > 0` an empty system has no
product tuple, while its batch self-composition still contains the empty
batch. -/
example :
    productSelfComposition 2 (∅ : TraceSystem Bool) = ∅ ∧
      (∅ : Finset Bool) ∈ FiniteSelfComposition 2 (∅ : TraceSystem Bool) :=
  ⟨productSelfComposition_empty (by norm_num), finiteSelfComposition_empty⟩

/-- Every `k`-safety hyperproperty is hypersafety in the observation topology,
so the reduction and the decomposition live in one development. -/
example :
    IsHyperSafetyOp (fun p t : Bool => p = t) voidHyperproperty :=
  hyperSafety_of_isKSafety (fun p t : Bool => p = t) voidHyperproperty_is_zero_safety

/-- The decomposition, read operationally rather than at an arbitrary
topology. -/
example (H : Hyperproperty Bool) :
    ∃ safetyPart livenessPart : Hyperproperty Bool,
      IsHyperSafetyOp (fun p t : Bool => p = t) safetyPart ∧
        IsHyperLivenessOp (fun p t : Bool => p = t) livenessPart ∧
        H = safetyPart ∩ livenessPart :=
  hyperSafety_hyperLiveness_decomposition (fun p t : Bool => p = t) H

open AISafetyAtlas.Compositional

example :
    IsRectangle (Set.univ : Set (Bool × Bool)) ↔
      ExchangeClosed (Set.univ : Set (Bool × Bool)) :=
  rectangle_iff_exchange_closed Set.univ

/-- The finite-index splice characterization, instantiated at a two-coordinate
Boolean index. -/
example :
    IsCoordinateProduct (Set.univ : Set (Fin 2 → Bool)) ↔
      SpliceClosed (Set.univ : Set (Fin 2 → Bool)) :=
  coordinate_product_iff_spliceClosed Set.univ ⟨fun _ => false, trivial⟩

/-- Finiteness is not decorative: over an infinite index, splice closure and
full unary projections do not give the full product. -/
example : SpliceClosed FinitelySupported ∧ ¬ IsCoordinateProduct FinitelySupported :=
  ⟨spliceClosed_finitelySupported, not_isCoordinateProduct_finitelySupported⟩

open AISafetyAtlas.Compositional.LocalContractBoundary

/-- Two agents agreeing on a bit is not a product of independent local
contracts. -/
example : ¬ IsRectangle Agreement :=
  not_isRectangle_agreement

/-- A 2-safety hyperproperty that cannot be decided by checking each trace
against a fixed allowed set. -/
example :
    IsKSafety (fun p t : Bool => p = t) 2 (AtMostOneTrace Bool) ∧
      ¬ IsPureTraceProperty (AtMostOneTrace Bool) :=
  atMostOneTrace_bool_boundary

open AISafetyAtlas.Compositional.Symmetry

/-- A concrete anonymous deterministic protocol whose nodes remain identical. -/
def uniformProtocol : Protocol Bool Unit Unit where
  observe := fun _ _ => ()
  decide := fun _ => ()
  symmetric_observation := by intros; rfl

example (rounds : ℕ) :
    ¬ HasUniqueLeader (fun _ : Unit => True)
      (uniformProtocol.run rounds (fun _ => ())) :=
  uniformProtocol.no_unique_leader_from_symmetric_start
    ⟨false, true, by decide⟩ (fun _ => True) (fun _ => ())
    (fun _ _ => rfl) rounds

open AISafetyAtlas.Compositional.Networks

/-- A two-node ring: each node's single port leads to the other node. -/
def twoRing : Network Bool 1 where
  port := fun v _ => !v

/-- Swapping the two nodes is a port-preserving automorphism, and it fixes
neither node. -/
def swap : Automorphism twoRing where
  toEquiv := ⟨Bool.not, Bool.not, by intro b; cases b <;> rfl, by intro b; cases b <;> rfl⟩
  port_equivariant := by intro v i; cases v <;> rfl

/-- With a fixed-point-free automorphism and a constant initial configuration,
no anonymous deterministic algorithm ever elects a unique leader. -/
example (A : Algorithm Unit Unit 1) (n : ℕ) :
    ¬ Symmetry.HasUniqueLeader (fun _ : Unit => True)
      (runFor twoRing A (fun _ => ()) n) :=
  no_unique_leader_of_fixedPointFree swap A
    (by intro v; cases v <;> decide)
    (fun _ => True)
    (invariant_of_constant swap (fun _ _ => rfl)) n

open AISafetyAtlas.Wireheading

/-- Utility equal to the history index, with unit horizon weights. -/
def linearObjective : Objective ℕ where
  utility := fun h => (h : ℝ)
  horizon := fun _ _ => 1

/-- Agrees with `linearObjective` below `2` and diverges from it above. -/
def cappedObjective : Objective ℕ where
  utility := fun h => if h < 2 then (h : ℝ) else 100
  horizon := fun _ _ => 1

/-- Locality: the two objectives agree on the window `[0, 2)`. -/
example : linearObjective.value 0 2 id = cappedObjective.value 0 2 id :=
  Objective.value_eq_of_agree_on_window linearObjective cappedObjective 0 2 id
    (fun _ _ => rfl)
    (fun i hi => by
      show (i : ℝ) = if i < 2 then (i : ℝ) else 100
      rw [if_pos hi])

/-- The same two objectives genuinely differ once the window includes index
`2`, so the locality hypothesis above is doing real work. -/
example : linearObjective.value 0 3 id ≠ cappedObjective.value 0 3 id := by
  simp [Objective.value, linearObjective, cappedObjective,
    Finset.sum_range_succ]

/-- Positive rescaling of utility leaves the optimal decisions unchanged. -/
example (dynamics : Bool → ℕ → ℕ) (feasible : Set Bool) (start duration : ℕ) :
    {d | (Objective.scaleUtility 3 linearObjective).IsOptimal
        dynamics feasible start duration d} =
      {d | linearObjective.IsOptimal dynamics feasible start duration d} :=
  Objective.optimal_decisions_eq_of_pos_scaleUtility linearObjective
    (by norm_num) dynamics feasible start duration

open AISafetyAtlas.Wireheading.Corruption

/-- A two-hypothesis complemented reward class with unit worst-case regret. -/
def binaryCorruption : ComplementedClass Bool Bool where
  returnValue := fun μ π => if μ = π then 1 else 0
  horizon := 1
  complement := Bool.not
  complement_involutive := by
    intro μ
    cases μ <;> rfl
  complement_return := by
    intro μ π
    cases μ <;> cases π <;> norm_num
  bestPolicy := id
  bestPolicy_best := by
    intro μ π
    cases μ <;> cases π <;> norm_num
  worstEnvironment := Bool.not
  worstEnvironment_worst := by
    intro π μ
    cases π <;> cases μ <;> norm_num
  worstPolicy := false
  worstPolicy_worst := by
    intro π
    cases π <;> norm_num

example (π : Bool) :
    binaryCorruption.worstCaseRegret binaryCorruption.worstPolicy / 2 ≤
      binaryCorruption.worstCaseRegret π :=
  binaryCorruption.everitt_theorem_eleven π

open AISafetyAtlas.Wireheading.CRMDP

/-- Endpoints of the continuous unit reward interval used by `CRMDP`. -/
def zeroReward : Reward := ⟨0, by norm_num⟩
def oneReward : Reward := ⟨1, by norm_num⟩

/-- A concrete corrupt-reward environment on two states: the true reward
distinguishes them, and the corruption channel is not the identity. -/
def sampleEnv : Env Bool where
  trueReward := fun s => if s then oneReward else zeroReward
  corruption := fun _ x => Env.rewardComplement x

/-- Indistinguishability on a concrete environment: the complement is observed
identically, which is why no policy can separate them. -/
example (s : Bool) : sampleEnv.complement.observed s = sampleEnv.observed s :=
  Env.observed_complement sampleEnv s

/-- Equation (3) on a concrete run: true returns in an environment and its
complement sum to the horizon. -/
example (transition : Bool → Unit → Bool) (t : ℕ) (π : Policy Bool Unit) :
    returnOver transition t true sampleEnv π +
        returnOver transition t true sampleEnv.complement π = (t : ℝ) :=
  return_add_complement transition t true sampleEnv π

/-- One-step dynamics in which the selected action is the next state. -/
def actionTransition : Bool → Bool → Bool := fun _ a => a

/-- At horizon one, return is exactly the reward of the selected action-state. -/
theorem returnOver_actionTransition_one (μ : Env Bool) (π : Policy Bool Bool) :
    returnOver actionTransition 1 false μ π =
      μ.trueReward (π ((false, μ.observed false), [])) := by
  simp [returnOver, stateAt, run, actionTransition]

/-- Choose the better of the two action-states. -/
noncomputable def greedyCRMDPPolicy (μ : Env Bool) : Policy Bool Bool :=
  fun _ =>
    if (μ.trueReward false : ℝ) ≤ (μ.trueReward true : ℝ) then true else false

theorem greedyCRMDPPolicy_best (μ : Env Bool) (π : Policy Bool Bool) :
    returnOver actionTransition 1 false μ π ≤
      returnOver actionTransition 1 false μ (greedyCRMDPPolicy μ) := by
  rw [returnOver_actionTransition_one, returnOver_actionTransition_one]
  by_cases h : (μ.trueReward false : ℝ) ≤ (μ.trueReward true : ℝ)
  · cases hπ : π ((false, μ.observed false), [])
    · simp [greedyCRMDPPolicy, h]
    · simp [greedyCRMDPPolicy, h]
  · have h' : (μ.trueReward true : ℝ) ≤ (μ.trueReward false : ℝ) :=
      le_of_lt (lt_of_not_ge h)
    cases hπ : π ((false, μ.observed false), [])
    · simp [greedyCRMDPPolicy, h]
    · simp [greedyCRMDPPolicy, h, h']

/-- The initial history produced by a channel that always reports zero. -/
def zeroHistory : History Bool Bool := ((false, zeroReward), [])

/--
For a policy `π`, report zero everywhere, give zero true reward to the action
that `π` takes on that report, and give one to the other action.
-/
noncomputable def adversarialEnv (π : Policy Bool Bool) : Env Bool where
  trueReward := fun s => if s = π zeroHistory then zeroReward else oneReward
  corruption := fun _ _ => zeroReward

@[simp] theorem adversarialEnv_observed (π : Policy Bool Bool) (s : Bool) :
    (adversarialEnv π).observed s = zeroReward := rfl

theorem adversarialEnv_policy_return (π : Policy Bool Bool) :
    returnOver actionTransition 1 false (adversarialEnv π) π = 0 := by
  rw [returnOver_actionTransition_one]
  simp [adversarialEnv, Env.observed, zeroHistory, zeroReward]

theorem adversarialEnv_best_return (π : Policy Bool Bool) :
    returnOver actionTransition 1 false (adversarialEnv π)
        (greedyCRMDPPolicy (adversarialEnv π)) = 1 := by
  rw [returnOver_actionTransition_one]
  simp only [adversarialEnv_observed]
  cases hπ : π zeroHistory <;>
    norm_num [greedyCRMDPPolicy, adversarialEnv, zeroReward, oneReward, hπ]

theorem returnOver_actionTransition_one_nonneg
    (μ : Env Bool) (π : Policy Bool Bool) :
    0 ≤ returnOver actionTransition 1 false μ π := by
  rw [returnOver_actionTransition_one]
  exact (μ.trueReward _).property.1

theorem returnOver_actionTransition_one_le_one
    (μ : Env Bool) (π : Policy Bool Bool) :
    returnOver actionTransition 1 false μ π ≤ 1 := by
  rw [returnOver_actionTransition_one]
  exact (μ.trueReward _).property.2

/--
A nonzero-regret `CRMDP.Model`: each policy has worst-case regret exactly one.

This witnesses that bounded continuous rewards make the complete environment
class substantive. It still does not derive extrema generically from the
source's finite reward grid.
-/
noncomputable def nonzeroCRMDPModel :
    AISafetyAtlas.Wireheading.CRMDP.Model Bool Bool where
  transition := actionTransition
  horizon := 1
  start := false
  bestPolicy := greedyCRMDPPolicy
  bestPolicy_best := greedyCRMDPPolicy_best
  worstEnvironment := adversarialEnv
  worstEnvironment_worst := by
    intro π μ
    rw [adversarialEnv_best_return, adversarialEnv_policy_return]
    linarith [returnOver_actionTransition_one_le_one μ (greedyCRMDPPolicy μ),
      returnOver_actionTransition_one_nonneg μ π]
  worstPolicy := fun _ => false
  worstPolicy_worst := by
    intro π
    rw [adversarialEnv_best_return, adversarialEnv_policy_return,
      adversarialEnv_best_return, adversarialEnv_policy_return]

/-- The concrete model's worst-case regret is genuinely nonzero. -/
theorem nonzeroCRMDPModel_worstCaseRegret (π : Policy Bool Bool) :
    nonzeroCRMDPModel.toComplementedClass.worstCaseRegret π = 1 := by
  simp [AISafetyAtlas.Wireheading.Corruption.ComplementedClass.worstCaseRegret,
    AISafetyAtlas.Wireheading.Corruption.ComplementedClass.regret,
    AISafetyAtlas.Wireheading.CRMDP.Model.toComplementedClass,
    nonzeroCRMDPModel, adversarialEnv_best_return, adversarialEnv_policy_return]

/-- The full CRMDP theorem is instantiated on a nonzero-regret model. -/
example (π : Policy Bool Bool) :
    nonzeroCRMDPModel.toComplementedClass.worstCaseRegret
          nonzeroCRMDPModel.toComplementedClass.worstPolicy / 2 ≤
      nonzeroCRMDPModel.toComplementedClass.worstCaseRegret π :=
  nonzeroCRMDPModel.everitt_theorem_eleven π

open AISafetyAtlas.Wireheading.GoalPreservation

/-- A concrete coherent realistic-value model. -/
noncomputable def stationaryGoalModel :
    AISafetyAtlas.Wireheading.GoalPreservation.Model Unit Unit ℕ where
  act := fun p _ => ((), p)
  next := fun _ _ => ()
  utility := fun _ _ => 0
  discount := 1 / 2
  discount_pos := by norm_num
  continuation := fun _ _ => 0
  coherent := by intros; norm_num
  names_surjective := by
    intro _ a
    exact ⟨a.2, by cases a.1; rfl⟩

example :
    stationaryGoalModel.qValue
        (stationaryGoalModel.run 4 0 ()).2
        (stationaryGoalModel.act (stationaryGoalModel.run 4 0 ()).1
          (stationaryGoalModel.run 4 0 ()).2) =
      stationaryGoalModel.qValue
        (stationaryGoalModel.run 4 0 ()).2
        (stationaryGoalModel.act 0 (stationaryGoalModel.run 4 0 ()).2) := by
  apply stationaryGoalModel.goal_preservation 0 () (fun _ _ => ?_)
  simp [AISafetyAtlas.Wireheading.GoalPreservation.Model.qValue,
    stationaryGoalModel]

/--
A cardinality-nondegenerate goal model: two world actions and an infinite
policy-name type.

`stationaryGoalModel` above uses `WorldAction = Unit`, where `names_surjective`
is trivially satisfiable. This model shows the field is satisfiable when the
world-action type is not a subsingleton. It cannot be witnessed with a finite
name type: `names_surjective` demands a surjection
`PolicyName → WorldAction × PolicyName` at each history, which for finite
nonempty `PolicyName` and at least two world actions is impossible by
cardinality. The utility and continuation are still zero; this is a
satisfiability witness, not a paper-faithful agent.
-/
noncomputable def twoActionGoalModel :
    AISafetyAtlas.Wireheading.GoalPreservation.Model Unit Bool ℕ where
  act := fun p _ => (p % 2 == 1, p / 2)
  next := fun _ _ => ()
  utility := fun _ _ => 0
  discount := 1 / 2
  discount_pos := by norm_num
  continuation := fun _ _ => 0
  coherent := by intros; norm_num
  names_surjective := by
    intro _ a
    obtain ⟨b, m⟩ := a
    cases b
    · exact ⟨2 * m, by simp⟩
    · refine ⟨2 * m + 1, ?_⟩
      simp
      omega

example :
    twoActionGoalModel.qValue
        (twoActionGoalModel.run 3 5 ()).2
        (twoActionGoalModel.act (twoActionGoalModel.run 3 5 ()).1
          (twoActionGoalModel.run 3 5 ()).2) =
      twoActionGoalModel.qValue
        (twoActionGoalModel.run 3 5 ()).2
        (twoActionGoalModel.act 5 (twoActionGoalModel.run 3 5 ()).2) := by
  apply twoActionGoalModel.goal_preservation 5 () (fun _ _ => ?_)
  simp [AISafetyAtlas.Wireheading.GoalPreservation.Model.qValue,
    twoActionGoalModel]

/--
A finite-percept inhabitant of the no-surjectivity induction-step interface.

There are two world actions, policy names, histories, and percepts. Percept
weights form the uniform full-support distribution, and the initial
continuation has value `1` while the other named continuation has value `0`.
Thus `initial_dominates` is genuinely nonconstant rather than a
zero-equals-zero witness.
-/
noncomputable def finitePerceptGoalModel :
    AISafetyAtlas.Wireheading.GoalPreservationSource.Model Bool Bool Bool Bool where
  act := fun p _ => (p, false)
  extend := fun _ _ e => e
  utility := fun _ => 0
  discount := 1
  discount_pos := by norm_num
  prob := fun _ _ _ => 1 / 2
  prob_sum_one := by intros; norm_num [Fintype.sum_bool]
  prob_pos := by intros; norm_num
  contValue := fun p _ => if p then 0 else 1
  initial := false
  initial_dominates := by
    intro p h
    cases p <;> norm_num

/-- Every named policy is locally optimal in the witness because it selects the
strictly dominant initial continuation. -/
example (p h : Bool) :
    finitePerceptGoalModel.OptimalAt p h := by
  rintro ⟨w, q⟩
  cases q <;>
    norm_num
      [AISafetyAtlas.Wireheading.GoalPreservationSource.Model.qValue,
       finitePerceptGoalModel]

/-- The dominated continuation is strictly worse in expected `Q` value; this
exercises positivity of the percept weights rather than only structure
inhabitation. -/
example (h w e : Bool) :
    finitePerceptGoalModel.qValue h (w, true) <
      finitePerceptGoalModel.qValue h (w, finitePerceptGoalModel.initial) :=
  finitePerceptGoalModel.qValue_lt_of_lt h w true e
    (by simp [finitePerceptGoalModel])

/-- The source-aligned induction step fires on a genuinely dominated
alternative continuation and a full-support two-percept distribution. -/
example (p h e : Bool) :
    finitePerceptGoalModel.contValue
          (finitePerceptGoalModel.act p h).2
          (finitePerceptGoalModel.extend h (finitePerceptGoalModel.act p h).1 e) =
      finitePerceptGoalModel.contValue finitePerceptGoalModel.initial
        (finitePerceptGoalModel.extend h (finitePerceptGoalModel.act p h).1 e) :=
  finitePerceptGoalModel.selected_matches_initial
    (by
      rintro ⟨w, q⟩
      cases q <;>
        norm_num
          [AISafetyAtlas.Wireheading.GoalPreservationSource.Model.qValue,
           finitePerceptGoalModel])
    e

open AISafetyAtlas.Preference

/--
The degenerate `c`-reasonable language: every complexity is zero.

This is the only model of `ReasonableLanguage` exhibited anywhere in the atlas.
It makes the degeneracy visible: in it, Propositions 7 and 8 hold but say
nothing, since all complexities coincide. Whether a *nontrivial* `c`-reasonable
language exists is argued informally in the source and is not settled here.
-/
def degenerateLanguage : ReasonableLanguage Unit Bool where
  KPair := fun _ => 0
  KPolicy := fun _ => 0
  c := 0
  eval_le := by intro _; omega
  indifferent_le := by intro _; omega
  greedy_le := by intro _; omega
  antirational_le := by intro _; omega
  neg_le := by intro _; omega

/-- Proposition 7 instantiated at the degenerate language: every bound is
`0 ≤ 0`, which is exactly why a nontrivial model is the interesting question. -/
example (π : Preference.Policy Unit Bool) (x : Pair Unit Bool)
    (h : ReasonableLanguage.Compatible x π) :
    degenerateLanguage.KPair (op1 (op5 π)) ≤ degenerateLanguage.KPair x + 2 * degenerateLanguage.c :=
  degenerateLanguage.indifferent_le_compatible π x h

/-- The degenerate language again, in the source's own parameterization: the
`F`-complexity is zero, so `c = 0`. -/
def degenerateForF : Source.ReasonableForF Unit Bool where
  KPair := fun _ => 0
  c := 0
  F_complexity_le := by intro _ _; omega

/-- Proposition 7 at the source's distance `c`, not `2 * c`. -/
example (π : Preference.Policy Unit Bool) :
    degenerateForF.AmongLowestCompatible π (op1 (op5 π)) ∧
      degenerateForF.AmongLowestCompatible π (op2 (op6 π)) ∧
      degenerateForF.AmongLowestCompatible π (op4 (op2 (op6 π))) :=
  degenerateForF.proposition_seven π

/-- A zero override model: nothing is ever suboptimal. -/
def zeroOverrideModel : OverrideModel Unit Bool Unit where
  resulting := fun _ _ => false
  value := fun _ _ => 0
  optValue := fun _ => 0
  le_optValue := by intros; norm_num
  noop := ()
  rationalise := fun _ => ()
  rationalise_optimal := by intros; norm_num

/--
An override model where leaving the human alone is strictly suboptimal.

Action `false` is the no-op and leaves the human at value `0`; action `true`
rationalises them to the optimum `1`. This is the witness that exercises the
strict inequality, which the zero model cannot.
-/
def suboptimalOverrideModel : OverrideModel Unit Bool Bool where
  resulting := fun a _ => a
  value := fun _ π => if π () then 1 else 0
  optValue := fun _ => 1
  le_optValue := by
    intro _ π
    by_cases h : π () <;> simp [h]
  noop := false
  rationalise := fun _ => true
  rationalise_optimal := by intro _; simp

/-- The no-op is strictly worse than rationalising, so
`rationalise_strictly_better` fires. -/
example (R : RewardFn Unit Bool) :
    suboptimalOverrideModel.value R (suboptimalOverrideModel.resulting suboptimalOverrideModel.noop) <
      suboptimalOverrideModel.value R
        (suboptimalOverrideModel.resulting (suboptimalOverrideModel.rationalise R)) :=
  suboptimalOverrideModel.rationalise_strictly_better R (by simp [suboptimalOverrideModel])

/-- Source equation (2) applies to the rationalising action, while action `0`
has its separately defined value. -/
example (ε : ℝ) (R : RewardFn Unit Bool) :
    suboptimalOverrideModel.noopValue R <
      suboptimalOverrideModel.mixtureValue ε R R :=
  suboptimalOverrideModel.noopValue_lt_mixtureValue_rationalise ε R
    (by simp [suboptimalOverrideModel])

/-- Inaction itself has positive regret here, so it counts as an override at
every threshold up to that regret. -/
example (R : RewardFn Unit Bool) :
    0 < suboptimalOverrideModel.regret R suboptimalOverrideModel.noop ∧
      ∀ θ ≤ suboptimalOverrideModel.regret R suboptimalOverrideModel.noop,
        suboptimalOverrideModel.Overrides R θ suboptimalOverrideModel.noop :=
  suboptimalOverrideModel.noop_overrides_of_suboptimal R
    (by simp [suboptimalOverrideModel])

end AISafetyAtlas.Examples.SixTargets
