module

public import AISafetyAtlas.Causal.DecisionNetwork

/-!
# Richens and Everitt's Figure 1, as a causal influence diagram

`AISafetyAtlas.Causal.DecisionNetwork` renders RE24 Definition 4 and the
Section 2.2 sentences on expected utility, optimality and regret. This module
runs them on the paper's own training diagram:

```
X ──▶ Y
│     │
▼     ▼
D ──▶ U
```

with `X` a fair bit, `Y` a copy of `X`, `D` the decision observing `X`, and `U`
the utility, which pays `1` exactly when the decision matches `Y`.

**Why this module exists.** `IsUnmediated` is Assumption 1, and
`mem_parents_utility_of_isUnmediated` is print's Appendix step conditional on it.
Both would be vacuous if no diagram satisfied the assumption. `figIsUnmediated`
is that diagram, and it is print's own.
-/

namespace AISafetyAtlas.Examples.Causal.DecisionNetwork

open AISafetyAtlas.Causal

/-- `0 = X`, `1 = Y`, `2 = D`, `3 = U`. -/
public abbrev Node := Fin 4

/-- Every variable is binary. -/
public abbrev figDim : Node → ℕ := binaryDim Node

/-- `X → Y`, `X → D`, and `Y, D → U`. -/
@[expose] public def figParents : Node → Finset Node :=
  fun v ↦ if v = 1 then {0} else if v = 2 then {0} else if v = 3 then {1, 2} else ∅

/-- The utility fires when the decision matches `Y`. -/
@[expose] public def figCpt (c : Node) (a : Fin (figDim c))
    (v : Assignment Node figDim) : ℚ :=
  if c = 3 then (if a = (if v 1 = v 2 then 1 else 0) then 1 else 0) else 1 / 2

/-- The CBN of Figure 1. -/
@[expose] public def figNet : Model Node figDim ℚ where
  dim_pos := by decide
  parents := figParents
  acyclic := ⟨fun v ↦ (v : ℕ), by decide⟩
  cpt := figCpt
  cpt_parents := by
    intro c a v w h
    by_cases hc : c = 3
    · subst hc
      have h1 : v 1 = w 1 := h 1 (by decide)
      have h2 : v 2 = w 2 := h 2 (by decide)
      simp [figCpt, h1, h2]
    · simp [figCpt, hc]
  cpt_nonneg := by
    intro c a v
    by_cases hc : c = 3
    · subst hc; simp only [figCpt]; split_ifs <;> norm_num
    · simp [figCpt, hc]
  cpt_sum := by
    intro c v
    by_cases hc : c = 3
    · subst hc; simp [figCpt]
    · simp [figCpt, hc]

/-- Figure 1 as a single-decision, single-utility CID. -/
@[expose] public def figCID : DecisionNetwork Node figDim ℚ where
  net := figNet
  decision := 2
  utility := 3
  decision_ne_utility := by decide
  uval := fun a ↦ (a : ℚ)

/-! ## Assumption 1 is satisfied -/

public theorem figNet_ancestors_zero : figNet.ancestors {0} = {0} := by decide

public theorem figNet_ancestors_one : figNet.ancestors {1} = {0, 1} := by decide

public theorem figNet_ancestors_three : figNet.ancestors {3} = Finset.univ := by decide

/-- **Assumption 1 holds on print's own diagram.** The decision's only proper
descendant is the utility, and the utility is not a proper ancestor of itself. -/
public theorem figIsUnmediated : figCID.IsUnmediated := by
  show Disjoint (figNet.properDescendants figCID.decision)
    (figNet.properAncestors figCID.utility)
  rw [Finset.disjoint_left]
  decide

/-- The decision is a proper ancestor of the utility, so the diagram is not the
trivial one print's Appendix sets aside. -/
public theorem figDecision_mem_properAncestors :
    figCID.decision ∈ figNet.properAncestors figCID.utility := by decide

/-- **Print's Appendix step, run.** Assumption 1 plus non-triviality forces the
direct edge, and here it is. -/
public theorem figDecision_mem_parents_utility :
    figCID.decision ∈ figNet.parents figCID.utility :=
  figCID.mem_parents_utility_of_isUnmediated figIsUnmediated figDecision_mem_properAncestors

/-- **The utility is a function of its parents**, which is print's Definition 4
clause, met here rather than assumed. -/
public theorem figIsDeterministicUtility : figCID.IsDeterministicUtility := by
  intro v
  exact ⟨if v 1 = v 2 then 1 else 0, by simp [figCID, figNet, figCpt]⟩

/-! ## A policy, and the diagram vocabulary read at it

`instNonemptyPolicy` inhabits `Policy` by ignoring the observation. The policy
below does not: it reads `X` and copies it, which on this diagram is the
decision that matches `Y`. Having one makes the regret and intervention lemmas
statements about an actual policy rather than about a bound variable.
-/

/-- **The policy that copies `X`.** `D`'s only parent is `X`, so this is a
legitimate `π(d | pa_D)`.

It is **not** the decision that matches the utility's target, and an earlier
version of this docstring said it was: `figParents` declares the edge `X → Y`,
but `figCpt` gives `Y` the constant table `1/2`, so `Y` is a fair coin whatever
`X` is. `figExpectedUtility_const` is that fact — every policy on this diagram
scores `1/2`. -/
@[expose] public def figCopyPolicy : figCID.Policy where
  prob := fun a v ↦ if a = v 0 then 1 else 0
  prob_nonneg := by
    intro a v
    split_ifs <;> norm_num
  prob_sum := by
    intro v
    simp
  prob_parents := by
    intro a v w h
    rw [h 0 (by decide)]

/-- **Regret against oneself is zero**, which is what makes regret a comparison
and not a score. -/
public theorem figRegret_self : figCID.regret figCopyPolicy figCopyPolicy = 0 :=
  AISafetyAtlas.Causal.DecisionNetwork.regret_self figCID figCopyPolicy

/-- **Installing a policy replaces the decision's table** and leaves every other
table alone -- the two halves of `withPolicy`, read at this diagram. -/
public theorem figWithPolicy_cpt_decision :
    (figNet.withPolicy figCopyPolicy).cpt 2 = figCopyPolicy.prob :=
  AISafetyAtlas.Causal.Model.withPolicy_cpt_decision figNet figCopyPolicy

public theorem figWithPolicy_cpt_utility :
    (figNet.withPolicy figCopyPolicy).cpt 3 = figNet.cpt 3 :=
  AISafetyAtlas.Causal.Model.withPolicy_cpt_of_ne figNet figCopyPolicy (by decide)

/-! ## The ancestry vocabulary, at Figure 1 -/

/-- Proper ancestry is ancestry with the vertex itself removed. -/
public theorem figMem_properAncestors_iff :
    (2 : Node) ∈ figNet.properAncestors 3 ↔
      (2 : Node) ≠ 3 ∧ (2 : Node) ∈ figNet.ancestors {3} :=
  AISafetyAtlas.Causal.Model.mem_properAncestors_iff figNet

/-- And proper descent is its converse, which is why Assumption 1 can be stated
with either. -/
public theorem figMem_properDescendants_iff :
    (2 : Node) ∈ figNet.properDescendants 3 ↔ (3 : Node) ∈ figNet.properAncestors 2 :=
  AISafetyAtlas.Causal.Model.mem_properDescendants_iff figNet

/-- **Ancestry is transitive**: `X` is an ancestor of `U`, so everything `X`
descends from does too -- here that closure is already all of `{0}`. -/
public theorem figAncestors_singleton_subset :
    figNet.ancestors {0} ⊆ figNet.ancestors {3} :=
  AISafetyAtlas.Causal.Model.ancestors_singleton_subset figNet
    (by rw [figNet_ancestors_three]; exact Finset.mem_univ 0)

/-! ## The factors the agreement runs on

`DecisionNetwork.factor_observationalProfile` and
`withPolicy_factor_observationalProfile` are the first step toward connecting
this diagram's expected utility to the unmediated projection of section 6. Here
they are on Figure 1.
-/

/-- The chance vertex `X` is a fair coin, and that is what its factor says. -/
public theorem figFactor_zero (v : Assignment Node figDim) :
    figNet.factor (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) v 0
      = 1 / 2 := by
  rw [AISafetyAtlas.Causal.DecisionNetwork.factor_observationalProfile]
  simp [figNet, figCpt]

/-- A policy for the decision that ignores its observation and plays `1`. -/
@[expose] public def figAlwaysOne : figCID.Policy where
  prob := fun a _ ↦ if a = 1 then 1 else 0
  prob_nonneg := by intro a v; split_ifs <;> norm_num
  prob_sum := by intro v; simp
  prob_parents := by intro a v w _; rfl

/-- **Installing it changes the decision's factor**, and nothing else. -/
public theorem figWithPolicy_factor_decision (v : Assignment Node figDim) :
    (figCID.net.withPolicy figAlwaysOne).factor
        (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) v 2
      = figAlwaysOne.prob (v figCID.decision) v := by
  rw [AISafetyAtlas.Causal.DecisionNetwork.withPolicy_factor_observationalProfile,
    if_pos (show (2 : Node) = figCID.decision from rfl)]

/-- …and the utility's factor is untouched by it. -/
public theorem figWithPolicy_factor_utility (v : Assignment Node figDim) :
    (figCID.net.withPolicy figAlwaysOne).factor
        (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) v 3
      = figCID.net.factor
          (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) v 3 := by
  rw [AISafetyAtlas.Causal.DecisionNetwork.withPolicy_factor_observationalProfile,
    if_neg (show ¬((3 : Node) = figCID.decision) from by decide)]

/-- **The ancestors of the utility carry their own factors**, which is the
hypothesis `sum_jointProb_mul` asks for and the set the agreement is proved
over. -/
public theorem figAncestors_selfDetermining :
    figNet.SelfDetermining (AISafetyAtlas.Causal.Model.observationalProfile Node figDim)
      (figNet.ancestors {3}) :=
  figNet.selfDetermining_of_parentClosed _ (figNet.parentClosed_ancestors _)

/-- **An expectation of a function of the utility vertex collapses onto that
set.** This is `sum_jointProb_mul` at Figure 1, with the integrand the utility's
own readout. -/
public theorem figSum_jointProb_mul :
    ∑ v : Assignment Node figDim,
        figNet.jointProb (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) v
          * figCID.uval (v 3)
      = ∑ r ∈ Finset.univ.image (fibreRep figNet (figNet.ancestors {3})),
          (∏ c ∈ figNet.ancestors {3},
            figNet.factor (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) r c)
            * figCID.uval (r 3) :=
  AISafetyAtlas.Causal.Model.sum_jointProb_mul_of_parentClosed figNet _
    (figNet.parentClosed_ancestors _)
    (fun v w h ↦ by rw [h 3 (by rw [figNet_ancestors_three]; exact Finset.mem_univ 3)])

/-- The same collapse read through the self-determining hypothesis rather than
through parent closure, which is the form `Model.marginal_eq_prod` actually
consumes. -/
public theorem figSum_jointProb_mul_selfDetermining :
    ∑ v : Assignment Node figDim,
        figNet.jointProb (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) v
          * figCID.uval (v 3)
      = ∑ r ∈ Finset.univ.image (fibreRep figNet (figNet.ancestors {3})),
          (∏ c ∈ figNet.ancestors {3},
            figNet.factor (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) r c)
            * figCID.uval (r 3) :=
  AISafetyAtlas.Causal.Model.sum_jointProb_mul figNet _ figAncestors_selfDetermining
    (fun v w h ↦ by rw [h 3 (by rw [figNet_ancestors_three]; exact Finset.mem_univ 3)])

/-! ## The agreement with the unmediated projection, at Figure 1 -/

/-- **The context the projection keeps**: `X` and `Y`. The decision and the
utility leave the graph and nothing else does. -/
public theorem figChanceContext : figCID.chanceContext = {0, 1} := by decide

/-- **The context is parent-closed**, which is Assumption 1 doing its work on
this diagram. -/
public theorem figParentClosed_chanceContext :
    figNet.ParentClosed figCID.chanceContext :=
  figCID.parentClosed_chanceContext figIsUnmediated

/-- The decision's observation survives the projection. -/
public theorem figParents_decision_subset :
    figNet.parents figCID.decision ⊆ figCID.chanceContext :=
  figCID.parents_decision_subset_chanceContext figDecision_mem_properAncestors

/-- `Y` is a parent of the utility other than the decision, so it is in the
context. -/
public theorem figOne_mem_chanceContext : (1 : Node) ∈ figCID.chanceContext :=
  figCID.mem_chanceContext_of_mem_parents_utility (by decide) (by decide)

/-- **Print's *U(pa_U)* is the utility vertex's conditional expectation here**,
because the utility fires with probability one on the matching state. -/
public theorem figUtilityMean (v : Assignment Node figDim) :
    figCID.utilityMean v = if v 1 = v 2 then 1 else 0 := by
  have h : figNet.cpt 3 (if v 1 = v 2 then 1 else 0) v = 1 := by
    simp [figNet, figCpt]
  rw [figCID.utilityMean_eq_uval_of_cpt_eq_one (a := if v 1 = v 2 then 1 else 0) h]
  by_cases hv : v 1 = v 2 <;> simp [figCID, hv]

/-- **Print's *U(pa_U)* recovered on Figure 1.** The diagram satisfies
Definition 4's determinacy clause, so the conditional expectation is a function
of the utility's parents read through `uval` -- the specialisation the agreement
does not need but print states. -/
public theorem figUtilityMean_eq_uval :
    ∃ f : Assignment Node figDim → Fin (figDim figCID.utility),
      (∀ v w, (∀ p ∈ figNet.parents figCID.utility, v p = w p) → f v = f w) ∧
        ∀ v, figCID.utilityMean v = figCID.uval (f v) :=
  figCID.utilityMean_eq_uval_of_isDeterministicUtility figIsDeterministicUtility

/-- The readout is in `[0,1]`, which is RE24 Appendix A.2 on this diagram. -/
public theorem figUval_mem_unitInterval :
    ∀ b : Fin (figDim figCID.utility), 0 ≤ figCID.uval b ∧ figCID.uval b ≤ 1 := by decide

/-- **The utility's conditional expectation is in `[0,1]` too**, which is the
field the projection's `Skeleton` carries. -/
public theorem figUtilityMean_mem_unitInterval (v : Assignment Node figDim) :
    0 ≤ figCID.utilityMean v ∧ figCID.utilityMean v ≤ 1 :=
  figCID.utilityMean_mem_unitInterval figUval_mem_unitInterval v

/-- **The decision's contribution at a context point** is the probability the
policy puts on matching `Y`. -/
public theorem figPolicyUtility (π : figCID.Policy) (q : Assignment Node figDim) :
    figCID.policyUtility π q = π.prob (q 1) q := by
  classical
  have hupd : ∀ a : Fin (figDim figCID.decision),
      figCID.utilityMean (Function.update q figCID.decision a)
        = if q 1 = a then 1 else 0 := by
    intro a
    rw [figUtilityMean]
    congr 1
  rw [AISafetyAtlas.Causal.DecisionNetwork.policyUtility]
  simp only [hupd, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.univ) (q 1) (fun a ↦ π.prob a q)]
  simp

/-- **`X` and `Y` are a fair coin each**, so the context factor is `1/4`
everywhere. -/
public theorem figContextProduct (q : Assignment Node figDim) :
    (∏ c ∈ figCID.chanceContext,
        figNet.factor (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) q c)
      = 1 / 4 := by
  rw [figChanceContext]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  rw [AISafetyAtlas.Causal.DecisionNetwork.factor_observationalProfile,
    AISafetyAtlas.Causal.DecisionNetwork.factor_observationalProfile]
  have h0 : figNet.cpt 0 (q 0) q = 1 / 2 := by simp [figNet, figCpt]
  have h1 : figNet.cpt 1 (q 1) q = 1 / 2 := by simp [figNet, figCpt]
  rw [h0, h1]
  norm_num

/-- **The agreement itself, on print's own diagram.** The diagram's
*E^π[U] = E[U | do(D = π(pa_D))]* equals `Model.value` on the unmediated
projection, at the policy that copies `X`. -/
public theorem figExpectedUtility_eq_value :
    figCID.expectedUtility figCopyPolicy
      = figNet.value (figCID.projectedSkeleton figUval_mem_unitInterval)
          (figNet.parents figCID.decision) (figCID.projectedPolicy figCopyPolicy)
          (AISafetyAtlas.Causal.ProbMixture.dirac
            (AISafetyAtlas.Causal.Model.observationalProfile Node figDim)) :=
  figCID.expectedUtility_eq_value figIsUnmediated figUval_mem_unitInterval figCopyPolicy

/-- And the same at the policy that ignores its observation. -/
public theorem figAlwaysOne_expectedUtility_eq_value :
    figCID.expectedUtility figAlwaysOne
      = figNet.value (figCID.projectedSkeleton figUval_mem_unitInterval)
          (figNet.parents figCID.decision) (figCID.projectedPolicy figAlwaysOne)
          (AISafetyAtlas.Causal.ProbMixture.dirac
            (AISafetyAtlas.Causal.Model.observationalProfile Node figDim)) :=
  figCID.expectedUtility_eq_value figIsUnmediated figUval_mem_unitInterval figAlwaysOne

/-! ### What the diagram's own tables make of it

The edge `X → Y` is declared in `figParents` and **ignored by `figCpt`**: `Y` is
a fair coin whatever `X` is. So the utility fires exactly when the decision
matches a coin nobody observes, and every policy scores `1/2`. That makes the
optimality and regret statements checkable here -- and it is why the policy that
copies `X` is optimal without being informative.
-/

/-- The four context representatives, written out. -/
@[expose] public def figRep (x y : Fin 2) : Assignment Node figDim :=
  fun c ↦ if c = 0 then x else if c = 1 then y else 0

public theorem figContextReps :
    Finset.univ.image (fibreRep figNet figCID.chanceContext)
      = {figRep 0 0, figRep 0 1, figRep 1 0, figRep 1 1} := by decide

/-- **Every policy on Figure 1 has expected utility `1/2`.** The utility's
target is a coin independent of everything the decision can read. -/
public theorem figExpectedUtility_const (π : figCID.Policy) :
    figCID.expectedUtility π = 1 / 2 := by
  classical
  rw [figCID.expectedUtility_eq_contextSum figIsUnmediated π,
    show figCID.net = figNet from rfl, figContextReps]
  have hread : ∀ (x y : Fin 2) (a : Fin (figDim figCID.decision)),
      π.prob a (figRep x y) = π.prob a (figRep x 0) :=
    fun x y a ↦ π.prob_parents a _ _ (fun q hq ↦ by
      have hq0 : ∀ p : Node, p ∈ figNet.parents figCID.decision → p = 0 := by decide
      rw [hq0 q hq]
      simp [figRep])
  simp only [figContextProduct, figPolicyUtility]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h00 : (figRep 0 0) 1 = (0 : Fin 2) := rfl
  have h01 : (figRep 0 1) 1 = (1 : Fin 2) := rfl
  have h10 : (figRep 1 0) 1 = (0 : Fin 2) := rfl
  have h11 : (figRep 1 1) 1 = (1 : Fin 2) := rfl
  rw [h00, h01, h10, h11, hread 0 1 1, hread 1 1 1]
  have hs0 := π.prob_sum (figRep 0 0)
  have hs1 := π.prob_sum (figRep 1 0)
  rw [Fin.sum_univ_two] at hs0 hs1
  linarith

/-- **Copying `X` is optimal**, for the uninformative reason above: nothing
beats `1/2` on this diagram. -/
public theorem figIsOptimal : figCID.IsOptimal figCopyPolicy := fun π' ↦ by
  rw [figExpectedUtility_const, figExpectedUtility_const]

/-- **The two optima agree**, so the projection's `optimalValue` is the
diagram's. -/
public theorem figOptimalValue_eq :
    figNet.optimalValue (figCID.projectedSkeleton figUval_mem_unitInterval)
        (figNet.parents figCID.decision)
        (AISafetyAtlas.Causal.ProbMixture.dirac
          (AISafetyAtlas.Causal.Model.observationalProfile Node figDim))
      = figCID.expectedUtility figCopyPolicy :=
  figCID.optimalValue_eq_expectedUtility figIsUnmediated figUval_mem_unitInterval figIsOptimal

/-- **RE24 §2.2 regret, carried across**, on print's own diagram. -/
public theorem figRegret_eq_value_regret :
    figCID.regret figCopyPolicy figAlwaysOne
      = figNet.regret (figCID.projectedSkeleton figUval_mem_unitInterval)
          (figNet.parents figCID.decision) (figCID.projectedPolicy figAlwaysOne)
          (AISafetyAtlas.Causal.ProbMixture.dirac
            (AISafetyAtlas.Causal.Model.observationalProfile Node figDim)) :=
  figCID.regret_eq_value_regret figIsUnmediated figUval_mem_unitInterval figIsOptimal

/-- **A policy outside the graph is a policy on the decision vertex**, and
`projectedPolicy` undoes `liftPolicy`. -/
public theorem figProjectedPolicy_liftPolicy
    (ρ : AISafetyAtlas.Causal.Policy (dim := figDim) (figNet.parents figCID.decision)
      (Fin (figDim figCID.decision)) ℚ) :
    figCID.projectedPolicy (figCID.liftPolicy ρ) = ρ :=
  figCID.projectedPolicy_liftPolicy ρ

/-- **The proper ancestors of the utility are parent-closed**, the hypothesis the
first collapse consumes. -/
public theorem figParentClosed_properAncestors :
    figNet.ParentClosed (figNet.properAncestors 3) :=
  figNet.parentClosed_properAncestors 3

/-- **A point-mass mixture is the observational profile itself.** -/
public theorem figJointProbMix_dirac (v : Assignment Node figDim) :
    figNet.jointProbMix
        (AISafetyAtlas.Causal.ProbMixture.dirac (𝕜 := ℚ)
          (AISafetyAtlas.Causal.Model.observationalProfile Node figDim)).1 v
      = figNet.jointProb (AISafetyAtlas.Causal.Model.observationalProfile Node figDim) v :=
  AISafetyAtlas.Causal.Model.jointProbMix_dirac figNet _ v

/-- **The representatives are exactly the assignments pinned off the context.** -/
public theorem figMem_image_fibreRep_iff (r : Assignment Node figDim) :
    r ∈ Finset.univ.image (fibreRep figNet figCID.chanceContext) ↔
      ∀ c ∉ figCID.chanceContext, r c = ⟨0, figNet.dim_pos c⟩ :=
  AISafetyAtlas.Causal.mem_image_fibreRep_iff figNet figCID.chanceContext r

/-- **One coordinate split off**, which is the step that turns the diagram's
expectation into the projection's. -/
public theorem figSum_image_fibreRep_erase (F : Assignment Node figDim → ℚ) :
    ∑ r ∈ Finset.univ.image (fibreRep figNet (figNet.ancestors {3})), F r
      = ∑ q ∈ Finset.univ.image
            (fibreRep figNet ((figNet.ancestors {3}).erase 3)),
          ∑ a : Fin (figDim 3), F (Function.update q 3 a) :=
  AISafetyAtlas.Causal.sum_image_fibreRep_erase figNet
    (by rw [figNet_ancestors_three]; exact Finset.mem_univ 3) F

/-- **Regret is non-negative against an optimal policy.** The sign convention
the whole regret layer rests on, run at the diagram's own optimum -- and the
file proved `regret_self = 0` without ever checking the inequality that makes
zero the floor. -/
public theorem figRegret_nonneg (π : figCID.Policy) : 0 ≤ figCID.regret figCopyPolicy π :=
  AISafetyAtlas.Causal.DecisionNetwork.regret_nonneg figCID figIsOptimal

/-- **Installing a policy does not move the graph.** The half of `withPolicy`
the file did not read: both conditional-table halves were checked and the
structural one, which is what makes the projection a projection rather than a
different diagram, was not. -/
public theorem figWithPolicy_parents :
    (figNet.withPolicy figCopyPolicy).parents = figNet.parents :=
  AISafetyAtlas.Causal.Model.withPolicy_parents figNet figCopyPolicy

end AISafetyAtlas.Examples.Causal.DecisionNetwork
