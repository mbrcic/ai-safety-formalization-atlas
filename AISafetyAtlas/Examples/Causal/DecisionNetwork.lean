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

end AISafetyAtlas.Examples.Causal.DecisionNetwork
