import AISafetyAtlas.Causal.DecisionNetwork

/-!
Richens and Everitt (ICLR 2024), Assumption 1, p. 3 and Appendix A.1,
p. 14. The intersection of the decision's proper descendants and the
utility's proper ancestors is empty. The cited predicate is
`DecisionNetwork.IsUnmediated`.

The map retains the finite graph, variable domains, and designated decision
and utility. It puts a real point mass at state zero at each vertex and
uses a constant-zero utility readout, giving a deterministic utility.

Checked: `lake env lean docs/provenance/transfers/269-unmediated-decision.lean`
-/

namespace Transfer269

open AISafetyAtlas.Causal

variable {C : Type*} [Fintype C] [DecidableEq C] {dim : C → ℕ}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

def PrintStatement (G : DecisionNetwork C dim ℝ) (_ : G.IsDeterministicUtility) : Prop :=
  G.net.properDescendants G.decision ∩ G.net.properAncestors G.utility = ∅

def LeanStatement (G : DecisionNetwork C dim 𝕜) : Prop :=
  G.IsUnmediated

private def firstState (G : DecisionNetwork C dim 𝕜) (c : C) : Fin (dim c) :=
  ⟨0, G.net.dim_pos c⟩

noncomputable def phi (G : DecisionNetwork C dim 𝕜) : DecisionNetwork C dim ℝ where
  net :=
    { dim_pos := G.net.dim_pos
      parents := G.net.parents
      acyclic := G.net.acyclic
      cpt := fun c a _ ↦ if a = firstState G c then 1 else 0
      cpt_parents := fun _ _ _ _ _ ↦ rfl
      cpt_nonneg := by
        intro c a v
        split <;> norm_num
      cpt_sum := by
        intro c v
        simp }
  decision := G.decision
  utility := G.utility
  decision_ne_utility := G.decision_ne_utility
  uval := fun _ ↦ 0

theorem print_hyp (G : DecisionNetwork C dim 𝕜) :
    (phi G).IsDeterministicUtility := by
  intro v
  refine ⟨firstState G G.utility, ?_⟩
  simp [phi]

theorem defining_condition (G : DecisionNetwork C dim 𝕜) :
    LeanStatement G ↔ PrintStatement (phi G) (print_hyp G) :=
  Finset.disjoint_iff_inter_eq_empty

theorem lean_of_print (G : DecisionNetwork C dim 𝕜) :
    PrintStatement (phi G) (print_hyp G) → LeanStatement G :=
  (defining_condition G).mpr

theorem print_of_lean (G : DecisionNetwork C dim ℝ) (hG : G.IsDeterministicUtility) :
    LeanStatement G → PrintStatement G hG :=
  Finset.disjoint_iff_inter_eq_empty.mp

end Transfer269
