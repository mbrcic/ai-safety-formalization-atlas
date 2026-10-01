module

public import AISafetyAtlas.Causal.Requisite

/-!
# An observation that is requisite, and diagrams where none is

The requisite-observation module renders Definition 7 of Everitt et al. 2021.
This module runs it on diagrams small enough to check by hand, in both
directions: an observation the decision cannot be separated from its utility
without, and the degenerate case where separation holds for want of anywhere to
go.

## What is proved here and what is not

Refuting nonrequisiteness is a matter of exhibiting one active path, which is
what `predictCID_isRequisite` does: the observation feeds the utility node
directly, that edge is a path, and neither of its endpoints is conditioned on.

Establishing nonrequisiteness on a diagram with a real graph is a different
matter — it quantifies over every path — and is **not** done here. The paper's
own illustration is Figure 3a, where a grade predictor's `Gender` observation is
nonrequisite while `High school` is requisite; deciding that needs the Bayes-Ball
computation to *run*, and it cannot at present. `CID.parents` is a `Set` with no
decidability of its own, so `cidToDAG` supplies `Classical.propDecidable` and
the `Decidable (CID.DSep …)` instance is `noncomputable`: `decide` has nothing
to evaluate even though upstream's predicate is computable.

Closing that means a second carrier taking `DecidableRel (· ∈ G.parents ·)` as a
hypothesis and a proof that it agrees with `cidToDAG`, after which Figure 3a is
a `decide`. It is a real gap and it is recorded rather than worked around: the
nonrequisite direction below is proved from
`CID.isNonrequisite_of_utilityDescendants_eq_empty`, which needs no path
reasoning, and it is the degenerate case rather than the paper's.
-/

namespace AISafetyAtlas.Examples.Causal.Requisite

open AISafetyAtlas.Causal

/-- A three-vertex prediction diagram: an observation `0`, the decision `1`, and
a utility node `2` fed by both. This is Figure 3a with everything but one
observation deleted -- the predictor sees `0`, acts, and is scored against
something `0` also determines. -/
@[expose] public noncomputable def predictCID : CID (Fin 3) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {0, 1} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦
    if v = 1 then NodeKind.decision
    else if v = 2 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

@[simp] public theorem predictCID_parents_decision : predictCID.parents 1 = {0} := rfl

public theorem predictCID_isUtility_two : predictCID.IsUtility 2 := rfl

public theorem predictCID_isDecision_one : predictCID.IsDecision 1 := rfl

/-- The utility node is downstream of the decision, so it is in `U^D`. -/
public theorem predictCID_mem_utilityDescendants :
    (2 : Fin 3) ∈ predictCID.utilityDescendants 1 :=
  CID.mem_utilityDescendants.mpr
    ⟨predictCID_isUtility_two, Relation.ReflTransGen.single (by simp [predictCID])⟩

/-- The conditioning set of Definition 7 at the observation `0` is just the
decision: the other observations are none, and `0` itself is removed. -/
public theorem predictCID_requisiteContext :
    predictCID.requisiteContext 1 0 = {1} := by
  ext v
  simp only [CID.mem_requisiteContext, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact absurd (by simpa [predictCID] using h) hne
    · exact h
  · rintro rfl
    exact ⟨Or.inr rfl, by decide⟩

/-- **The observation is requisite.** The edge `0 → 2` is an active path from
the observation to a utility node downstream of the decision, and neither
endpoint is conditioned on, so Definition 7's separation fails.

This is the direction the paper's `High school` node illustrates. -/
public theorem predictCID_isRequisite : predictCID.IsRequisite 1 0 := by
  intro h
  refine h.2 ⟨[0, 2], by simp, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact Or.inl (by simp [cidToDAG, predictCID])
  · intro i hi
    simp at hi
  · refine Finset.mem_image.mpr ⟨0, ?_, rfl⟩
    simp [predictCID_requisiteContext]
  · refine Finset.mem_image.mpr ⟨2, ?_, rfl⟩
    rw [Finset.mem_sdiff, predictCID_requisiteContext]
    exact ⟨predictCID_mem_utilityDescendants, by decide⟩

/-! ## Definition 7's bookkeeping, at the diagram that makes it bite

The lemmas below are the module's structural statements about Definition 7,
applied at `predictCID` -- the one diagram in this file where the observation is
requisite and the decision is a genuine decision, so that both hypotheses of
`CID.requisite_sets_pairwise_disjoint` hold rather than being assumed.
-/

/-- The parent set as a `Finset`, at the prediction diagram. -/
public theorem predictCID_mem_parentsFinset :
    (0 : Fin 3) ∈ predictCID.parentsFinset 1 :=
  CID.mem_parentsFinset.mpr (by simp [predictCID_parents_decision])

/-- Requisiteness is the negation of nonrequisiteness, read where it holds. -/
public theorem predictCID_isRequisite_iff :
    predictCID.IsRequisite 1 0 ↔ ¬ predictCID.IsNonrequisite 1 0 :=
  CID.isRequisite_iff predictCID 1 0

/-- And so the observation is not nonrequisite. -/
public theorem predictCID_not_isNonrequisite :
    ¬ predictCID.IsNonrequisite 1 0 :=
  (CID.not_isNonrequisite_iff predictCID 1 0).mpr predictCID_isRequisite

/-- Print's *"otherwise"* is exhaustive ... -/
public theorem predictCID_nonrequisite_or_requisite :
    predictCID.IsNonrequisite 1 0 ∨ predictCID.IsRequisite 1 0 :=
  CID.isNonrequisite_or_isRequisite predictCID 1 0

/-- ... and exclusive. -/
public theorem predictCID_not_nonrequisite_and_requisite :
    ¬ (predictCID.IsNonrequisite 1 0 ∧ predictCID.IsRequisite 1 0) :=
  CID.not_and_isRequisite predictCID 1 0

/-- The observation under test is never in its own conditioning set, which is
the content of the `\ {X}` in print's displayed condition. -/
public theorem predictCID_not_mem_requisiteContext :
    (0 : Fin 3) ∉ predictCID.requisiteContext 1 0 :=
  CID.not_mem_requisiteContext predictCID 1 0

/-- **The three sets of Definition 7 are pairwise disjoint here.** Both
hypotheses are met rather than assumed: `1` is a decision, and `0` is one of its
parents -- which is exactly the configuration the module's docstring says the
lemma needs and an arbitrary `D` would not supply. -/
public theorem predictCID_requisite_sets_pairwise_disjoint :
    Disjoint ({0} : Finset (Fin 3)) (predictCID.utilityDescendants 1) ∧
      Disjoint ({0} : Finset (Fin 3)) (predictCID.requisiteContext 1 0) ∧
      Disjoint (predictCID.utilityDescendants 1)
        (predictCID.requisiteContext 1 0) :=
  CID.requisite_sets_pairwise_disjoint predictCID predictCID_isDecision_one
    (by simp [predictCID_parents_decision])

/-- A diagram with no utility node at all: the decision `1` observes `0` and
nothing scores it. -/
@[expose] public noncomputable def unscoredCID : CID (Fin 2) where
  parents := fun v ↦ if v = 1 then {0} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦ if v = 1 then NodeKind.decision else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> simp_all

public theorem unscoredCID_utilities : unscoredCID.utilities = ∅ := by decide

/-- **Every observation is nonrequisite when nothing is downstream to inform.**

`U^D` is empty, so Definition 7's separation holds with no path argument. The
definition does not silently presume that the decision influences a utility, and
this is the witness that it does not. -/
public theorem unscoredCID_isNonrequisite (x : Fin 2) :
    unscoredCID.IsNonrequisite 1 x := by
  refine CID.isNonrequisite_of_utilityDescendants_eq_empty unscoredCID ?_ x
  rw [CID.utilityDescendants, unscoredCID_utilities]
  simp

/-! ## Definition 7 at print's generality

`AISafetyAtlas.Causal.CID.isNonrequisiteSet_iff` is what makes the `Finset` form
above a computation of Definition 7 rather than a second definition. It is
exercised here at both diagrams, so every result on this page is a result about
print's Definition 7.
-/

/-- `U^D` as print's set, at `predictCID`. -/
public theorem predictCID_mem_utilityDescendantsSet :
    (2 : Fin 3) ∈ predictCID.utilityDescendantsSet 1 :=
  CID.mem_utilityDescendantsSet.mpr
    ⟨predictCID_isUtility_two, Relation.ReflTransGen.single (by simp [predictCID])⟩

/-- And print's conditioning set, at the same observation. -/
public theorem predictCID_mem_requisiteContextSet :
    (1 : Fin 3) ∈ predictCID.requisiteContextSet 1 0 :=
  CID.mem_requisiteContextSet.mpr ⟨Or.inr rfl, by decide⟩

/-- The observation under test is never in its own conditioning set, at print's
generality. -/
public theorem predictCID_not_mem_requisiteContextSet :
    (0 : Fin 3) ∉ predictCID.requisiteContextSet 1 0 :=
  CID.not_mem_requisiteContextSet predictCID 1 0

/-- The two renderings of `U^D` agree on a finite carrier. -/
public theorem predictCID_coe_utilityDescendants :
    ↑(predictCID.utilityDescendants 1) = predictCID.utilityDescendantsSet 1 :=
  CID.coe_utilityDescendants predictCID 1

/-- And so do the two renderings of the conditioning set. -/
public theorem predictCID_coe_requisiteContext :
    ↑(predictCID.requisiteContext 1 0) = predictCID.requisiteContextSet 1 0 :=
  CID.coe_requisiteContext predictCID 1 0

/-- **The observation is requisite under print's own definition**, not only
under the computed one: `predictCID_isRequisite` transferred along the
equivalence. -/
public theorem predictCID_not_isNonrequisiteSet :
    ¬ predictCID.IsNonrequisiteSet 1 0 :=
  fun h ↦ predictCID_isRequisite ((CID.isNonrequisiteSet_iff predictCID 1 0).mp h)

/-- **And the degenerate case holds under print's definition too**: with no
utility downstream, every observation is nonrequisite. -/
public theorem unscoredCID_isNonrequisiteSet (x : Fin 2) :
    unscoredCID.IsNonrequisiteSet 1 x :=
  (CID.isNonrequisiteSet_iff unscoredCID 1 x).mpr (unscoredCID_isNonrequisite x)

/-- **Definition 7 under print's own word for a path**, at the diagram where the
observation is requisite. -/
public theorem predictCID_not_dSepPath :
    ¬ predictCID.DSepPath {0} (predictCID.utilityDescendantsSet 1)
      (predictCID.requisiteContextSet 1 0) :=
  fun h ↦ predictCID_not_isNonrequisiteSet
    ((CID.isNonrequisiteSet_iff_dSepPath predictCID 1 0).mpr h)

end AISafetyAtlas.Examples.Causal.Requisite
