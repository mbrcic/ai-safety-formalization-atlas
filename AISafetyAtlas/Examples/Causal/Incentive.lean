module

public import AISafetyAtlas.Causal.Incentive

/-!
# A diagram with an instrumental control incentive, and a vertex without one

`AISafetyAtlas.Causal.Incentive` renders Definition 17 and Theorem 18 of Everitt
et al. 2021, both directions. This module runs them on a diagram small enough to
check by hand: a chain `D → X → U` with a fourth vertex `W` off it.

The point is that Definition 17 is a condition something meets. An incentive
definition that no model satisfies is a valid definition and says nothing, and
the conditional expectations it compares are quotients that could easily be
equal for a reason having nothing to do with the graph.

**Why the exogenous variables are trivial here.** Every `E^V` is one-element, so
`ExoAssignment` is a singleton, `P(ε) = 1` on it, and both conditional
expectations reduce to their integrand at the single draw. That keeps the
example about Definition 17 rather than about summation. It costs nothing:
Theorem 18's completeness construction in print is likewise deterministic — its
model *"sets all other variables to 0"* and never reads the noise.

**The incentive holds against every policy, not only the optimal ones.** Print's
Definition 17 quantifies over optimal policies, and here the stronger statement
is available: at *any* policy, the counterfactual decision `d` that disagrees
with what the policy plays makes the two conditional expectations differ. So the
witness needs no analysis of which policies are optimal, and
`chainSCIM_hasICI_on_X` follows from `chainSCIM_forall_policy`.

**A second diagram, with two decisions**, is at the end. Print's Theorem 18 is
stated for single-decision CIDs and says nothing about it; the criterion decides
it anyway. That is the witness that
`Causal.CID.admitsICI_iff_of_decisionFree`'s hypothesis is genuinely weaker than
print's rather than a restatement of it.
-/

namespace AISafetyAtlas.Examples.Causal.Incentive

open AISafetyAtlas.Causal

/-! ## The diagram

`D = 0 → X = 1 → U = 2`, with `W = 3` isolated. The decision observes nothing,
which makes the decision context vacuous and every exogenous draw admissible.
-/

/-- Four binary variables. -/
public abbrev chainDim : Fin 4 → Type := fun _ ↦ Fin 2

/-- No randomness anywhere: every exogenous variable is one-element. -/
public abbrev chainExo : Fin 4 → Type := fun _ ↦ Fin 1

/-- `D → X → U`, and `W` attached to nothing. -/
public noncomputable def chainCID : CID (Fin 4) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {1} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦
    if v = 0 then NodeKind.decision
    else if v = 2 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

public theorem chainCID_decisions : chainCID.decisions = {0} := by decide

public theorem chainCID_utilities : chainCID.utilities = {2} := by decide

public theorem chainCID_singleDecision : chainCID.IsSingleDecision :=
  ⟨0, chainCID_decisions⟩

/-- The decision observes nothing, so there is exactly one decision context and
it has probability one. -/
public theorem chainCID_parents_decision : chainCID.parents 0 = ∅ := by
  simp [chainCID]

/-! ## The model

`X` copies `D`, `U` copies `X`, `W` is constant. Utility states read as their own
index, so `U`'s real value is the decision's bit.
-/

/-- `X` copies `D`; `U` copies `X`; `W` is `0`. `D` has no structural function
until a policy supplies one. -/
@[expose] public def chainF (v : Fin 4) (a : EndoAssignment (Fin 4) chainDim) :
    chainDim v :=
  if v = 1 then a 0 else if v = 2 then a 1 else 0

/-- The chain, as a SCIM. -/
@[expose] public noncomputable def chainSCIM : SCIM (Fin 4) chainDim chainExo where
  dom_nonempty := fun _ ↦ ⟨0⟩
  graph := chainCID
  utilityValue := fun _ _ i ↦ (i : ℝ)
  utilityValue_injective := by
    intro _ _ i j h
    have hc : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (Nat.cast_injective hc)
  f := fun v _ a _ ↦ chainF v a
  f_parents := by
    intro v hv a b e hab
    fin_cases v
    · exact absurd (by decide) hv
    · have h0 : a 0 = b 0 := hab 0 (by simp [chainCID])
      simp [chainF, h0]
    · have h1 : a 1 = b 1 := hab 1 (by simp [chainCID])
      simp [chainF, h1]
    · simp [chainF]
  exoProb := fun _ _ ↦ 1
  exoProb_nonneg := by intro v e; norm_num
  exoProb_tsum := by intro v; rw [tsum_fintype]; simp

@[simp] public theorem chainSCIM_graph : chainSCIM.graph = chainCID := rfl

/-- The chain is evaluable: the vertex index is a rank. -/
public instance instIsWellFoundedChainSCIM : chainSCIM.graph.IsWellFounded :=
  ⟨wellFounded_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; simp only [chainSCIM_graph, chainCID] at hp
    fin_cases v <;> fin_cases p <;> simp_all)⟩

/-! ## The chain propagates

Each copy step, stated once for every intervention that leaves the copying
vertex alone. `submodel` only ever deletes edges, so the same two rewrites serve
the factual model and both counterfactual ones.
-/

variable {π : chainSCIM.Policy} {S : Finset (Fin 4)}
  {x : EndoAssignment (Fin 4) chainDim} {ε : ExoAssignment (Fin 4) chainExo}

/-- `U` copies `X`, in any submodel that does not force `U`. -/
public theorem chain_eval_utility (h : (2 : Fin 4) ∉ S) :
    ((chainSCIM.withPolicy π).submodel S x).eval ε 2 =
      ((chainSCIM.withPolicy π).submodel S x).eval ε 1 := by
  rw [SCM.submodel_eval_notMem _ S x ε h,
    SCIM.withPolicy_f_notMem chainSCIM π (v := 2) (by decide)]
  simp [chainSCIM, chainF]

/-- `X` copies `D`, in any submodel that does not force `X`. -/
public theorem chain_eval_mid (h : (1 : Fin 4) ∉ S) :
    ((chainSCIM.withPolicy π).submodel S x).eval ε 1 =
      ((chainSCIM.withPolicy π).submodel S x).eval ε 0 := by
  rw [SCM.submodel_eval_notMem _ S x ε h,
    SCIM.withPolicy_f_notMem chainSCIM π (v := 1) (by decide)]
  simp [chainSCIM, chainF]

/-! ## The two quantities Definition 17 compares

`W` is the only vertex whose value never enters, which is why it is here: the
total utility is `U` alone, and `U`'s value is a decision bit that the chain
carries unchanged.
-/

/-- `𝐔 = {U}`, so the total utility is one term. -/
public theorem chain_totalUtilityIn (N : SCM (Fin 4) chainDim chainExo)
    [N.IsWellFounded] :
    chainSCIM.totalUtilityIn N ε = ((N.eval ε 2).val : ℝ) := by
  have h : ∀ u ∈ chainSCIM.graph.utilities.attach,
      chainSCIM.utilityValue u.1 ((chainSCIM.graph.mem_utilities_iff u.1).mp u.2)
          (N.eval ε u.1) = ((N.eval ε u.1).val : ℝ) := fun _ _ ↦ rfl
  rw [SCIM.totalUtilityIn, Finset.sum_congr rfl h,
    Finset.sum_attach _ fun u ↦ ((N.eval ε u).val : ℝ),
    show chainSCIM.graph.utilities = {2} from chainCID_utilities,
    Finset.sum_singleton]

/-- The same two copy steps in the factual model, which is `Mπ` itself rather
than a submodel of it. -/
public theorem chain_eval_utility_factual :
    (chainSCIM.withPolicy π).eval ε 2 = (chainSCIM.withPolicy π).eval ε 1 := by
  rw [SCM.eval_eq_f, SCIM.withPolicy_f_notMem chainSCIM π (v := 2) (by decide)]
  simp [chainSCIM, chainF]

public theorem chain_eval_mid_factual :
    (chainSCIM.withPolicy π).eval ε 1 = (chainSCIM.withPolicy π).eval ε 0 := by
  rw [SCM.eval_eq_f, SCIM.withPolicy_f_notMem chainSCIM π (v := 1) (by decide)]
  simp [chainSCIM, chainF]

/-! ## Conditioning is trivial here, and that is the point

The decision observes nothing, so the single decision context has probability
one and `condExp` is evaluation at the unique exogenous draw. Definition 17's
inequality is then an inequality of two utilities rather than of two quotients,
and nothing in the witness turns on the division convention the module docstring
records.
-/

public instance : Unique (ExoAssignment (Fin 4) chainExo) :=
  inferInstanceAs (Unique ((_ : Fin 4) → Fin 1))

public theorem chain_exoJoint : (chainSCIM.withPolicy π).exoJoint ε = 1 := by
  simp [SCM.exoJoint, chainSCIM, SCIM.withPolicy]

/-- `Pa^D = ∅`, so every draw is in every decision context's fibre. -/
public theorem chain_contextFiber (c : EndoAssignment (Fin 4) chainDim) :
    chainSCIM.contextFiber π 0 c = Finset.univ := by
  ext ε
  simp [SCIM.contextFiber, chainCID_parents_decision]

public theorem chain_condExp (c : EndoAssignment (Fin 4) chainDim)
    (g : ExoAssignment (Fin 4) chainExo → ℝ) :
    chainSCIM.condExp π 0 c g = g default := by
  rw [SCIM.condExp, chain_contextFiber]
  simp [chain_exoJoint]

/-! ## Definition 17, inhabited -/

/-- **`U_{X_d}(ε) = d`.** Forcing `X` to the value it would take under
`do(D = d)` forces `U` to `d`, because the chain copies both ways. -/
public theorem chain_nestedUtility (d : Fin 2) :
    chainSCIM.nestedUtility π 0 d 1 ε = (d.val : ℝ) := by
  have hresp : chainSCIM.responseTo π 0 d ε 1 = d := by
    rw [SCIM.responseTo, chain_eval_mid (by decide),
      SCM.submodel_eval _ {0} _ ε (Finset.mem_singleton_self 0),
      SCIM.point_self]
  rw [SCIM.nestedUtility, chain_totalUtilityIn, chain_eval_utility (by decide),
    SCM.submodel_eval _ {1} _ ε (Finset.mem_singleton_self 1),
    SCIM.point_self, hresp]

/-- **`U(ε)` is the decision's own bit**, which is what makes the comparison
bite: whatever the policy plays, some counterfactual decision disagrees with it. -/
public theorem chain_factualUtility :
    chainSCIM.totalUtilityIn (chainSCIM.withPolicy π) ε =
      (((chainSCIM.withPolicy π).eval ε 0).val : ℝ) := by
  rw [chain_totalUtilityIn, chain_eval_utility_factual, chain_eval_mid_factual]

/-- **Definition 17 is a condition a model meets**, and here it is met against
*every* policy rather than only the optimal ones. Print quantifies over optimal
policies; nothing in this witness needs that restriction, so the analysis of
which policies are optimal never has to be done. -/
public theorem chainSCIM_forall_policy (c : EndoAssignment (Fin 4) chainDim)
    (π : chainSCIM.Policy) :
    ∃ d : chainDim 0,
      chainSCIM.condExp π 0 c (chainSCIM.nestedUtility π 0 d 1) ≠
        chainSCIM.condExp π 0 c (chainSCIM.totalUtilityIn (chainSCIM.withPolicy π)) := by
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, (chainSCIM.withPolicy π).eval default 0 = b := ⟨_, rfl⟩
  refine ⟨if b = 0 then 1 else 0, ?_⟩
  rw [chain_condExp, chain_condExp, chain_nestedUtility, chain_factualUtility, hb]
  intro h
  have hn : (if b = 0 then (1 : Fin 2) else 0).val = b.val := Nat.cast_injective h
  fin_cases b <;> simp at hn

/-- **An instrumental control incentive on `X`.** The decision reaches `X` and
`X` reaches the utility node, and Definition 17 holds. -/
public theorem chainSCIM_hasICI_on_X : chainSCIM.HasICI 0 1 :=
  ⟨fun _ ↦ 0, fun π _ ↦ chainSCIM_forall_policy _ π⟩

/-- The right-hand side of Theorem 18 at `X`, so this diagram is on the sound
side of the criterion rather than a counterexample to it. -/
public theorem chainSCIM_pathThrough_X : chainSCIM.PathThrough 0 1 :=
  ⟨Relation.ReflTransGen.single (by simp [chainCID]),
    ⟨2, by decide, Relation.ReflTransGen.single (by simp [chainCID])⟩⟩

/-! ## And a vertex with no incentive

`W` is attached to nothing, so no directed path reaches it from the decision and
Theorem 18's soundness applies. This is the negative half: `HasICI` is not a
predicate that holds of every vertex once it holds of one.
-/

public theorem chainCID_not_descendant_W :
    ¬ chainSCIM.graph.IsDescendant 0 3 := by
  intro h
  cases h with
  | tail _ hp => simp [chainCID] at hp

public theorem chainSCIM_not_pathThrough_W : ¬ chainSCIM.PathThrough 0 3 :=
  fun h ↦ chainCID_not_descendant_W h.1

/-- **Theorem 18's soundness, run.** No model over this diagram has an
instrumental control incentive on `W`, at any decision context and under any
policy. -/
public theorem chainSCIM_not_hasICI_on_W : ¬ chainSCIM.HasICI 0 3 :=
  chainSCIM.not_hasICI_of_not_pathThrough chainSCIM_not_pathThrough_W

/-! ## Theorem 18, run in both directions

The criterion is an equivalence, so it decides every vertex of this diagram, and
it does so from the graph alone — no model is exhibited on either side. The
witness `Causal.SCIM.iciWitness` supplies the model for the `X` case; the `W`
case rules out every model at once.
-/

public instance instIsWellFoundedChainCID : chainCID.IsWellFounded :=
  instIsWellFoundedChainSCIM

/-- `D` reaches `X` and `X` reaches the utility node, so the diagram admits an
instrumental control incentive on `X`. -/
public theorem chainCID_admitsICI_on_X : chainCID.AdmitsICI 0 1 :=
  (CID.admitsICI_iff chainCID chainCID_decisions).mpr
    ⟨Relation.ReflTransGen.single (by simp [chainCID]),
      2, by decide, Relation.ReflTransGen.single (by simp [chainCID])⟩

/-- Nothing reaches `W` from the decision, so no compatible model has an
incentive on it. -/
public theorem chainCID_not_admitsICI_on_W : ¬ chainCID.AdmitsICI 0 3 :=
  fun h ↦ chainCID_not_descendant_W
    ((CID.admitsICI_iff chainCID chainCID_decisions).mp h).1

/-! ## A diagram print's Theorem 18 does not reach

Theorem 18 is stated for a *single-decision* CID, and `chainCID` is one. The
same diagram with `W` promoted to a second decision is not, so print's statement
says nothing whatever about it — yet nothing has changed near the path, and the
criterion still decides both vertices.

`CID.admitsICI_iff_of_decisionFree` is what applies, and this is the witness that
its hypothesis is weaker than print's rather than a restatement of it: the
diagram has two decisions and the equivalence holds anyway. Note that no SCIM is
built here. The widened criterion constructs its own.
-/

/-- `chainCID` with `W` promoted to a second decision. Same edges, so the same
two segments — and `W` is off both of them and out of `Pa^D`. -/
public noncomputable def twoDecisionCID : CID (Fin 4) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {1} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦
    if v = 0 ∨ v = 3 then NodeKind.decision
    else if v = 2 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

public theorem twoDecisionCID_decisions : twoDecisionCID.decisions = {0, 3} := by
  decide

/-- Print's hypothesis fails here, which is the point. -/
public theorem twoDecisionCID_not_singleDecision :
    ¬ twoDecisionCID.IsSingleDecision := by
  rintro ⟨d, hd⟩
  rw [twoDecisionCID_decisions] at hd
  have h0 : (0 : Fin 4) ∈ ({d} : Finset (Fin 4)) := hd ▸ (by decide)
  have h3 : (3 : Fin 4) ∈ ({d} : Finset (Fin 4)) := hd ▸ (by decide)
  rw [Finset.mem_singleton] at h0 h3
  exact absurd (h0.trans h3.symm) (by decide)

public theorem twoDecisionCID_not_descendant_W {a : Fin 4}
    (h : twoDecisionCID.IsDescendant a 3) : a = 3 := by
  cases h with
  | refl => rfl
  | tail _ hp => simp [twoDecisionCID] at hp

/-- The second decision is clear of both segments and of `Pa^D`, which is all
the widened criterion asks. -/
public theorem twoDecisionCID_decisionFree (u : Fin 4) :
    twoDecisionCID.DecisionFree 0 1 u := by
  intro w hw hne
  have hw3 : w = 3 := by
    have : w ∈ twoDecisionCID.decisions := (twoDecisionCID.mem_decisions_iff w).mpr hw
    rw [twoDecisionCID_decisions] at this
    rcases Finset.mem_insert.mp this with h | h
    · exact absurd h hne
    · exact Finset.mem_singleton.mp h
  subst hw3
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, by simp [twoDecisionCID]⟩
  · exact absurd (twoDecisionCID_not_descendant_W h.1) (by decide)
  · exact absurd (twoDecisionCID_not_descendant_W h.1) (by decide)

/-- **The criterion decides a two-decision diagram.** `D` reaches `X`, `X`
reaches the utility node, and the incentive is admitted — on a diagram Theorem 18
as printed does not quantify over. -/
public theorem twoDecisionCID_admitsICI_on_X : twoDecisionCID.AdmitsICI 0 1 :=
  (CID.admitsICI_iff_of_decisionFree twoDecisionCID
      fun u _ _ ↦ twoDecisionCID_decisionFree u).mpr
    ⟨Relation.ReflTransGen.single (by simp [twoDecisionCID]),
      2, by decide, Relation.ReflTransGen.single (by simp [twoDecisionCID])⟩

/-- And refuses the vertex nothing reaches, on the same diagram. Soundness needs
no hypothesis at all, so this direction never depended on the widening. -/
public theorem twoDecisionCID_not_admitsICI_on_W :
    ¬ twoDecisionCID.AdmitsICI 0 3 :=
  CID.not_admitsICI_of_not_pathThrough
    fun h ↦ absurd (twoDecisionCID_not_descendant_W h.1) (by decide)

/-! ## Why `DecisionFree` cannot simply be dropped

`CID.DecisionFree` asks that no decision but `D` sit on either segment. That is a
real restriction and not slack left in the construction, and this section is the
witness for its first clause.

`D = 0 → D' = 1 → X = 2 → U = 3`, with **both** `0` and `1` decisions. The path
`D ⇢ X ⇢ 𝐔` is present in full, so Theorem 18's right-hand side holds. But `D'`
sits on the near segment, and its structural function belongs to the agent rather
than to the model: a policy that ignores its parent and plays `1` makes the
utility constant at its maximum, so that policy is **optimal**, and under it `X`
no longer moves when the decision is intervened on. The incentive is absent at an
optimal policy, which is exactly what Definition 17 forbids.

What this does and does not show. It shows the *mechanism* — the copy chain the
completeness construction relies on is breakable by a policy that is optimal, so
the hypothesis is doing work. It does **not** show that Theorem 18's criterion
fails on such a diagram: that would be `¬ AdmitsICI`, a claim about every
compatible SCIM, and this is one SCIM. That question is open here.
-/

/-- `D → D' → X → U`, with two decisions and `D'` on the near segment. -/
public noncomputable def segCID : CID (Fin 4) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {1} else if v = 3 then {2} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦
    if v = 0 ∨ v = 1 then NodeKind.decision
    else if v = 3 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

public theorem segCID_utilities : segCID.utilities = {3} := by decide

/-- Theorem 18's right-hand side holds on this diagram. -/
public theorem segCID_pathThrough :
    segCID.IsDescendant 0 2 ∧ ∃ u, segCID.IsUtility u ∧ segCID.IsDescendant 2 u := by
  refine ⟨Relation.ReflTransGen.tail (b := 1) ?_ ?_, 3, by decide, ?_⟩
  · exact Relation.ReflTransGen.single (by simp [segCID])
  · simp [segCID]
  · exact Relation.ReflTransGen.single (by simp [segCID])

/-- And its `DecisionFree` hypothesis does not: `D'` is a decision on the near
segment. -/
public theorem segCID_not_decisionFree : ¬ segCID.DecisionFree 0 2 3 := by
  intro h
  refine (h 1 (by decide) (by decide)).1 ⟨?_, ?_⟩
  · exact Relation.ReflTransGen.single (show (0:Fin 4) ∈ segCID.parents 1 by simp [segCID])
  · exact Relation.ReflTransGen.single (show (1:Fin 4) ∈ segCID.parents 2 by simp [segCID])

/-- `X` copies `D'`; `U` copies `X`. Both decisions await a policy. -/
@[expose] public def segF (v : Fin 4) (a : EndoAssignment (Fin 4) chainDim) :
    chainDim v :=
  if v = 2 then a 1 else if v = 3 then a 2 else 0

@[expose] public noncomputable def segSCIM : SCIM (Fin 4) chainDim chainExo where
  dom_nonempty := fun _ ↦ ⟨0⟩
  graph := segCID
  utilityValue := fun _ _ i ↦ (i : ℝ)
  utilityValue_injective := by
    intro _ _ i j h
    have hc : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (Nat.cast_injective hc)
  f := fun v _ a _ ↦ segF v a
  f_parents := by
    intro v hv a b e hab
    fin_cases v
    · exact absurd (by decide) hv
    · exact absurd (by decide) hv
    · have h1 : a 1 = b 1 := hab 1 (by simp [segCID])
      simp [segF, h1]
    · have h2 : a 2 = b 2 := hab 2 (by simp [segCID])
      simp [segF, h2]
  exoProb := fun _ _ ↦ 1
  exoProb_nonneg := by intro v e; norm_num
  exoProb_tsum := by intro v; rw [tsum_fintype]; simp

@[simp] public theorem segSCIM_graph : segSCIM.graph = segCID := rfl

public instance instIsWellFoundedSegSCIM : segSCIM.graph.IsWellFounded :=
  segCID.isWellFounded_of_fintype

/-- **The deviating policy**: play `1` everywhere, reading nothing. -/
@[expose] public noncomputable def segConstPolicy : segSCIM.Policy :=
  ⟨fun _ _ _ ↦ 1, fun _ _ _ _ _ ↦ rfl⟩


/-! ### The deviating policy is optimal, and kills the incentive -/

variable {S' : Finset (Fin 4)} {x' : EndoAssignment (Fin 4) chainDim}
  {ε' : ExoAssignment (Fin 4) chainExo} {ρ : segSCIM.Policy}

/-- `U` copies `X`, in any submodel that does not force `U`. -/
public theorem seg_eval_utility (h : (3 : Fin 4) ∉ S') :
    ((segSCIM.withPolicy ρ).submodel S' x').eval ε' 3 =
      ((segSCIM.withPolicy ρ).submodel S' x').eval ε' 2 := by
  rw [SCM.submodel_eval_notMem _ S' x' ε' h,
    SCIM.withPolicy_f_notMem segSCIM ρ (v := 3) (by decide)]
  simp [segSCIM, segF]

/-- `X` copies `D'`, in any submodel that does not force `X`. -/
public theorem seg_eval_mid (h : (2 : Fin 4) ∉ S') :
    ((segSCIM.withPolicy ρ).submodel S' x').eval ε' 2 =
      ((segSCIM.withPolicy ρ).submodel S' x').eval ε' 1 := by
  rw [SCM.submodel_eval_notMem _ S' x' ε' h,
    SCIM.withPolicy_f_notMem segSCIM ρ (v := 2) (by decide)]
  simp [segSCIM, segF]

/-- **The second decision ignores its parent**, so forcing `D` does not reach it.
This is the step the copy chain needs and does not get. -/
public theorem seg_eval_secondDecision (h : (1 : Fin 4) ∉ S') :
    ((segSCIM.withPolicy segConstPolicy).submodel S' x').eval ε' 1 = 1 := by
  rw [SCM.submodel_eval_notMem _ S' x' ε' h,
    SCIM.withPolicy_f_mem segSCIM segConstPolicy (d := 1) (by decide)]
  rfl

public theorem seg_totalUtilityIn (N : SCM (Fin 4) chainDim chainExo)
    [N.IsWellFounded] :
    segSCIM.totalUtilityIn N ε' = ((N.eval ε' 3).val : ℝ) := by
  have h : ∀ u ∈ segSCIM.graph.utilities.attach,
      segSCIM.utilityValue u.1 ((segSCIM.graph.mem_utilities_iff u.1).mp u.2)
          (N.eval ε' u.1) = ((N.eval ε' u.1).val : ℝ) := fun _ _ ↦ rfl
  rw [SCIM.totalUtilityIn, Finset.sum_congr rfl h,
    Finset.sum_attach _ fun u ↦ ((N.eval ε' u).val : ℝ),
    show segSCIM.graph.utilities = {3} from segCID_utilities, Finset.sum_singleton]

/-- The second decision plays `1` in the factual model. -/
public theorem seg_const_eval_one :
    (segSCIM.withPolicy segConstPolicy).eval ε' 1 = 1 := by
  rw [SCM.eval_eq_f, SCIM.withPolicy_f_mem segSCIM segConstPolicy (d := 1) (by decide)]
  rfl

public theorem seg_const_eval_two :
    (segSCIM.withPolicy segConstPolicy).eval ε' 2 = 1 := by
  rw [SCM.eval_eq_f,
    SCIM.withPolicy_f_notMem segSCIM segConstPolicy (v := 2) (by decide)]
  exact seg_const_eval_one

public theorem seg_const_eval_utility :
    (segSCIM.withPolicy segConstPolicy).eval ε' 3 = 1 := by
  rw [SCM.eval_eq_f,
    SCIM.withPolicy_f_notMem segSCIM segConstPolicy (v := 3) (by decide)]
  exact seg_const_eval_two

public theorem seg_expectedUtility (ρ : segSCIM.Policy) :
    segSCIM.expectedUtility ρ =
      (((segSCIM.withPolicy ρ).eval default 3).val : ℝ) := by
  rw [SCIM.expectedUtility_eq_sum, Fintype.sum_unique]
  have hj : (segSCIM.withPolicy ρ).exoJoint default = 1 := by
    simp [SCM.exoJoint, segSCIM, SCIM.withPolicy]
  rw [hj, one_mul, seg_totalUtilityIn]

/-- **The deviating policy is optimal**: it already attains the largest value the
utility can take, so nothing beats it. This is what makes the failure below a
failure of Definition 17 rather than of an arbitrarily chosen policy. -/
public theorem segConstPolicy_optimal : segSCIM.IsOptimalPolicy segConstPolicy := by
  intro ρ
  rw [seg_expectedUtility, seg_expectedUtility, seg_const_eval_utility]
  have h : ((segSCIM.withPolicy ρ).eval default 3).val ≤ 1 :=
    Nat.lt_succ_iff.mp ((segSCIM.withPolicy ρ).eval default 3).isLt
  exact_mod_cast h

/-- **`DecisionFree`'s segment clause is doing work.** The path `D ⇢ X ⇢ 𝐔` is
present in `segCID`, and this compatible SCIM still has **no** instrumental
control incentive on `X` — because an optimal policy cuts the chain at the second
decision, so `X` stops moving when the decision is intervened on.

Compare `chainSCIM_hasICI_on_X`: the same shape of diagram with the middle vertex
an ordinary structure node, where the incentive is present. The only difference
is who owns that vertex's structural function.

This does not show that `segCID` fails Theorem 18's criterion — that would be
`¬ AdmitsICI`, a claim about every compatible SCIM, and this is one of them. It
shows the mechanism the hypothesis exists to exclude. -/
public theorem segSCIM_not_hasICI : ¬ segSCIM.HasICI 0 2 := by
  rintro ⟨c, hc⟩
  obtain ⟨d, hd⟩ := hc segConstPolicy segConstPolicy_optimal
  refine hd (SCIM.condExp_congr _ segConstPolicy 0 c fun ε _ ↦ ?_)
  rw [SCIM.nestedUtility, seg_totalUtilityIn, seg_totalUtilityIn,
    seg_eval_utility (by decide),
    SCM.submodel_eval _ {2} _ ε (Finset.mem_singleton_self 2), SCIM.point_self,
    SCIM.responseTo, seg_eval_mid (by decide),
    seg_eval_secondDecision (by decide), seg_const_eval_utility]

/-- **Lemma 30's witness carries the diagram it is built on, unchanged**, at
`chainCID`. -/
public theorem chain_iciWitness_graph :
    (SCIM.iciWitness chainCID 0 1 2).graph = chainCID :=
  SCIM.iciWitness_graph chainCID 0 1 2

end AISafetyAtlas.Examples.Causal.Incentive
