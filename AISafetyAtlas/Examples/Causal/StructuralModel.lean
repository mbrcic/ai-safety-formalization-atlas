module

public import AISafetyAtlas.Causal.StructuralModel

/-!
# A worked structural causal model, a worked diagram, and a material observation

`AISafetyAtlas.Causal.StructuralModel` renders Definitions 1–5 of Everitt et al.
2021. This module runs them on objects small enough to check by hand, and gives
the clauses that are stated rather than derived their teeth: that evaluation
really is print's recursion, that *"utility nodes have no children"* is a
condition a graph can fail, and that materiality is a condition an observation
can meet — with the deleted information link shown to be what does the work.
-/

namespace AISafetyAtlas.Examples.Causal.StructuralModel

open AISafetyAtlas.Causal

/-! ## A two-variable structural causal model

`A` is a fair bit copied from its own exogenous variable; `B` copies `A`. So `B`
is determined by `A`'s noise alone, through one level of recursion. -/

public abbrev Two := Fin 2

public abbrev bits : Two → ℕ := fun _ ↦ 2

/-- `A = ε_A`, and `B = A`. -/
public noncomputable def copyChain : SCM Two bits bits where
  dom_pos := fun _ ↦ by norm_num
  parents := fun v ↦ if v = 1 then {0} else ∅
  acyclic := acyclic_of_rank (fun v ↦ if v = 1 then 1 else 0) (by
    intro v p hp; fin_cases v <;> simp_all)
  f := fun v a e ↦ if v = 1 then a 0 else e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v = 1
    · simp only [if_pos hv]
      exact h 0 (by simp [hv])
    · simp [hv]
  exoProb := fun _ _ ↦ 1 / 2
  exoProb_nonneg := fun _ _ ↦ by norm_num
  exoProb_sum := fun _ ↦ by rw [Fin.sum_univ_two]; norm_num

/-- `copyChain` is evaluable: the rank `B ↦ 1`, `A ↦ 0` discharges the
recursion's hypothesis, which is the cheapest route on a finite diagram.
`SCM.acyclic` is print's own word and is not enough on its own — see
`chainParents` — so an example that evaluates supplies this. -/
public instance instIsWellFoundedCopyChain : copyChain.IsWellFounded :=
  ⟨wellFounded_of_rank (fun v ↦ if v = 1 then 1 else 0) (by
    intro v p hp; simp only [copyChain] at hp; fin_cases v <;> simp_all)⟩

/-- The root reads its own noise. -/
public theorem copyChain_eval_zero (ε : ExoAssignment Two bits) :
    copyChain.eval ε 0 = ε 0 := by
  rw [copyChain.eval_eq_f ε 0]
  simp [copyChain]

/-- **The recursion is a real one.** `B`'s value is `A`'s value, which is `A`'s
noise — so reading `B` requires the iteration to have already settled `A`. A
single application of `F` to the seed would give the wrong answer whenever
`ε 0 ≠ 0`. -/
public theorem copyChain_eval_one (ε : ExoAssignment Two bits) :
    copyChain.eval ε 1 = ε 0 := by
  rw [copyChain.eval_eq_f ε 1]
  simp only [copyChain]
  exact copyChain_eval_zero ε

/-! ## Intervening

`do(A = 1)` forces the root, and `B` follows it. -/

public theorem copyChain_do_root (ε : ExoAssignment Two bits)
    (x : Assignment Two bits) :
    (copyChain.submodel {0} x).eval ε 0 = x 0 :=
  SCM.submodel_eval _ _ _ _ (by simp)

/-! ## The diagram, and the clause that is stated rather than derived -/

/-- One structure node, one decision, one utility. The decision observes the
structure node; the utility reads the decision. -/
public noncomputable def tinyCID : CID (Fin 3) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {1} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> simp_all)
  kind := fun v ↦
    if v = 1 then NodeKind.decision
    else if v = 2 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

public theorem tinyCID_decisions : tinyCID.decisions = {1} := by decide

public theorem tinyCID_utilities : tinyCID.utilities = {2} := by decide

/-- The decision's observations are print's `Pa_D`. -/
public theorem tinyCID_observations : tinyCID.observations 1 = {0} := by
  simp [CID.observations, tinyCID]

public theorem tinyCID_singleDecision : tinyCID.IsSingleDecision :=
  ⟨1, tinyCID_decisions⟩

/-- **Teeth for `utility_childless`.** The same graph with the utility node given
a child fails that clause and nothing else, so the field is a real condition and
not a consequence of acyclicity or of the partition. -/
public theorem utility_childless_has_teeth :
    ¬ (∀ u, (fun v : Fin 3 ↦
        if v = 1 then NodeKind.decision
        else if v = 2 then NodeKind.utility
        else NodeKind.structureNode) u = NodeKind.utility →
      ∀ v, u ∉ (fun v : Fin 3 ↦ if v = 1 then ({0} : Set (Fin 3))
        else if v = 2 then {1} else {2}) v) := by
  intro h; exact h 2 (by decide) 0 (by simp)

/-! ## A worked SCIM, and an observation that is material

Print's Figure 2a in miniature: posts `D` influence clicks `U`, and the user's
opinion `O` is what makes the choice of post worth conditioning on. Here `O` is
a fair coin, `D` observes it, and the click happens exactly when the post
matches the opinion.

The point of the example is Definition 5. Copying `O` earns `1`; with the
information link `O → D` removed a policy cannot see the coin and earns `1/2`
whatever it does. So `O` is **material**, and `IsMaterial` is a condition some
observation actually meets rather than a definition nothing satisfies.

`E^D` and `E^U` are one-element here, so the policies are the deterministic
ones. That is an instance of Definition 4, not a restriction of it — print's
`E^D` *"provides randomness to allow the policy to be a stochastic function"*,
and a model may decline to use it. -/

/-- Three binary variables: opinion, post, click. -/
public abbrev figDim : Fin 3 → ℕ := fun _ ↦ 2

/-- Only the opinion is random. -/
public abbrev figExo : Fin 3 → ℕ := fun v ↦ if v = 0 then 2 else 1

/-- `O → D`, and both into `U`. -/
public noncomputable def figCID : CID (Fin 3) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {0, 1} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦
    if v = 1 then NodeKind.decision
    else if v = 2 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

public theorem figCID_decisions : figCID.decisions = {1} := by decide

public theorem figCID_utilities : figCID.utilities = {2} := by decide

public theorem figCID_parents_decision : figCID.parents 1 = {0} := by
  simp [figCID]

/-- The opinion node copies its own noise; the click fires when post and opinion
agree. The post has no structural function until a policy supplies one, which is
Definition 4's whole asymmetry. -/
@[expose] public def figF (v : Fin 3) (a : Assignment (Fin 3) figDim)
    (e : Fin (figExo v)) : Fin (figDim v) :=
  if v = 0 then ⟨e.val % 2, Nat.mod_lt _ (by norm_num)⟩
  else if a 0 = a 1 then 1 else 0

/-- The SCIM of Figure 2a. -/
@[expose] public noncomputable def figSCIM : SCIM (Fin 3) figDim figExo where
  dom_pos := by decide
  graph := figCID
  utilityValue := fun _ _ i ↦ (i : ℝ)
  utilityValue_injective := by
    intro _ _ i j h
    have hc : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (Nat.cast_injective hc)
  f := fun v _ ↦ figF v
  f_parents := by
    intro v hv a b e hab
    fin_cases v
    · simp [figF]
    · exact absurd (by decide) hv
    · have ha0 : a 0 = b 0 := hab 0 (by simp [figCID])
      have ha1 : a 1 = b 1 := hab 1 (by simp [figCID])
      simp [figF, ha0, ha1]
  exoProb := fun v _ ↦ if v = 0 then 1 / 2 else 1
  exoProb_nonneg := by
    intro v e
    by_cases h : v = 0 <;> simp [h]
  exoProb_sum := by
    intro v
    by_cases h : v = 0 <;> simp [h]

/-- Figure 2a's diagram is evaluable: the vertex index is a rank. Definition 5's
`V*(M)` runs `W(ε)` in `Mπ`, so every statement below about `optimalValue` and
materiality reads through this instance. -/
public instance instIsWellFoundedFigSCIM : figSCIM.graph.IsWellFounded :=
  ⟨wellFounded_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; simp only [figSCIM, figCID] at hp
    fin_cases v <;> fin_cases p <;> simp_all)⟩

@[simp] public theorem figSCIM_graph : figSCIM.graph = figCID := rfl

@[simp] public theorem figSCIM_utilityValue (u : Fin 3)
    (hu : figSCIM.graph.IsUtility u) (i : Fin (figDim u)) :
    figSCIM.utilityValue u hu i = (i : ℝ) := rfl

public theorem figSCIM_utilities : figSCIM.graph.utilities = {2} := by
  rw [figSCIM_graph]; exact figCID_utilities

/-- **Print's *"not in *Desc_D*"*, inhabited.** The opinion is a parent of the
decision, so nothing reaches it from the decision and the invariance sentence
applies to it. -/
public theorem figCID_notDownstream_zero : figCID.NotDownstream 0 := by
  intro d hd hdesc
  have hd1 : d = 1 := by
    have hmem : d ∈ figCID.decisions := (figCID.mem_decisions_iff d).mpr hd
    rw [figCID_decisions, Finset.mem_singleton] at hmem
    exact hmem
  subst hd1
  rcases Relation.ReflTransGen.cases_tail hdesc with h | ⟨b, -, hb⟩
  · exact absurd h (by decide)
  · simp [figCID] at hb

/-- **Print's `Pr(x)` on the worked diagram.** *"For a set of variables `X` not
in *Desc_D*, `Pr^π(x)` is independent of `π` and we simply write `Pr(x)`."* Here
`X` is the opinion, and the marginal really is the same under every policy. -/
public theorem figSCIM_marginal_opinion_policy_free (π π' : figSCIM.Policy)
    (x : Assignment (Fin 3) figDim) :
    (figSCIM.withPolicy π).marginal {0} x
      = (figSCIM.withPolicy π').marginal {0} x :=
  figSCIM.marginal_withPolicy_eq_of_notDownstream π π' {0}
    (by
      intro c hc
      simp only [Finset.mem_singleton] at hc
      subst hc
      exact figCID_notDownstream_zero) x

/-! ### Evaluating a policy -/

public theorem figSCIM_notMem_decisions_zero : ¬ figCID.IsDecision (0 : Fin 3) := by
  decide

public theorem figSCIM_notMem_decisions_two : ¬ figCID.IsDecision (2 : Fin 3) := by
  decide

public theorem figSCIM_mem_decisions_one : figCID.IsDecision (1 : Fin 3) := by
  decide

/-- The opinion is its own noise. -/
public theorem figSCIM_eval_zero (π : figSCIM.Policy)
    (ε : ExoAssignment (Fin 3) figExo) :
    (figSCIM.withPolicy π).eval ε 0 = ε 0 := by
  rw [SCM.eval_eq_f,
    figSCIM.withPolicy_f_notMem π (v := 0) figSCIM_notMem_decisions_zero]
  simp only [figSCIM, figF]
  exact Fin.ext (Nat.mod_eq_of_lt (ε 0).isLt)

/-- The post is whatever the policy says. -/
public theorem figSCIM_eval_one (π : figSCIM.Policy)
    (ε : ExoAssignment (Fin 3) figExo) :
    (figSCIM.withPolicy π).eval ε 1
      = π.1 ⟨1, figSCIM_mem_decisions_one⟩ ((figSCIM.withPolicy π).eval ε) (ε 1) := by
  rw [SCM.eval_eq_f, figSCIM.withPolicy_f_mem π (d := 1) figSCIM_mem_decisions_one]

/-- The click fires exactly when post and opinion agree. -/
public theorem figSCIM_eval_two (π : figSCIM.Policy)
    (ε : ExoAssignment (Fin 3) figExo) :
    (figSCIM.withPolicy π).eval ε 2
      = if (figSCIM.withPolicy π).eval ε 0 = (figSCIM.withPolicy π).eval ε 1
        then 1 else 0 := by
  rw [SCM.eval_eq_f,
    figSCIM.withPolicy_f_notMem π (v := 2) figSCIM_notMem_decisions_two]
  simp [figSCIM, figF]

/-- `Eπ[U]` on this SCIM is the click probability. -/
public theorem figSCIM_expectedUtility (π : figSCIM.Policy) :
    figSCIM.expectedUtility π
      = ∑ ε : ExoAssignment (Fin 3) figExo,
          (figSCIM.withPolicy π).exoJoint ε *
            (((figSCIM.withPolicy π).eval ε 2).val : ℝ) := by
  have hattach : ∀ F : Fin 3 → ℝ,
      ∑ x ∈ figSCIM.graph.utilities.attach, F x.1 = F 2 := by
    intro F
    rw [Finset.sum_attach figSCIM.graph.utilities F, figSCIM_utilities,
      Finset.sum_singleton]
  unfold SCIM.expectedUtility
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  congr 1
  simpa using hattach fun v ↦ (((figSCIM.withPolicy π).eval ε v).val : ℝ)

/-! ### The optimum, and what it is worth -/

/-- Copying the opinion. -/
public noncomputable def figCopy : figSCIM.Policy :=
  ⟨fun _ a _ ↦ a 0, by
    intro d a b _ hab
    have hd : (d : Fin 3) = 1 :=
      Finset.mem_singleton.mp (by
        rw [← figCID_decisions]
        exact (figSCIM.graph.mem_decisions_iff d.1).mpr d.2)
    exact hab 0 (by simp [figSCIM_graph, hd, figCID_parents_decision])⟩

public theorem figSCIM_expectedUtility_copy : figSCIM.expectedUtility figCopy = 1 := by
  rw [figSCIM_expectedUtility]
  have hval : ∀ ε : ExoAssignment (Fin 3) figExo,
      (((figSCIM.withPolicy figCopy).eval ε 2).val : ℝ) = 1 := by
    intro ε
    rw [figSCIM_eval_two, if_pos]
    · norm_num
    · rw [figSCIM_eval_one, figSCIM_eval_zero]
      simp [figCopy, figSCIM_eval_zero]
  simp only [hval, mul_one]
  exact (figSCIM.withPolicy figCopy).exoJoint_sum

public theorem figSCIM_expectedUtility_le_one (π : figSCIM.Policy) :
    figSCIM.expectedUtility π ≤ 1 := by
  rw [figSCIM_expectedUtility]
  calc ∑ ε : ExoAssignment (Fin 3) figExo,
        (figSCIM.withPolicy π).exoJoint ε *
          (((figSCIM.withPolicy π).eval ε 2).val : ℝ)
      ≤ ∑ ε : ExoAssignment (Fin 3) figExo, (figSCIM.withPolicy π).exoJoint ε *
          1 := by
        refine Finset.sum_le_sum fun ε _ ↦ ?_
        refine mul_le_mul_of_nonneg_left ?_ ((figSCIM.withPolicy π).exoJoint_nonneg ε)
        have := ((figSCIM.withPolicy π).eval ε 2).isLt
        have : (((figSCIM.withPolicy π).eval ε 2).val : ℝ) ≤ 1 := by
          exact_mod_cast Nat.lt_succ_iff.mp this
        exact this
    _ = 1 := by
        simp only [mul_one]
        exact (figSCIM.withPolicy π).exoJoint_sum

/-- **`V*(M) = 1`.** The opinion can be copied, and nothing beats a certain
click. -/
public theorem figSCIM_optimalValue : figSCIM.optimalValue = 1 := by
  refine le_antisymm ?_
    (figSCIM_expectedUtility_copy ▸ figSCIM.expectedUtility_le_optimalValue figCopy)
  obtain ⟨π, -, hπ⟩ := figSCIM.exists_isOptimalPolicy
  rw [← hπ]
  exact figSCIM_expectedUtility_le_one π

/-! ### Removing the information link

`M_{O↛D}`. The graph loses the edge `O → D` and nothing else changes, so a
policy's congruence clause is now over the empty parent set: it must ignore the
opinion. Every such policy earns exactly `1/2`. -/

@[expose] public noncomputable def figCut : SCIM (Fin 3) figDim figExo :=
  figSCIM.removeInfoLink figSCIM_mem_decisions_one 0

/-- `figCut` is `figSCIM` with one edge deleted, so it inherits evaluability —
but `figCut` is a definition rather than the `removeInfoLink` application, so
instance search needs this step to see through the name. -/
public instance instIsWellFoundedFigCut : figCut.graph.IsWellFounded :=
  SCIM.instIsWellFoundedRemoveInfoLink figSCIM figSCIM_mem_decisions_one 0

public theorem figCut_parents_one : figCut.graph.parents 1 = ∅ := by
  simp [figCut, SCIM.removeInfoLink, figCID_parents_decision]

public theorem figCut_mem_decisions_one : figCut.graph.IsDecision (1 : Fin 3) :=
  figSCIM_mem_decisions_one

/-- A policy in `M_{O↛D}` cannot read the opinion: its parent set is empty. -/
public theorem figCut_policy_const (π : figCut.Policy)
    (d : {d : Fin 3 // figCut.graph.IsDecision d})
    (a b : Assignment (Fin 3) figDim) (e : Fin (figExo d.1)) :
    π.1 d a e = π.1 d b e := by
  refine π.2 d a b e fun p hp ↦ ?_
  have hd : (d : Fin 3) = 1 :=
    Finset.mem_singleton.mp (by
      rw [← figCID_decisions]
      exact (figCut.graph.mem_decisions_iff d.1).mpr d.2)
  rw [hd, figCut_parents_one] at hp
  exact absurd hp (Set.notMem_empty p)

public theorem figCut_eval_zero (π : figCut.Policy)
    (ε : ExoAssignment (Fin 3) figExo) :
    (figCut.withPolicy π).eval ε 0 = ε 0 := by
  rw [SCM.eval_eq_f,
    figCut.withPolicy_f_notMem π (v := 0) figSCIM_notMem_decisions_zero]
  simp only [figCut, SCIM.removeInfoLink, figSCIM, figF]
  exact Fin.ext (Nat.mod_eq_of_lt (ε 0).isLt)

public theorem figCut_eval_two (π : figCut.Policy)
    (ε : ExoAssignment (Fin 3) figExo) :
    (figCut.withPolicy π).eval ε 2
      = if (figCut.withPolicy π).eval ε 0 = (figCut.withPolicy π).eval ε 1
        then 1 else 0 := by
  rw [SCM.eval_eq_f,
    figCut.withPolicy_f_notMem π (v := 2) figSCIM_notMem_decisions_two]
  simp [figCut, SCIM.removeInfoLink, figSCIM, figF]

/-- The post the policy settles on, independent of `ε` and of the opinion. -/
@[expose] public noncomputable def figCutChoice (π : figCut.Policy) : Fin 2 :=
  π.1 ⟨1, figCut_mem_decisions_one⟩ (fun _ ↦ 0) 0

public theorem figCut_eval_one (π : figCut.Policy)
    (ε : ExoAssignment (Fin 3) figExo) :
    (figCut.withPolicy π).eval ε 1 = figCutChoice π := by
  rw [SCM.eval_eq_f, figCut.withPolicy_f_mem π (d := 1) figCut_mem_decisions_one]
  have h1 : ε 1 = 0 := Fin.ext (Nat.lt_one_iff.mp (ε 1).isLt)
  rw [figCutChoice, figCut_policy_const π ⟨1, figCut_mem_decisions_one⟩ _ (fun _ ↦ 0),
    h1]

public theorem figCut_utilities : figCut.graph.utilities = {2} := figSCIM_utilities

@[simp] public theorem figCut_utilityValue (u : Fin 3)
    (hu : figCut.graph.IsUtility u) (i : Fin (figDim u)) :
    figCut.utilityValue u hu i = (i : ℝ) := rfl

public theorem figCut_expectedUtility (π : figCut.Policy) :
    figCut.expectedUtility π
      = ∑ ε : ExoAssignment (Fin 3) figExo,
          (figCut.withPolicy π).exoJoint ε *
            (((figCut.withPolicy π).eval ε 2).val : ℝ) := by
  have hattach : ∀ F : Fin 3 → ℝ,
      ∑ x ∈ figCut.graph.utilities.attach, F x.1 = F 2 := by
    intro F
    rw [Finset.sum_attach figCut.graph.utilities F, figCut_utilities,
      Finset.sum_singleton]
  unfold SCIM.expectedUtility
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  congr 1
  simpa using hattach fun v ↦ (((figCut.withPolicy π).eval ε v).val : ℝ)

/-- **Every blind policy earns `1/2`.** The click happens exactly when the coin
lands on the post the policy already committed to. -/
public theorem figCut_expectedUtility_eq (π : figCut.Policy) :
    figCut.expectedUtility π = 1 / 2 := by
  classical
  rw [figCut_expectedUtility]
  obtain ⟨c, hc⟩ : ∃ c : Fin 2, figCutChoice π = c := ⟨_, rfl⟩
  have hval : ∀ ε : ExoAssignment (Fin 3) figExo,
      (((figCut.withPolicy π).eval ε 2).val : ℝ)
        = if (ε 0).val = c.val then (1 : ℝ) else 0 := by
    intro ε
    have h0 : ((figCut.withPolicy π).eval ε 0).val = (ε 0).val :=
      congrArg Fin.val (figCut_eval_zero π ε)
    have h1 : ((figCut.withPolicy π).eval ε 1).val = c.val := by
      rw [figCut_eval_one, hc]
    rw [figCut_eval_two]
    by_cases h : (figCut.withPolicy π).eval ε 0 = (figCut.withPolicy π).eval ε 1
    · rw [if_pos h, if_pos (by rw [← h0, ← h1, h])]
      norm_num
    · rw [if_neg h, if_neg (fun hv ↦ h (Fin.ext (by rw [h0, h1]; exact hv)))]
      norm_num
  have hprod : ∀ ε : ExoAssignment (Fin 3) figExo,
      (if (ε 0).val = c.val then (1 : ℝ) else 0)
        = ∏ v : Fin 3,
            (if v = 0 then (if (ε v).val = c.val then (1 : ℝ) else 0) else 1) := by
    intro ε
    rw [Fin.prod_univ_three, if_pos rfl, if_neg (by decide : ¬((1 : Fin 3) = 0)),
      if_neg (by decide : ¬((2 : Fin 3) = 0)), mul_one, mul_one]
  simp only [hval, hprod]
  rw [(figCut.withPolicy π).exoJoint_mul_prod
    (fun v e ↦ if v = 0 then (if e.val = c.val then (1 : ℝ) else 0) else 1)]
  have hexo : ∀ (v : Fin 3) (e : Fin (figExo v)),
      (figCut.withPolicy π).exoProb v e = if v = 0 then 1 / 2 else 1 := fun _ _ ↦ rfl
  simp only [hexo, Fin.prod_univ_three,
    if_neg (by decide : ¬((1 : Fin 3) = 0)),
    if_neg (by decide : ¬((2 : Fin 3) = 0)), if_true, one_mul]
  have hsum : (∑ x : Fin (figExo 0),
      (1 : ℝ) / 2 * if (x : ℕ) = (c : ℕ) then 1 else 0) = 1 / 2 := by
    show (∑ x : Fin 2, (1 : ℝ) / 2 * if (x : ℕ) = (c : ℕ) then 1 else 0) = 1 / 2
    rw [Fin.sum_univ_two]
    fin_cases c <;> norm_num
  have h1 : (∑ _x : Fin (figExo 1), (1 : ℝ)) = 1 := by
    show (∑ _x : Fin 1, (1 : ℝ)) = 1
    simp
  have h2 : (∑ _x : Fin (figExo 2), (1 : ℝ)) = 1 := by
    show (∑ _x : Fin 1, (1 : ℝ)) = 1
    simp
  rw [hsum, h1, h2, mul_one, mul_one]

/-- **`V*(M_{O↛D}) = 1/2`.** -/
public theorem figCut_optimalValue : figCut.optimalValue = 1 / 2 := by
  obtain ⟨π, -, hπ⟩ := figCut.exists_isOptimalPolicy
  rw [← hπ, figCut_expectedUtility_eq]

/-- **The information link is what `figCut_policy_const` removes.** In `M` a
policy *may* read the opinion, and `figCopy` does; only in `M_{O↛D}` is every
policy forced to commit blind. Without this the `1/2` would be a number computed
on a second structure whose difference from the first was never exercised. -/
public theorem figSCIM_policy_not_const :
    ¬ ∀ (π : figSCIM.Policy) (a b : Assignment (Fin 3) figDim)
        (e : Fin (figExo 1)),
        π.1 ⟨1, figSCIM_mem_decisions_one⟩ a e
          = π.1 ⟨1, figSCIM_mem_decisions_one⟩ b e := by
  intro h
  have hne : ((0 : Fin (figDim 0))) = 1 :=
    h figCopy (fun _ ↦ 0) (fun _ ↦ 1) 0
  exact absurd hne (by decide)

/-- **Definition 5, met.** The opinion is a material observation: deleting the
information link `O → D` costs the agent half its utility. -/
public theorem figSCIM_opinion_isMaterial :
    figSCIM.IsMaterial figSCIM_mem_decisions_one
      (show (0 : Fin 3) ∈ figSCIM.graph.parents 1 by
        simp [figSCIM_graph, figCID_parents_decision]) := by
  show figCut.optimalValue < figSCIM.optimalValue
  rw [figCut_optimalValue, figSCIM_optimalValue]
  norm_num

end AISafetyAtlas.Examples.Causal.StructuralModel
