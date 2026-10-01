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

public abbrev bits : Two → Type := fun _ ↦ Fin 2

/-- `A = ε_A`, and `B = A`. -/
public noncomputable def copyChain : SCM Two bits bits where
  dom_nonempty := fun _ ↦ ⟨0⟩
  parents := fun v ↦ if v = 1 then {0} else ∅
  acyclic := Causal.acyclic_of_rank (fun v ↦ if v = 1 then 1 else 0) (by
    intro v p hp; fin_cases v <;> simp_all)
  f := fun v a e ↦ if v = 1 then a 0 else e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v = 1
    · simp only [if_pos hv]
      exact h 0 (by simp [hv])
    · simp [hv]
  exoProb := fun _ _ ↦ 1 / 2
  exoProb_nonneg := fun _ _ ↦ by norm_num
  exoProb_tsum := fun _ ↦ by rw [tsum_fintype, Fin.sum_univ_two]; norm_num

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

/-- **The joint law is a probability.** The structural model's induced
distribution over endogenous assignments sums to one, which is the fact every
expectation in this cluster silently rests on. -/
public theorem copyChain_jointProb_sum :
    ∑ w : EndoAssignment Two bits, copyChain.jointProb w = 1 :=
  SCM.jointProb_sum copyChain

/-- **Evaluation depends on the exogenous draw only through the vertex and its
parents.** Two draws agreeing at `B` and agreeing on `B`'s evaluated parents
give the same value at `B`. This is the locality that makes the recursion a
recursion, and nothing had run it. -/
public theorem copyChain_eval_congr (ε ε' : ExoAssignment Two bits)
    (hε : ε 1 = ε' 1) (hp : ∀ p ∈ copyChain.parents 1, copyChain.eval ε p = copyChain.eval ε' p) :
    copyChain.eval ε 1 = copyChain.eval ε' 1 :=
  SCM.eval_congr copyChain ε ε' 1 hε hp

/-! ## No rank function on the integer chain

`chainParents` is the diagram print's own acyclicity admits and evaluation does
not. The rank characterisation says why in one step: a well-founded parent
relation with finite parent sets is exactly one carrying a rank into `ℕ`, and
the chain has no bottom to start counting from. -/

/-- Each vertex of the chain has one parent, so the characterisation applies. -/
public theorem chainParents_finite (v : ℤ) : (chainParents v).Finite :=
  Set.finite_singleton _

/-- **So no rank exists.** Not merely that none is obvious: the equivalence
turns `chainParents_not_wellFounded` into the non-existence directly. -/
public theorem chainParents_no_rank :
    ¬ ∃ rank : ℤ → ℕ, ∀ v, ∀ p ∈ chainParents v, rank p < rank v :=
  fun h => chainParents_not_wellFounded
    ((wellFounded_iff_exists_rank chainParents_finite).mpr h)

/-- **And the determinacy really fails there**, which is why `eval` takes a
well-foundedness hypothesis rather than print's word `acyclic`: the copying
equation on that chain has two constant solutions. -/
public theorem chainParents_two_solutions :
    ∃ W W' : ℤ → Fin 2, W ≠ W' ∧
      (∀ v, W v = W (v - 1)) ∧ (∀ v, W' v = W' (v - 1)) :=
  chainParents_fixedPoint_not_unique

/-! ## Intervening

`do(A = 1)` forces the root, and `B` follows it. -/

public theorem copyChain_do_root (ε : ExoAssignment Two bits)
    (x : EndoAssignment Two bits) :
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

/-- **A vertex is not both a decision and a utility.** Print states the two roles
as separate sets and never says they are disjoint; the atlas derives it from the
labelling, and this runs it at the diagram above where the two sets are `{1}`
and `{2}`. -/
public theorem tinyCID_roles_disjoint : Disjoint tinyCID.decisions tinyCID.utilities :=
  CID.decisions_disjoint_utilities tinyCID

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
public abbrev figDim : Fin 3 → Type := fun _ ↦ Fin 2

/-- Only the opinion is random. -/
public abbrev figExo : Fin 3 → Type := fun v ↦ Fin (if v = 0 then 2 else 1)

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
@[expose] public def figF (v : Fin 3) (a : EndoAssignment (Fin 3) figDim)
    (e : figExo v) : figDim v :=
  if v = 0 then ⟨e.val % 2, Nat.mod_lt _ (by norm_num)⟩
  else if a 0 = a 1 then 1 else 0

/-- The SCIM of Figure 2a. -/
@[expose] public noncomputable def figSCIM : SCIM (Fin 3) figDim figExo where
  dom_nonempty := by intro v; fin_cases v <;> exact ⟨0⟩
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
  exoProb_tsum := by
    intro v
    rw [tsum_fintype]
    by_cases h : v = 0 <;> simp [h, Finset.sum_const]

/-- Figure 2a's diagram is evaluable: the vertex index is a rank. Definition 5's
`V*(M)` runs `W(ε)` in `Mπ`, so every statement below about `optimalValue` and
materiality reads through this instance. -/
public instance instIsWellFoundedFigSCIM : figSCIM.graph.IsWellFounded :=
  ⟨wellFounded_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; simp only [figSCIM, figCID] at hp
    fin_cases v <;> fin_cases p <;> simp_all)⟩

@[simp] public theorem figSCIM_graph : figSCIM.graph = figCID := rfl

@[simp] public theorem figSCIM_utilityValue (u : Fin 3)
    (hu : figSCIM.graph.IsUtility u) (i : figDim u) :
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
    (x : EndoAssignment (Fin 3) figDim) :
    (figSCIM.withPolicy π).marginal {0} x
      = (figSCIM.withPolicy π').marginal {0} x :=
  figSCIM.marginal_withPolicy_eq_of_notDownstream π π' {0}
    (by
      intro c hc
      simp only [Finset.mem_singleton] at hc
      subst hc
      exact figCID_notDownstream_zero) x

/-- **The same printed sentence at the probability law, and inhabited.** This is
the general statement, with no finite vertex set and an arbitrary set of
observables; `SCM.measurable_exo` discharges both side conditions here because
the diagram has finitely many vertices, so on print's own figure the general
form costs nothing the finite one did not. -/
public theorem figSCIM_observableLaw_opinion_policy_free (π π' : figSCIM.Policy) :
    (figSCIM.withPolicy π).observableLaw {0} (SCM.measurable_exo _)
      = (figSCIM.withPolicy π').observableLaw {0} (SCM.measurable_exo _) :=
  figSCIM.observableLaw_withPolicy_eq_of_notDownstream π π' {0}
    (by
      intro c hc
      simp only [Set.mem_singleton_iff] at hc
      subst hc
      exact figCID_notDownstream_zero) _ _

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
  -- `simp` normalises both sides to the same term but no longer closes on it.
  simp [figSCIM, figF]
  rfl

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
      -- `simp` unfolds `figCopy` past its anonymous constructor, which destroys
      -- the rewrite pattern; `simp only` stops where the lemma still applies.
      simp only [figCopy]
      rw [figSCIM_eval_zero]
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
    (a b : EndoAssignment (Fin 3) figDim) (e : figExo d.1) :
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
  rfl

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
    (hu : figCut.graph.IsUtility u) (i : figDim u) :
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
    rw [Fin.prod_univ_three]
    simp only [show ¬((1 : Fin 3) = 0) by decide,
      show ¬((2 : Fin 3) = 0) by decide, if_false, mul_one]
    simp
  simp only [hval, hprod]
  rw [(figCut.withPolicy π).exoJoint_mul_prod
    (fun v e ↦ if v = 0 then (if e.val = c.val then (1 : ℝ) else 0) else 1)]
  have hexo : ∀ (v : Fin 3) (e : figExo v),
      (figCut.withPolicy π).exoProb v e = if v = 0 then 1 / 2 else 1 := fun _ _ ↦ rfl
  simp only [hexo, Fin.prod_univ_three,
    if_neg (by decide : ¬((1 : Fin 3) = 0)),
    if_neg (by decide : ¬((2 : Fin 3) = 0)), if_true, one_mul]
  have hsum : (∑ x : figExo 0,
      (1 : ℝ) / 2 * if (x : ℕ) = (c : ℕ) then 1 else 0) = 1 / 2 := by
    show (∑ x : Fin 2, (1 : ℝ) / 2 * if (x : ℕ) = (c : ℕ) then 1 else 0) = 1 / 2
    rw [Fin.sum_univ_two]
    fin_cases c <;> norm_num
  have h1 : (∑ _x : figExo 1, (1 : ℝ)) = 1 := by
    show (∑ _x : Fin 1, (1 : ℝ)) = 1
    simp
  have h2 : (∑ _x : figExo 2, (1 : ℝ)) = 1 := by
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
    ¬ ∀ (π : figSCIM.Policy) (a b : EndoAssignment (Fin 3) figDim)
        (e : figExo 1),
        π.1 ⟨1, figSCIM_mem_decisions_one⟩ a e
          = π.1 ⟨1, figSCIM_mem_decisions_one⟩ b e := by
  intro h
  have hne : ((0 : figDim 0)) = 1 :=
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

/-- Countably many independent bits: the new product-law layer is inhabited
outside the finite vertex class of the old joint-probability operations. -/
@[expose] public noncomputable def independentBits : SCM ℕ (fun _ ↦ Fin 2) (fun _ ↦ Fin 2) where
  dom_nonempty := fun _ ↦ ⟨0⟩
  parents := fun _ ↦ ∅
  acyclic := by
    intro v hv
    cases hv with
    | single h => exact h
    | tail _ h => exact h
  f := fun _ _ e ↦ e
  f_parents := by intros; rfl
  exoProb := fun _ _ ↦ 1 / 2
  exoProb_nonneg := by intros; norm_num
  exoProb_tsum := by intro v; rw [tsum_fintype]; norm_num [Fin.sum_univ_two]

/-- A cylinder event in the infinite product has the original bit probability. -/
public theorem independentBits_first_zero :
    (independentBits.exoLaw : MeasureTheory.Measure (ExoAssignment ℕ (fun _ ↦ Fin 2)))
      {ε | ε 0 = 0} = 1 / 2 := by
  have hm := independentBits.exoLaw_map_eval 0
  have he := congrArg (fun μ : MeasureTheory.Measure (Fin 2) ↦ μ {0}) hm
  rw [MeasureTheory.Measure.map_apply (measurable_pi_apply 0)
    (measurableSet_singleton 0)] at he
  change (independentBits.exoLaw : MeasureTheory.Measure (ExoAssignment ℕ (fun _ ↦ Fin 2)))
    ((fun ε ↦ ε 0) ⁻¹' ({0} : Set (Fin 2))) = 1 / 2
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at he
  rw [he]
  show ENNReal.ofReal (independentBits.exoProb 0 0) = 1 / 2
  norm_num [independentBits, ENNReal.ofReal_div_of_pos]

/-- The bits have no parents, so the recursion bottoms out at once. -/
public instance instIsWellFoundedIndependentBits : independentBits.IsWellFounded :=
  ⟨⟨fun v ↦ ⟨v, fun p hp ↦ absurd hp (by simp [independentBits])⟩⟩⟩

/-- Each bit is its own noise. -/
public theorem independentBits_eval (ε : ExoAssignment ℕ (fun _ ↦ Fin 2)) (v : ℕ) :
    independentBits.eval ε v = ε v :=
  independentBits.eval_eq_f ε v

/-- Evaluation is measurable here, which is what `SCM.endoLaw` asks for and what
a vertex reading infinitely many parents would not give. Each bit reads one
coordinate. -/
public theorem independentBits_measurable_eval :
    Measurable fun ε : ExoAssignment ℕ (fun _ ↦ Fin 2) ↦ independentBits.eval ε := by
  refine measurable_pi_lambda _ fun v ↦ ?_
  simp only [independentBits_eval]
  exact measurable_pi_apply v

/-- **Print's induced joint distribution, outside the finite vertex class.**

`SCM.jointProb` is a sum over the fibres of `eval` and cannot be written at
`V = ℕ` at all; `SCM.endoLaw` is print's *"this induces a joint distribution"*
and can. Here evaluation is the identity, so the induced joint is the exogenous
law and the first bit is still fair. -/
public theorem independentBits_endoLaw_first_zero :
    (independentBits.endoLaw independentBits_measurable_eval :
      MeasureTheory.Measure (Assignment ℕ (fun _ ↦ 2))) {w | w 0 = 0} = 1 / 2 := by
  rw [SCM.endoLaw]
  show ((independentBits.exoLaw : MeasureTheory.Measure (ExoAssignment ℕ (fun _ ↦ Fin 2))).map
    (fun ε ↦ independentBits.eval ε)) {w | w 0 = 0} = 1 / 2
  rw [MeasureTheory.Measure.map_apply independentBits_measurable_eval
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)]
  have hpre : (fun ε : ExoAssignment ℕ (fun _ ↦ Fin 2) ↦ independentBits.eval ε) ⁻¹'
      {w : Assignment ℕ (fun _ ↦ 2) | w 0 = 0} = {ε | ε 0 = 0} := by
    ext ε
    simp [independentBits_eval]
  rw [hpre]
  exact independentBits_first_zero

/-! ## The structural bookkeeping, at these two models

The lemmas below are applied at `copyChain` and `figSCIM` rather than left
general. `figIgnore` exists so that the policy-invariance statement compares two
genuinely different policies instead of one against itself.
-/

/-- Ignoring the opinion: the decision that is constant whatever it observes. -/
public noncomputable def figIgnore : figSCIM.Policy :=
  ⟨fun _ _ _ ↦ 0, by intros; rfl⟩

/-- **Installing a policy does not touch the graph.** -/
public theorem figSCIM_withPolicy_parents :
    (figSCIM.withPolicy figCopy).parents = figSCIM.graph.parents :=
  AISafetyAtlas.Causal.SCIM.withPolicy_parents figSCIM figCopy

/-- **The exogenous law does not depend on the policy.** Compared here at the
copying policy and one that ignores its observation, so the statement is about
two policies that differ. -/
public theorem figSCIM_exoLaw_withPolicy_eq :
    (figSCIM.withPolicy figCopy).exoLaw = (figSCIM.withPolicy figIgnore).exoLaw :=
  AISafetyAtlas.Causal.SCIM.exoLaw_withPolicy_eq figSCIM figCopy figIgnore

/-- The exogenous law of a singleton is the product of the exogenous
probabilities, at the chain that evaluates. -/
public theorem copyChain_exoLaw_singleton (ε : ExoAssignment Two bits) :
    (copyChain.exoLaw : MeasureTheory.Measure (ExoAssignment Two bits)) {ε}
      = ENNReal.ofReal (copyChain.exoJoint ε) :=
  AISafetyAtlas.Causal.SCM.exoLaw_singleton copyChain ε

/-- **The induced joint is nonnegative.** `instIsWellFoundedCopyChain` is what
lets this be asked at all: the hypothesis is discharged, not assumed. -/
public theorem copyChain_jointProb_nonneg (w : EndoAssignment Two bits) :
    0 ≤ copyChain.jointProb w :=
  AISafetyAtlas.Causal.SCM.jointProb_nonneg copyChain w

/-! ## Print's expectation, and the finite sums that compute it

`SCIM.expectedUtility`, `SCIM.optimalValue` and `SCM.jointProb` are finite sums
and exist only at a finite vertex set. Print's `Eπ[U]` and `Pr(W = w)` are an
expectation and a distribution under `P(ε)`, which denote at any vertex set.
The converting lemmas are exercised here, so every value computed above is a
value of print's object.
-/

/-- The utility vertices of `figSCIM` form a finite type, which is what print's
sum over `𝐔` needs in order to denote. It is not a bound on the vertex set. -/
public noncomputable instance instFintypeFigUtilities :
    Fintype {v : Fin 3 // figSCIM.graph.IsUtility v} :=
  Fintype.ofFinite _

/-- **The copying policy earns `1` under print's expectation**, not merely under
the finite sum that computes it. -/
public theorem figSCIM_expectedUtilityLaw_copy :
    figSCIM.expectedUtilityLaw figCopy (SCM.measurable_exo _) = 1 := by
  rw [figSCIM.expectedUtilityLaw_eq figCopy]
  exact figSCIM_expectedUtility_copy

/-- **And it is optimal in print's sense**, which is a comparison of expectations
and needs no attainment. -/
public theorem figSCIM_isOptimalPolicyLaw_copy :
    figSCIM.IsOptimalPolicyLaw figCopy fun _ ↦ SCM.measurable_exo _ := by
  rw [← figSCIM.isOptimalPolicy_iff_law figCopy]
  intro π
  exact figSCIM_expectedUtility_copy ▸ figSCIM_expectedUtility_le_one π

/-- **`V*(M)` maximises print's expectation.** The `Fintype` on the vertex set is
here for the maximum print writes, not for the expectation. -/
public theorem figSCIM_optimalValue_law :
    figSCIM.optimalValue = Finset.univ.sup' Finset.univ_nonempty
      fun π : figSCIM.Policy ↦ figSCIM.expectedUtilityLaw π (SCM.measurable_exo _) :=
  figSCIM.optimalValue_eq_sup'_law

/-- **The induced joint is the law's singleton mass**, at the chain where the
finite sum is already computed. -/
public theorem copyChain_endoLaw_singleton (w : EndoAssignment Two bits) :
    (copyChain.endoLaw (SCM.measurable_exo _) :
      MeasureTheory.Measure (EndoAssignment Two bits)).real {w} = copyChain.jointProb w :=
  copyChain.endoLaw_singleton w

/-! ## Domains that are not `Fin n`

Print's Definition 1 writes `dom(V)` with no cardinality condition, and imposes
finiteness only at Definition 4, on domains. `SCM` carries a family of **types**
for that reason, and these two models are what makes the difference visible: one
whose domains are `Bool` rather than an index into `Fin 2`, and one whose
domains are **infinite**, where `SCM.jointProb` cannot be written at all.
-/

/-- A one-variable model whose domain is `Bool` — a type print's `dom(V)`
admits and `Fin`-indexed domains name only up to an isomorphism nobody supplies.
-/
@[expose] public noncomputable def boolFlip : SCM Unit (fun _ ↦ Bool) (fun _ ↦ Bool) where
  dom_nonempty := fun _ ↦ ⟨false⟩
  parents := fun _ ↦ ∅
  acyclic := by
    intro v hv
    cases hv with
    | single h => exact h
    | tail _ h => exact h
  f := fun _ _ e ↦ !e
  f_parents := by intros; rfl
  exoProb := fun _ _ ↦ 1 / 2
  exoProb_nonneg := by intros; norm_num
  exoProb_tsum := by
    intro v
    rw [tsum_fintype, Fintype.sum_bool]
    norm_num

/-- It evaluates, and the value is the negated noise. -/
public instance instIsWellFoundedBoolFlip : boolFlip.IsWellFounded :=
  ⟨⟨fun v ↦ ⟨v, fun p hp ↦ absurd hp (by simp [boolFlip])⟩⟩⟩

/-- **Print's recursion at a `Bool` domain.** -/
public theorem boolFlip_eval (ε : ExoAssignment Unit (fun _ ↦ Bool)) (v : Unit) :
    boolFlip.eval ε v = !ε v := by
  rw [boolFlip.eval_eq_f ε v]
  rfl

/-- The finite sums apply to it too: `Bool` is a `Fintype`, so print's
Definition 4 layer is available without the domains being `Fin`-indexed. -/
public theorem boolFlip_jointProb_sum :
    ∑ w : EndoAssignment Unit (fun _ ↦ Bool), boolFlip.jointProb w = 1 :=
  boolFlip.jointProb_sum

/-- **A model with infinite domains.** The exogenous variable is a geometric
draw on `ℕ` and the endogenous variable copies it, so `dom` and `edom` are both
`ℕ`. Nothing here can be summed over the assignment space; `SCM.eval` and
`SCM.submodel` are exactly the operations print's Definition 1 and Definition 2
name, and they do not ask to be. -/
@[expose] public noncomputable def geometricCopy : SCM Unit (fun _ ↦ ℕ) (fun _ ↦ ℕ) where
  dom_nonempty := fun _ ↦ ⟨0⟩
  parents := fun _ ↦ ∅
  acyclic := by
    intro v hv
    cases hv with
    | single h => exact h
    | tail _ h => exact h
  f := fun _ _ e ↦ e
  f_parents := by intros; rfl
  exoProb := fun _ n ↦ (1 / 2 : ℝ) ^ (n + 1)
  exoProb_nonneg := by
    intro v n
    positivity
  exoProb_tsum := by
    intro v
    have h : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n ↦ by ring
    rw [h, tsum_geometric_two]
    norm_num

/-- It evaluates. -/
public instance instIsWellFoundedGeometricCopy : geometricCopy.IsWellFounded :=
  ⟨⟨fun v ↦ ⟨v, fun p hp ↦ absurd hp (by simp [geometricCopy])⟩⟩⟩

/-- **Print's recursion at an infinite domain.** -/
public theorem geometricCopy_eval (ε : ExoAssignment Unit (fun _ ↦ ℕ)) (v : Unit) :
    geometricCopy.eval ε v = ε v := by
  rw [geometricCopy.eval_eq_f ε v]
  rfl

/-- **Print's Definition 2 at an infinite domain.** Forcing the variable to `7`
makes it `7`, and no sum over the assignment space is written anywhere. -/
public theorem geometricCopy_submodel_eval
    (ε : ExoAssignment Unit (fun _ ↦ ℕ)) (x : EndoAssignment Unit (fun _ ↦ ℕ)) :
    (geometricCopy.submodel {()} x).eval ε () = x () :=
  SCM.submodel_eval _ _ _ _ (by simp)

/-- The marginals really are a distribution on an infinite domain. -/
public theorem geometricCopy_exoProb_tsum (v : Unit) :
    ∑' n : ℕ, geometricCopy.exoProb v n = 1 :=
  geometricCopy.exoProb_tsum v

/-! ### A policy is its decision rule, and nothing else

`policy_ext_single` is what makes `SCIM.Policy` print's `π` at *"single-decision
settings with `𝐃 = {D}`"*: the type is a family indexed by decision vertices,
and print's datum is one rule. The two must agree, and on this diagram they do.

Both halves are here. `constPolicy` supplies two policies that genuinely differ,
so the extensionality below is not a statement about a one-element type; and
`policy_eq_of_agree_at_decision` is the extensionality itself.
-/

/-- The policy that plays a fixed post whatever it sees. -/
@[expose] public noncomputable def constPolicy (k : Fin 2) : figSCIM.Policy :=
  ⟨fun _ _ _ => k, fun _ _ _ _ _ => rfl⟩

/-- **Two of them differ**, so `figSCIM.Policy` is not a singleton and the
extensionality below has something to rule out. -/
public theorem constPolicy_ne : constPolicy 0 ≠ constPolicy 1 := by
  intro h
  have := congrFun (congrFun (congrFun (Subtype.ext_iff.mp h)
    ⟨1, figSCIM_mem_decisions_one⟩) (fun _ => 0)) 0
  exact absurd this (by decide)

/-- **A policy is determined by what it does at the one decision.** Print writes
`π` for a single rule; the atlas carries a family indexed by decision vertices,
and on a single-decision diagram the two agree. -/
public theorem policy_eq_of_agree_at_decision (π π' : figSCIM.Policy)
    (h : ∀ (hd : figSCIM.graph.IsDecision 1) a e, π.1 ⟨1, hd⟩ a e = π'.1 ⟨1, hd⟩ a e) :
    π = π' :=
  figSCIM.policy_ext_single figCID_decisions h

/-- So a policy agreeing with a constant one at the decision *is* that constant
one -- the direction an argument uses when it has pinned down the rule. -/
public theorem eq_constPolicy_of_agree (π : figSCIM.Policy)
    (h : ∀ (hd : figSCIM.graph.IsDecision 1) a e, π.1 ⟨1, hd⟩ a e = 0) :
    π = constPolicy 0 :=
  policy_eq_of_agree_at_decision π (constPolicy 0) (fun hd a e => h hd a e)

end AISafetyAtlas.Examples.Causal.StructuralModel
