module

public import AISafetyAtlas.Causal.Decision

/-!
# Decision tasks as causal influence diagrams

Richens and Everitt, *Robust agents learn causal world models*, ICLR 2024,
Section 2.2, from the published proceedings PDF.

> **Definition 4 (Causal influence diagram).** A (single-decision,
> single-utility) causal influence diagram (CID) is a CBN `M = (G, P)` where the
> variables `V` are partitioned into decision, utility, and chance variables,
> `V = ({D}, {U}, C)`. The utility variable is a real-valued function of its
> parents, *U(pa_U)*.

> The conditional probability distribution for the decision node *π(d | pa_D)*
> (the policy) is not a fixed parameter of the model but is set by the agent so
> as to maximise its expected utility, which for a policy `π` is
> *E^π[U] = E[U | do(D = π(pa_D))]*. A policy `π*` is optimal if it maximises
> `E^π[U]`. Typically, agents do not behave optimally and incur some regret `δ`,
> which is the decrease in expected utility compared to an optimal policy
> `δ := E^{π*}[U] − E^π[U]`.

> **Assumption 1 (Unmediated decision task).** *Desc_D ∩ Anc_U = ∅*.

**This is the mediated object.** `Causal.Decision` renders the same section's
expected utility and regret *after* Assumption 1 has been applied, with the
decision and the utility living outside the graph — print's Assumption 1
projection. Here the decision and the utility are **vertices of the CBN**, which
is what Definition 4 says they are, and Assumption 1 is a hypothesis a diagram
may or may not satisfy rather than a shape baked into the types.

***do(D = π(pa_D))* is a soft intervention, not a hard one.** Print writes `do`,
and RE24's own Definition 2 severs a hard-intervened vertex's incoming edges.
That is not what a policy does: *π(d | pa_D)* *reads* *pa_D*. So `withPolicy`
keeps `parents` and swaps the table, exactly as `SCM.softIntervention` does for
the structural layer, and `withPolicy_parents` records that the edges survive.
Reading print's `do` as a hard intervention here would delete the observations
the policy is defined to depend on.

**`Anc` and `Desc` are proper.** Print says so: *"Note in particular that *Anc_i*
and *Desc_i* refer to proper ancestors and descendants, i.e. *V_i ∉ Anc_i* and
*V_i ∉ Desc_i*."* This matters for Assumption 1: on print's own Figure 1 the
decision is a parent of the utility, so *D ∈ Anc_U*, and an improper reading
would make the assumption unsatisfiable. Read properly it says that `D`'s only
route to `U` is the direct edge -- which is what print's own Appendix argument
*"*D ∈ Anc_U* which with *Desc_D ∩ Anc_U = ∅* implies *D ∈ Pa_U*"* uses.

**Inherited from `Causal.Model`.** A diagram here is a `Model`, so it carries
that structure's `parents : C → Finset C` and `ℕ`-ranked `acyclic`, and a finite
vertex set. Those are graded on `Causal.Model`'s own rows and are not restated
per declaration below.
-/

namespace AISafetyAtlas.Causal

variable {C : Type*} [Fintype C] [DecidableEq C] {dim : C → ℕ}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace Model

/-! ## Proper ancestors and descendants -/

/-- *"proper ancestors ... *V_i ∉ Anc_i*"*: *Anc_c*. -/
@[expose] public def properAncestors (M : Model C dim 𝕜) (c : C) : Finset C :=
  (M.ancestors {c}).erase c

/-- *"descendants *Desc_i* as the set of all downstream variables"*, proper:
*x ∈ Desc_c* when `c` is a proper ancestor of `x`. -/
@[expose] public def properDescendants (M : Model C dim 𝕜) (c : C) : Finset C :=
  Finset.univ.filter fun x ↦ c ∈ M.properAncestors x

public theorem mem_properAncestors_iff (M : Model C dim 𝕜) {c x : C} :
    x ∈ M.properAncestors c ↔ x ≠ c ∧ x ∈ M.ancestors {c} := by
  simp [properAncestors, Finset.mem_erase]

public theorem mem_properDescendants_iff (M : Model C dim 𝕜) {c x : C} :
    x ∈ M.properDescendants c ↔ c ∈ M.properAncestors x := by
  simp [properDescendants]

/-- The ancestor closure is transitive: an ancestor of an ancestor is an
ancestor. This is `ancestors` being the least parent-closed superset. -/
public theorem ancestors_singleton_subset (M : Model C dim 𝕜) {s : Finset C} {x : C}
    (hx : x ∈ M.ancestors s) : M.ancestors {x} ⊆ M.ancestors s :=
  M.ancestors_subset (Finset.singleton_subset_iff.mpr hx) (M.parentClosed_ancestors s)

/-- An ancestor never ranks later than what it is an ancestor of: the set of
vertices ranked no later is parent-closed. -/
public theorem rank_le_of_mem_ancestors (M : Model C dim 𝕜) {rank : C → ℕ}
    (hrank : ∀ c, ∀ p ∈ M.parents c, rank p < rank c) {c x : C}
    (hx : x ∈ M.ancestors {c}) : rank x ≤ rank c := by
  classical
  have hsub : M.ancestors {c} ⊆ Finset.univ.filter fun y ↦ rank y ≤ rank c := by
    refine M.ancestors_subset ?_ ?_
    · simp
    · intro y hy p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact le_of_lt (lt_of_lt_of_le (hrank y p hp) hy)
  simpa using hsub hx

/-- An ancestor of `c` is not also a child of `c`: that would be a cycle. -/
public theorem notMem_parents_of_mem_ancestors (M : Model C dim 𝕜) {c x : C}
    (hx : x ∈ M.ancestors {c}) : c ∉ M.parents x := by
  obtain ⟨rank, hrank⟩ := M.acyclic
  exact fun h ↦ absurd (lt_of_lt_of_le (hrank x c h) (M.rank_le_of_mem_ancestors hrank hx))
    (lt_irrefl _)

/-- A parent is a proper ancestor. -/
public theorem mem_properAncestors_of_mem_parents (M : Model C dim 𝕜) {c p : C}
    (hp : p ∈ M.parents c) : p ∈ M.properAncestors c := by
  refine M.mem_properAncestors_iff.mpr ⟨fun h ↦ M.notMem_parents_self c (h ▸ hp), ?_⟩
  exact M.parentClosed_ancestors {c} c (M.subset_ancestors {c} (Finset.mem_singleton_self c)) p hp

/-- A table cell equal to one leaves nothing for any other cell, so the state it
names is unique. This is what makes a probability-one table a *function*. -/
public theorem cpt_eq_one_unique (M : Model C dim 𝕜) {c : C} {a b : Fin (dim c)}
    {v : Assignment C dim} (ha : M.cpt c a v = 1) (hb : M.cpt c b v = 1) : a = b := by
  classical
  by_contra hne
  have hpair : ∑ x ∈ ({a, b} : Finset (Fin (dim c))), M.cpt c x v
      ≤ ∑ x : Fin (dim c), M.cpt c x v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ ↦ M.cpt_nonneg c x v)
  rw [Finset.sum_pair hne, ha, hb, M.cpt_sum c v] at hpair
  linarith

/-! ## Policies, and *do(D = π(pa_D))* -/

end Model

/-- **A policy**: *"The conditional probability distribution for the decision
node *π(d | pa_D)*"*. It is a conditional distribution over the decision's
states that reads only *pa_D*. -/
public structure DecisionPolicy (M : Model C dim 𝕜) (d : C) where
  /-- *π(a | pa_D)*. -/
  prob : Fin (dim d) → Assignment C dim → 𝕜
  /-- A conditional probability is nonnegative. -/
  prob_nonneg : ∀ a v, 0 ≤ prob a v
  /-- Each conditional distribution sums to one. -/
  prob_sum : ∀ v, ∑ a : Fin (dim d), prob a v = 1
  /-- *"*π(d | pa_D)*"*: the policy reads only the decision's parents. -/
  prob_parents : ∀ a v w, (∀ p ∈ M.parents d, v p = w p) → prob a v = prob a w

namespace Model

/-- ***do(D = π(pa_D))*.** The diagram with the decision's table replaced by the
policy. A *soft* intervention: the parent set is untouched, because the policy
is defined to read *pa_D*. -/
@[expose] public noncomputable def withPolicy (M : Model C dim 𝕜) {d : C}
    (π : DecisionPolicy M d) : Model C dim 𝕜 where
  dim_pos := M.dim_pos
  parents := M.parents
  acyclic := M.acyclic
  cpt := Function.update M.cpt d π.prob
  cpt_parents := by
    intro c a v w h
    by_cases hc : c = d
    · subst hc
      simp only [Function.update_self]
      exact π.prob_parents a v w h
    · simp only [Function.update_of_ne hc]
      exact M.cpt_parents c a v w h
  cpt_nonneg := by
    intro c a v
    by_cases hc : c = d
    · subst hc; simp only [Function.update_self]; exact π.prob_nonneg a v
    · simp only [Function.update_of_ne hc]; exact M.cpt_nonneg c a v
  cpt_sum := by
    intro c v
    by_cases hc : c = d
    · subst hc; simp only [Function.update_self]; exact π.prob_sum v
    · simp only [Function.update_of_ne hc]; exact M.cpt_sum c v

@[simp] public theorem withPolicy_parents (M : Model C dim 𝕜) {d : C}
    (π : DecisionPolicy M d) : (M.withPolicy π).parents = M.parents := rfl

@[simp] public theorem withPolicy_cpt_decision (M : Model C dim 𝕜) {d : C}
    (π : DecisionPolicy M d) : (M.withPolicy π).cpt d = π.prob :=
  Function.update_self _ _ _

@[simp] public theorem withPolicy_cpt_of_ne (M : Model C dim 𝕜) {d c : C}
    (π : DecisionPolicy M d) (hc : c ≠ d) : (M.withPolicy π).cpt c = M.cpt c :=
  Function.update_of_ne hc _ _

end Model

/-! ## Definition 4 -/

/-- **RE24 Definition 4.** A single-decision, single-utility causal influence
diagram: a CBN whose vertices carry a distinguished decision and utility, with
the utility's states read as reals.

Print partitions `V = ({D}, {U}, C)`; here the chance variables are the rest,
`decision_ne_utility` is the only disjointness a two-element distinguished part
needs, and `IsChance` names the third block. -/
public structure DecisionNetwork (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] where
  /-- The CBN the diagram is built on. -/
  net : Model C dim 𝕜
  /-- `D`. -/
  decision : C
  /-- `U`. -/
  utility : C
  /-- `{D}` and `{U}` are distinct blocks of the partition. -/
  decision_ne_utility : decision ≠ utility
  /-- *"The utility variable is a real-valued function of its parents"*: the
  states of `U` read as reals. Determinacy in the parents is
  `IsDeterministicUtility`, a hypothesis rather than a field -- see there. -/
  uval : Fin (dim utility) → 𝕜

namespace DecisionNetwork

variable (G : DecisionNetwork C dim 𝕜)

/-- `C`, the third block of print's partition. -/
@[expose] public def IsChance (c : C) : Prop := c ≠ G.decision ∧ c ≠ G.utility

/-- A policy for this diagram's decision vertex. -/
public abbrev Policy := DecisionPolicy G.net G.decision

/-- A policy may ignore its observations, so one always exists. -/
public noncomputable instance instNonemptyPolicy : Nonempty G.Policy :=
  ⟨{ prob := fun a v ↦ G.net.cpt G.decision a v
     prob_nonneg := fun a v ↦ G.net.cpt_nonneg G.decision a v
     prob_sum := fun v ↦ G.net.cpt_sum G.decision v
     prob_parents := fun a v w h ↦ G.net.cpt_parents G.decision a v w h }⟩

/-- ***E^π[U] = E[U | do(D = π(pa_D))]*.** The expectation of the utility
vertex's real readout in the diagram with the policy installed. -/
@[expose] public noncomputable def expectedUtility (π : G.Policy) : 𝕜 :=
  ∑ v : Assignment C dim,
    (G.net.withPolicy π).jointProb (Model.observationalProfile C dim) v * G.uval (v G.utility)

/-- *"A policy `π*` is optimal if it maximises `E^π[U]`."* -/
@[expose] public def IsOptimal (π : G.Policy) : Prop :=
  ∀ π' : G.Policy, G.expectedUtility π' ≤ G.expectedUtility π

/-- **`δ := E^{π*}[U] − E^π[U]`**, *"the decrease in expected utility compared to
an optimal policy"*. Print writes it against an optimal `π*`; the subtraction is
defined for any pair and `regret_nonneg` is where optimality is used. -/
@[expose] public noncomputable def regret (πStar π : G.Policy) : 𝕜 :=
  G.expectedUtility πStar - G.expectedUtility π

public theorem regret_nonneg {πStar π : G.Policy} (h : G.IsOptimal πStar) :
    0 ≤ G.regret πStar π :=
  sub_nonneg.mpr (h π)

@[simp] public theorem regret_self (π : G.Policy) : G.regret π π = 0 :=
  sub_self _

/-- **Assumption 1 (Unmediated decision task).** *Desc_D ∩ Anc_U = ∅*, with both
sets proper as print states. -/
@[expose] public def IsUnmediated : Prop :=
  Disjoint (G.net.properDescendants G.decision) (G.net.properAncestors G.utility)

/-- *"The utility variable is a real-valued function of its parents, *U(pa_U)*."*

Carried as a **hypothesis, not a field**, so that `DecisionNetwork` is the
`Definition 4` tuple and this is the restriction print puts on it. The atlas
therefore defines expected utility on a strictly larger class than print's, in
the disclosed direction; `IsDeterministicUtility` pins print's case and
`exists_utilityFunction` is where print's function is recovered. -/
@[expose] public def IsDeterministicUtility : Prop :=
  ∀ v : Assignment C dim, ∃ a : Fin (dim G.utility), G.net.cpt G.utility a v = 1

/-- **Print's *U(pa_U)*, recovered as an actual function.** Under
`IsDeterministicUtility` the utility vertex's state is determined by its parents,
which is what *"a real-valued function of its parents"* asserts. Without this
hypothesis `expectedUtility` is still defined -- that is the disclosed widening
-- but the utility is a conditional distribution rather than a function. -/
public theorem exists_utilityFunction (h : G.IsDeterministicUtility) :
    ∃ f : Assignment C dim → Fin (dim G.utility),
      (∀ v, G.net.cpt G.utility (f v) v = 1) ∧
      ∀ v w, (∀ p ∈ G.net.parents G.utility, v p = w p) → f v = f w := by
  choose f hf using h
  refine ⟨f, hf, fun v w hvw ↦ ?_⟩
  refine G.net.cpt_eq_one_unique (hf v) ?_
  rw [G.net.cpt_parents G.utility (f w) v w hvw]
  exact hf w

/-- **Assumption 1, in the form print's own argument uses it.** No proper
ancestor of the utility reads the decision: such a vertex would be a proper
descendant of the decision and a proper ancestor of the utility at once. -/
public theorem decision_notMem_parents_of_isUnmediated (h : G.IsUnmediated)
    {c : C} (hc : c ∈ G.net.properAncestors G.utility) :
    G.decision ∉ G.net.parents c := fun hd ↦
  (Finset.disjoint_left.mp h)
    (G.net.mem_properDescendants_iff.mpr (G.net.mem_properAncestors_of_mem_parents hd)) hc

/-- **Print's Appendix step**: *"As D ∈ Pa_U (iii), then Pa_U ⊆ Anc_U … If
D ∉ Anc_U then the CID is trivial … Therefore D ∈ Anc_U which with
Desc_D ∩ Anc_U = ∅ implies D ∈ Pa_U."*

This is the whole force of *unmediated*: the decision reaches the utility, and
under Assumption 1 the only route left is the direct edge. The proof is the
one print's phrase compresses -- if the decision reached the utility through any
intermediate vertex, that vertex would sit in both sets. -/
public theorem mem_parents_utility_of_isUnmediated (h : G.IsUnmediated)
    (hd : G.decision ∈ G.net.properAncestors G.utility) :
    G.decision ∈ G.net.parents G.utility := by
  classical
  by_contra hnd
  set M := G.net with hM
  set bad : Finset C := insert G.decision (M.properDescendants G.decision) with hbad
  set T : Finset C := insert G.utility ((M.ancestors {G.utility}) \ bad) with hT
  have hdne : G.decision ≠ G.utility := (M.mem_properAncestors_iff.mp hd).1
  have hdbad : G.decision ∈ bad := Finset.mem_insert_self _ _
  have hdT : G.decision ∉ T := by
    rw [hT]
    intro hx
    rcases Finset.mem_insert.mp hx with h1 | h2
    · exact hdne h1
    · exact (Finset.mem_sdiff.mp h2).2 hdbad
  have hclosed : M.ParentClosed T := by
    intro c hc p hp
    have hcanc : c ∈ M.ancestors {G.utility} := by
      rcases Finset.mem_insert.mp hc with h1 | h2
      · exact h1 ▸ M.subset_ancestors _ (Finset.mem_singleton_self _)
      · exact (Finset.mem_sdiff.mp h2).1
    have hpanc : p ∈ M.ancestors {G.utility} :=
      M.parentClosed_ancestors {G.utility} c hcanc p hp
    have hpU : p ≠ G.utility := by
      rintro rfl
      exact M.notMem_parents_of_mem_ancestors hcanc hp
    have hpprop : p ∈ M.properAncestors G.utility :=
      M.mem_properAncestors_iff.mpr ⟨hpU, hpanc⟩
    have hpdesc : p ∉ M.properDescendants G.decision := fun hx ↦
      (Finset.disjoint_left.mp h) hx hpprop
    have hpd : p ≠ G.decision := by
      rintro rfl
      rcases Finset.mem_insert.mp hc with h1 | h2
      · exact hnd (h1 ▸ hp)
      · refine (Finset.mem_sdiff.mp h2).2 ?_
        rw [hbad]
        exact Finset.mem_insert_of_mem
          (M.mem_properDescendants_iff.mpr (M.mem_properAncestors_of_mem_parents hp))
    refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hpanc, ?_⟩)
    rw [hbad]
    exact fun hx ↦ (Finset.mem_insert.mp hx).elim hpd hpdesc
  have hsub : M.ancestors {G.utility} ⊆ T :=
    M.ancestors_subset (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) hclosed
  exact hdT (hsub (M.mem_properAncestors_iff.mp hd).2)

end DecisionNetwork

end AISafetyAtlas.Causal
