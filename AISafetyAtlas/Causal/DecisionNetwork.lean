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

/-- **The proper ancestors of a vertex are parent-closed.** A parent of a proper
ancestor is an ancestor, and it is not the vertex itself -- that would be a
cycle. This is the hypothesis `Model.sum_jointProb_mul_of_parentClosed` asks for
at *Anc_U*. -/
public theorem parentClosed_properAncestors (M : Model C dim 𝕜) (u : C) :
    M.ParentClosed (M.properAncestors u) := by
  intro c hc p hp
  obtain ⟨-, hcanc⟩ := M.mem_properAncestors_iff.mp hc
  have hpanc : p ∈ M.ancestors {u} := M.parentClosed_ancestors {u} c hcanc p hp
  refine M.mem_properAncestors_iff.mpr ⟨?_, hpanc⟩
  rintro rfl
  exact M.notMem_parents_of_mem_ancestors hcanc hp

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

/-! ## What the observational profile contributes

`Model.value`, in `AISafetyAtlas.Causal.Decision`, is print's §2.2 expected
utility on the **unmediated projection**, where the decision and the utility are not
vertices. This diagram's `expectedUtility` is the same quantity where they are,
and `expectedUtility_eq_value` below is the proof.

These two lemmas are where it starts, and they are the whole of what the
observational profile contributes: a factor at the observational profile is just
the conditional table, and installing a policy changes exactly one factor.
-/

/-- **A factor at the observational profile is the conditional table itself.**
Intervening nowhere leaves `RE24` equation (1)'s sum with one surviving term. -/
public theorem factor_observationalProfile (M : Model C dim 𝕜)
    (v : Assignment C dim) (c : C) :
    M.factor (Model.observationalProfile C dim) v c = M.cpt c (v c) v := by
  have h := Finset.sum_eq_single (M := 𝕜) (s := (Finset.univ : Finset (Fin (dim c))))
    (f := fun a ↦ if identityIntervention a = v c then M.cpt c a v else 0) (v c)
    (fun b _ hb ↦ if_neg hb) (fun h ↦ absurd (Finset.mem_univ (v c)) h)
  exact h.trans (if_pos rfl)

/-- **Installing a policy changes exactly one factor.** *do(D = π(pa_D))* is a
soft intervention, so every vertex but the decision keeps its table. -/
public theorem withPolicy_factor_observationalProfile (M : Model C dim 𝕜) {d : C}
    (π : DecisionPolicy M d) (v : Assignment C dim) (c : C) :
    (M.withPolicy π).factor (Model.observationalProfile C dim) v c
      = if c = d then π.prob (v d) v
        else M.factor (Model.observationalProfile C dim) v c := by
  by_cases hc : c = d
  · subst hc
    rw [factor_observationalProfile, if_pos rfl, Model.withPolicy_cpt_decision M π]
  · rw [if_neg hc, factor_observationalProfile, factor_observationalProfile,
      Model.withPolicy_cpt_of_ne M π hc]

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

/-! ## The agreement with the unmediated projection

`Causal.Decision`'s `Skeleton` carries a **real-valued** utility of a decision
and an environment. That is weaker than print's *U(pa_U)*, and the difference is
what makes the agreement statable without determinacy: the number a `Skeleton`
needs is the utility vertex's conditional *expectation*, which exists at every
diagram. `IsDeterministicUtility` is therefore **not** a hypothesis of the
agreement; it is the special case in which `utilityMean` is print's own function
composed with `uval`, recorded as `utilityMean_eq_uval_of_isDeterministicUtility`.

The route is one lemma applied twice. `Model.sum_jointProb_mul_of_parentClosed`
collapses an expectation onto a parent-closed set, and
`Model.sum_image_fibreRep_erase` splits the resulting sum by one coordinate.
Taking the utility's coordinate out of *Anc_U* turns the diagram's expectation
into `utilityMean`; taking the decision's coordinate out of what remains turns
the policy's table into the projection's outside-the-graph policy. Assumption 1
enters once, as `parentClosed_chanceContext`: no proper ancestor of the utility
reads the decision, so the context is closed under parents.
-/

/-- **The utility vertex's conditional expectation**, *E[U | pa_U]* read through
`uval`. This is the number the projection's `Skeleton` asks for. -/
@[expose] public noncomputable def utilityMean (v : Assignment C dim) : 𝕜 :=
  ∑ b : Fin (dim G.utility), G.net.cpt G.utility b v * G.uval b

/-- The conditional expectation reads the utility's parents and nothing else. -/
public theorem utilityMean_congr {v w : Assignment C dim}
    (hvw : ∀ p ∈ G.net.parents G.utility, v p = w p) :
    G.utilityMean v = G.utilityMean w :=
  Finset.sum_congr rfl fun b _ ↦ by
    rw [G.net.cpt_parents G.utility b v w hvw]

/-- Print's Appendix A.2 normalization, transported: a convex combination of
values in `[0,1]` is in `[0,1]`. -/
public theorem utilityMean_mem_unitInterval
    (h01 : ∀ b : Fin (dim G.utility), 0 ≤ G.uval b ∧ G.uval b ≤ 1)
    (v : Assignment C dim) : 0 ≤ G.utilityMean v ∧ G.utilityMean v ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun b _ ↦
      mul_nonneg (G.net.cpt_nonneg G.utility b v) (h01 b).1
  · calc G.utilityMean v
        ≤ ∑ b : Fin (dim G.utility), G.net.cpt G.utility b v * 1 :=
          Finset.sum_le_sum fun b _ ↦ by
            exact mul_le_mul_of_nonneg_left (h01 b).2 (G.net.cpt_nonneg G.utility b v)
      _ = 1 := by simpa using G.net.cpt_sum G.utility v

/-- **A probability-one cell is the whole expectation.** -/
public theorem utilityMean_eq_uval_of_cpt_eq_one {v : Assignment C dim}
    {a : Fin (dim G.utility)} (ha : G.net.cpt G.utility a v = 1) :
    G.utilityMean v = G.uval a := by
  classical
  have hzero : ∀ b ∈ (Finset.univ : Finset (Fin (dim G.utility))), b ≠ a →
      G.net.cpt G.utility b v * G.uval b = 0 := by
    intro b _ hb
    have hle : ∑ x ∈ ({b, a} : Finset (Fin (dim G.utility))), G.net.cpt G.utility x v
        ≤ ∑ x : Fin (dim G.utility), G.net.cpt G.utility x v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ ↦ G.net.cpt_nonneg G.utility x v)
    rw [Finset.sum_pair hb, ha, G.net.cpt_sum G.utility v] at hle
    have hb0 : G.net.cpt G.utility b v = 0 :=
      le_antisymm (by linarith) (G.net.cpt_nonneg G.utility b v)
    rw [hb0, zero_mul]
  rw [utilityMean, Finset.sum_eq_single a hzero (fun hx ↦ absurd (Finset.mem_univ _) hx),
    ha, one_mul]

/-- **Print's *U(pa_U)*, back again.** When the utility vertex is a function of
its parents -- print's Definition 4 -- its conditional expectation *is* that
function, read through `uval`. So the agreement below specialises to print's
case without having been stated at it. -/
public theorem utilityMean_eq_uval_of_isDeterministicUtility
    (hdet : G.IsDeterministicUtility) :
    ∃ f : Assignment C dim → Fin (dim G.utility),
      (∀ v w, (∀ p ∈ G.net.parents G.utility, v p = w p) → f v = f w) ∧
        ∀ v, G.utilityMean v = G.uval (f v) := by
  obtain ⟨f, hf, hpar⟩ := G.exists_utilityFunction hdet
  exact ⟨f, hpar, fun v ↦ G.utilityMean_eq_uval_of_cpt_eq_one (hf v)⟩

/-! ### The context the projection keeps -/

/-- ***Anc_U ∖ {U, D}***: the chance vertices the unmediated projection keeps.
The decision and the utility leave the graph, and what is left is exactly what
both the policy and the utility read. -/
@[expose] public def chanceContext : Finset C :=
  (G.net.properAncestors G.utility).erase G.decision

/-- **Assumption 1, as a closure property.** The context is closed under parents.
The only vertex that could leave it is the decision, and
`decision_notMem_parents_of_isUnmediated` is exactly the statement that no proper
ancestor of the utility reads the decision. This is where print's Assumption 1
enters the agreement. -/
public theorem parentClosed_chanceContext (h : G.IsUnmediated) :
    G.net.ParentClosed G.chanceContext := by
  intro c hc p hp
  obtain ⟨-, hcP⟩ := Finset.mem_erase.mp hc
  have hpP : p ∈ G.net.properAncestors G.utility :=
    G.net.parentClosed_properAncestors G.utility c hcP p hp
  refine Finset.mem_erase.mpr ⟨?_, hpP⟩
  rintro rfl
  exact G.decision_notMem_parents_of_isUnmediated h hcP hp

/-- A parent of the utility other than the decision is in the context. -/
public theorem mem_chanceContext_of_mem_parents_utility {p : C}
    (hp : p ∈ G.net.parents G.utility) (hpd : p ≠ G.decision) :
    p ∈ G.chanceContext :=
  Finset.mem_erase.mpr ⟨hpd, G.net.mem_properAncestors_of_mem_parents hp⟩

/-- **When the decision matters, everything it observes is in the context.**
If the decision is an ancestor of the utility then its own ancestors are too, so
*pa_D* survives the projection. -/
public theorem parents_decision_subset_chanceContext
    (hd : G.decision ∈ G.net.properAncestors G.utility) :
    G.net.parents G.decision ⊆ G.chanceContext := by
  intro p hp
  obtain ⟨-, hdanc⟩ := G.net.mem_properAncestors_iff.mp hd
  have hpanc : p ∈ G.net.ancestors {G.utility} :=
    G.net.ancestors_singleton_subset hdanc
      (G.net.mem_properAncestors_iff.mp (G.net.mem_properAncestors_of_mem_parents hp)).2
  have hpu : p ≠ G.utility := by
    rintro rfl
    exact G.net.notMem_parents_of_mem_ancestors hdanc hp
  have hpd : p ≠ G.decision := fun hx ↦ G.net.notMem_parents_self G.decision (hx ▸ hp)
  exact Finset.mem_erase.mpr ⟨hpd, G.net.mem_properAncestors_iff.mpr ⟨hpu, hpanc⟩⟩

/-- **When the decision does not matter, the utility never reads it.** -/
public theorem decision_notMem_parents_utility_of_notMem
    (hd : G.decision ∉ G.net.properAncestors G.utility) :
    G.decision ∉ G.net.parents G.utility := fun hp ↦
  hd (G.net.mem_properAncestors_of_mem_parents hp)

/-! ### The projection's data, read off the diagram -/

/-- **The decision's contribution at one environment**: the policy's average of
the utility's conditional expectation over the decision's states. This is the
integrand both sides of the agreement reduce to. -/
@[expose] public noncomputable def policyUtility (π : G.Policy) (v : Assignment C dim) : 𝕜 :=
  ∑ a : Fin (dim G.decision), π.prob a v * G.utilityMean (Function.update v G.decision a)

/-- **The integrand reads the context and nothing else**, which is what
`Model.sum_jointProb_mul_of_parentClosed` asks of it.

Both cases of print's Appendix step are here. If the decision is an ancestor of
the utility, the policy reads *pa_D ⊆ Anc_U* and the utility reads
*pa_U ∖ {D}*, both inside the context. If it is not, *"the CID is trivial"*: the
decision changes no utility, the policy's distribution sums away, and what is
left reads *pa_U* alone. -/
public theorem policyUtility_congr (π : G.Policy) {v w : Assignment C dim}
    (hvw : ∀ c ∈ G.chanceContext, v c = w c) :
    G.policyUtility π v = G.policyUtility π w := by
  classical
  by_cases hd : G.decision ∈ G.net.properAncestors G.utility
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hprob : π.prob a v = π.prob a w :=
      π.prob_parents a v w fun p hp ↦ hvw p (G.parents_decision_subset_chanceContext hd hp)
    have hmean : G.utilityMean (Function.update v G.decision a)
        = G.utilityMean (Function.update w G.decision a) := by
      refine G.utilityMean_congr fun p hp ↦ ?_
      by_cases hpd : p = G.decision
      · subst hpd; simp
      · rw [Function.update_of_ne hpd, Function.update_of_ne hpd]
        exact hvw p (G.mem_chanceContext_of_mem_parents_utility hp hpd)
    rw [hprob, hmean]
  · have hnotpar : G.decision ∉ G.net.parents G.utility :=
      G.decision_notMem_parents_utility_of_notMem hd
    have hdrop : ∀ (u : Assignment C dim) (a : Fin (dim G.decision)),
        G.utilityMean (Function.update u G.decision a) = G.utilityMean u := by
      intro u a
      refine G.utilityMean_congr fun p hp ↦ ?_
      have hpd : p ≠ G.decision := by rintro rfl; exact hnotpar hp
      rw [Function.update_of_ne hpd]
    have hmean : G.utilityMean v = G.utilityMean w := by
      refine G.utilityMean_congr fun p hp ↦ ?_
      have hpd : p ≠ G.decision := by rintro rfl; exact hnotpar hp
      exact hvw p (G.mem_chanceContext_of_mem_parents_utility hp hpd)
    unfold policyUtility
    simp only [hdrop]
    rw [← Finset.sum_mul, ← Finset.sum_mul, π.prob_sum v, π.prob_sum w, one_mul, one_mul, hmean]

/-- **Print's projection, read off the diagram.** The observed variables are
*pa_D*, the utility's parents lose the decision, and the utility of a decision
at an environment is the utility vertex's conditional expectation with that
decision written in. `[0,1]` is RE24 Appendix A.2, carried as the hypothesis
`h01` on `uval` rather than assumed of the diagram. -/
@[expose] public noncomputable def projectedSkeleton
    (h01 : ∀ b : Fin (dim G.utility), 0 ≤ G.uval b ∧ G.uval b ≤ 1) :
    Skeleton C dim (Fin (dim G.decision)) 𝕜 where
  observed := G.net.parents G.decision
  utilityParents := (G.net.parents G.utility).erase G.decision
  utility := fun d v ↦ G.utilityMean (Function.update v G.decision d)
  utility_parents := by
    intro d v w hvw
    refine G.utilityMean_congr fun p hp ↦ ?_
    by_cases hpd : p = G.decision
    · subst hpd; simp
    · rw [Function.update_of_ne hpd, Function.update_of_ne hpd]
      exact hvw p (Finset.mem_erase.mpr ⟨hpd, hp⟩)
  utility_mem_unitInterval := fun _ v ↦ G.utilityMean_mem_unitInterval h01 _

/-- **The same policy, outside the graph.** A `DecisionPolicy` on the decision
vertex is a `Policy` on the projection: the arguments swap and nothing else
changes, because both read *pa_D*. -/
@[expose] public noncomputable def projectedPolicy (π : G.Policy) :
    AISafetyAtlas.Causal.Policy (dim := dim) (G.net.parents G.decision)
      (Fin (dim G.decision)) 𝕜 where
  prob := fun v d ↦ π.prob d v
  prob_nonneg := fun v d ↦ π.prob_nonneg d v
  prob_sum := fun v ↦ π.prob_sum v
  prob_parents := fun v w d hvw ↦ π.prob_parents d v w hvw

/-! ### The two sides, in one normal form -/

/--
**The diagram's expected utility, collapsed onto the context.**

Two applications of `Model.sum_image_fibreRep_erase`. Taking the utility's
coordinate out of *Anc_U* replaces `uval` by the utility vertex's conditional
expectation; taking the decision's coordinate out of what remains replaces the
decision's table by the policy, and the factors of the remaining vertices do not
see the change because no proper ancestor of the utility reads the decision.
-/
public theorem expectedUtility_eq_contextSum (h : G.IsUnmediated) (π : G.Policy) :
    G.expectedUtility π
      = ∑ q ∈ Finset.univ.image (fibreRep G.net G.chanceContext),
          (∏ c ∈ G.chanceContext,
              G.net.factor (Model.observationalProfile C dim) q c) * G.policyUtility π q := by
  classical
  set M := G.net with hMdef
  set σ := Model.observationalProfile C dim with hσdef
  set M' := M.withPolicy π with hM'def
  set A := M.ancestors {G.utility} with hAdef
  set P := M.properAncestors G.utility with hPdef
  have hUA : G.utility ∈ A := M.subset_ancestors _ (Finset.mem_singleton_self _)
  have hUP : G.utility ∉ P := Finset.notMem_erase _ _
  have hUD : G.utility ≠ G.decision := Ne.symm G.decision_ne_utility
  have hfib : fibreRep M' = fibreRep M := rfl
  have hancM' : M'.ancestors {G.utility} = A := rfl
  -- the whole expectation collapses onto the utility's ancestors
  have h1 : G.expectedUtility π
      = ∑ r ∈ Finset.univ.image (fibreRep M A),
          (∏ c ∈ A, M'.factor σ r c) * G.uval (r G.utility) := by
    have := Model.sum_jointProb_mul_of_parentClosed M' σ
      (s := A) (hancM' ▸ M'.parentClosed_ancestors {G.utility})
      (g := fun v ↦ G.uval (v G.utility))
      (fun v w hvw ↦ by rw [hvw G.utility hUA])
    rw [hfib] at this
    exact this
  -- one factor at a time: the utility's coordinate
  have hfacU : ∀ (s : Assignment C dim) (b : Fin (dim G.utility)),
      M'.factor σ (Function.update s G.utility b) G.utility = M.cpt G.utility b s := by
    intro s b
    rw [withPolicy_factor_observationalProfile, if_neg hUD, factor_observationalProfile,
      Function.update_self]
    refine M.cpt_parents G.utility b _ s fun p hp ↦ ?_
    have hpU : p ≠ G.utility := by rintro rfl; exact M.notMem_parents_self _ hp
    exact Function.update_of_ne hpU _ _
  have hfacP : ∀ (s : Assignment C dim) (b : Fin (dim G.utility)), ∀ c ∈ P,
      M'.factor σ (Function.update s G.utility b) c = M'.factor σ s c := by
    intro s b c hc
    obtain ⟨hcU, hcanc⟩ := M.mem_properAncestors_iff.mp hc
    refine M'.factor_congr σ _ _ c (fun p hp ↦ ?_) (Function.update_of_ne hcU _ _)
    have hpU : p ≠ G.utility := by
      rintro rfl
      exact M.notMem_parents_of_mem_ancestors hcanc hp
    exact Function.update_of_ne hpU _ _
  have h2 : ∀ s : Assignment C dim,
      ∑ b : Fin (dim G.utility),
          (∏ c ∈ A, M'.factor σ (Function.update s G.utility b) c) *
            G.uval (Function.update s G.utility b G.utility)
        = (∏ c ∈ P, M'.factor σ s c) * G.utilityMean s := by
    intro s
    have hins : A = insert G.utility P := (Finset.insert_erase hUA).symm
    rw [utilityMean, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Function.update_self, hins, Finset.prod_insert hUP, hfacU s b,
      Finset.prod_congr rfl (fun c hc ↦ hfacP s b c hc)]
    ring
  have h3 : G.expectedUtility π
      = ∑ s ∈ Finset.univ.image (fibreRep M P),
          (∏ c ∈ P, M'.factor σ s c) * G.utilityMean s := by
    rw [h1, sum_image_fibreRep_erase M hUA
      (fun r ↦ (∏ c ∈ A, M'.factor σ r c) * G.uval (r G.utility))]
    exact Finset.sum_congr rfl fun s _ ↦ h2 s
  rw [h3]
  by_cases hd : G.decision ∈ P
  · have hDQ : G.decision ∉ G.chanceContext := Finset.notMem_erase _ _
    have hins : P = insert G.decision G.chanceContext := (Finset.insert_erase hd).symm
    rw [sum_image_fibreRep_erase M hd
      (fun s ↦ (∏ c ∈ P, M'.factor σ s c) * G.utilityMean s)]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [policyUtility, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hfacD : M'.factor σ (Function.update q G.decision a) G.decision = π.prob a q := by
      rw [withPolicy_factor_observationalProfile, if_pos rfl, Function.update_self]
      refine π.prob_parents a _ q fun p hp ↦ ?_
      have hpd : p ≠ G.decision := by rintro rfl; exact M.notMem_parents_self _ hp
      exact Function.update_of_ne hpd _ _
    have hfacQ : ∀ c ∈ G.chanceContext,
        M'.factor σ (Function.update q G.decision a) c = M.factor σ q c := by
      intro c hc
      have hcd : c ≠ G.decision := (Finset.mem_erase.mp hc).1
      rw [withPolicy_factor_observationalProfile, if_neg hcd]
      refine M.factor_congr σ _ _ c (fun p hp ↦ ?_) (Function.update_of_ne hcd _ _)
      have hpd : p ≠ G.decision := by
        rintro rfl
        exact G.decision_notMem_parents_of_isUnmediated h (Finset.mem_erase.mp hc).2 hp
      exact Function.update_of_ne hpd _ _
    rw [hins, Finset.prod_insert hDQ, hfacD, Finset.prod_congr rfl hfacQ]
    ring
  · have heq : G.chanceContext = P := Finset.erase_eq_of_notMem hd
    have hnotpar : G.decision ∉ M.parents G.utility :=
      G.decision_notMem_parents_utility_of_notMem hd
    rw [heq]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hfac : ∀ c ∈ P, M'.factor σ s c = M.factor σ s c := by
      intro c hc
      have hcd : c ≠ G.decision := by rintro rfl; exact hd hc
      rw [withPolicy_factor_observationalProfile, if_neg hcd]
    have hpu : G.policyUtility π s = G.utilityMean s := by
      have hdrop : ∀ a : Fin (dim G.decision),
          G.utilityMean (Function.update s G.decision a) = G.utilityMean s := by
        intro a
        refine G.utilityMean_congr fun p hp ↦ ?_
        have hpd : p ≠ G.decision := by rintro rfl; exact hnotpar hp
        exact Function.update_of_ne hpd _ _
      unfold policyUtility
      simp only [hdrop]
      rw [← Finset.sum_mul, π.prob_sum s, one_mul]
    rw [Finset.prod_congr rfl hfac, hpu]

/-- **The projection's value, collapsed onto the same context.** Assumption 1
enters here, and only here: `parentClosed_chanceContext` is what lets the
context carry its own factors. -/
public theorem value_eq_contextSum (h : G.IsUnmediated)
    (h01 : ∀ b : Fin (dim G.utility), 0 ≤ G.uval b ∧ G.uval b ≤ 1) (π : G.Policy) :
    G.net.value (G.projectedSkeleton h01) (G.net.parents G.decision) (G.projectedPolicy π)
        (ProbMixture.dirac (Model.observationalProfile C dim))
      = ∑ q ∈ Finset.univ.image (fibreRep G.net G.chanceContext),
          (∏ c ∈ G.chanceContext,
              G.net.factor (Model.observationalProfile C dim) q c) * G.policyUtility π q := by
  classical
  rw [Model.value_eq]
  have hbody : ∀ v : Assignment C dim,
      G.net.jointProbMix
          (ProbMixture.dirac (𝕜 := 𝕜) (Model.observationalProfile C dim)).1 v *
        ∑ d : Fin (dim G.decision), (G.projectedPolicy π).prob v d *
          (G.projectedSkeleton h01).utility d v
        = G.net.jointProb (Model.observationalProfile C dim) v * G.policyUtility π v := by
    intro v
    rw [Model.jointProbMix_dirac]
    rfl
  rw [Finset.sum_congr rfl (fun v _ ↦ hbody v)]
  exact Model.sum_jointProb_mul_of_parentClosed G.net _ (G.parentClosed_chanceContext h)
    (fun v w hvw ↦ G.policyUtility_congr π hvw)

/--
**RE24 Section 2.2, both ways of writing it, and they agree.**

The diagram's *E^π[U] = E[U | do(D = π(pa_D))]*, with the decision and the
utility as vertices, equals `Model.value` on print's Assumption 1 projection,
where neither is a vertex. Print asserts the two are the same quantity and never
proves it; this is the proof, and it says what the identification costs.

The hypotheses are print's own and nothing else. `IsUnmediated` is Assumption 1.
`h01` is the Appendix A.2 normalization of the utility's range, which the
projection's `Skeleton` carries as a field. **`IsDeterministicUtility` is not
needed**: a `Skeleton`'s utility is a number, so the utility vertex's conditional
expectation serves where print's *U(pa_U)* would, and
`utilityMean_eq_uval_of_isDeterministicUtility` is that specialisation.
-/
public theorem expectedUtility_eq_value (h : G.IsUnmediated)
    (h01 : ∀ b : Fin (dim G.utility), 0 ≤ G.uval b ∧ G.uval b ≤ 1) (π : G.Policy) :
    G.expectedUtility π
      = G.net.value (G.projectedSkeleton h01) (G.net.parents G.decision)
          (G.projectedPolicy π) (ProbMixture.dirac (Model.observationalProfile C dim)) :=
  (G.expectedUtility_eq_contextSum h π).trans (G.value_eq_contextSum h h01 π).symm

/-! ### Optimality and regret, carried across -/

/-- Every vertex has at least one state, so the decision does. `Model.optimalValue`
and `Model.regret` want it as an instance, and it is given a low priority because
its head is `Nonempty (Fin (dim G.decision))` -- a shape that any
`Nonempty (Fin n)` goal would otherwise try before the ones that will work. -/
public instance (priority := low) instNonemptyDecisionState
    (G : DecisionNetwork C dim 𝕜) : Nonempty (Fin (dim G.decision)) :=
  Fin.pos_iff_nonempty.mp (G.net.dim_pos G.decision)

/-- **The projection's policies are the diagram's policies.** The inverse of
`projectedPolicy`: a policy outside the graph reads *pa_D*, which is what the
decision vertex's table is allowed to read. -/
@[expose] public noncomputable def liftPolicy
    (ρ : AISafetyAtlas.Causal.Policy (dim := dim) (G.net.parents G.decision)
      (Fin (dim G.decision)) 𝕜) : G.Policy where
  prob := fun a v ↦ ρ.prob v a
  prob_nonneg := fun a v ↦ ρ.prob_nonneg v a
  prob_sum := fun v ↦ ρ.prob_sum v
  prob_parents := fun a v w hvw ↦ ρ.prob_parents v w a hvw

@[simp] public theorem projectedPolicy_liftPolicy
    (ρ : AISafetyAtlas.Causal.Policy (dim := dim) (G.net.parents G.decision)
      (Fin (dim G.decision)) 𝕜) :
    G.projectedPolicy (G.liftPolicy ρ) = ρ := rfl

/-- **The two optima are one optimum.** `Model.optimalValue` maximises over
policies outside the graph; `IsOptimal` maximises over the decision vertex's
tables. Because `liftPolicy` inverts `projectedPolicy`, the two ranges are the
same, so an optimal diagram policy attains the projection's optimal value. -/
public theorem optimalValue_eq_expectedUtility (h : G.IsUnmediated)
    (h01 : ∀ b : Fin (dim G.utility), 0 ≤ G.uval b ∧ G.uval b ≤ 1)
    {πStar : G.Policy} (hopt : G.IsOptimal πStar) :
    G.net.optimalValue (G.projectedSkeleton h01) (G.net.parents G.decision)
        (ProbMixture.dirac (Model.observationalProfile C dim))
      = G.expectedUtility πStar := by
  classical
  refine le_antisymm ?_ ?_
  · rw [← Model.value_bestPolicy G.net (G.projectedSkeleton h01) (G.net.parents G.decision)
      (ProbMixture.dirac (Model.observationalProfile C dim)),
      ← G.projectedPolicy_liftPolicy (G.net.bestPolicy (G.projectedSkeleton h01)
        (G.net.parents G.decision) (ProbMixture.dirac (Model.observationalProfile C dim))),
      ← G.expectedUtility_eq_value h h01]
    exact hopt _
  · rw [G.expectedUtility_eq_value h h01]
    exact Model.value_le_optimal G.net _ _ _ _

/-- **RE24 §2.2 regret, both ways of writing it.** *δ := E^{π*}[U] − E^π[U]* on
the diagram is `Model.regret` on print's projection. -/
public theorem regret_eq_value_regret (h : G.IsUnmediated)
    (h01 : ∀ b : Fin (dim G.utility), 0 ≤ G.uval b ∧ G.uval b ≤ 1)
    {πStar π : G.Policy} (hopt : G.IsOptimal πStar) :
    G.regret πStar π
      = G.net.regret (G.projectedSkeleton h01) (G.net.parents G.decision)
          (G.projectedPolicy π) (ProbMixture.dirac (Model.observationalProfile C dim)) := by
  rw [Model.regret, G.optimalValue_eq_expectedUtility h h01 hopt, regret,
    G.expectedUtility_eq_value h h01 π]

end DecisionNetwork

end AISafetyAtlas.Causal
