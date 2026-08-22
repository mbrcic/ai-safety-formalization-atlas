module

public import AISafetyAtlas.Causal.Model

/-!
# Pearl's causal Bayesian network, as a condition on a family

`AISafetyAtlas.Causal.Model` is Pearl's *formula*: a graph together with tables,
from which `Model.jointProb_hardInterventionProfile` computes the truncated
product of equation (1.37). Pearl's Definition 1.3.1 is the other direction. It
fixes a whole **family** of interventional distributions — one per hard
intervention — and asks when a DAG is *compatible* with it:

* the graph is a DAG;
* every member is Markov relative to `G`;
* a forced variable takes its forced value with probability one;
* the mechanism of an unintervened variable is the one it has observationally.

Nothing in the atlas said that, because the family was not an object. This
module builds it, and the three `No` rows in the Pearl section of
`docs/provenance/source-coverage-audit.md` were the same absence three times.

## The two things worth checking before trusting the rendering

**Pearl's conditions (iii) and (ii) are stated here on tables, not on
conditionals, and that is a fidelity decision rather than convenience.** Print
writes (iii) as `P_x(v_i | pa_i) = P(v_i | pa_i)`. A conditional is a quotient,
and `P(pa_i) = 0` is reachable — it is exactly what the margin conditions of
`Causal.MarginClass` exist to exclude, so it cannot be assumed away here. A
quotient rendering would be undefined or silently `0` on those fibres, and the
condition would stop biting precisely where a degenerate table needs constraining.
`ConditionalTables` carries the mechanisms as data instead, so (iii) is an
equation between tables and has no null-fibre hole.

**The existential is hoisted once, and that is what makes (iii) bite.** There is
one observational table family `q`, and each member is factorized by its own `r`
which must agree with `q` off the intervened set. Had the Markov clause carried a private
existential per member, no witness would tie the members together and (iii) would
constrain nothing: any family that factorized *somehow* would qualify.

## What is derived rather than assumed

`IsCausalBayesNetwork` is the three conditions. The truncated product is **not**
part of it — `eq_family_of_isCausalBayesNetwork` derives equation (1.37) from
them, as Pearl does, and `isCausalBayesNetwork_family` is the converse. Together
they say a family is a causal Bayesian network over `G` exactly when it is the
truncated product of some table family, which is the sense in which Definition
1.3.1 is a *semantics*: it determines every interventional distribution from the
graph and the mechanisms.

Not every interventional distribution is determined by the **observational** one,
and no claim here says otherwise. Where a parent configuration carries zero
observational mass its child's mechanism is unconstrained by `P ∅`, while
`do(pa)` still reads it. Determination is by `(G, q)`, which is what
`eq_family_of_isCausalBayesNetwork` states.

Equations (1.38) and (1.39) — Pearl's Properties 1 and 2 — are not in *this*
module. They compare *marginals* of two members, so they live where the
marginalization layer does: `Model.marginal_insert_parents` is (1.38) cleared of
denominators and `Model.marginal_singleton_do_parents` is (1.39). This module
supplies the semantics they are stated against.
-/

namespace AISafetyAtlas.Causal

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {dim : C → ℕ}

/-- **Pearl's `P_*`**: one distribution over assignments for each hard
intervention, indexed by the forced set and the forced values.

Hard interventions only, which is Definition 1.3.1's own index set.
`Model.jointProb` accepts arbitrary local maps and is wider than print there;
keeping this family narrow is what lets a statement about it grade against the
printed definition rather than past it. -/
public abbrev InterventionalFamily (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :=
  Finset C → Assignment C dim → Assignment C dim → 𝕜

/-- The mechanisms `P(v_i | pa_i)` as data: one simplex per variable per parent
configuration, reading only the declared parents. -/
public structure ConditionalTables (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (G : C → Finset C) where
  /-- The mechanism itself. -/
  table : (c : C) → Fin (dim c) → Assignment C dim → 𝕜
  /-- A mechanism reads only its declared parents. -/
  reads_parents : ∀ c a v w, (∀ p ∈ G c, v p = w p) → table c a v = table c a w
  /-- Mechanisms are nonnegative. -/
  nonneg : ∀ c a v, 0 ≤ table c a v
  /-- And normalized. -/
  sum_one : ∀ c v, ∑ a : Fin (dim c), table c a v = 1

/-- The family a graph and its mechanisms induce — Pearl equation (1.37). -/
@[expose] public def ConditionalTables.family {G : C → Finset C}
    (q : ConditionalTables C dim 𝕜 G) : InterventionalFamily C dim 𝕜 :=
  fun targets target v ↦
    ∏ c : C, if c ∈ targets then (if target c = v c then 1 else 0)
      else q.table c (v c) v

/-- The point-mass mechanism a forced variable carries: Pearl's condition (ii),
*"`P_x(v_i) = 1` for forced `v_i`"*, as a table. -/
@[expose] public def forcedTable (target : Assignment C dim) (c : C) :
    Fin (dim c) → Assignment C dim → 𝕜 :=
  fun a _ ↦ if target c = a then 1 else 0

/-- **Pearl, Definition 1.3.1.** `G` is a causal Bayesian network compatible
with the family `P`.

The four conjuncts are the printed ones. `q` is the observational mechanism
family; each member is factorized by its own `r`, whose forced coordinates are
point masses (condition ii) and whose free coordinates are `q`'s (condition iii).
Condition (i), Markov relative to `G`, is the factorization itself together with
`ConditionalTables`' own requirement that a table read only its parents. -/
@[expose] public def IsCausalBayesNetwork (G : C → Finset C)
    (P : InterventionalFamily C dim 𝕜) : Prop :=
  (∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c) ∧
    ∃ q : ConditionalTables C dim 𝕜 G,
      ∀ (targets : Finset C) (target : Assignment C dim),
        ∃ r : ConditionalTables C dim 𝕜 G,
          (∀ v, P targets target v = ∏ c : C, r.table c (v c) v) ∧
          (∀ c ∈ targets, r.table c = forcedTable target c) ∧
          (∀ c ∉ targets, r.table c = q.table c)

/-- **Equation (1.37), derived from Definition 1.3.1 rather than built.**

Pearl's own derivation: on the forced coordinates condition (ii) replaces the
mechanism by a point mass, on the free ones condition (iii) replaces it by the
observational mechanism, and condition (i) multiplies them. -/
public theorem eq_family_of_isCausalBayesNetwork {G : C → Finset C}
    {P : InterventionalFamily C dim 𝕜} (h : IsCausalBayesNetwork G P) :
    ∃ q : ConditionalTables C dim 𝕜 G, P = q.family := by
  obtain ⟨-, q, hq⟩ := h
  refine ⟨q, ?_⟩
  funext targets target v
  obtain ⟨r, hfac, hforced, hfree⟩ := hq targets target
  rw [hfac v, ConditionalTables.family]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  by_cases hc : c ∈ targets
  · rw [hforced c hc]
    simp [forcedTable, hc]
  · rw [hfree c hc]
    simp [hc]

/-- The converse: a truncated product is a causal Bayesian network over its own
graph. With the theorem above this is Definition 1.3.1's content as an `iff` —
a family is compatible with `G` exactly when it is the truncated product of some
mechanism family. -/
public theorem isCausalBayesNetwork_family {G : C → Finset C}
    (hG : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (q : ConditionalTables C dim 𝕜 G) :
    IsCausalBayesNetwork G q.family := by
  refine ⟨hG, q, fun targets target ↦ ?_⟩
  refine ⟨⟨fun c ↦ if c ∈ targets then forcedTable target c else q.table c,
    ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro c a v w hvw
    by_cases hc : c ∈ targets
    · simp [hc, forcedTable]
    · simpa [hc] using q.reads_parents c a v w hvw
  · intro c a v
    by_cases hc : c ∈ targets
    · by_cases hval : target c = a <;> simp [hc, forcedTable, hval]
    · simpa [hc] using q.nonneg c a v
  · intro c v
    by_cases hc : c ∈ targets
    · simp [hc, forcedTable]
    · simpa [hc] using q.sum_one c v
  · intro v
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    by_cases hc : c ∈ targets <;> simp [hc, forcedTable]
  · intro c hc
    simp [hc]
  · intro c hc
    simp [hc]

/-- **A family is a causal Bayesian network over `G` exactly when it is a
truncated product.** Definition 1.3.1 read as a semantics: the graph and the
mechanisms determine every interventional distribution. -/
public theorem isCausalBayesNetwork_iff {G : C → Finset C}
    (hG : ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c)
    (P : InterventionalFamily C dim 𝕜) :
    IsCausalBayesNetwork G P ↔ ∃ q : ConditionalTables C dim 𝕜 G, P = q.family := by
  refine ⟨eq_family_of_isCausalBayesNetwork, ?_⟩
  rintro ⟨q, rfl⟩
  exact isCausalBayesNetwork_family hG q

/-! ## Every atlas model is one -/

/-- A model's own mechanisms. -/
@[expose] public def Model.tables (M : Model C dim 𝕜) :
    ConditionalTables C dim 𝕜 M.parents where
  table := M.cpt
  reads_parents := M.cpt_parents
  nonneg := M.cpt_nonneg
  sum_one := M.cpt_sum

/-- The interventional family a model presents: its joint under each hard
intervention. -/
@[expose] public def Model.interventionalFamily (M : Model C dim 𝕜) :
    InterventionalFamily C dim 𝕜 :=
  fun targets target v ↦ M.jointProb (hardInterventionProfile targets target) v

/-- It is the truncated product of the model's own tables — which is
`jointProb_hardInterventionProfile` read as a statement about the family. -/
public theorem Model.interventionalFamily_eq (M : Model C dim 𝕜) :
    M.interventionalFamily = M.tables.family := by
  funext targets target v
  exact M.jointProb_hardInterventionProfile targets target v

/-- **Pearl Definition 1.3.1 holds of every model in the atlas kernel.** The
graph a model carries is compatible with the family the model presents, so the
constructive object really is an instance of the semantic one. -/
public theorem Model.isCausalBayesNetwork (M : Model C dim 𝕜) :
    IsCausalBayesNetwork M.parents M.interventionalFamily := by
  rw [M.interventionalFamily_eq]
  exact isCausalBayesNetwork_family M.acyclic M.tables

end AISafetyAtlas.Causal
