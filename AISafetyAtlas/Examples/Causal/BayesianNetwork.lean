module

public import AISafetyAtlas.Causal.BayesianNetwork
public import AISafetyAtlas.Examples.Causal.BehavioralCollision

/-!
# Worked model of Pearl's Definition 1.3.1

`AISafetyAtlas.Causal.BayesianNetwork` renders Definition 1.3.1 as a condition on
a family of interventional distributions. Two things about that rendering are
easy to assert and easy to get wrong, and this module checks both.

* **The kernel really is an instance.** `Model.isCausalBayesNetwork` says every
  atlas model presents a compatible family; `edgeless_isCausalBayesNetwork` runs
  it on a checked model rather than leaving it general.
* **Condition (iii) has teeth.** The invariance clause is the one that ties the
  members of the family together, and a rendering where each member carried its
  own private factorization would constrain nothing. `badFamily` is the witness:
  each of its two exhibited members *is* a truncated product — so conditions (i)
  and (ii) hold of them — and yet no single mechanism family works for both, so
  the family is not a causal Bayesian network.
-/

namespace AISafetyAtlas.Examples.Causal.BayesianNetwork

open AISafetyAtlas.Causal

/-! ## The kernel is an instance -/

/-- Pearl's Definition 1.3.1 holds of the checked edgeless model. -/
public theorem edgeless_isCausalBayesNetwork :
    IsCausalBayesNetwork AISafetyAtlas.Examples.Causal.edgeless.parents
      AISafetyAtlas.Examples.Causal.edgeless.interventionalFamily :=
  AISafetyAtlas.Examples.Causal.edgeless.isCausalBayesNetwork

/-! ## Condition (iii) has teeth

The graph below is the one-edge shape `0 → 1`. Two mechanism families live over
it: `uniformTables`, where every table is `1/2`, and `skewTables`, which differs
only in the child's mechanism. -/

/-- The one-edge graph `0 → 1`. -/
@[expose] public def G2 : Fin 2 → Finset (Fin 2) :=
  fun c ↦ if c = 1 then {0} else ∅

public theorem g2_acyclic : ∃ rank : Fin 2 → ℕ, ∀ c, ∀ p ∈ G2 c, rank p < rank c := by
  refine ⟨fun c ↦ c.val, fun c p hp ↦ ?_⟩
  by_cases hc : c = 1
  · subst hc
    simp [G2] at hp
    subst hp
    decide
  · simp [G2, hc] at hp

/-- Every mechanism uniform. -/
@[expose] public noncomputable def uniformTables :
    ConditionalTables (Fin 2) (binaryDim (Fin 2)) ℝ G2 where
  table := fun _ _ _ ↦ 1 / 2
  reads_parents := by intro c a v w _; rfl
  nonneg := by intro c a v; norm_num
  sum_one := by intro c v; norm_num

/-- The same root mechanism, a different child mechanism. -/
@[expose] public noncomputable def skewTables :
    ConditionalTables (Fin 2) (binaryDim (Fin 2)) ℝ G2 where
  table := fun c a _ ↦ if c = 1 then (if a = 0 then 1 / 4 else 3 / 4) else 1 / 2
  reads_parents := by intro c a v w _; rfl
  nonneg := by
    intro c a v
    by_cases hc : c = 1 <;> by_cases ha : a = 0 <;> norm_num [hc, ha]
  sum_one := by
    intro c v
    by_cases hc : c = 1 <;> norm_num [hc, Fin.sum_univ_two]

/-- **A family whose members are truncated products, but not all of the same
mechanisms.** The observational member uses `uniformTables`; every interventional
member uses `skewTables`. -/
@[expose] public noncomputable def badFamily :
    InterventionalFamily (Fin 2) (binaryDim (Fin 2)) ℝ :=
  fun targets target v ↦
    if targets = ∅ then uniformTables.family ∅ target v
    else skewTables.family targets target v

/-- Its observational member is a truncated product, so conditions (i) and (ii)
hold of that member. -/
public theorem badFamily_empty : badFamily ∅ = uniformTables.family ∅ := by
  funext target v
  simp [badFamily]

/-- So is the member that forces the root. -/
public theorem badFamily_singleton :
    badFamily {0} = skewTables.family {0} := by
  funext target v
  have h : ({0} : Finset (Fin 2)) ≠ ∅ := by decide
  simp only [badFamily, if_neg h]

/-- **And yet it is not a causal Bayesian network.** No single mechanism family
factorizes both members, which is exactly what condition (iii) demands and what a
per-member factorization would have failed to notice. -/
public theorem not_isCausalBayesNetwork_badFamily :
    ¬ IsCausalBayesNetwork G2 badFamily := by
  intro h
  obtain ⟨q, hq⟩ := eq_family_of_isCausalBayesNetwork h
  set v00 : Assignment (Fin 2) (binaryDim (Fin 2)) := fun _ ↦ 0 with hv00
  set v10 : Assignment (Fin 2) (binaryDim (Fin 2)) := fun c ↦ if c = 0 then 1 else 0 with hv10
  -- forcing the root reads the child's mechanism directly
  have hchild : q.table 1 0 v00 = 1 / 4 := by
    have := congrFun (congrFun (congrFun hq {0}) v00) v00
    rw [badFamily_singleton] at this
    simpa [ConditionalTables.family, skewTables, Fin.prod_univ_two, hv00] using this.symm
  -- the observational member then pins the root's mechanism
  have hroot : q.table 0 0 v00 = 1 := by
    have := congrFun (congrFun (congrFun hq ∅) v00) v00
    rw [badFamily_empty] at this
    simp only [ConditionalTables.family, uniformTables, Fin.prod_univ_two,
      Finset.notMem_empty, if_false] at this
    rw [hchild] at this
    norm_num at this
    linarith [this]
  have hzero : q.table 0 1 v00 = 0 := by
    have hsum := q.sum_one 0 v00
    rw [Fin.sum_univ_two] at hsum
    rw [hroot] at hsum
    linarith
  -- the root has no parents, so its mechanism cannot vary
  have hzero' : q.table 0 1 v10 = 0 := by
    rw [q.reads_parents 0 1 v10 v00 (by intro p hp; simp [G2] at hp)]
    exact hzero
  -- but the observational member needs it positive
  have := congrFun (congrFun (congrFun hq ∅) v10) v10
  rw [badFamily_empty] at this
  simp only [ConditionalTables.family, uniformTables, Fin.prod_univ_two,
    Finset.notMem_empty, if_false] at this
  rw [show v10 0 = 1 from by simp [hv10], hzero'] at this
  norm_num at this

end AISafetyAtlas.Examples.Causal.BayesianNetwork
