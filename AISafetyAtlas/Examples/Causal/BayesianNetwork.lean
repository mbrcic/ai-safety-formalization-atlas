module

public import AISafetyAtlas.Causal.BayesianNetwork
public import AISafetyAtlas.Causal.DiscreteMarginal
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import Mathlib.Analysis.SpecificLimits.Basic

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
  obtain ⟨q, hq⟩ := AISafetyAtlas.Causal.eq_family_of_isCausalBayesNetwork h
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

/-- **Pearl's condition is exactly "comes from a table family".** The forward
direction is what `edgeless_isCausalBayesNetwork` uses; the equivalence says
nothing else can satisfy Definition 1.3.1 on an acyclic graph, so the tables are
not one presentation among several. Run at the one-edge graph, whose acyclicity
is `g2_acyclic` and whose family is `uniformTables`. -/
public theorem g2_isCausalBayesNetwork_iff :
    IsCausalBayesNetwork G2 uniformTables.family ↔
      ∃ q : ConditionalTables (Fin 2) (binaryDim (Fin 2)) ℝ G2, uniformTables.family = q.family :=
  AISafetyAtlas.Causal.isCausalBayesNetwork_iff g2_acyclic uniformTables.family

/-! ## Discrete variables: a child with countably many values

Pearl's Definition 1.3.1 asks for discrete variables, not finite-valued ones.
`geomCopyTables` is a two-node network `A → B` over `ℝ` in which `A` is
geometric on `ℕ` (`P(A = n) = 1/2^(n+1)`) and `B` copies `A`: both variables take
countably many values, so no `Fin (dim c)` model states it. -/

/-- The graph `false → true`: `true` (the child `B`) has the one parent `false`
(the root `A`). -/
public def geomCopyGraph : Bool → Finset Bool := fun c ↦ if c then {false} else ∅

/-- `A` geometric on `ℕ`, `B` a copy of `A`. -/
public noncomputable def geomCopyTables :
    Discrete.ConditionalTables Bool (fun _ ↦ ℕ) ℝ geomCopyGraph where
  table c n v := if c then (if n = v false then 1 else 0) else 1 / 2 / 2 ^ n
  reads_parents c a v w h := by
    cases c
    · rfl
    · simp only [if_true]
      rw [h false (by simp [geomCopyGraph])]
  nonneg c a v := by
    cases c
    · simp only [Bool.false_eq_true, if_false]
      positivity
    · simp only [if_true]
      split_ifs <;> norm_num
  hasSum_one c v := by
    cases c
    · simpa using hasSum_geometric_two' (1 : ℝ)
    · simpa using hasSum_ite_eq (v false) (1 : ℝ)

/-- **Definition 1.3.1 holds at a countably-valued network**: the truncated
product of `geomCopyTables` is a causal Bayesian network over its graph, the
instance the `Fin`-valued layer cannot express. -/
public theorem geomCopy_isCausalBayesNetwork :
    Discrete.IsCausalBayesNetwork geomCopyGraph geomCopyTables.family :=
  AISafetyAtlas.Causal.Discrete.isCausalBayesNetwork_family
    ⟨fun c ↦ if c then 1 else 0, fun c p hp ↦ by
      cases c <;> simp_all [geomCopyGraph]⟩ geomCopyTables

/-- **Forcing both variables of the countably-valued network** leaves the point
mass, and an outcome function is evaluated at the forced value: Pearl's (1.37)
at `X = V`, here with `ℕ`-valued variables. -/
public theorem geomCopy_tsum_univ_mul (t : Bool → ℕ) (g : (Bool → ℕ) → ℝ) :
    ∑' v, geomCopyTables.family Finset.univ t v * g v = g t :=
  AISafetyAtlas.Causal.Discrete.IsCausalBayesNetwork.tsum_univ_mul
    geomCopy_isCausalBayesNetwork t g

/-- The `Fin`-valued Definition 1.3.1 is the discrete one at `Fin`-valued
variables, run on the one-edge model above. -/
public theorem g2_isCausalBayesNetwork_discrete :
    Discrete.IsCausalBayesNetwork (V := fun c : Fin 2 ↦ Fin (binaryDim (Fin 2) c)) G2
      uniformTables.family :=
  (AISafetyAtlas.Causal.Discrete.isCausalBayesNetwork_iff_discrete _).mp
    (AISafetyAtlas.Causal.isCausalBayesNetwork_family g2_acyclic uniformTables)

/-- Equation (1.37) derived at the countably-valued network: its family is the
truncated product of some discrete mechanism family. -/
example : ∃ q : Discrete.ConditionalTables Bool (fun _ ↦ ℕ) ℝ geomCopyGraph,
    geomCopyTables.family = q.family :=
  AISafetyAtlas.Causal.Discrete.eq_family_of_isCausalBayesNetwork geomCopy_isCausalBayesNetwork

/-- Definition 1.3.1 as a semantics, at the countably-valued network. -/
example : Discrete.IsCausalBayesNetwork geomCopyGraph geomCopyTables.family ↔
    ∃ q : Discrete.ConditionalTables Bool (fun _ ↦ ℕ) ℝ geomCopyGraph,
      geomCopyTables.family = q.family :=
  AISafetyAtlas.Causal.Discrete.isCausalBayesNetwork_iff
    ⟨fun c ↦ if c then 1 else 0, fun c p hp ↦ by cases c <;> simp_all [geomCopyGraph]⟩ _

/-- Forcing both `ℕ`-valued variables leaves the point mass. -/
example (t v : Bool → ℕ) :
    geomCopyTables.family Finset.univ t v = if v = t then 1 else 0 :=
  AISafetyAtlas.Causal.Discrete.IsCausalBayesNetwork.apply_univ
    geomCopy_isCausalBayesNetwork t v

example (t v : Bool → ℕ) :
    geomCopyTables.family Finset.univ t v = if v = t then 1 else 0 :=
  AISafetyAtlas.Causal.Discrete.ConditionalTables.family_univ geomCopyTables t v

/-! ### Pearl's Properties 1 and 2 on the geometric copy

Both variables take every value in `ℕ`, so neither property can be stated in the
`Fin`-valued layer. `AISafetyAtlas.Causal.DiscreteMarginal` states them here. -/

/-- Every member of the geometric copy's family is a probability distribution over
the assignments `Bool → ℕ`. -/
public theorem geomCopy_hasSum_one (targets : Finset Bool) (t : Bool → ℕ) :
    HasSum (geomCopyTables.family targets t) 1 :=
  Discrete.IsCausalBayesNetwork.hasSum_one geomCopy_isCausalBayesNetwork targets t

/-- **Property 2 at `B`**: setting `B`'s parent `A`, with or without forcing `A` a
second time, leaves `B`'s marginal unchanged. -/
public theorem geomCopy_property_two (t : Bool → ℕ) :
    Discrete.marginal geomCopyTables.family (geomCopyGraph true ∪ {false}) t {true} t =
      Discrete.marginal geomCopyTables.family (geomCopyGraph true) t {true} t :=
  Discrete.IsCausalBayesNetwork.marginal_do_parents_union geomCopy_isCausalBayesNetwork
    (c := true) (S := {false}) (by simp) t

/-- **Property 1 at `B`**, multiplied out: `P(b, a) = P(a) · P_a(b)`. -/
public theorem geomCopy_property_one (w : Bool → ℕ) :
    Discrete.marginal geomCopyTables.family ∅ w (insert true (geomCopyGraph true)) w =
      Discrete.marginal geomCopyTables.family ∅ w (geomCopyGraph true) w *
        Discrete.marginal geomCopyTables.family (geomCopyGraph true) w {true} w :=
  Discrete.IsCausalBayesNetwork.marginal_insert_parents geomCopy_isCausalBayesNetwork true w

/-- The mechanism-level forms on the same tables: the marginal of `B` under
`do(A)` is `B`'s table, and the observational joint of `B` and `A` factors through
it. The marginal series converges. -/
public theorem geomCopy_table_forms (w : Bool → ℕ) :
    Discrete.marginal geomCopyTables.family (geomCopyGraph true ∪ ∅) w {true} w
        = geomCopyTables.table true (w true) w ∧
      Discrete.marginal geomCopyTables.family ∅ w (insert true (geomCopyGraph true)) w
        = Discrete.marginal geomCopyTables.family ∅ w (geomCopyGraph true) w *
            geomCopyTables.table true (w true) w ∧
      HasSum (fun v : {v : Bool → ℕ // ∀ d ∈ ({true} : Finset Bool), v d = w d} =>
          geomCopyTables.family ∅ w v.1)
        (Discrete.marginal geomCopyTables.family ∅ w {true} w) := by
  have hG : ∃ rank : Bool → ℕ, ∀ c, ∀ p ∈ geomCopyGraph c, rank p < rank c :=
    ⟨fun c ↦ if c then 1 else 0, fun c p hp ↦ by cases c <;> simp_all [geomCopyGraph]⟩
  exact ⟨Discrete.ConditionalTables.marginal_singleton_do_parents hG geomCopyTables
      (c := true) (extra := ∅) (Finset.notMem_empty true) w,
    Discrete.ConditionalTables.marginal_insert_parents hG geomCopyTables true w,
    Discrete.ConditionalTables.hasSum_marginal hG geomCopyTables ∅ w {true} w⟩

end AISafetyAtlas.Examples.Causal.BayesianNetwork
