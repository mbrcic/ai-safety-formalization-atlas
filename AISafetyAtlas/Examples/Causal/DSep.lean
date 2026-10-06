module

public import AISafetyAtlas.Causal.DSep

/-!
# Where Definition 6 is wider than the library it is built on

The d-separation module states Everitt et al.'s Definition 6 at print's
generality, which admits `X`, `Y` and `Z` that overlap, while the upstream
`Causalean.Graph.DAG.dSep` requires the three to be pairwise disjoint. That is a claim
about a difference, and a difference nothing exhibits is a difference nobody has
checked. This module exhibits it.

Two general facts and one diagram:

* `dSep_of_subset_conditioning` — clause 3 of Definition 6 doing work. When
  every source node is already conditioned on, every path from `X` is blocked at
  its own first vertex, so `X` is d-separated from anything at all.
* `not_causalean_dSep_of_mem_inter` — the same configuration refutes the
  upstream predicate, for the reason that it is not a statement about paths:
  the disjointness is a conjunct of the definition.
* `edgeCID`, a two-vertex diagram with a single edge, on which both are
  instantiated, together with `edgeCID_not_dSep` showing the definition is not
  vacuously true.
* `edgeCID_not_dSep_self` and `edgeCID_dSep_self_of_conditioned` — the other
  half of clause 3, at `X ∩ Y` rather than at `X ∩ Z`: a set is not separated
  from itself until the shared node is conditioned on.

Taken together these say the widening is real rather than notational: there is a
diagram and a triple of sets at which `CID.DSep` holds and
`Causalean.Graph.DAG.dSep` fails, and the failure is not a disagreement about
d-separation but about what the predicate is allowed to be asked.

## And a second diagram, on a carrier that is not finite

`intChain` is the integer chain `Pa_n = {n - 1}`, the diagram
`AISafetyAtlas.Causal.chainParents_acyclic` is already stated for. It is here
because Definition 6 bounds no vertex set and the Bayes-Ball computation of it
does: nothing in `CID.DSep` can be asked about this diagram at all, and
`CID.DSepSet` and `CID.DSepPath` can. `intChain_not_dSepSet` and
`intChain_not_dSepPath` answer it in the negative and `intChain_dSepSet` in the
positive, so the generality the definition is stated at is exercised and not
merely available.

The two readings of *path* are exercised alongside it —
`AISafetyAtlas.Causal.CID.dSepSet_iff_dSepPath` says they agree — as is the
machinery the agreement runs on: `intChain_activated`,
`intChain_not_activated_one` and `intChain_not_blocked_iff_isActive`.
-/


namespace AISafetyAtlas.Examples.Causal.DSep

open AISafetyAtlas.Causal

section General

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Clause 3 of Definition 6.** If every node of `X` is conditioned on, then
`X` is d-separated from every `Y` by `Z`, in every diagram.

Print blocks a path when *"one or both of the endpoints is in `Z`"*, and here
every path out of `X` has its first endpoint in `Z`. No path property is
consulted: the conclusion holds for arbitrary `Y`. -/
public theorem dSep_of_subset_conditioning (G : CID V) {X : Finset V} (Y : Finset V)
    {Z : Finset V} (hXZ : X ⊆ Z) : G.DSep X Y Z := by
  have hempty : X \ Z = (∅ : Finset V) :=
    Finset.sdiff_eq_empty_iff_subset.mpr hXZ
  refine ⟨by simp [hempty], ?_⟩
  rintro ⟨p, -, -, hhead, -⟩
  obtain ⟨x, hx, -⟩ := Finset.mem_image.mp hhead
  rw [hempty] at hx
  simp at hx

/-- The upstream predicate cannot be asked about a source node that is also
conditioned on: disjointness is one of its conjuncts, so a single shared element
refutes it outright, whatever the diagram does. -/
public theorem not_causalean_dSep_of_mem_inter (G : CID V) {X Y Z : Finset V} {a : V}
    (haX : a ∈ X) (haZ : a ∈ Z) : ¬ (cidToDAG G).dSep X Y Z := by
  rintro ⟨-, hXZ, -, -⟩
  exact (Finset.disjoint_left.mp hXZ haX) haZ

/-- So on any diagram, at any triple where a source node is conditioned on, the
two predicates disagree: print's holds and upstream's fails.

This is the widening, stated once and for all rather than per diagram. -/
public theorem dSep_and_not_causalean_dSep (G : CID V) {X : Finset V} (Y : Finset V)
    {Z : Finset V} {a : V} (hXZ : X ⊆ Z) (haX : a ∈ X) :
    G.DSep X Y Z ∧ ¬ (cidToDAG G).dSep X Y Z :=
  ⟨dSep_of_subset_conditioning G Y hXZ,
    not_causalean_dSep_of_mem_inter G haX (hXZ haX)⟩

end General

/-- A two-vertex diagram with the single edge `0 → 1`, vertex `1` a utility
node. Small enough that every simple path is visible: there is exactly one, and
it has no intermediate vertex, so clauses 1 and 2 of Definition 6 never fire on
it and only clause 3 can block anything. Walks may of course revisit — `[0,1,0]`
is one — which is why the underlying predicate quantifies over lists. -/
@[expose] public noncomputable def edgeCID : CID (Fin 2) where
  parents := fun v ↦ if v = 1 then {0} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦ if v = 1 then NodeKind.utility else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

/-- On `edgeCID`, conditioning on the source separates it from the utility node,
and the upstream predicate refuses the question. -/
public theorem edgeCID_dSep_and_not_causalean :
    edgeCID.DSep {0} {1} {0} ∧ ¬ (cidToDAG edgeCID).dSep {0} {1} {0} :=
  dSep_and_not_causalean_dSep edgeCID {1} (a := 0) (Finset.Subset.refl _) (by simp)

/-- Conditioning on nothing, the source is **not** separated from the utility
node: the single edge is an active path. So `CID.DSep` is not vacuously true,
and `edgeCID_dSep_and_not_causalean` is not separation holding for want of any
path at all. -/
public theorem edgeCID_not_dSep : ¬ edgeCID.DSep {0} {1} (∅ : Finset (Fin 2)) := by
  intro h
  refine h.2 ⟨[0, 1], by simp, ⟨?_, ?_⟩, by simp, by simp⟩
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact Or.inl (by simp [cidToDAG, edgeCID])
  · intro i hi
    simp at hi

/-- **Clause 3 at a shared endpoint.** A set is not d-separated from itself by
the empty set: the trivial path at `0` runs from `{0}` to `{0}` and nothing
blocks it.

This is the part of Definition 6 that the `Disjoint (X \ Z) (Y \ Z)` conjunct
carries, and it is the reading under which footnote 5's *"potentially
overlapping sets"* has content at `X ∩ Y`. -/
public theorem edgeCID_not_dSep_self : ¬ edgeCID.DSep {0} {0} (∅ : Finset (Fin 2)) := by
  rintro ⟨hdisj, -⟩
  simp at hdisj

/-- Conditioning on the shared node restores separation, which is clause 3
doing the blocking rather than the sets being disjoint. -/
public theorem edgeCID_dSep_self_of_conditioned : edgeCID.DSep {0} {0} {0} :=
  dSep_of_subset_conditioning edgeCID {0} (Finset.Subset.refl _)

/-! ## Three more leaves, at `edgeCID` -/

/-- **The transported edge relation is the parent relation, at `edgeCID`.** -/
public theorem edgeCID_cidToDAG_edge :
    (cidToDAG edgeCID).edge 0 1 ↔ (0 : Fin 2) ∈ edgeCID.parents 1 :=
  cidToDAG_edge edgeCID 0 1

/-- **`X ∩ Y ⊆ Z` for any d-separated triple, at the witness already
established**: `edgeCID_dSep_self_of_conditioned` gives `DSep {0} {0} {0}`. -/
public theorem edgeCID_inter_subset_of_dSep :
    ({0} : Finset (Fin 2)) ∩ {0} ⊆ {0} :=
  CID.inter_subset_of_dSep edgeCID edgeCID_dSep_self_of_conditioned

/-- **The equivalence with the upstream predicate, at a pairwise-disjoint
triple.** `edgeCID_not_dSep` is exactly this pair with `Z = ∅`, so the
equivalence recovers a fact already on record through the route the module's
widening claim rests on. -/
public theorem edgeCID_dSep_iff_causalean :
    edgeCID.DSep {0} {1} (∅ : Finset (Fin 2)) ↔
      (cidToDAG edgeCID).dSep {0} {1} (∅ : Finset (Fin 2)) :=
  CID.dSep_iff_causalean edgeCID (by simp) (by simp)

/-! ## Definition 6 at print's generality, on a carrier that is not finite

Everything above this heading runs on `Fin 2`. The point of
`AISafetyAtlas.Causal.CID.DSepSet` is that Definition 6 needs no such bound, and
a definition whose generality is never exercised is a generality nobody has
checked. `intChain` is the integer chain — the same diagram
`AISafetyAtlas.Causal.chainParents_acyclic` is stated for — and Definition 6 is
asked and answered on it, in both directions, with no `Fintype` anywhere.
-/

section Print

variable {V : Type*} [DecidableEq V]

/-- **Clause 3, at print's generality.** A source set already conditioned on is
d-separated from anything, because every path out of it is blocked at its own
first vertex. No path property is consulted and no bound on `V` is used. -/
public theorem dSepSet_of_subset_conditioning (G : CID V) {X : Set V} (Y : Set V)
    {Z : Set V} (hXZ : X ⊆ Z) : G.DSepSet X Y Z := by
  rintro p - ⟨x, hxX, hx⟩ -
  exact Or.inr (Or.inr (Or.inl ⟨x, hXZ hxX, hx⟩))

end Print

/-- The integer chain `Pa_n = {n - 1}` as a diagram. Every vertex is a structure
node, so `utility_childless` is vacuous, and acyclicity is
`AISafetyAtlas.Causal.chainParents_acyclic` verbatim.

`ℤ` is not a `Fintype`, so nothing in `AISafetyAtlas.Causal.DSep`'s Bayes-Ball
half can be asked about this diagram at all. Definition 6 can. -/
@[expose] public def intChain : CID ℤ where
  parents := chainParents
  acyclic := chainParents_acyclic
  kind := fun _ ↦ NodeKind.structureNode
  utility_childless := by
    intro u hu
    exact absurd hu (by decide)

/-- Consecutive integers are adjacent in the chain. -/
public theorem intChain_uAdj : intChain.UAdj 0 1 :=
  Or.inl (by simp [intChain, chainParents])

/-- `[0, 1]` is a path of the chain. -/
public theorem intChain_isWalk : intChain.IsWalk [0, 1] := by
  intro i hi
  have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
  subst hi0
  exact intChain_uAdj

/-- **Definition 6 is not vacuous on an infinite diagram.** The edge `0 → 1` is
an unblocked path, so the empty set does not d-separate `{0}` from `{1}`. -/
public theorem intChain_not_dSepSet : ¬ intChain.DSepSet {0} {1} (∅ : Set ℤ) := by
  intro h
  rcases h [0, 1] intChain_isWalk ⟨0, rfl, by simp⟩ ⟨1, rfl, by simp⟩ with
    ⟨i, hi, -⟩ | ⟨i, hi, -⟩ | ⟨x, hx, -⟩ | ⟨y, hy, -⟩
  · simp only [List.length_cons, List.length_nil] at hi; omega
  · simp only [List.length_cons, List.length_nil] at hi; omega
  · exact hx
  · exact hy

/-- **And it holds where print says it holds**, by clause 3, on the same
infinite diagram. -/
public theorem intChain_dSepSet : intChain.DSepSet {0} Set.univ {0} :=
  dSepSet_of_subset_conditioning intChain Set.univ (Set.Subset.refl _)

/-- `X ∩ Y ⊆ Z` at print's generality, read off the witness above. -/
public theorem intChain_inter_subset_of_dSepSet :
    ({0} : Set ℤ) ∩ Set.univ ⊆ {0} :=
  CID.inter_subset_of_dSepSet intChain intChain_dSepSet

/-- The one-vertex path is a path, on the infinite chain. -/
public theorem intChain_isWalk_singleton : intChain.IsWalk [(0 : ℤ)] :=
  CID.isWalk_singleton intChain 0

/-- And it is blocked exactly by conditioning on its own vertex, which is clause
3 with nothing else available. -/
public theorem intChain_blocked_singleton :
    intChain.Blocked {(0 : ℤ)} [(0 : ℤ)] :=
  (CID.blocked_singleton_iff intChain {(0 : ℤ)} 0).mpr rfl

/-- **Clause 1's two conjuncts are one**, at a vertex of the chain: descent is
reflexive, so *"no descendant in `Z`"* already says *"not in `Z`"*. -/
public theorem intChain_blocked_collider_iff :
    ((0 : ℤ) ∉ ({0} : Set ℤ) ∧ ∀ w, intChain.IsDescendant 0 w → w ∉ ({0} : Set ℤ)) ↔
      ∀ w, intChain.IsDescendant 0 w → w ∉ ({0} : Set ℤ) :=
  CID.blocked_collider_iff intChain {(0 : ℤ)} 0

/-- **Clause 2 is clause 1's complement**, at the chain triple `0 → 1 → 2`:
adjacent on both sides, and a chain rather than a collider. -/
public theorem intChain_isChainOrFork_iff :
    intChain.IsChainOrFork 0 1 2 ↔ ¬ intChain.IsCollider 0 1 2 :=
  CID.isChainOrFork_iff_not_isCollider intChain intChain_uAdj
    (Or.inl (by simp [intChain, chainParents]))

/-- The chain triple is a chain, so the conditioned middle blocks it — print's
clause 2. -/
public theorem intChain_isChainOrFork : intChain.IsChainOrFork 0 1 2 :=
  Or.inl ⟨by simp [intChain, chainParents], by simp [intChain, chainParents]⟩

/-! ## The bridge, at `edgeCID`

`AISafetyAtlas.Causal.CID.dSepSet_iff_dSep` is what makes the `Finset` predicate
above a computation of the definition rather than a second definition. It is
exercised here at the witness already on record.
-/

/-- The transported undirected edge is print's, at `edgeCID`. -/
public theorem edgeCID_cidToDAG_uAdj :
    (cidToDAG edgeCID).UAdj 0 1 ↔ edgeCID.UAdj 0 1 :=
  cidToDAG_uAdj edgeCID 0 1

/-- The transported collider is print's, at `edgeCID`. -/
public theorem edgeCID_cidToDAG_isCollider :
    (cidToDAG edgeCID).IsCollider 0 1 0 ↔ edgeCID.IsCollider 0 1 0 :=
  cidToDAG_isCollider edgeCID 0 1 0

/-- **Upstream's collider-activation set is print's descendant condition**, at
`edgeCID`: the utility node `1` is in the ancestral closure of `{1}` because it
is its own descendant. -/
public theorem edgeCID_mem_bbZAncestors :
    (1 : Fin 2) ∈ (cidToDAG edgeCID).bbZAncestors {1} ↔
      ∃ z ∈ ({1} : Finset (Fin 2)), edgeCID.IsDescendant 1 z :=
  mem_bbZAncestors_iff edgeCID {1} 1

/-- **A path is unblocked exactly when it is active and misses `Z` at both
ends**, at the single edge of `edgeCID` with nothing conditioned on. -/
public theorem edgeCID_not_blocked_iff :
    ¬ edgeCID.Blocked (↑(∅ : Finset (Fin 2))) [0, 1] ↔
      (cidToDAG edgeCID).IsActiveWalk ∅ [0, 1] ∧
        (∀ x, ([0, 1] : List (Fin 2)).head? = some x → x ∉ (∅ : Finset (Fin 2))) ∧
        (∀ y, ([0, 1] : List (Fin 2)).getLast? = some y → y ∉ (∅ : Finset (Fin 2))) :=
  CID.not_blocked_iff edgeCID (by
    intro i hi
    have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    exact Or.inl (by simp [edgeCID]))

/-- **Definition 6 and its computation agree at `edgeCID`**, so
`edgeCID_dSep_self_of_conditioned` is a fact about print's definition and not
only about the Bayes-Ball predicate. -/
public theorem edgeCID_dSepSet_self_of_conditioned :
    edgeCID.DSepSet ↑({0} : Finset (Fin 2)) ↑({0} : Finset (Fin 2))
      ↑({0} : Finset (Fin 2)) :=
  (CID.dSepSet_iff_dSep edgeCID {0} {0} {0}).mpr edgeCID_dSep_self_of_conditioned

/-! ## Print's own word for a path, on the same two diagrams

`AISafetyAtlas.Causal.CID.dSepSet_iff_dSepPath` says reading Definition 6 over
paths and reading it over walks come to the same thing. Both readings are
exercised here, and so is the machinery the proof runs on.
-/

/-- A conditioned vertex activates itself, on the infinite chain. -/
public theorem intChain_activated : intChain.Activated {(0 : ℤ)} 0 :=
  CID.activated_of_mem intChain rfl

/-- With nothing conditioned on, nothing is activated. -/
public theorem intChain_not_activated : ¬ intChain.Activated (∅ : Set ℤ) 0 := by
  rintro ⟨z, hz, -⟩
  exact hz

/-- **Failure to activate travels forwards along an edge**, which is the step the
splice argument runs on. -/
public theorem intChain_not_activated_one : ¬ intChain.Activated (∅ : Set ℤ) 1 :=
  CID.not_activated_of_mem_parents intChain intChain_not_activated
    (by simp [intChain, chainParents])

/-- **Unblocked is active plus clear endpoints**, at the chain's single edge. -/
public theorem intChain_not_blocked_iff_isActive :
    ¬ intChain.Blocked (∅ : Set ℤ) [0, 1] ↔
      intChain.IsActive (∅ : Set ℤ) [0, 1] ∧
        (∀ x, ([0, 1] : List ℤ).head? = some x → x ∉ (∅ : Set ℤ)) ∧
        (∀ y, ([0, 1] : List ℤ).getLast? = some y → y ∉ (∅ : Set ℤ)) :=
  CID.not_blocked_iff_isActive intChain intChain_isWalk

/-- **Definition 6 under print's own word**, on a carrier with no `Fintype`: the
chain is not d-separated from its successor by nothing. -/
public theorem intChain_not_dSepPath : ¬ intChain.DSepPath {0} {1} (∅ : Set ℤ) :=
  fun h ↦ intChain_not_dSepSet ((intChain.dSepSet_iff_dSepPath {0} {1} ∅).mpr h)

/-- And it holds where clause 3 makes it hold, under the same reading. -/
public theorem intChain_dSepPath : intChain.DSepPath {0} Set.univ {0} :=
  (intChain.dSepSet_iff_dSepPath {0} Set.univ {0}).mp intChain_dSepSet

/-- **Print's Definition 6 and the Bayes-Ball computation, at `edgeCID`**, with
no step of the chain left implicit. -/
public theorem edgeCID_dSepPath_self_of_conditioned :
    edgeCID.DSepPath ↑({0} : Finset (Fin 2)) ↑({0} : Finset (Fin 2))
      ↑({0} : Finset (Fin 2)) :=
  (CID.dSepPath_iff_dSep edgeCID {0} {0} {0}).mpr edgeCID_dSep_self_of_conditioned

end AISafetyAtlas.Examples.Causal.DSep
