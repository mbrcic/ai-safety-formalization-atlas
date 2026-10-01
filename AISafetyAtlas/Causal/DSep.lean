module

public import AISafetyAtlas.Causal.StructuralModel
public import Causalean.Graph.DSep.Separation

/-!
# d-separation on a causal influence diagram

Everitt, Carey, Langlois, Ortega and Legg, *Agent Incentives: A Causal
Perspective*, AAAI 2021, Definition 6, after Verma and Pearl 1988.

> **Definition 6** (d-separation). *A path `p` is said to be d-separated by a
> set of nodes `Z` if and only if:*
> 1. *`p` contains a collider `X → W ← Y`, such that the middle node `W` is not
>    in `Z` and no descendants of `W` are in `Z`, or*
> 2. *`p` contains a chain `X → W → Y` or fork `X ← W → Y` where `W` is in `Z`,
>    or*
> 3. *one or both of the endpoints of `p` is in `Z`.*
>
> *A set `Z` is said to d-separate `X` from `Y` if and only if `Z` d-separates
> every path from a node in `X` to a node in `Y`.*

**Definition 6 is stated three times here, and two of the three are computations
of the first.** `CID.DSepPath` is print's sentence word for word: three clauses,
on `Set V`, over *paths*, on a carrier with no cardinality bound, which is all
print asks for. `CID.DSepSet` is the same over *walks*, and
`CID.dSepSet_iff_dSepPath` proves the two readings coincide — that is the
splicing argument, and it is why the choice of reading costs nothing. `CID.DSep`
is what both come to on a `Fintype`, where Bayes Ball can run, with
`CID.dSepSet_iff_dSep` and `CID.dSepPath_iff_dSep` as the converting lemmas.
Every consumer reads the last and is therefore, through those lemmas, a consumer
of print's own sentence.

The Bayes-Ball machinery is not built here. It is taken from `Causalean`, whose
`Causalean.DAG.IsActivePath` is print's clauses 1 and 2 read positively, and whose
`bbReachableVertices` computes it. That machinery is `Finset`-valued and asks for
`[Fintype V]` throughout, which is exactly why print's definition could not be
the imported predicate: importing it *is* the narrowing. This file supplies
print's definition, the carrier bridge, clause 3, and the two equivalences.

## Clause 3 is the whole content of this file

Upstream's `Causalean.DAG.IsActivePath` constrains the **intermediate** vertices of a path
only — its collider condition is indexed by `i + 2 < p.length`, so the two
endpoints are unconstrained. Print's clause 3 blocks a path outright when either
endpoint lies in `Z`. The two therefore disagree exactly when `X` or `Y` meets
`Z`, and upstream's `DAG.dSep` closes that gap the other way, by requiring `X`,
`Y` and `Z` to be pairwise disjoint in the definition itself.

Taking `DAG.dSep` as Definition 6 would be **narrower than print**, and print
says so itself. Footnote 5 of the paper reads *"Def. 6 defines d-separation for
potentially overlapping sets"* — the authors flag the overlapping case as
something their definition deliberately covers.

Definition 7, the first consumer, does **not** exercise that generality: it
conditions on `Pa^D ∪ {D} \ {X}`, removing `X` precisely so the sets stay
disjoint. That is a reason to state Definition 6 carefully, not a reason to
think the narrow form would have sufficed -- this row grades Definition 6, and
Definition 6 is what print wrote.

So `CID.DSep` is stated at print's generality, with clause 3 carried by removing
`Z` from both endpoint sets, and `dSep_iff_causalean` recovers upstream's
predicate under the disjointness it assumes. `Examples.Causal.DSep` exhibits a
diagram where the two disagree, so the generalisation is witnessed and not
merely asserted.

## What is not bridged

Only the graph layer. `Causalean.SCM` carries arbitrary measurable domains where
this repository's SCM is finite with real-valued marginals, so upstream's
do-calculus -- its rule-2 and rule-3 files and the global Markov property --
does not transfer at this repository's SCM. That is a model bridge across the
axes section 8 of the coverage audit records as open, and is not attempted here.

## Consumers

The requisite-observation module alongside this one is the first: Definition 7
is d-separation at one conditioning set. Everitt's Theorem 9 is the intended one beyond that. Theorem 18, already proved in
the incentive module alongside this one, needs no separation property and does
not read this file.
-/


namespace AISafetyAtlas.Causal

/-! ## Definition 6 as print writes it

Everything below the next heading needs `[Fintype V]`, because the Bayes-Ball
computation it is bridged to is a `Finset` algorithm. Print's Definition 6 needs
nothing of the kind: it quantifies over *a set of nodes* `Z` and over paths in a
graph whose vertex set the paper never bounds. This section is that statement,
on an arbitrary carrier, and `CID.dSepSet_iff_dSep` below is the equivalence
that makes the `Finset` form its computation rather than its definition.

`[DecidableEq V]` stays, because it is a parameter of `CID` itself and so is not
an axis this definition could drop on its own.
-/

section Print

variable {V : Type*} [DecidableEq V]

/-- Print's undirected edge, the parent relation read in either direction.
Definition 6's paths are undirected, so this is the relation they run along. -/
@[expose] public def CID.UAdj (G : CID V) (u v : V) : Prop :=
  u ∈ G.parents v ∨ v ∈ G.parents u

/-- Print's ***collider*** `X → W ← Y`: both outer vertices are parents of the
middle one. -/
@[expose] public def CID.IsCollider (G : CID V) (l m r : V) : Prop :=
  l ∈ G.parents m ∧ r ∈ G.parents m

/-- Print's ***chain*** `X → W → Y` and ***fork*** `X ← W → Y`, the two shapes
clause 2 lists, as one predicate. A chain is listed in both directions because
Definition 6's path is undirected. -/
@[expose] public def CID.IsChainOrFork (G : CID V) (l m r : V) : Prop :=
  (l ∈ G.parents m ∧ m ∈ G.parents r) ∨ (r ∈ G.parents m ∧ m ∈ G.parents l) ∨
    (m ∈ G.parents l ∧ m ∈ G.parents r)

/-- **Clause 2 is clause 1's complement on a path, and acyclicity is what makes
that true.**

On an adjacent triple the three shapes print names are exhaustive and exclusive.
Exhaustive is immediate from undirected adjacency. Exclusive is not: a chain
`X → W → Y` is also a collider when `Y → W` as well, and that is precisely a
two-cycle between `W` and `Y`, which `CID.acyclic` forbids.

So the negation in clause 2 may be written either way, and the definition below
transcribes print's *"chain or fork"* rather than *"not a collider"* — which is
what upstream's `Causalean.DAG.IsActivePath` writes. -/
public theorem CID.isChainOrFork_iff_not_isCollider (G : CID V) {l m r : V}
    (hlm : G.UAdj l m) (hmr : G.UAdj m r) :
    G.IsChainOrFork l m r ↔ ¬ G.IsCollider l m r := by
  constructor
  · rintro (⟨_, hr⟩ | ⟨_, hl⟩ | ⟨hl, _⟩) ⟨hcl, hcr⟩
    · exact G.acyclic m (Relation.TransGen.tail (Relation.TransGen.single hr) hcr)
    · exact G.acyclic m (Relation.TransGen.tail (Relation.TransGen.single hl) hcl)
    · exact G.acyclic m (Relation.TransGen.tail (Relation.TransGen.single hl) hcl)
  · intro hnc
    rcases hlm with hl | hl
    · rcases hmr with hr | hr
      · exact Or.inl ⟨hl, hr⟩
      · exact absurd ⟨hl, hr⟩ hnc
    · rcases hmr with hr | hr
      · exact Or.inr (Or.inr ⟨hl, hr⟩)
      · exact Or.inr (Or.inl ⟨hr, hl⟩)

/-- A path of Definition 6: consecutive vertices are undirected-adjacent.

**Walks, not paths.** Nothing here asks for `p.Nodup`, so this quantifies over
walks where print says *path*. `CID.DSepPath` is the other reading and
`CID.dSepSet_iff_dSepPath` proves they agree, so this is a convenience of
statement and not a restriction. -/
@[expose] public def CID.IsWalk (G : CID V) (p : List V) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < p.length),
    G.UAdj (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)

/-- **Definition 6, the three clauses, on one path.**

1. a collider whose middle node is outside `Z` and has no descendant in `Z`;
2. a chain or fork whose middle node is in `Z`;
3. an endpoint of `p` in `Z`.

**Clause 1's first conjunct is redundant and is kept anyway.** `CID.IsDescendant`
is reflexive on purpose — a vertex is its own descendant — so *"no descendants of
`W` are in `Z`"* already gives *"`W` is not in `Z`"*. Print writes both, and so
does this; `CID.blocked_collider_iff` is the collapse. -/
@[expose] public def CID.Blocked (G : CID V) (Z : Set V) (p : List V) : Prop :=
  (∃ (i : ℕ) (hi : i + 2 < p.length),
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) ∧
        p.get ⟨i + 1, by omega⟩ ∉ Z ∧
        ∀ w, G.IsDescendant (p.get ⟨i + 1, by omega⟩) w → w ∉ Z) ∨
    (∃ (i : ℕ) (hi : i + 2 < p.length),
      G.IsChainOrFork (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) ∧
        p.get ⟨i + 1, by omega⟩ ∈ Z) ∨
    (∃ x ∈ Z, p.head? = some x) ∨ (∃ y ∈ Z, p.getLast? = some y)

/-- Clause 1's two conjuncts are one, by reflexivity of descent. -/
public theorem CID.blocked_collider_iff (G : CID V) (Z : Set V) (m : V) :
    (m ∉ Z ∧ ∀ w, G.IsDescendant m w → w ∉ Z) ↔ ∀ w, G.IsDescendant m w → w ∉ Z :=
  ⟨And.right, fun h ↦ ⟨h m Relation.ReflTransGen.refl, h⟩⟩

/-! ### Blocking read positively

The splice argument below needs the *unblocked* side of a triple as a predicate
it can push along an edge, so clause 1's condition gets a name.
-/

/-- **`Z` is reachable from `m`**: some vertex of `Z` is a descendant of it. This
is print's clause 1 negated, by `CID.blocked_collider_iff`. -/
@[expose] public def CID.Activated (G : CID V) (Z : Set V) (m : V) : Prop :=
  ∃ z ∈ Z, G.IsDescendant m z

/-- A conditioned vertex activates itself, descent being reflexive. -/
public theorem CID.activated_of_mem (G : CID V) {Z : Set V} {m : V} (h : m ∈ Z) :
    G.Activated Z m :=
  ⟨m, h, Relation.ReflTransGen.refl⟩

/-- **Activation travels backwards along an edge, so its failure travels
forwards.** This is the step that makes the splice argument terminate: from an
unactivated vertex, every vertex downstream of it is unactivated too. -/
public theorem CID.not_activated_of_mem_parents (G : CID V) {Z : Set V} {v c : V}
    (h : ¬ G.Activated Z v) (hvc : v ∈ G.parents c) : ¬ G.Activated Z c :=
  fun ⟨z, hz, hd⟩ ↦ h ⟨z, hz, Relation.ReflTransGen.head hvc hd⟩

/-- **A path with no blocking triple**, which is clauses 1 and 2 of Definition 6
denied at every interior vertex. Clause 3 is not part of it, so this is a
property of the path and not of where it ends. -/
@[expose] public def CID.IsActive (G : CID V) (Z : Set V) (p : List V) : Prop :=
  ∀ (i : ℕ) (hi : i + 2 < p.length),
    (G.IsCollider p[i] p[i + 1] p[i + 2] → G.Activated Z p[i + 1]) ∧
      (¬ G.IsCollider p[i] p[i + 1] p[i + 2] → p[i + 1] ∉ Z)

/-- **A path is unblocked exactly when it is active and misses `Z` at both
ends**, at print's generality and with no `Fintype` in sight. -/
public theorem CID.not_blocked_iff_isActive (G : CID V) {Z : Set V} {p : List V}
    (hw : G.IsWalk p) :
    ¬ G.Blocked Z p ↔
      G.IsActive Z p ∧ (∀ x, p.head? = some x → x ∉ Z) ∧
        (∀ y, p.getLast? = some y → y ∉ Z) := by
  simp only [CID.Blocked, not_or]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i hi ↦ ⟨fun hcol ↦ ?_, fun hncol hmZ ↦ ?_⟩,
      fun x hx hxZ ↦ h3 ⟨x, hxZ, hx⟩, fun y hy hyZ ↦ h4 ⟨y, hyZ, hy⟩⟩
    · by_contra hna
      exact h1 ⟨i, hi, hcol, fun hZ ↦ hna ⟨_, hZ, Relation.ReflTransGen.refl⟩,
        fun w hwd hwZ ↦ hna ⟨w, hwZ, hwd⟩⟩
    · refine h2 ⟨i, hi, ?_, hmZ⟩
      exact (G.isChainOrFork_iff_not_isCollider (hw i (by omega))
        (hw (i + 1) (by omega))).mpr hncol
  · rintro ⟨hact, hhead, hlast⟩
    refine ⟨?_, ?_, fun ⟨x, hxZ, hx⟩ ↦ hhead x hx hxZ, fun ⟨y, hyZ, hy⟩ ↦ hlast y hy hyZ⟩
    · rintro ⟨i, hi, hcol, -, hdesc⟩
      obtain ⟨z, hzZ, hzd⟩ := (hact i hi).1 hcol
      exact hdesc z hzd hzZ
    · rintro ⟨i, hi, hcf, hmZ⟩
      exact (hact i hi).2 ((G.isChainOrFork_iff_not_isCollider (hw i (by omega))
        (hw (i + 1) (by omega))).mp hcf) hmZ

/-- **Definition 6.** `Z` d-separates `X` from `Y` when it blocks every path
from a node in `X` to a node in `Y`.

Stated on `Set V` throughout, at an unbounded vertex set, which is print's
generality on both counts. `X`, `Y` and `Z` may overlap, which footnote 5 of the
paper flags as deliberate. -/
@[expose] public def CID.DSepSet (G : CID V) (X Y Z : Set V) : Prop :=
  ∀ p : List V, G.IsWalk p → (∃ x ∈ X, p.head? = some x) → (∃ y ∈ Y, p.getLast? = some y) →
    G.Blocked Z p

/-- **The one-vertex path, which is what clause 3 is for at `X ∩ Y`.**

`[v]` is a path with no triple in it, so clauses 1 and 2 are vacuous and clause 3
decides it alone. -/
public theorem CID.blocked_singleton_iff (G : CID V) (Z : Set V) (v : V) :
    G.Blocked Z [v] ↔ v ∈ Z := by
  constructor
  · rintro (⟨i, hi, -⟩ | ⟨i, hi, -⟩ | ⟨x, hx, hxv⟩ | ⟨y, hy, hyv⟩)
    · simp at hi
    · simp at hi
    · simp only [List.head?_cons, Option.some.injEq] at hxv
      subst hxv
      exact hx
    · simp only [List.getLast?_singleton, Option.some.injEq] at hyv
      subst hyv
      exact hy
  · exact fun hv ↦ Or.inr (Or.inr (Or.inl ⟨v, hv, rfl⟩))

/-- A one-vertex path is a path. -/
public theorem CID.isWalk_singleton (G : CID V) (v : V) : G.IsWalk [v] := by
  intro i hi
  simp at hi

/-- **The classical side condition, at print's generality.** A node shared by
`X` and `Y` and left unconditioned leaves the two d-connected, so d-separation
forces `X ∩ Y ⊆ Z`. -/
public theorem CID.inter_subset_of_dSepSet (G : CID V) {X Y Z : Set V}
    (h : G.DSepSet X Y Z) : X ∩ Y ⊆ Z := by
  intro v hv
  exact (G.blocked_singleton_iff Z v).mp
    (h [v] (G.isWalk_singleton v) ⟨v, hv.1, rfl⟩ ⟨v, hv.2, rfl⟩)


/-! ### From a walk to a path

Print says *path*; `CID.IsWalk` asks for no `p.Nodup`. The two give the same
d-separation, and this is the argument that says so: delete the segment between
two occurrences of a repeated vertex and the result is still active.

Exactly one triple of the spliced path is new — the one straddling the join —
and the case that is not immediate is the one where the repeated vertex `v` is
unactivated and both of its old triples are non-colliders. Then `v` points
forwards on both sides, and following the deleted segment forwards reaches its
far end unactivated with an incoming edge, which makes that far end a collider
and contradicts the original path's activity.
-/

omit [DecidableEq V] in
private theorem length_splice {p : List V} {i j : ℕ} (hij : i < j) (hj : j < p.length) :
    (p.take (i + 1) ++ p.drop (j + 1)).length + (j - i) = p.length := by
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

omit [DecidableEq V] in
private theorem getElem_splice_left {p : List V} {i j k : ℕ} (hk : k < i + 1)
    (hi : i < p.length) (h : k < (p.take (i + 1) ++ p.drop (j + 1)).length) :
    (p.take (i + 1) ++ p.drop (j + 1))[k] = p[k]'(by omega) := by
  rw [List.getElem_append_left (by simp only [List.length_take]; omega), List.getElem_take]

omit [DecidableEq V] in
private theorem getElem_splice_right {p : List V} {i j k : ℕ} (hk : i + 1 ≤ k)
    (hij : i < j) (hi : i < p.length)
    (h : k < (p.take (i + 1) ++ p.drop (j + 1)).length) :
    (p.take (i + 1) ++ p.drop (j + 1))[k] = p[k + (j - i)]'(by
      have := List.length_append (as := p.take (i + 1)) (bs := p.drop (j + 1))
      simp only [List.length_take, List.length_drop] at this
      omega) := by
  have hlen : (p.take (i + 1)).length = i + 1 := by simp only [List.length_take]; omega
  rw [List.getElem_append_right (by omega), List.getElem_drop]
  congr 1
  omega

/-- **From an unactivated vertex, an active path runs forwards to its end.**

At an unactivated vertex no triple can be a collider, since a collider there
would activate it; so each step keeps pointing forwards, and each vertex reached
is unactivated in turn. This is the engine of the splice argument's one hard
case. -/
private theorem forward_of_not_activated {G : CID V} {Z : Set V} {p : List V}
    (hw : G.IsWalk p) (hactive : G.IsActive Z p) {a : ℕ} (ha : a + 1 < p.length)
    (hna : ¬ G.Activated Z (p[a]'(by omega)))
    (hedge : (p[a]'(by omega)) ∈ G.parents (p[a + 1]'ha)) :
    ∀ k, a ≤ k → ∀ hk : k + 1 < p.length,
      (p[k]'(by omega)) ∈ G.parents (p[k + 1]'hk) ∧ ¬ G.Activated Z (p[k + 1]'hk) := by
  intro k hak
  induction k, hak using Nat.le_induction with
  | base => exact fun _ ↦ ⟨hedge, G.not_activated_of_mem_parents hna hedge⟩
  | succ k hak ih =>
    intro hk
    simp only [show k + 1 + 1 = k + 2 from rfl] at hk ⊢
    obtain ⟨hek, hnk⟩ := ih (by omega)
    have hncol : ¬ G.IsCollider (p[k]'(by omega)) (p[k + 1]'(by omega)) (p[k + 2]'hk) :=
      fun hcol ↦ hnk ((hactive k hk).1 hcol)
    have hedge' : (p[k + 1]'(by omega)) ∈ G.parents (p[k + 2]'hk) := by
      rcases hw (k + 1) (by omega) with h | h
      · exact h
      · exact absurd ⟨hek, h⟩ hncol
    exact ⟨hedge', G.not_activated_of_mem_parents hnk hedge'⟩

/-- A path never repeats a vertex twice in a row: that would be a self-loop, and
`CID.acyclic` forbids one. -/
private theorem walk_ne_succ {G : CID V} {p : List V} (hw : G.IsWalk p) {i : ℕ}
    (hi : i + 1 < p.length) : (p[i]'(by omega)) ≠ p[i + 1]'hi := by
  intro h
  have hadj : G.UAdj (p[i]'(by omega)) (p[i + 1]'hi) := hw i hi
  rw [h] at hadj
  rcases hadj with hadj | hadj <;>
    exact G.acyclic (p[i + 1]'hi) (Relation.TransGen.single hadj)

/-- Splicing out a repeated vertex leaves a path. -/
private theorem isWalk_splice {G : CID V} {p : List V} (hw : G.IsWalk p)
    {i j : ℕ} (hij : i + 1 < j) (hj : j < p.length)
    (heq : (p[i]'(by omega)) = p[j]'hj) :
    G.IsWalk (p.take (i + 1) ++ p.drop (j + 1)) := by
  have hqlen := length_splice (p := p) (i := i) (j := j) (by omega) hj
  intro k hk
  simp only [List.get_eq_getElem]
  rcases Nat.lt_or_ge k i with hc | hc
  · rw [getElem_splice_left (j := j) (by omega) (by omega) (by omega),
      getElem_splice_left (j := j) (by omega) (by omega) hk]
    exact hw k (by omega)
  rcases Nat.eq_or_lt_of_le hc with rfl | hc
  · rw [getElem_splice_left (j := j) (by omega) (by omega) (by omega),
      getElem_splice_right (j := j) (by omega) (by omega) (by omega) hk]
    simp only [show i + 1 + (j - i) = j + 1 from by omega]
    rw [heq]
    exact hw j (by omega)
  · rw [getElem_splice_right (j := j) (by omega) (by omega) (by omega) (by omega),
      getElem_splice_right (j := j) (by omega) (by omega) (by omega) hk]
    simp only [show k + 1 + (j - i) = k + (j - i) + 1 from by omega]
    exact hw (k + (j - i)) (by omega)

/-- **Splicing out a repeated vertex leaves the path active.**

Exactly one triple is new, the one straddling the join, and it is the second
case below. The others are old triples of `p` under a shift. -/
private theorem isActive_splice {G : CID V} {Z : Set V} {p : List V}
    (hw : G.IsWalk p) (hactive : G.IsActive Z p)
    {i j : ℕ} (hij : i + 1 < j) (hj : j < p.length)
    (heq : (p[i]'(by omega)) = p[j]'hj) :
    G.IsActive Z (p.take (i + 1) ++ p.drop (j + 1)) := by
  have hqlen := length_splice (p := p) (i := i) (j := j) (by omega) hj
  intro k hk
  rcases Nat.lt_or_ge (k + 2) (i + 1) with hc | hc
  · rw [getElem_splice_left (j := j) (by omega) (by omega) (by omega),
      getElem_splice_left (j := j) (by omega) (by omega) (by omega),
      getElem_splice_left (j := j) (by omega) (by omega) hk]
    exact hactive k (by omega)
  rcases Nat.lt_or_ge k i with hc2 | hc2
  · -- `k + 1 = i`: the one new triple, straddling the join.
    have hki : k + 1 = i := by omega
    have hjlen : j + 1 < p.length := by omega
    rw [getElem_splice_left (j := j) (by omega) (by omega) (by omega),
      getElem_splice_left (j := j) (by omega) (by omega) (by omega),
      getElem_splice_right (j := j) (by omega) (by omega) (by omega) hk]
    simp only [show k + 2 + (j - i) = j + 1 from by omega, hki]
    by_cases hvZ : (p[i]'(by omega : i < p.length)) ∈ Z
    · -- The repeated vertex is conditioned on, so both old triples are colliders.
      have hT1 : G.IsCollider (p[k]'(by omega)) (p[i]'(by omega)) (p[i + 1]'(by omega)) := by
        by_contra hnc
        refine ((hactive k (by omega)).2 ?_) ?_
        · simp only [hki, show k + 2 = i + 1 from by omega]; exact hnc
        · simp only [hki]; exact hvZ
      have hT2 : G.IsCollider (p[j - 1]'(by omega)) (p[j]'hj) (p[j + 1]'hjlen) := by
        by_contra hnc
        refine ((hactive (j - 1) (by omega)).2 ?_) ?_
        · simp only [show j - 1 + 1 = j from by omega, show j - 1 + 2 = j + 1 from by omega]
          exact hnc
        · simp only [show j - 1 + 1 = j from by omega, ← heq]
          exact hvZ
      exact ⟨fun _ ↦ G.activated_of_mem hvZ, fun hnc ↦ absurd ⟨hT1.1, heq ▸ hT2.2⟩ hnc⟩
    · -- The repeated vertex is not conditioned on; a collider there must activate it.
      refine ⟨fun hcol ↦ ?_, fun _ ↦ hvZ⟩
      by_contra hna
      have hedge : (p[i]'(by omega)) ∈ G.parents (p[i + 1]'(by omega)) := by
        rcases hw i (by omega) with h | h
        · exact h
        · refine absurd ((hactive k (by omega)).1 ?_) ?_
          · simp only [hki, show k + 2 = i + 1 from by omega]; exact ⟨hcol.1, h⟩
          · simp only [hki]; exact hna
      have hfwd := forward_of_not_activated hw hactive (a := i) (by omega) hna hedge
        (j - 1) (by omega) (by omega)
      refine hna (heq ▸ ?_)
      have hcol2 : G.IsCollider (p[j - 1]'(by omega)) (p[j]'hj) (p[j + 1]'hjlen) := by
        refine ⟨?_, ?_⟩
        · have := hfwd.1
          simp only [show j - 1 + 1 = j from by omega] at this
          exact this
        · rw [← heq]; exact hcol.2
      have := (hactive (j - 1) (by omega)).1 (by
        simp only [show j - 1 + 1 = j from by omega, show j - 1 + 2 = j + 1 from by omega]
        exact hcol2)
      simp only [show j - 1 + 1 = j from by omega] at this
      exact this
  rcases Nat.eq_or_lt_of_le hc2 with rfl | hc2
  · -- `k = i`: the old triple at `j`.
    rw [getElem_splice_left (j := j) (by omega) (by omega) (by omega),
      getElem_splice_right (j := j) (by omega) (by omega) (by omega) (by omega),
      getElem_splice_right (j := j) (by omega) (by omega) (by omega) hk]
    simp only [show i + 1 + (j - i) = j + 1 from by omega,
      show i + 2 + (j - i) = j + 2 from by omega, heq]
    exact hactive j (by omega)
  · -- Past the join: an old triple, shifted.
    rw [getElem_splice_right (j := j) (by omega) (by omega) (by omega) (by omega),
      getElem_splice_right (j := j) (by omega) (by omega) (by omega) (by omega),
      getElem_splice_right (j := j) (by omega) (by omega) (by omega) hk]
    simp only [show k + 1 + (j - i) = k + (j - i) + 1 from by omega,
      show k + 2 + (j - i) = k + (j - i) + 2 from by omega]
    exact hactive (k + (j - i)) (by omega)

omit [DecidableEq V] in
/-- Splicing keeps the first vertex: the kept prefix is nonempty. -/
private theorem head?_splice {p : List V} {i j : ℕ} (hij : i + 1 < j) (hj : j < p.length) :
    (p.take (i + 1) ++ p.drop (j + 1)).head? = p.head? := by
  have hqlen := length_splice (p := p) (i := i) (j := j) (by omega) hj
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?,
    List.getElem?_eq_getElem (show 0 < (p.take (i + 1) ++ p.drop (j + 1)).length by omega),
    List.getElem?_eq_getElem (show 0 < p.length by omega),
    getElem_splice_left (j := j) (by omega) (by omega) (by omega)]

omit [DecidableEq V] in
/-- And the last: either the dropped suffix is nonempty and carries it, or the
repetition was at the very end and the kept prefix ends on the same vertex. -/
private theorem getLast?_splice {p : List V} {i j : ℕ} (hij : i + 1 < j) (hj : j < p.length)
    (heq : (p[i]'(by omega)) = p[j]'hj) :
    (p.take (i + 1) ++ p.drop (j + 1)).getLast? = p.getLast? := by
  have hqlen := length_splice (p := p) (i := i) (j := j) (by omega) hj
  have hqge : i + 1 ≤ (p.take (i + 1) ++ p.drop (j + 1)).length := by
    simp only [List.length_append, List.length_take]; omega
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (show
      (p.take (i + 1) ++ p.drop (j + 1)).length - 1 <
        (p.take (i + 1) ++ p.drop (j + 1)).length by omega),
    List.getElem?_eq_getElem (show p.length - 1 < p.length by omega)]
  rcases Nat.lt_or_ge ((p.take (i + 1) ++ p.drop (j + 1)).length - 1) (i + 1) with hc | hc
  · have hq : (p.take (i + 1) ++ p.drop (j + 1)).length = i + 1 := by omega
    rw [getElem_splice_left (j := j) hc (by omega) (by omega)]
    simp only [hq, Nat.add_sub_cancel, show p.length - 1 = j from by omega]
    exact congrArg some heq
  · rw [getElem_splice_right (j := j) hc (by omega) (by omega) (by omega)]
    simp only [show (p.take (i + 1) ++ p.drop (j + 1)).length - 1 + (j - i) = p.length - 1
      from by omega]

omit [DecidableEq V] in
/-- A list that is not `Nodup` repeats a vertex at two indices. -/
private theorem exists_repeat {p : List V} (h : ¬ p.Nodup) :
    ∃ i j, ∃ _ : i < j, ∃ hj : j < p.length, (p[i]'(by omega)) = p[j]'hj := by
  rw [List.nodup_iff_injective_get] at h
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp h
  rcases lt_or_gt_of_ne (fun hh : a = b ↦ hne hh) with hlt | hlt
  · exact ⟨a.1, b.1, hlt, b.2, by simpa using hab⟩
  · exact ⟨b.1, a.1, hlt, a.2, by simpa using hab.symm⟩

/-- **Every active path has an active `Nodup` path with the same endpoints.**

Induction on the length: a repeated vertex is spliced out, which shortens the
list, and `isWalk_splice`, `isActive_splice`, `head?_splice` and
`getLast?_splice` say the four properties survive. -/
private theorem exists_nodup_aux {G : CID V} {Z : Set V} :
    ∀ (n : ℕ) (p : List V), p.length ≤ n → G.IsWalk p → G.IsActive Z p →
      ∃ q : List V, q.Nodup ∧ G.IsWalk q ∧ G.IsActive Z q ∧
        q.head? = p.head? ∧ q.getLast? = p.getLast? := by
  intro n
  induction n with
  | zero =>
    intro p hp hw ha
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], List.nodup_nil, hw, ha, rfl, rfl⟩
  | succ n ih =>
    intro p hp hw ha
    by_cases hnd : p.Nodup
    · exact ⟨p, hnd, hw, ha, rfl, rfl⟩
    obtain ⟨i, j, hij, hj, heq⟩ := exists_repeat hnd
    have hij' : i + 1 < j := by
      rcases Nat.lt_or_ge (i + 1) j with h | h
      · exact h
      · exfalso
        have hji : j = i + 1 := by omega
        subst hji
        exact walk_ne_succ hw hj heq
    have hqlen := length_splice (p := p) (i := i) (j := j) (by omega) hj
    obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ :=
      ih (p.take (i + 1) ++ p.drop (j + 1)) (by omega)
        (isWalk_splice hw hij' hj heq) (isActive_splice hw ha hij' hj heq)
    exact ⟨q, hq1, hq2, hq3, hq4.trans (head?_splice hij' hj),
      hq5.trans (getLast?_splice hij' hj heq)⟩

/-- **Definition 6 with print's own word.** `Z` d-separates `X` from `Y` when it
blocks every *path* — no repeated vertex — from a node in `X` to a node in `Y`.

`CID.dSepSet_iff_dSepPath` proves this is `CID.DSepSet`, so the choice of
reading costs nothing and neither statement is narrower than the other. -/
@[expose] public def CID.DSepPath (G : CID V) (X Y Z : Set V) : Prop :=
  ∀ p : List V, p.Nodup → G.IsWalk p → (∃ x ∈ X, p.head? = some x) →
    (∃ y ∈ Y, p.getLast? = some y) → G.Blocked Z p

/-- **Print's *path* and this file's *walk* give the same d-separation.**

One direction is free, a path being a walk. The other is the splicing argument:
an unblocked walk from `X` to `Y` yields an unblocked path from `X` to `Y` by
deleting the segment between two occurrences of a repeated vertex.

This is the axis the coverage audit carried open on Definitions 6 and 7 from
2026-09-09. Upstream supplies nothing to reuse — `Causalean.DAG.IsActivePath`
takes a bare `List V` and no file under `Causalean/Graph/` mentions `Nodup`. -/
public theorem CID.dSepSet_iff_dSepPath (G : CID V) (X Y Z : Set V) :
    G.DSepSet X Y Z ↔ G.DSepPath X Y Z := by
  constructor
  · exact fun h p _ hw hx hy ↦ h p hw hx hy
  · intro h p hw hx hy
    by_contra hb
    obtain ⟨hactive, hhead, hlast⟩ := (G.not_blocked_iff_isActive hw).mp hb
    obtain ⟨q, hnd, hqw, hqa, hqh, hql⟩ := exists_nodup_aux p.length p le_rfl hw hactive
    refine (G.not_blocked_iff_isActive hqw).mpr ⟨hqa, ?_, ?_⟩
      (h q hnd hqw (by rw [hqh]; exact hx) (by rw [hql]; exact hy))
    · intro x hx'; exact hhead x (hqh ▸ hx')
    · intro y hy'; exact hlast y (hql ▸ hy')

end Print

/-! ## The Bayes-Ball computation, on a finite carrier -/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A `CID` viewed as a `Causalean.DAG` on the same carrier.

`u` is an edge into `v` exactly when `u` is a parent of `v`, and acyclicity is
the same proposition on both sides, so `CID.acyclic` is the field verbatim.
Decidability of the edge relation is supplied classically: `CID.parents` is a
`Set`, carrying no decidability of its own, and nothing here is evaluated. -/
@[expose] public noncomputable def cidToDAG (G : CID V) : Causalean.DAG V where
  edge := fun u v ↦ u ∈ G.parents v
  decEdge := fun _ _ ↦ Classical.propDecidable _
  acyclic := G.acyclic

/-- The transported edge relation is the parent relation, definitionally. -/
public theorem cidToDAG_edge (G : CID V) (u v : V) :
    (cidToDAG G).edge u v ↔ u ∈ G.parents v := Iff.rfl

/-- **Definition 6.** `Z` d-separates `X` from `Y` when every path from a node
in `X` to a node in `Y` is blocked.

Clauses 1 and 2 are `Causalean.DAG.IsActivePath` read negatively. Clause 3 —
*"one or both of the endpoints of `p` is in `Z`"* — is carried twice, because it
has two jobs on overlapping sets:

* **`X` or `Y` meeting `Z`**: removing `Z` from both endpoint sets. A path with
  an endpoint in `Z` is blocked, so only paths between `X \ Z` and `Y \ Z` can
  be active.
* **`X` meeting `Y`**: the `Disjoint (X \ Z) (Y \ Z)` conjunct. For
  `x ∈ X ∩ Y` the trivial path `[x]` runs from a node of `X` to a node of `Y`,
  clauses 1 and 2 are vacuous on it for want of a triple, and clause 3 blocks it
  exactly when `x ∈ Z`. So an unconditioned shared node leaves the sets
  d-connected.

**Print does not settle the length convention here and this is the reading the
footnote forces.** *"A directed path (of length at least zero)"* is said of the
directed notion; Definition 6's `p` is undirected and print fixes nothing. Under
the other reading there is no path from `x` to itself at all, an unconditioned
shared node would leave the sets d-separated, and footnote 5's *"potentially
overlapping sets"* would have no content at `X ∩ Y`. Upstream reads it the same
way: `Disjoint X Y` is a conjunct of `DAG.dSep`, which is clause 3 on the
trivial path and not a refusal to answer.

Stated at print's generality, which admits overlapping `X`, `Y` and `Z`.

**The walk reading is not a restriction**, though neither this predicate nor
upstream's asks for `p.Nodup`. An active walk exists exactly when an active path
does — the standard fact Bayes-Ball correctness already rests on, formalized
here as `CID.dSepSet_iff_dSepPath` because upstream carries no path machinery at
all. -/
@[expose] public noncomputable def CID.DSep (G : CID V) (X Y Z : Finset V) : Prop :=
  Disjoint (X \ Z) (Y \ Z) ∧
    ¬ (cidToDAG G).HasActivePath (X \ Z) (Y \ Z) Z

/-- An active path between two sets is exactly a failure of Bayes-Ball
disjointness. This is upstream's correctness theorem repackaged, and it needs no
disjointness hypothesis of its own. -/
public theorem hasActivePath_iff_not_disjoint (G : CID V) (A B Z : Finset V) :
    (cidToDAG G).HasActivePath A B Z ↔
      ¬ Disjoint ((cidToDAG G).bbReachableVertices Z A) B := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨p, hlen, hact, hhead, hlast⟩
    obtain ⟨x, hxA, hx⟩ := Finset.mem_image.mp hhead
    obtain ⟨y, hyB, hy⟩ := Finset.mem_image.mp hlast
    refine ⟨y, ?_, hyB⟩
    exact ((cidToDAG G).bbReachableVertices_iff_activePath A Z y).mpr
      ⟨x, hxA, p, hlen, hact, hx.symm, hy.symm⟩
  · rintro ⟨y, hy, hyB⟩
    obtain ⟨x, hxA, p, hlen, hact, hhead, hlast⟩ :=
      ((cidToDAG G).bbReachableVertices_iff_activePath A Z y).mp hy
    exact ⟨p, hlen, hact, Finset.mem_image.mpr ⟨x, hxA, hhead.symm⟩,
      Finset.mem_image.mpr ⟨y, hyB, hlast.symm⟩⟩

/-- Definition 6 computed by Bayes Ball. This is what makes `CID.DSep`
decidable. -/
public theorem CID.dSep_iff_bbReachable (G : CID V) (X Y Z : Finset V) :
    G.DSep X Y Z ↔
      Disjoint (X \ Z) (Y \ Z) ∧
        Disjoint ((cidToDAG G).bbReachableVertices Z (X \ Z)) (Y \ Z) := by
  rw [CID.DSep, hasActivePath_iff_not_disjoint, not_not]

/-- d-separation is decidable, through the Bayes-Ball characterisation rather
than by searching paths. -/
public noncomputable instance (G : CID V) (X Y Z : Finset V) : Decidable (G.DSep X Y Z) :=
  decidable_of_iff _ (G.dSep_iff_bbReachable X Y Z).symm

/-- **The classical side condition falls out as a theorem.**

d-separation is usually stated only for pairwise disjoint sets, and *"`X` and
`Y` d-separated by `Z` implies `X ∩ Y ⊆ Z`"* is then imposed as a hypothesis or
left implicit. Here it is proved: clause 3 blocks the trivial path at a shared
node exactly when that node is conditioned on, so a shared node outside `Z`
leaves the sets d-connected.

This is the sharpest evidence that the length-zero reading of Definition 6 is
the right one. Under the other reading the statement below would be false, and
the standard fact about d-separation would fail of the atlas's rendering of
it. -/
public theorem CID.inter_subset_of_dSep (G : CID V) {X Y Z : Finset V}
    (h : G.DSep X Y Z) : X ∩ Y ⊆ Z := by
  intro v hv
  rw [Finset.mem_inter] at hv
  by_contra hvZ
  exact (Finset.disjoint_left.mp h.1 (Finset.mem_sdiff.mpr ⟨hv.1, hvZ⟩))
    (Finset.mem_sdiff.mpr ⟨hv.2, hvZ⟩)

/-- **Where print is wider than the library.** At pairwise disjoint sets,
Definition 6 is upstream's `dSep`.

Only two disjointness hypotheses are needed, not three. `Disjoint X Y` is *not*
assumed: it appears on both sides — as upstream's first conjunct, and here as
clause 3 on the trivial path — so it is content the two definitions share rather
than a restriction either needs. What upstream additionally requires, and print
answers instead, is `X` and `Y` being disjoint from `Z`.

Under those two the predicates agree, so every upstream lemma about `dSep`
transfers to `CID.DSep` by rewriting along this equivalence. -/
public theorem CID.dSep_iff_causalean (G : CID V) {X Y Z : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    G.DSep X Y Z ↔ (cidToDAG G).dSep X Y Z := by
  have hX : X \ Z = X := Finset.sdiff_eq_self_of_disjoint hXZ
  have hY : Y \ Z = Y := Finset.sdiff_eq_self_of_disjoint hYZ
  rw [CID.dSep_iff_bbReachable, hX, hY, Causalean.DAG.dSep]
  exact ⟨fun h ↦ ⟨h.1, hXZ, hYZ, h.2⟩, fun h ↦ ⟨h.1, h.2.2.2⟩⟩

/-! ## Print's definition and the computation are the same predicate

`CID.dSepSet_iff_dSep` is the converting lemma the coverage audit asks for when
a definition is graded at print's generality and computed at less: Definition 6
is `CID.DSepSet`, and `CID.DSep` is what it comes to on a finite carrier, where
Bayes Ball can run.
-/

/-- The transported undirected edge is print's. -/
public theorem cidToDAG_uAdj (G : CID V) (u v : V) :
    (cidToDAG G).UAdj u v ↔ G.UAdj u v := Iff.rfl

/-- The transported collider is print's. -/
public theorem cidToDAG_isCollider (G : CID V) (l m r : V) :
    (cidToDAG G).IsCollider l m r ↔ G.IsCollider l m r := Iff.rfl

/-- **Upstream's collider-activation set is print's clause 1, negated.**

`bbZAncestors Z` is the ancestral closure of `Z`, and a vertex lies in it exactly
when some vertex of `Z` is one of its descendants — which is the failure of
*"`W` is not in `Z` and no descendants of `W` are in `Z`"*. The reflexive case
carries the `W ∈ Z` half, by `CID.blocked_collider_iff`. -/
public theorem mem_bbZAncestors_iff (G : CID V) (Z : Finset V) (m : V) :
    m ∈ (cidToDAG G).bbZAncestors Z ↔ ∃ z ∈ Z, G.IsDescendant m z := by
  rw [Causalean.DAG.bbZAncestors, Causalean.DAG.ancestralSet, Finset.mem_union]
  constructor
  · rintro (hm | hm)
    · exact ⟨m, hm, Relation.ReflTransGen.refl⟩
    · simp only [Causalean.DAG.ancestorsSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hm
      obtain ⟨z, hz, ha⟩ := hm
      exact ⟨z, hz, (((cidToDAG G).isAncestor_iff_transGen).mp ha).to_reflTransGen⟩
  · rintro ⟨z, hz, hd⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hd with rfl | ht
    · exact Or.inl hz
    · refine Or.inr ?_
      simp only [Causalean.DAG.ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨z, hz, ((cidToDAG G).isAncestor_iff_transGen).mpr ht⟩

/-- **A path is unblocked exactly when it is active and misses `Z` at both
ends.**

Clauses 1 and 2 negated are upstream's collider condition — clause 1 through
`mem_bbZAncestors_iff`, clause 2 through `CID.isChainOrFork_iff_not_isCollider`,
which is where acyclicity is spent. Clause 3 negated is the two endpoint
conditions, which upstream carries in `dSep`'s disjointness hypotheses instead. -/
public theorem CID.not_blocked_iff (G : CID V) {Z : Finset V} {p : List V}
    (hw : G.IsWalk p) :
    ¬ G.Blocked (↑Z) p ↔
      (cidToDAG G).IsActivePath Z p ∧ (∀ x, p.head? = some x → x ∉ Z) ∧
        (∀ y, p.getLast? = some y → y ∉ Z) := by
  simp only [CID.Blocked, not_or, Finset.mem_coe]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨hw, fun i hi ↦ ?_⟩, fun x hx hxZ ↦ h3 ⟨x, hxZ, hx⟩,
      fun y hy hyZ ↦ h4 ⟨y, hyZ, hy⟩⟩
    by_cases hc : (cidToDAG G).IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩)
        (p.get ⟨i + 2, hi⟩)
    · simp only [hc, if_true]
      rw [mem_bbZAncestors_iff]
      by_contra hmem
      exact h1 ⟨i, hi, (cidToDAG_isCollider G _ _ _).mp hc,
        fun hZ ↦ hmem ⟨_, hZ, Relation.ReflTransGen.refl⟩, fun w hwd hwZ ↦ hmem ⟨w, hwZ, hwd⟩⟩
    · simp only [hc, if_false]
      intro hmZ
      refine h2 ⟨i, hi, ?_, hmZ⟩
      rw [G.isChainOrFork_iff_not_isCollider (hw i (by omega)) (hw (i + 1) (by omega))]
      exact fun hcc ↦ hc ((cidToDAG_isCollider G _ _ _).mpr hcc)
  · rintro ⟨⟨-, hact⟩, hhead, hlast⟩
    refine ⟨?_, ?_, fun ⟨x, hxZ, hx⟩ ↦ hhead x hx hxZ, fun ⟨y, hyZ, hy⟩ ↦ hlast y hy hyZ⟩
    · rintro ⟨i, hi, hcol, -, hdesc⟩
      have hc := hact i hi
      simp only [(cidToDAG_isCollider G _ _ _).mpr hcol, if_true] at hc
      obtain ⟨z, hzZ, hzd⟩ := (mem_bbZAncestors_iff G Z _).mp hc
      exact hdesc z hzd hzZ
    · rintro ⟨i, hi, hcf, hmZ⟩
      have hnc : ¬ (cidToDAG G).IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩)
          (p.get ⟨i + 2, hi⟩) := by
        rw [cidToDAG_isCollider]
        exact (G.isChainOrFork_iff_not_isCollider (hw i (by omega))
          (hw (i + 1) (by omega))).mp hcf
      have hc := hact i hi
      simp only [hnc, if_false] at hc
      exact hc hmZ

/-- **Definition 6 is the Bayes-Ball predicate on a finite carrier.**

This is the whole point of the section: the statement graded against print needs
no `Fintype`, and the `Finset` form is what it comes to where the computation can
run. Every consumer of `CID.DSep` — Definition 7 below it, and Theorem 9 beyond
— is therefore a consumer of print's definition, by rewriting along this.

The two halves of the right-hand side are the two lengths a path can have. A
one-vertex path is blocked only by clause 3, so it is `Disjoint (X \ Z) (Y \ Z)`;
everything longer is upstream's `HasActivePath`. -/
public theorem CID.dSepSet_iff_dSep (G : CID V) (X Y Z : Finset V) :
    G.DSepSet ↑X ↑Y ↑Z ↔ G.DSep X Y Z := by
  constructor
  · intro h
    refine ⟨Finset.disjoint_left.mpr fun v hvX hvY ↦ ?_, ?_⟩
    · rw [Finset.mem_sdiff] at hvX hvY
      exact hvX.2 ((G.blocked_singleton_iff (↑Z) v).mp
        (h [v] (G.isWalk_singleton v) ⟨v, hvX.1, rfl⟩ ⟨v, hvY.1, rfl⟩))
    · rintro ⟨p, -, hact, hhead, hlast⟩
      obtain ⟨x, hxX, hx⟩ := Finset.mem_image.mp hhead
      obtain ⟨y, hyY, hy⟩ := Finset.mem_image.mp hlast
      rw [Finset.mem_sdiff] at hxX hyY
      have hw : G.IsWalk p := hact.1
      refine (G.not_blocked_iff hw).mpr ⟨hact, ?_, ?_⟩ ?_
      · intro x' hx' hx'Z
        rw [← hx] at hx'
        exact hxX.2 (Option.some_injective _ hx' ▸ hx'Z)
      · intro y' hy' hy'Z
        rw [← hy] at hy'
        exact hyY.2 (Option.some_injective _ hy' ▸ hy'Z)
      · exact h p hw ⟨x, hxX.1, hx.symm⟩ ⟨y, hyY.1, hy.symm⟩
  · rintro ⟨hdisj, hnoact⟩ p hw ⟨x, hxX, hx⟩ ⟨y, hyY, hy⟩
    by_contra hb
    obtain ⟨hact, hhead, hlast⟩ := (G.not_blocked_iff hw).mp hb
    have hxZ : x ∉ Z := hhead x hx
    have hyZ : y ∉ Z := hlast y hy
    rcases Nat.lt_or_ge p.length 2 with hlen | hlen
    · have hp : p = [x] := by
        rcases p with _ | ⟨a, _ | ⟨b, tl⟩⟩
        · simp at hx
        · simp only [List.head?_cons, Option.some.injEq] at hx
          simp [hx]
        · simp at hlen
      have hxy : x = y := by
        rw [hp] at hy
        simpa using hy
      exact Finset.disjoint_left.mp hdisj (Finset.mem_sdiff.mpr ⟨hxX, hxZ⟩)
        (Finset.mem_sdiff.mpr ⟨hxy ▸ hyY, hxy ▸ hyZ⟩)
    · exact hnoact ⟨p, hlen, hact, Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hxX, hxZ⟩, hx.symm⟩,
        Finset.mem_image.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hyY, hyZ⟩, hy.symm⟩⟩

/-- **Print's Definition 6, word for word, is the Bayes-Ball predicate on a
finite carrier.** `CID.dSepSet_iff_dSep` composed with
`CID.dSepSet_iff_dSepPath`, so no axis of this row separates the definition from
its computation. -/
public theorem CID.dSepPath_iff_dSep (G : CID V) (X Y Z : Finset V) :
    G.DSepPath ↑X ↑Y ↑Z ↔ G.DSep X Y Z :=
  (G.dSepSet_iff_dSepPath ↑X ↑Y ↑Z).symm.trans (G.dSepSet_iff_dSep X Y Z)

end AISafetyAtlas.Causal
