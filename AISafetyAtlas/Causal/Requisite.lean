module

public import AISafetyAtlas.Causal.DSep

/-!
# Requisite and nonrequisite observations

Everitt, Carey, Langlois, Ortega and Legg, *Agent Incentives: A Causal
Perspective*, AAAI 2021, Definition 7, after Lauritzen and Nilsson 2001.

> **Definition 7** (Nonrequisite observation). *Let `U^D := 𝐔 ∩ Desc^D` be the
> utility nodes downstream of `D`. An observation `X ∈ Pa^D` in a
> single-decision CID `𝒢` is nonrequisite if*
> `X ⊥ U^D | Pa^D ∪ {D} \ {X}`.
> *In this case, the edge `X → D` is also called nonrequisite. Otherwise `X` and
> `X → D` are requisite.*

This is d-separation at one specific conditioning set, so the whole of it is
`CID.DSep` applied to sets this file names. Nothing here is a new separation
argument.

## Two places print's phrasing has to be read

**The membership is a precondition, not a conjunct.** Print says *"an
observation `X ∈ Pa^D` ... is nonrequisite if"*, which restricts what the word
is being defined for rather than adding a clause to the condition. So
`CID.IsNonrequisite` is stated at an arbitrary vertex and says nothing about
membership, and the results that need `X` to be an observation take it as a
hypothesis. That is wider than print, on the same axis and for the same reason
as the incentive module's `HasICIAt`: at print's own restriction it is print's
condition exactly, and off it the definition still denotes.

Reading the membership *into* the definition would also be the awkward choice
here, because `Pa^D ∪ {D} \ {X}` is written with the removal already performed:
print takes `X` out of the conditioning set whether or not it went in, and the
displayed condition is well-formed at any `X`.

**The single-decision restriction is not used.** Print states Definition 7 for a
single-decision CID. Nothing in the condition mentions a second decision, and
`Desc^D`, `𝐔` and `Pa^D` are defined at any diagram, so the definition is given
here without that hypothesis. Theorem 9, when it arrives, may need it; the
definition does not.

`requisite_sets_pairwise_disjoint` does ask that `D` be a decision, which is a
weaker thing than asking that it be the only one, and it asks for a reason
recorded at that lemma.

## What the conditioning set is

`Pa^D ∪ {D} \ {X}` — the other observations, plus the decision itself, minus the
one being tested. `CID.parents` is a `Set`, so `parentsFinset` is its
`Fintype`-indexed rendering; both the filter and the descendant test go through
classical decidability, which is why the definitions here are `noncomputable`.
Nothing in this file is evaluated.
-/


namespace AISafetyAtlas.Causal

/-! ## Definition 7 as print writes it

Print's `U^D`, its conditioning set and its condition are all sets, on a vertex
set the paper never bounds. The `Finset` forms below are what they come to on a
finite carrier, where `AISafetyAtlas.Causal.CID.DSep` can be computed;
`CID.isNonrequisiteSet_iff` is the converting lemma.
-/

section Print

variable {V : Type*} [DecidableEq V]

/-- `U^D := 𝐔 ∩ Desc^D`, as print's set. -/
@[expose] public def CID.utilityDescendantsSet (G : CID V) (d : V) : Set V :=
  {u | G.IsUtility u ∧ G.IsDescendant d u}

@[simp] public theorem CID.mem_utilityDescendantsSet {G : CID V} {d u : V} :
    u ∈ G.utilityDescendantsSet d ↔ G.IsUtility u ∧ G.IsDescendant d u := Iff.rfl

/-- `Pa^D ∪ {D} \ {X}`, as print's set. -/
@[expose] public def CID.requisiteContextSet (G : CID V) (d x : V) : Set V :=
  (G.parents d ∪ {d}) \ {x}

@[simp] public theorem CID.mem_requisiteContextSet {G : CID V} {d x v : V} :
    v ∈ G.requisiteContextSet d x ↔ (v ∈ G.parents d ∨ v = d) ∧ v ≠ x := Iff.rfl

/-- **Definition 7**, at print's generality: `X` is d-separated from the utility
nodes downstream of `D`, given the other observations and the decision. -/
@[expose] public def CID.IsNonrequisiteSet (G : CID V) (d x : V) : Prop :=
  G.DSepSet {x} (G.utilityDescendantsSet d) (G.requisiteContextSet d x)

/-- The observation under test is never in its own conditioning set. -/
public theorem CID.not_mem_requisiteContextSet (G : CID V) (d x : V) :
    x ∉ G.requisiteContextSet d x := fun h ↦ h.2 rfl

/-- **Definition 7 under print's own word for a path.** The condition may be read
over paths rather than over walks without changing it, by
`AISafetyAtlas.Causal.CID.dSepSet_iff_dSepPath`. -/
public theorem CID.isNonrequisiteSet_iff_dSepPath (G : CID V) (d x : V) :
    G.IsNonrequisiteSet d x ↔
      G.DSepPath {x} (G.utilityDescendantsSet d) (G.requisiteContextSet d x) :=
  G.dSepSet_iff_dSepPath _ _ _

end Print

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- `Pa^D` as a `Finset`. `CID.parents` is a `Set` with no decidability of its
own, so membership is decided classically. -/
@[expose] public noncomputable def CID.parentsFinset (G : CID V) (d : V) : Finset V :=
  letI := Classical.decPred (· ∈ G.parents d)
  Finset.univ.filter (· ∈ G.parents d)

@[simp] public theorem CID.mem_parentsFinset {G : CID V} {d x : V} :
    x ∈ G.parentsFinset d ↔ x ∈ G.parents d := by
  classical
  simp [CID.parentsFinset]

/-- `U^D := 𝐔 ∩ Desc^D`, the utility nodes downstream of `D`.

`CID.IsDescendant` is reflexive, so `D` is in this set exactly when `D` is
itself a utility node. At a decision it is not — a decision is never a utility
node — but nothing here assumes `D` is one, and a utility node may have parents,
so the reflexive case is real rather than hypothetical. -/
@[expose] public noncomputable def CID.utilityDescendants (G : CID V) (d : V) : Finset V :=
  letI := Classical.decPred (G.IsDescendant d)
  G.utilities.filter (G.IsDescendant d)

@[simp] public theorem CID.mem_utilityDescendants {G : CID V} {d u : V} :
    u ∈ G.utilityDescendants d ↔ G.IsUtility u ∧ G.IsDescendant d u := by
  classical
  simp [CID.utilityDescendants]

/-- The conditioning set of Definition 7: the other observations, the decision
itself, and not the observation under test. -/
@[expose] public noncomputable def CID.requisiteContext (G : CID V) (d x : V) : Finset V :=
  (G.parentsFinset d ∪ {d}) \ {x}

@[simp] public theorem CID.mem_requisiteContext {G : CID V} {d x v : V} :
    v ∈ G.requisiteContext d x ↔ (v ∈ G.parents d ∨ v = d) ∧ v ≠ x := by
  simp [CID.requisiteContext, or_comm]

/-- **Definition 7.** `X` is a nonrequisite observation for the decision `D`
when it is d-separated from the utility nodes downstream of `D`, given the other
observations and the decision.

Stated at an arbitrary `X`; print restricts the word to `X ∈ Pa^D`, and the
results below take that as a hypothesis where they need it. -/
@[expose] public noncomputable def CID.IsNonrequisite (G : CID V) (d x : V) : Prop :=
  G.DSep {x} (G.utilityDescendants d) (G.requisiteContext d x)

/-- **Definition 7, the other half.** *"Otherwise `X` and `X → D` are
requisite."* -/
@[expose] public noncomputable def CID.IsRequisite (G : CID V) (d x : V) : Prop :=
  ¬ G.IsNonrequisite d x

public theorem CID.isRequisite_iff (G : CID V) (d x : V) :
    G.IsRequisite d x ↔ ¬ G.IsNonrequisite d x := Iff.rfl

public theorem CID.not_isNonrequisite_iff (G : CID V) (d x : V) :
    ¬ G.IsNonrequisite d x ↔ G.IsRequisite d x := Iff.rfl

/-- The two are exclusive and exhaustive, which is what *"otherwise"* asserts. -/
public theorem CID.isNonrequisite_or_isRequisite (G : CID V) (d x : V) :
    G.IsNonrequisite d x ∨ G.IsRequisite d x := em _

public theorem CID.not_and_isRequisite (G : CID V) (d x : V) :
    ¬ (G.IsNonrequisite d x ∧ G.IsRequisite d x) := fun h ↦ h.2 h.1

/-- **A decision with no utility downstream has every observation
nonrequisite.**

With `U^D` empty there is no target to reach, so the separation holds for want
of anywhere to go. This is the degenerate case, and it is worth having as a
theorem because it shows the definition does not silently presume that `D`
influences a utility. -/
public theorem CID.isNonrequisite_of_utilityDescendants_eq_empty (G : CID V) {d : V}
    (h : G.utilityDescendants d = ∅) (x : V) : G.IsNonrequisite d x := by
  have hempty : G.utilityDescendants d \ G.requisiteContext d x = (∅ : Finset V) := by
    simp [h]
  refine ⟨by simp [hempty], ?_⟩
  rintro ⟨p, -, -, -, hlast⟩
  obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hlast
  rw [hempty] at hy
  simp at hy

/-- **The observation under test is never in its own conditioning set**, which
is the content of the `\ {X}` in print's displayed condition. -/
public theorem CID.not_mem_requisiteContext (G : CID V) (d x : V) :
    x ∉ G.requisiteContext d x := by simp

/-- Definition 7 asks a question its sets never make degenerate: at an
observation, the source, target and conditioning sets are pairwise disjoint.

`X ∈ Pa^D` has a child, so it is not a utility node; `X` is removed from the
conditioning set by construction; and `D` is in that set but is a decision, so
it is not a utility either.

**That last step is why `D` must be assumed a decision here**, and the
assumption is not slack. Print's `𝐔` is childless, but nothing stops a utility
node from having *parents*, so at an arbitrary `D` with `Pa^D` nonempty the
diagram may have `D` itself a utility node — and then `D` lies in both
`U^D`, reflexively, and its own conditioning set, and the three sets are not
disjoint. The definition still denotes there; only this lemma fails.

So this is the configuration in which `CID.DSep` agrees with the upstream
predicate, and Definition 7 at a genuine decision does not exercise the
overlapping-set generality that Definition 6 is stated at. -/
public theorem CID.requisite_sets_pairwise_disjoint (G : CID V) {d x : V}
    (hd : G.IsDecision d) (hx : x ∈ G.parents d) :
    Disjoint ({x} : Finset V) (G.utilityDescendants d) ∧
      Disjoint ({x} : Finset V) (G.requisiteContext d x) ∧
      Disjoint (G.utilityDescendants d) (G.requisiteContext d x) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finset.disjoint_singleton_left, CID.mem_utilityDescendants]
    rintro ⟨hu, -⟩
    exact G.utility_childless x hu d hx
  · simp
  · rw [Finset.disjoint_left]
    intro u hu hu'
    have hU : G.IsUtility u := (CID.mem_utilityDescendants.mp hu).1
    rcases (CID.mem_requisiteContext.mp hu').1 with h | h
    · exact G.utility_childless u hU d h
    · subst h
      exact absurd (hd.symm.trans hU) (by decide)

/-! ## Print's Definition 7 and the computed one are the same predicate -/

@[simp] public theorem CID.coe_utilityDescendants (G : CID V) (d : V) :
    ↑(G.utilityDescendants d) = G.utilityDescendantsSet d := by
  ext u
  simp [CID.utilityDescendantsSet]

@[simp] public theorem CID.coe_requisiteContext (G : CID V) (d x : V) :
    ↑(G.requisiteContext d x) = G.requisiteContextSet d x := by
  ext v
  simp [CID.requisiteContextSet, or_comm]

/-- **Definition 7 is the computed predicate on a finite carrier**, by
`AISafetyAtlas.Causal.CID.dSepSet_iff_dSep` at Definition 7's three sets. Every
result about `CID.IsNonrequisite` below is therefore a result about print's
Definition 7, by rewriting along this. -/
public theorem CID.isNonrequisiteSet_iff (G : CID V) (d x : V) :
    G.IsNonrequisiteSet d x ↔ G.IsNonrequisite d x := by
  rw [CID.IsNonrequisiteSet, CID.IsNonrequisite, ← G.dSepSet_iff_dSep,
    Finset.coe_singleton, CID.coe_utilityDescendants, CID.coe_requisiteContext]

end AISafetyAtlas.Causal
