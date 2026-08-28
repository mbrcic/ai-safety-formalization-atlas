module

public import AISafetyAtlas.Analysis.Semialgebraic

/-!
# Worked semialgebraic sets

`AISafetyAtlas.Analysis.Semialgebraic` supplies the notion MAIS-A2 `prob:exact`
names and Mathlib does not have. This module runs it on concrete sets, so the
definition is checked against examples rather than only asserted to be the
standard one.

The pairing that matters for `prob:exact` is **compact and semialgebraic at
once**: the unit square below is both, which is what makes print's hypothesis
non-vacuous as a shape. A half-plane is semialgebraic and not compact, which is
what makes the compactness half of the hypothesis do work.
-/

namespace AISafetyAtlas.Examples.Analysis.Semialgebraic

open AISafetyAtlas.Analysis
open MvPolynomial

/-! ## The unit square is compact semialgebraic -/

/-- The unit square in `ℝ²`, as a closed box. -/
public noncomputable def unitSquare : Set (Fin 2 → ℝ) := ClosedBox (fun _ ↦ 0) 1

public theorem unitSquare_semialgebraic : IsSemialgebraic unitSquare :=
  isSemialgebraic_closedBox _ _

public theorem unitSquare_compact : IsCompact unitSquare :=
  isCompact_closedBox _ _

/-- Membership is the expected inequality pair, so `ClosedBox` is the box it
claims to be and not merely something with the right closure properties. -/
public theorem mem_unitSquare (x : Fin 2 → ℝ) :
    x ∈ unitSquare ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  simp [unitSquare, ClosedBox]

/-! ## A set cut out by one sign condition -/

/-- The closed half-plane `x₀ ≥ 0`, given by a single sign condition. -/
public noncomputable def halfPlane : Set (Fin 2 → ℝ) :=
  BasicSemialgebraic {(X 0, PolySign.nonneg)}

public theorem halfPlane_semialgebraic : IsSemialgebraic halfPlane :=
  IsSemialgebraic.basic _

public theorem mem_halfPlane (x : Fin 2 → ℝ) : x ∈ halfPlane ↔ 0 ≤ x 0 := by
  simp [halfPlane, BasicSemialgebraic, PolySign.Holds]

/-- The half-plane is **not** compact, so the two words in *"compact
semialgebraic"* are independent and print's compactness hypothesis is not
implied by the semialgebraic one. -/
public theorem halfPlane_not_compact : ¬ IsCompact halfPlane := by
  intro hc
  obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn
    ⟨fun _ ↦ 0, by rw [mem_halfPlane]⟩
    (continuous_apply (0 : Fin 2)).continuousOn
  have hmem : (fun _ ↦ x 0 + 1 : Fin 2 → ℝ) ∈ halfPlane := by
    rw [mem_halfPlane]
    have h0 := (mem_halfPlane x).mp hx
    linarith
  have hle := hmax hmem
  simp only [Set.mem_setOf_eq] at hle
  linarith

/-! ## Unions stay semialgebraic -/

/-- Two disjoint boxes, which is the shape a class spread over two graphs
projects to one graph at a time. -/
public theorem twoBoxes_semialgebraic (c₁ c₂ : Fin 2 → ℝ) (r : ℝ) :
    IsSemialgebraic (ClosedBox c₁ r ∪ ClosedBox c₂ r) :=
  (isSemialgebraic_closedBox c₁ r).union (isSemialgebraic_closedBox c₂ r)

/-- The empty set and the whole space are the two degenerate cases. -/
public theorem empty_and_univ_semialgebraic :
    IsSemialgebraic (∅ : Set (Fin 2 → ℝ)) ∧
      IsSemialgebraic (Set.univ : Set (Fin 2 → ℝ)) :=
  ⟨isSemialgebraic_empty, isSemialgebraic_univ⟩

/-! ## The rest of the Boolean algebra

Closure under union is the one third of BCR §2.1's closure statement that
`prob:exact` exercises for free, because a class is presented as a union of
boxes. These run the other two thirds — intersection, complement, and the
difference they combine into — on sets the reader can see.
-/

/-- Two boxes meet in a semialgebraic set. Nothing about unions gives this. -/
public theorem twoBoxes_inter_semialgebraic (c₁ c₂ : Fin 2 → ℝ) (r : ℝ) :
    IsSemialgebraic (ClosedBox c₁ r ∩ ClosedBox c₂ r) :=
  (isSemialgebraic_closedBox c₁ r).inter (isSemialgebraic_closedBox c₂ r)

/-- A family of boxes indexed by an arbitrary `Finset` meets in a semialgebraic
set. The finite closure lemmas are stated over a `Finset` rather than a `Fin n`,
so the index type is the caller's choice. -/
public theorem boxes_biInter_semialgebraic {α : Type} (t : Finset α)
    (c : α → Fin 2 → ℝ) (r : ℝ) :
    IsSemialgebraic (⋂ a ∈ t, ClosedBox (c a) r) :=
  isSemialgebraic_biInter t fun a _ ↦ isSemialgebraic_closedBox (c a) r

/-! ## The case that forces the two-piece split -/

/-- The line `x₀ = 0` in `ℝ²`, cut out by a single `zero` condition. -/
public noncomputable def axis : Set (Fin 2 → ℝ) :=
  BasicSemialgebraic {(X 0, PolySign.zero)}

public theorem mem_axis (x : Fin 2 → ℝ) : x ∈ axis ↔ x 0 = 0 := by
  simp [axis, BasicSemialgebraic, PolySign.Holds]

public theorem axis_compl_semialgebraic : IsSemialgebraic axisᶜ :=
  (IsSemialgebraic.basic _).compl

public theorem mem_axis_compl (x : Fin 2 → ℝ) : x ∈ axisᶜ ↔ x 0 ≠ 0 := by
  simp [Set.mem_compl_iff, mem_axis]

/-- The complement is the union of the two open half-planes.

This is the negation table's one splitting case made explicit: of the three sign
conditions, `p = 0` is the only one whose negation is not a single basic piece,
and this is what that looks like on a set one can draw. It is also why the
complement of a basic set is a *union* over its conditions rather than another
basic set. -/
public theorem axis_compl_eq :
    axisᶜ = BasicSemialgebraic {(X 0, PolySign.pos)}
      ∪ BasicSemialgebraic {(-X 0, PolySign.pos)} := by
  ext x
  simp only [Set.mem_compl_iff, mem_axis, Set.mem_union, BasicSemialgebraic,
    Set.mem_setOf_eq, Finset.mem_singleton, forall_eq, PolySign.Holds, map_neg,
    eval_X]
  constructor
  · intro hx
    rcases lt_trichotomy (x 0) 0 with h | h | h
    · exact Or.inr (by linarith)
    · exact absurd h hx
    · exact Or.inl h
  · rintro (h | h) hx <;> rw [hx] at h <;> linarith

/-! ## Cutting one set down by another -/

/-- The half-plane with the unit square removed. This is the shape a caller
cutting one class down by another writes; it is the first thing closure under
union cannot supply, and it needs both `inter` and `compl`. -/
public theorem halfPlane_sdiff_unitSquare_semialgebraic :
    IsSemialgebraic (halfPlane \ unitSquare) :=
  halfPlane_semialgebraic.sdiff unitSquare_semialgebraic

/-- The difference is inhabited, so the closure lemma above is not closing over
a degenerate set. -/
public theorem mem_halfPlane_sdiff_unitSquare :
    (fun _ ↦ 2 : Fin 2 → ℝ) ∈ halfPlane \ unitSquare := by
  refine ⟨?_, ?_⟩
  · rw [mem_halfPlane]
    norm_num
  · intro hmem
    have h := ((mem_unitSquare _).mp hmem 0).2
    norm_num at h

end AISafetyAtlas.Examples.Analysis.Semialgebraic
