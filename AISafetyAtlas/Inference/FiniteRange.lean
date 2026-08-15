module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Finset.Image

/-!
# Finiteness on the map, not on the universe

Wolpert states finiteness where it belongs: Definition 6 asks that `X(U)` and
`Γ(U)` be countable, Definition 9 that `Γ` have *"finite range"*, Definition 11 is
*"phrased for countable `X(U)`"*. None of them asks `U` itself to be finite, and
`U` is the set of worldlines, so a finite `U` excludes the intended model outright.

`FiniteRange` is that hypothesis. It lives in its own module because section 5's
inference complexity and section 8's probability both need it and neither should
depend on the other. It is deliberately **not** an import: the only Lean library
carrying such a class is PFR, and this development does not depend on PFR.
-/

namespace AISafetyAtlas.Inference

universe u v

variable {U : Type u}

/-- The source's finiteness hypothesis, on the map rather than on `U`. -/
public class FiniteRange {α : Type v} (X : U → α) : Prop where
  /-- `X(U)` is finite. -/
  finite_range : (Set.range X).Finite

/-- `X(U)`, as a `Finset`. -/
@[expose] public noncomputable def rangeFinset {α : Type v} (X : U → α) [FiniteRange X] :
    Finset α :=
  (FiniteRange.finite_range (X := X)).toFinset

@[simp] public theorem mem_rangeFinset {α : Type v} (X : U → α) [FiniteRange X] (a : α) :
    a ∈ rangeFinset X ↔ ∃ u, X u = a := by
  simp [rangeFinset, Set.mem_range]

/-- A map out of a finite type has finite range. The finite models in `Examples/`
reach section 5 and section 8 through this instance. -/
public instance instFiniteRangeOfFinite [Finite U] {α : Type v} (X : U → α) :
    FiniteRange X where
  finite_range := Set.finite_range X

public theorem self_mem_rangeFinset {α : Type v} (X : U → α) [FiniteRange X] (u : U) :
    X u ∈ rangeFinset X :=
  (mem_rangeFinset X (X u)).mpr ⟨u, rfl⟩

end AISafetyAtlas.Inference
