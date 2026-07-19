/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/


module

public import Mathlib.Computability.Partrec
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.List.Basic

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Core Definitions of Algorithmic Information Theory

This module establishes the foundational ontology for Kolmogorov complexity.
It defines maps as partial recursive functions (`Partrec`),
programs, and the core metrics: conditional (`condK`) and plain (`plainK`) complexity.
Finally, it formalizes the concept of an optimal universal decompressor,
which is the prerequisite for the Invariance Theorem.
-/

namespace Kolmogorov

/-! ### Basic Types -/

/-- A bit string is simply a list of booleans. -/
public abbrev BitString := List Bool

/-- A Map in our context is a partial function taking a pair of
    (program, context) and potentially returning a computed BitString.
    We use `Part` to naturally model programs that loop indefinitely. -/
public abbrev Map := BitString × BitString →. BitString

/-! ### Metrics & Execution -/

/-- The length of a program is the number of bits it contains.
    Defined as `abbrev` so Lean automatically reduces it to `List.length`. -/
public abbrev programLength (p : BitString) : ℕ := p.length

/-- A map is a valid decompressor if its execution is partial recursive. -/
public abbrev isDecompressor (D : Map) : Prop := Partrec D

/-- A map `D` produces output `x` given program `p` and context `y`.
    Using the membership operator `∈` is the standard Mathlib idiom for `Part.some`. -/
public abbrev produces (D : Map) (p y x : BitString) : Prop := x ∈ D (p, y)

/-- The set of lengths of all valid programs that produce `x` given `y`. -/
public abbrev candidateLengths (D : Map) (x y : BitString) : Set ENat :=
  {n | ∃ p, produces D p y x ∧ (programLength p : ENat) = n}

/-! ### Kolmogorov Complexity Definitions -/

/-- Conditional Kolmogorov Complexity K_D(x|y).
    Defined as the infimum of the lengths of all valid programs.
    If no program produces `x`, the set is empty, and `sInf ∅ = ⊤` (infinity). -/
@[expose]
public noncomputable def condK (D : Map) (x y : BitString) : ENat :=
  sInf (candidateLengths D x y)

/-- Plain Kolmogorov Complexity K_D(x).
    Defined as the conditional complexity with an empty context. -/
@[expose]
public noncomputable def plainK (D : Map) (x : BitString) : ENat :=
  condK D x []

/-! ### Optimality (Universality) -/

/-- A map `U` is optimal (universal) if it can simulate any other
    computable decompressor `D` with at most a constant additive overhead `c`
    to the program length. -/
@[expose]
public def isOptimalConditional (U : Map) : Prop :=
  isDecompressor U ∧
  ∀ D, isDecompressor D → ∃ c : ℕ, ∀ x y, condK U x y ≤ condK D x y + (c : ENat)

end Kolmogorov
