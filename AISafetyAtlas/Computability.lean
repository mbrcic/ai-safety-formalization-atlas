module

public import Mathlib.Computability.Halting

/-!
# Computability limits

Atlas-facing names for the maintained Rice and halting-problem results in
`Mathlib.Computability.Halting`. These are thin, attributed wrappers: the proofs
remain Mathlib's, and no AI-safety bridge is asserted.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Computability

/--
Rice's theorem in extensional-function form. If membership in `C` is computable,
then any partial recursive function belongs to `C` whenever one does.

Source: `ComputablePred.rice` in Mathlib v4.32.0.
-/
public theorem rice
    (C : Set (ℕ →. ℕ))
    (decidableC : ComputablePred fun code => eval code ∈ C)
    {f g : ℕ →. ℕ}
    (computableF : Nat.Partrec f)
    (computableG : Nat.Partrec g)
    (f_mem : f ∈ C) :
    g ∈ C :=
  ComputablePred.rice C decidableC computableF computableG f_mem

/--
Rice's theorem for extensional sets of program codes: a decidable extensional
set of codes is empty or universal.

Source: `ComputablePred.rice₂` in Mathlib v4.32.0.
-/
public theorem rice_code_iff
    (C : Set Code)
    (extensional : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred fun code => code ∈ C) ↔ C = ∅ ∨ C = Set.univ :=
  ComputablePred.rice₂ C extensional

/-- The halting predicate for a fixed input is recursively enumerable.

Source: `ComputablePred.halting_problem_re` in Mathlib v4.32.0.
-/
public theorem halting_re (input : ℕ) : REPred fun code => (eval code input).Dom :=
  ComputablePred.halting_problem_re input

/-- The halting predicate for a fixed input is not computable.

Source: `ComputablePred.halting_problem` in Mathlib v4.32.0.
-/
public theorem halting_problem (input : ℕ) :
    ¬ComputablePred fun code => (eval code input).Dom :=
  ComputablePred.halting_problem input

/-- The complement of the halting predicate is not recursively enumerable.

Source: `ComputablePred.halting_problem_not_re` in Mathlib v4.32.0.
-/
public theorem nonhalting_not_re (input : ℕ) :
    ¬REPred fun code => ¬(eval code input).Dom :=
  ComputablePred.halting_problem_not_re input

end AISafetyAtlas.Computability
