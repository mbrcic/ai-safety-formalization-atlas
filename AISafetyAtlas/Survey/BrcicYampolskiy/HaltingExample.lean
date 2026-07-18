module

public import AISafetyAtlas.Computability

/-!
# Worked example: the halting problem

The survey lists Turing/Church undecidability as a deductive impossibility. For
one precise, machine-checked instance, Mathlib fixes an input `n` and considers
program codes `c`; `eval c n` is a partial computation, and `.Dom` states that
it terminates. The theorem below witnesses that this predicate is not
computable.

This establishes the encoded halting result only. It does not establish that a
particular AI property is undecidable or that a real system is uncontrollable.
The declaration is intentionally an anonymous compiling documentation example,
not a second public theorem, and this module is not imported by the atlas root.
-/

open Nat.Partrec.Code

namespace AISafetyAtlas.Survey.BrcicYampolskiy

example (input : ℕ) : ¬ComputablePred fun code => (eval code input).Dom :=
  AISafetyAtlas.Computability.halting_problem input

end AISafetyAtlas.Survey.BrcicYampolskiy
