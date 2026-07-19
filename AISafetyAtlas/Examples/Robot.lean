module

import AISafetyAtlas

/-!
# A paced reactive computation

This example witnesses that the switching certificate required by
`AISafetyAtlas.Verification.Robot.action_safety_unverifiable` is realizable.
It mirrors the construction in van Leeuwen and Wiedermann's proof: each
operational cycle performs a bounded approximation of an encoded computation,
producing the acceptable action `none` until a result is found and an
unacceptable `some result` action thereafter.

The example deliberately adds no public atlas declarations.  It demonstrates
the computability mechanism, not a claim that this small model captures a
physical robot or an ethical property.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Examples.Robot

private def pacedBehavior (input : ℕ) :
    Code → AISafetyAtlas.Verification.Robot.Behavior Unit (Option ℕ) :=
  fun source _ cycle => evaln cycle source input

private def noResultAction : Unit → ℕ → Option ℕ → Prop :=
  fun _ _ action => action = none

private theorem paced_always_iff_nonhalting (input : ℕ) (source : Code) :
    AISafetyAtlas.Verification.Robot.AlwaysSatisfies
      (pacedBehavior input) noResultAction source ↔
      ¬(eval source input).Dom := by
  simp only [AISafetyAtlas.Verification.Robot.AlwaysSatisfies,
    pacedBehavior, noResultAction]
  constructor
  · intro alwaysSatisfies halts
    rcases Part.dom_iff_mem.mp halts with ⟨result, resultMem⟩
    rcases evaln_complete.mp resultMem with ⟨cycle, boundedResult⟩
    have noResult := alwaysSatisfies () cycle
    rw [noResult] at boundedResult
    exact Option.not_mem_none result boundedResult
  · intro doesNotHalt _ cycle
    cases bounded : evaln cycle source input with
    | none => rfl
    | some result =>
        exfalso
        apply doesNotHalt
        apply Part.dom_iff_mem.mpr
        exact ⟨result, evaln_sound (by simpa [bounded])⟩

private def pacedConstruction (input : ℕ) :
    AISafetyAtlas.Verification.Robot.SwitchingConstruction
      (fun _ : Code => True) (pacedBehavior input) noResultAction where
  sourceInput := input
  compile := id
  computable_compile := Computable.id
  compiled_structured := fun _ => trivial
  satisfies_iff_nonhalting := paced_always_iff_nonhalting input

example (input : ℕ) :
    ¬ Nonempty (AISafetyAtlas.Verification.Robot.Verifier
      (fun _ : Code => True) (pacedBehavior input) noResultAction) :=
  AISafetyAtlas.Verification.Robot.action_safety_unverifiable
    (fun _ : Code => True) (pacedBehavior input) noResultAction
    (pacedConstruction input)

end AISafetyAtlas.Examples.Robot
