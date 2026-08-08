module

import AISafetyAtlas.Explainability
import AISafetyAtlas.Verification.AgentBehavior
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Non-vacuity witnesses for published gate predicates

These anonymous compile-time examples provide concrete inhabitants for the
hypotheses used by the published Rice and attribution bridges.  The regret
gate is witnessed in `Examples.WorkbenchConsumers` by
`binaryCorruption.halfMaximalRegretBound`.  No public declarations are added.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Examples.NonVacuity

private def zeroOnly : AISafetyAtlas.Verification.BehavioralProperty :=
  {behavior | behavior 0 = Part.some 0}

/-! A total, extensional property with one accepted and one rejected code. -/
example : AISafetyAtlas.Verification.Nontrivial zeroOnly := by
  constructor
  · refine ⟨Code.const 0, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]
  · refine ⟨Code.const 1, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]

example : AISafetyAtlas.Verification.AgentBehavior.SpecNontrivial zeroOnly := by
  constructor
  · refine ⟨Code.const 0, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]
  · refine ⟨Code.const 1, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]

private def twoFeatures : AISafetyAtlas.Explainability.FeatureIndex where
  P := 2
  L := 1
  hP := by decide
  groupOf := fun _ => 0

private def oppositeAttribution : Fin 2 → Bool → ℝ :=
  fun feature model =>
    if feature.val = 0 then
      if model then 1 else 0
    else
      if model then 0 else 1

/-! Two features in one group exchange order across two concrete models. -/
example : AISafetyAtlas.Explainability.RashomonProperty
    twoFeatures Bool oppositeAttribution := by
  intro ℓ j k hj hk hjk
  dsimp [twoFeatures] at ℓ j k hj hk hjk ⊢
  fin_cases ℓ
  all_goals fin_cases j
  all_goals fin_cases k
  · exact (hjk rfl).elim
  · refine ⟨true, false, ?_, ?_⟩ <;> norm_num [oppositeAttribution]
  · refine ⟨false, true, ?_, ?_⟩ <;> norm_num [oppositeAttribution]
  · exact (hjk rfl).elim

end AISafetyAtlas.Examples.NonVacuity
