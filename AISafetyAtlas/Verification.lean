module

public import AISafetyAtlas.Computability

/-!
# Verification limits for extensional program behavior

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `rice` | No total verifier for nontrivial behavioral properties |
| **Bridge** | `AgentBehavior.no_behavioral_safety_verifier` | Downstream packaging (BY-012; reviewed bridge) |
| **Bridge** | `Robot.action_safety_unverifiable` | Robot-facing RELATED reduction (BY-033; reviewed) |

Also via root: `Verification.AgentBehavior`, `Verification.Robot`.

## Statement intent

- Object: partial ℕ I/O behavior; codes via Mathlib `eval`.
- Conclusion: no total computable verifier for nontrivial behavioral properties.
- Source form: `Computability.rice_code_iff`.

## Explicit non-claims

Does **not** claim every practical AI property is behavioral, that a particular
system is this evaluator, or that sound incomplete methods are impossible.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Verification

/-- A property stated directly on partial input/output behavior. -/
public abbrev BehavioralProperty := Set (ℕ →. ℕ)

/-- The behavior represented by `program` satisfies `property`. -/
@[expose] public def Holds (property : BehavioralProperty) (program : Code) : Prop :=
  eval program ∈ property

/-- A behavioral property with accepted and rejected representable behaviors. -/
@[expose] public def Nontrivial (property : BehavioralProperty) : Prop :=
  (∃ accepted, Holds property accepted) ∧
    (∃ rejected, ¬ Holds property rejected)

/-- The property has a total computable decision procedure on program codes. -/
@[expose] public def HasVerifier (property : BehavioralProperty) : Prop :=
  ComputablePred (Holds property)

/--
Rice's theorem as a program-verification limit: a nontrivial extensional
behavioral property has no total computable verifier.
-/
public theorem rice (property : BehavioralProperty)
    (nontrivial : Nontrivial property) :
    ¬ HasVerifier property := by
  intro verifier
  let codes : Set Code := {program | Holds property program}
  have extensional : ∀ program₁ program₂,
      eval program₁ = eval program₂ →
      (program₁ ∈ codes ↔ program₂ ∈ codes) := by
    intro program₁ program₂ sameBehavior
    simp only [codes, Set.mem_setOf_eq, Holds]
    rw [sameBehavior]
  have computableCodes : ComputablePred fun code => code ∈ codes := by
    simpa only [codes, Set.mem_setOf_eq, HasVerifier] using verifier
  have trivial : codes = ∅ ∨ codes = Set.univ :=
    (AISafetyAtlas.Computability.rice_code_iff codes extensional).mp computableCodes
  rcases nontrivial with ⟨⟨accepted, acceptedHolds⟩, ⟨rejected, rejectedFails⟩⟩
  rcases trivial with empty | universal
  · have acceptedMem : accepted ∈ codes := by
      simpa only [codes, Set.mem_setOf_eq] using acceptedHolds
    rw [empty] at acceptedMem
    exact acceptedMem
  · have rejectedMem : rejected ∈ codes := by
      rw [universal]
      exact Set.mem_univ rejected
    exact rejectedFails (by
      simpa only [codes, Set.mem_setOf_eq] using rejectedMem)

end AISafetyAtlas.Verification
