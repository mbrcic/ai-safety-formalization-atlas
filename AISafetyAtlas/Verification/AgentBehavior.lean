module

public import AISafetyAtlas.Verification

/-!
# Downstream consumer of `Verification.rice`

## Statement intent

- **System object:** an *encoded agent* is a Mathlib program code whose
  operational meaning is a partial input/output map `ℕ →. ℕ`.
- **Safety specification:** a set of acceptable partial I/O behaviors
  (`SafetySpec` = `BehavioralProperty`).
- **Decider:** a total computable `BehavioralSafetyVerifier` that is sound and
  complete for whether an agent satisfies the specification.
- **Assumption:** the specification is nontrivial — some representable agent is
  safe and some is not.
- **Conclusion:** no such total verifier exists.
- **Source:** reduces through `AISafetyAtlas.Verification.rice` (semantic-to-code
  bridge over Mathlib Rice), not by re-proving Rice. Classical statement:
  H. G. Rice, *Classes of Recursively Enumerable Sets and Their Decision
  Problems*, Trans. AMS 74(2):358–366, 1953 (survey BY-012 / `survey-ref-037`).

## Related literature (computability packaging)

This module packages classical Rice for an *encoded agent* and a nontrivial
extensional I/O specification: no total sound-and-complete computable verifier
exists for all program codes.

Melo, Máximo, Soma, and Castro ([arXiv:2408.08995](https://arxiv.org/abs/2408.08995);
Sci. Rep. 2025; catalog `atlas-ref-melo-2024`, landscape `LAND-MELO-001`) apply
Rice to a stated decision problem: whether an arbitrary AI model (as a program)
always satisfices a fixed non-trivial judge of input/output pairs. Basics and
coverage estimate: `docs/guide/related-literature.md`. The atlas formalizes the
Rice packaging, not their full narrative or architecture proposals.

Related but distinct: Alfonseca et al., *Superintelligence cannot be contained*
(JAIR 2021; `survey-ref-056`).

Registry BY-012 (statement layer). Coverage:
`docs/status/paper-coverage.md`. Review:
`docs/bridges/review-by-012-agentbehavior.md`.

CT-4 / R6-8 consumer of `Verification.rice`. Does not claim that every
practical safety property is extensional I/O behavior, that a particular
system is encoded by `eval`, or that incomplete verifiers are impossible.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Verification.AgentBehavior

/-- An encoded agent: a program code with partial recursive I/O semantics. -/
public abbrev Agent := Code

/-- A behavioral safety specification on partial input/output maps. -/
public abbrev SafetySpec := AISafetyAtlas.Verification.BehavioralProperty

/-- Agent `agent` realizes a behavior in the safety specification. -/
public def Satisfies (spec : SafetySpec) (agent : Agent) : Prop :=
  AISafetyAtlas.Verification.Holds spec agent

/-- The specification accepts at least one representable agent and rejects another. -/
public abbrev SpecNontrivial (spec : SafetySpec) : Prop :=
  AISafetyAtlas.Verification.Nontrivial spec

/--
A total computable procedure that correctly classifies every encoded agent
against a fixed behavioral safety specification.
-/
public structure BehavioralSafetyVerifier (spec : SafetySpec) where
  decide : Agent → Bool
  computable_decide : Computable decide
  correct : ∀ agent, (decide agent : Prop) ↔ Satisfies spec agent

/--
No total computable behavioral safety verifier exists for a nontrivial I/O
safety specification on encoded agents.

Machine-checked reduction to `AISafetyAtlas.Verification.rice`. Same
agent/program + nontrivial I/O-judge pattern as Melo et al.
(arXiv:2408.08995); see the module docstring for scope.
-/
public theorem no_behavioral_safety_verifier
    (spec : SafetySpec) (nontrivial : SpecNontrivial spec) :
    ¬ Nonempty (BehavioralSafetyVerifier spec) := by
  rintro ⟨verifier⟩
  have hasVerifier : AISafetyAtlas.Verification.HasVerifier spec := by
    refine ComputablePred.computable_iff.mpr
      ⟨verifier.decide, verifier.computable_decide, ?_⟩
    funext agent
    exact propext (verifier.correct agent).symm
  exact AISafetyAtlas.Verification.rice spec nontrivial hasVerifier

end AISafetyAtlas.Verification.AgentBehavior
