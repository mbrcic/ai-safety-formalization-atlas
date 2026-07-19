module

public import AISafetyAtlas.Verification

/-!
# Verification limits for reactive robot programs

This module isolates the **computability core** of Theorem 1 and Corollary 1
of van Leeuwen and Wiedermann, *Impossibility Results for the Online
Verification of Ethical and Legal Behaviour of Robots* (UU-PCS-2021-02, 2021).
Full extracted statements and a proof comparison live in
`docs/guide/robot-verification-model.md`.

## Paper statements (extracted)

**Theorem 1.** Let *P* be any non-trivial robot property. There does not exist
an algorithmic procedure that will enable an observer to tell, given an
arbitrary robot with potentially unbounded memory, whether the actions of the
robot always satisfy *P*.

**Corollary 1.** Let *P* be a non-trivial robot property. There does not exist
an algorithmic procedure that will enable an observer to tell, given any robot
(with potentially unbounded memory) that is programmed by a structured program,
whether the actions of the robot always satisfy *P*.

The paper proof builds an explicit Sense–Plan–Act program `τₓ` (Fig. 1) from
non-triviality (Def. 3): pace a simulation of `Mₓ` on `x` across operational
cycles; run like a base program `ρ` that always satisfies *P* until the
simulation reports halt, then switch to alternative actions that violate *P*.
That construction is longer than the reduction step because it has to stay
inside their robotics programming model (hyper-commands, structured programs,
paced finite cycles, unbounded memory for the TM configuration). Once `τₓ`
exists, the remainder is a short reduction from the diagonal halting set.

## What Lean checks

This module does **not** mechanize Def. 3 or Fig. 1. It packages the effective
existence of such a `τ` as `SwitchingConstruction` and proves: if that
certificate exists, no total computable `Verifier` is sound and complete for
`AlwaysSatisfies` on every `structured` program. That is the reduction half of
Theorem 1 / Corollary 1; relationship to the paper is therefore `RELATED`.

Interface (total action traces, not geometry):

* `Scenario` can encode an environment, observation history, and scheduler;
* `behavior program scenario cycle` is the action produced in that cycle; and
* `acceptable scenario cycle action` is the property being checked.

`SwitchingConstruction` is where potentially unbounded memory and the paper's
program-composition assumptions enter. Consequently,
`action_safety_unverifiable` does not apply automatically to finite-state or
otherwise bounded program classes, and it does not rule out sound incomplete
verification. Instantiating this interface for a concrete robotics or AI-system
model remains a separate modeling and review task.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Verification.Robot

/-- A total action trace for each complete scenario. -/
public abbrev Behavior (Scenario Action : Type*) := Scenario → ℕ → Action

/-- Every action produced in every scenario and operational cycle is acceptable. -/
public abbrev AlwaysSatisfies
    {Program Scenario Action : Type*}
    (behavior : Program → Behavior Scenario Action)
    (acceptable : Scenario → ℕ → Action → Prop)
    (program : Program) : Prop :=
  ∀ scenario cycle, acceptable scenario cycle (behavior program scenario cycle)

/--
A total computable Boolean procedure that is correct on the designated class of
structured programs.  Its behavior outside that class is intentionally
unconstrained.
-/
public structure Verifier
    {Program Scenario Action : Type*} [Primcodable Program]
    (structured : Program → Prop)
    (behavior : Program → Behavior Scenario Action)
    (acceptable : Scenario → ℕ → Action → Prop) where
  decide : Program → Bool
  computable_decide : Computable decide
  correct : ∀ program, structured program →
    ((decide program : Prop) ↔ AlwaysSatisfies behavior acceptable program)

/--
An effective version of the paper's `τ` construction.  For a fixed input,
`compile source` keeps producing acceptable actions exactly when the encoded
source computation does not halt; if it halts, the compiled program switches
to behavior that violates the universal action property.

Requiring `compile` to be computable and its outputs to be structured prevents
the reduction from being smuggled in as an arbitrary logical assumption.
-/
public structure SwitchingConstruction
    {Program Scenario Action : Type*} [Primcodable Program]
    (structured : Program → Prop)
    (behavior : Program → Behavior Scenario Action)
    (acceptable : Scenario → ℕ → Action → Prop) where
  sourceInput : ℕ
  compile : Code → Program
  computable_compile : Computable compile
  compiled_structured : ∀ source, structured (compile source)
  satisfies_iff_nonhalting : ∀ source,
    AlwaysSatisfies behavior acceptable (compile source) ↔
      ¬(eval source sourceInput).Dom

/--
No total computable verifier is sound and complete for the universal action
property on every structured program when the program model admits the
effective switching construction above.

Paper correspondence (UU-PCS-2021-02):

* **Theorem 1** — no algorithmic observer for always-*P* on arbitrary robots
  with potentially unbounded memory, for non-trivial *P*.
* **Corollary 1** — same conclusion restricted to structured programs.

Lean proves the **conditional reduction**: given `SwitchingConstruction`
(the paper's `τₓ` construction abstracted), no total `Verifier` exists. It
does not derive that construction from the paper's Def. 3 non-triviality
inside a Sense–Plan–Act syntax. The paper uses the diagonal set
`K = {x | φₓ(x)↓}`; this statement uses Mathlib's fixed-input
`(eval source sourceInput).Dom`, an equivalent undecidable source problem.
See `docs/guide/robot-verification-model.md` for extracted paper text and the
step-by-step comparison.
-/
public theorem action_safety_unverifiable
    {Program Scenario Action : Type*} [Primcodable Program]
    (structured : Program → Prop)
    (behavior : Program → Behavior Scenario Action)
    (acceptable : Scenario → ℕ → Action → Prop)
    (construction : SwitchingConstruction structured behavior acceptable) :
    ¬ Nonempty (Verifier structured behavior acceptable) := by
  rintro ⟨verifier⟩
  let decision : Code → Bool := fun source =>
    verifier.decide (construction.compile source)
  have decisionComputable : Computable decision :=
    verifier.computable_decide.comp construction.computable_compile
  have decisionCorrect : ∀ source,
      ((decision source : Prop) ↔ ¬(eval source construction.sourceInput).Dom) := by
    intro source
    exact
      (verifier.correct (construction.compile source)
        (construction.compiled_structured source)).trans
        (construction.satisfies_iff_nonhalting source)
  have nonhaltingComputable :
      ComputablePred fun source : Code =>
        ¬(eval source construction.sourceInput).Dom :=
    ComputablePred.computable_iff.mpr ⟨decision, decisionComputable, by
      funext source
      exact propext (decisionCorrect source).symm⟩
  have haltingComputable :
      ComputablePred fun source : Code =>
        (eval source construction.sourceInput).Dom := by
    classical
    simpa only [not_not] using nonhaltingComputable.not
  exact AISafetyAtlas.Computability.halting_problem
    construction.sourceInput haltingComputable

end AISafetyAtlas.Verification.Robot
