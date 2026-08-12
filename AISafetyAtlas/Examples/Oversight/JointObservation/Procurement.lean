module

public import AISafetyAtlas.Oversight.JointObservation
public import Mathlib.Tactic.DeriveFintype

/-!
# Example — a four-state procurement architecture

A minimal, fully explicit consumer of the joint-observation API. Its purpose is to
validate the interface and to serve as a regression example: every declaration here
is built from the kernel's own vocabulary, so a later change that quietly weakens the
kernel breaks this file.

## The architecture

Two principals. The data owner knows whether the training dataset is access
restricted; the model owner knows whether the checkpoint is access restricted.
Neither restriction is a hazard on its own. The hazard is the *conjunction*: a
restricted dataset combined with a restricted checkpoint leaves the deployed system
externally unauditable.

| Execution | Dataset field | Checkpoint field | Hazard |
|---|---|---|---|
| `sigma00` | unrestricted | public | safe |
| `sigma10` | restricted | public | safe |
| `sigma01` | unrestricted | restricted | safe |
| `sigma11` | restricted | restricted | **hazardous** |

so `h σab = a && b`.

## The declared interface is not empty

The asymmetry is the point. Dataset restriction *is* declared: `emit dataOwner` is
the identity, so the data owner's emitted view carries real information and rules out
many potential collisions. Checkpoint access policy is *not* in the declared
interface: `emit modelOwner` forgets it. The complete existing emitted interface is
therefore genuinely informative and still insufficient — a strictly stronger and more
honest statement than one obtained by declaring nothing at all.

## Two different failures, kept apart

`localCandidate i` sees only what `i` *declares*; `privateSingletonCandidate i` sees
`i`'s full private evidence. The example checks both, because they say different
things. Local monitors fail partly because the interface is lossy. Private singletons
fail even with unrestricted access to one principal's evidence — that failure is about
the *hazard* being relational, and it is what stops a reader from concluding that the
positive joint result recovers information the architecture says does not exist. The
checkpoint bit `b` exists privately throughout; it is simply never emitted, and a
permitted coalition computation may use it without publishing it.

## What is checked

* no candidate in the family of local monitors covers the hazard;
* singleton-data failure over private evidence, with witness `(sigma10, sigma11)`;
* singleton-model failure over private evidence, with witness `(sigma01, sigma11)`;
* the complete emitted interface fails, with witness `(sigma10, sigma11)`, and by
  `postprocess_cannot_repair_collision` so does *arbitrary computation over it*;
* one narrowly permitted joint predicate over coalition-indexed private evidence
  covers the hazard on all four executions;
* everything above holds under the fixed truthful mechanism `M0` only.

This file is a formal API example. Downstream applications, their data, and their
reporting belong in their own repositories and never move upstream into the Atlas.
-/

namespace AISafetyAtlas.Examples.Oversight.JointObservation.Procurement

open AISafetyAtlas.Oversight.JointObservation

/-! ## The four-state universe -/

/-- The two principals holding evidence about the procurement. -/
public inductive Principal
  /-- Holds the training dataset and its access policy. -/
  | dataOwner
  /-- Holds the model checkpoint and its access policy. -/
  | modelOwner
  deriving DecidableEq, Fintype

/-- The four executions, indexed by the two relational bits. -/
public inductive Exec
  /-- Unrestricted dataset, public checkpoint. -/
  | sigma00
  /-- Restricted dataset, public checkpoint. -/
  | sigma10
  /-- Unrestricted dataset, restricted checkpoint. -/
  | sigma01
  /-- Restricted dataset, restricted checkpoint. -/
  | sigma11
  deriving DecidableEq, Fintype

/-- Whether the training dataset is access restricted in this execution. -/
@[expose] public def datasetRestricted : Exec → Bool
  | .sigma00 => false
  | .sigma10 => true
  | .sigma01 => false
  | .sigma11 => true

/-- Whether the model checkpoint is access restricted in this execution. -/
@[expose] public def checkpointRestricted : Exec → Bool
  | .sigma00 => false
  | .sigma10 => false
  | .sigma01 => true
  | .sigma11 => true

/-- Each principal privately holds its own restriction bit. -/
@[expose] public def PrivateField : Principal → Type
  | .dataOwner => Bool
  | .modelOwner => Bool

/--
The declared interface. Dataset restriction is disclosed; checkpoint access policy is
not part of what the model owner declares.
-/
@[expose] public def EmittedView : Principal → Type
  | .dataOwner => Bool
  | .modelOwner => Unit

/-- The evidence each principal actually holds in an execution. -/
@[expose] public def privateState : (i : Principal) → Exec → PrivateField i
  | .dataOwner, σ => datasetRestricted σ
  | .modelOwner, σ => checkpointRestricted σ

/-- The declared interface projection: lossy for the model owner. -/
@[expose] public def emit : (i : Principal) → PrivateField i → EmittedView i
  | .dataOwner, b => b
  | .modelOwner, _ => ()

/-- The procurement evidence architecture. -/
@[expose] public def arch : EvidenceArchitecture where
  Principal := Principal
  Execution := Exec
  PrivateField := PrivateField
  EmittedView := EmittedView
  privateState := privateState
  emit := emit

/-! ### Executability instances

Transported by `inferInstanceAs` rather than declared as architecture fields: the
kernel deliberately keeps `Fintype` and `DecidableEq` out of `EvidenceArchitecture`,
so a consumer that wants to *run* the checker supplies them here. -/

public instance : Fintype arch.Principal := inferInstanceAs (Fintype Principal)

public instance : DecidableEq arch.Principal := inferInstanceAs (DecidableEq Principal)

public instance : Fintype arch.Execution := inferInstanceAs (Fintype Exec)

public instance : DecidableEq arch.Execution := inferInstanceAs (DecidableEq Exec)

/-- Named rather than anonymous because the emitted views differ per principal —
`Bool` for the data owner, `Unit` for the model owner — so the instance cannot be
found by a single `inferInstanceAs` and has to be dispatched on the principal. -/
public instance instDecidableEqEmittedView :
    (i : Principal) → DecidableEq (EmittedView i)
  | .dataOwner => inferInstanceAs (DecidableEq Bool)
  | .modelOwner => inferInstanceAs (DecidableEq Unit)

/-- The relational hazard: restricted dataset **and** restricted checkpoint. -/
@[expose] public def hazard : Hazard arch := fun σ =>
  datasetRestricted σ && checkpointRestricted σ

/-! ## The candidates -/

/--
The data owner acting alone, with **unrestricted access to its own private
evidence** — not merely to what it declares. Strictly stronger than
`localCandidate arch .dataOwner`.
-/
@[expose] public def qC : CandidateObservation arch :=
  privateSingletonCandidate arch .dataOwner

/--
The model owner acting alone, with unrestricted access to its own private evidence.
It knows the checkpoint bit `b` even though `b` never appears in its emitted view;
`qD` failing therefore says the hazard is relational, not that the interface is lossy.
-/
@[expose] public def qD : CandidateObservation arch :=
  privateSingletonCandidate arch .modelOwner

/-- The complete existing emitted interface: the tuple of all declared views. -/
@[expose] public def qEmitted : CandidateObservation arch :=
  emittedArchitectureCandidate arch

/--
The narrowly permitted joint predicate: the two-member coalition computes the
conjunction of the private restriction bits, and reports nothing else.
-/
@[expose] public def qCD : CandidateObservation arch where
  coalition := Finset.univ
  Output := Bool
  joint := fun x =>
    x ⟨.dataOwner, Finset.mem_univ _⟩ && x ⟨.modelOwner, Finset.mem_univ _⟩

/-- Output equality for the joint predicate, so the certified checker can run on it. -/
public instance : DecidableEq qCD.Output := inferInstanceAs (DecidableEq Bool)

/--
Output equality for the complete emitted interface: a dependent tuple over finitely
many principals, each component decidable.
-/
public instance : DecidableEq qEmitted.Output :=
  inferInstanceAs (DecidableEq ((i : Principal) → EmittedView i))

/-! ## Negative results — the declared interface is blind -/

/-- The four executions, listed. This is the finiteness the checker runs on. -/
@[expose] public def execEnum : ExecutionEnum arch where
  toList := [.sigma00, .sigma10, .sigma01, .sigma11]
  complete := by decide

/--
Singleton-data failure witness: the data owner cannot separate a restricted dataset
with a public checkpoint from a restricted dataset with a restricted checkpoint --
even though it sees its own bit in full.
-/
public def dataCollision : CollisionWitness qC hazard where
  left := .sigma10
  right := .sigma11
  sameObservation := rfl
  hazardDiffers := by decide

/--
Singleton-model failure witness: the model owner cannot separate an unrestricted
dataset with a restricted checkpoint from a restricted dataset with a restricted
checkpoint, though it knows the checkpoint bit exactly.
-/
public def modelCollision : CollisionWitness qD hazard where
  left := .sigma01
  right := .sigma11
  sameObservation := rfl
  hazardDiffers := by decide

/--
The complete emitted interface still collides: disclosure of dataset restriction does
not distinguish `sigma10` from `sigma11`, because checkpoint policy is undisclosed.
-/
public def emittedCollision : CollisionWitness qEmitted hazard where
  left := .sigma10
  right := .sigma11
  sameObservation := by funext i; cases i <;> rfl
  hazardDiffers := by decide

/-- The data owner does not cover the hazard, even with full access to its own
private evidence. -/
public theorem not_covers_qC : ¬ Covers qC hazard :=
  not_covers_of_collisionWitness dataCollision

/-- The model owner does not cover the hazard, even with full access to its own
private evidence. -/
public theorem not_covers_qD : ¬ Covers qD hazard :=
  not_covers_of_collisionWitness modelCollision

/-- No monitor built on a single principal's *declared view* covers the hazard. -/
public theorem localFamily_blind : FamilyBlind (localFamily arch) hazard := by
  intro i
  cases i with
  | dataOwner =>
      exact not_covers_of_collisionWitness
        { left := .sigma10, right := .sigma11,
          sameObservation := rfl, hazardDiffers := by decide }
  | modelOwner =>
      exact not_covers_of_collisionWitness
        { left := .sigma01, right := .sigma11,
          sameObservation := rfl, hazardDiffers := by decide }

/-- The complete existing emitted interface does not cover the hazard. -/
public theorem not_covers_qEmitted : ¬ Covers qEmitted hazard :=
  not_covers_of_collisionWitness emittedCollision

/--
**The architectural conclusion.** Not merely the declared tuple, but *any* computation
over the complete existing emitted interface fails. Repair requires changing evidence
access, not adding analysis.
-/
public theorem not_covers_postprocess_qEmitted
    {β : Type} (g : qEmitted.Output → β) :
    ¬ Covers (qEmitted.postprocess g) hazard :=
  postprocess_cannot_repair_collision not_covers_qEmitted g

/-! ## Positive result — one permitted joint predicate suffices -/

/--
The narrowly permitted joint predicate covers the hazard on all four executions.

Coverage is restored by *changing what may be read*, not by computing harder over the
existing interface. The checkpoint bit is used without ever being emitted.
-/
public theorem covers_qCD : Covers qCD hazard :=
  ⟨id, by intro σ; cases σ <;> rfl⟩

/--
The certified checker agrees, **by execution**: `decideCoverage` reduces to the
coverage branch for `qCD`.
-/
public theorem decideCoverage_qCD_covered :
    (decideCoverage execEnum qCD hazard).covered = true := by
  decide

/-- The certified checker reduces to the collision branch for the emitted interface. -/
public theorem decideCoverage_qEmitted_not_covered :
    (decideCoverage execEnum qEmitted hazard).covered = false := by
  decide

/-! ## Scope

Every statement above is about *informational* coverage under the fixed truthful
mechanism `M0`: `observe` feeds each candidate the principals' actual private fields.
Nothing here shows that the coalition would report truthfully, that forming it is
permissible, or that the joint predicate is minimal among alternatives. -/

end AISafetyAtlas.Examples.Oversight.JointObservation.Procurement
