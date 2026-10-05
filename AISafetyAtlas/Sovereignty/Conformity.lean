module

public import AISafetyAtlas.Sovereignty.Catalogue

/-!
# Passing every item of a checklist, and not being operable

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Catalogue`, which is
about commitments and demand catalogues and mentions no AI system. What is added
here is the reading as a **conformity assessment**, and what that reading makes
checkable.

## The question

A conformity assessment checks requirements. It checks them **one at a time**:
for each requirement, is there a way of operating the system that meets it? A
system that answers yes to every item passes.

What a deployment needs is different: **one** way of operating that meets every
requirement at once, fixed before anyone knows which requirement will be
examined.

## What is stated

`Assessment` is a system, the party that operates it, and the requirements it is
assessed against.

* `PassesEach` is the checklist reading — `Demandwise`, one commitment per
  requirement, chosen knowing which requirement it must serve.
* `Operable` is the deployment reading — `DemandwiseUniform`, a single
  commitment whose outcomes lie inside every requirement.
* `passesEach_of_operable` — operability implies passing, so the checklist is
  not measuring the wrong thing. It is measuring a **weaker** thing.
* `conflicting_requirements_are_not_operable` — two requirements with nothing in
  common admit no single commitment, however each looks alone.
* `passes_every_check_and_not_operable` is the pair stated together: an
  assessment can pass every item of its own checklist and have no way of being
  run. The certificate is then evidence about the assessment procedure and not
  about the deployment.
* `operable_meets_all_at_once` says what operability buys that passing does not:
  the intersection of every requirement is forced, which is the property a
  deployment actually needs.

## What this does not claim

The atlas has **no requirement language, no assessment procedure and no
certificate**. Nothing here says any real conformity scheme checks requirements
one at a time — a scheme that demands a single documented operating policy and
tests it against the whole catalogue is simply not an instance of `PassesEach`,
and that is the useful reading: the distinction is the property a scheme must be
designed to have.

Nor is a conflicting catalogue a defect of the assessor. Print's own conclusion
is that conflicting requirements need allocation, time-indexing or arbitration —
the obstruction is in the requirement set, and naming which pair is disjoint is
the actionable output.

Identifying `requirements` with any real standard is layer 4 and is not done
here.
-/

namespace AISafetyAtlas.Sovereignty.Conformity

universe u v w

/--
A **conformity assessment**: a system, the party that operates it, and the
requirements it is assessed against.

`operator` is a coalition rather than an individual because the party that can
commit to an operating policy is often several — a vendor and a deployer, say —
and nothing below needs them to be one.
-/
public structure Assessment (N : Type u) (X : Type v) where
  /-- The system, as a game form: who can do what, and what results. -/
  system : GameForm.{u, v, w} N X
  /-- The party or parties that commit to an operating policy. -/
  operator : Set N
  /-- The requirements the system is assessed against. -/
  requirements : Set (Set X)

variable {N : Type u} {X : Type v} (A : Assessment.{u, v, w} N X)

/--
**The checklist reading.** For each requirement separately, the operator has
*some* way of meeting it. Nothing asks for the ways to be the same way.
-/
@[expose] public def PassesEach : Prop :=
  Demandwise A.system A.operator A.requirements

/--
**The deployment reading.** *One* commitment whose possible outcomes lie inside
every requirement at once — chosen before anyone knows which requirement will be
examined.
-/
@[expose] public def Operable : Prop :=
  DemandwiseUniform A.system A.operator A.requirements

/-- **Operability implies passing.** The checklist is not measuring the wrong
quantity; it is measuring a strictly weaker one. -/
public theorem passesEach_of_operable (h : Operable A) : PassesEach A :=
  demandwise_of_demandwiseUniform h

/-- **What operability buys.** A single commitment forces the intersection of
every requirement, which is the property a deployment needs and the checklist
never establishes. -/
public theorem operable_meets_all_at_once (h : Operable A) :
    Forces A.system A.operator (⋂₀ A.requirements) :=
  forces_sInter_of_demandwiseUniform h

/-- **Two requirements with nothing in common admit no operating policy**,
however each of them looks when examined on its own. -/
public theorem conflicting_requirements_are_not_operable
    [∀ i, Nonempty (A.system.strategy i)] {Φ Ψ : Set X}
    (hΦ : Φ ∈ A.requirements) (hΨ : Ψ ∈ A.requirements) (hd : Disjoint Φ Ψ) :
    ¬ Operable A :=
  not_demandwiseUniform_of_disjoint hΦ hΨ hd

/--
**Both at once: a system can pass every item of its checklist and have no way of
being run.**

The hypothesis is the assessment's own result — it passed. The conclusion keeps
that and adds that no single operating policy exists, on the strength of a
disjoint pair inside the requirement set itself.

So a certificate of this shape is evidence about the assessment procedure and
not about the deployment, and the defect is visible in the requirements without
examining the system at all.
-/
public theorem passes_every_check_and_not_operable
    [∀ i, Nonempty (A.system.strategy i)] {Φ Ψ : Set X}
    (hpass : PassesEach A)
    (hΦ : Φ ∈ A.requirements) (hΨ : Ψ ∈ A.requirements) (hd : Disjoint Φ Ψ) :
    PassesEach A ∧ ¬ Operable A :=
  ⟨hpass, conflicting_requirements_are_not_operable A hΦ hΨ hd⟩

/--
**Dropping a requirement cannot create the conflict, so the diagnosis is
stable.** Operability is antitone: if a sub-catalogue is already inoperable, so
is the whole one. A scheme that responds to this obstruction by removing
requirements has to remove one of the conflicting pair, not merely some
requirement.
-/
public theorem not_operable_of_subset_not_operable {ℛ : Set (Set X)}
    (hsub : ℛ ⊆ A.requirements) (h : ¬ DemandwiseUniform A.system A.operator ℛ) :
    ¬ Operable A :=
  fun hop => h (DemandwiseUniform.mono hop hsub)

end AISafetyAtlas.Sovereignty.Conformity
