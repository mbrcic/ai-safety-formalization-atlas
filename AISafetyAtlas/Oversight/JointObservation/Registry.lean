module

public import AISafetyAtlas.Oversight.JointObservation.Coverage

/-!
# Audit registries along a value chain: what publishing declarations can settle

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../../docs/agent/policy/ledger-coverage.md)'s four
layers: *(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is
`AISafetyAtlas.Oversight.JointObservation`, which is about principals, evidence
and coverage and names no audit scheme. What is added here is the arrow to a
governance question, at the coalition level the question is actually asked at.

## The question

Reuel, Bucknall et al., *Open Problems in Technical AI Governance*, TMLR
04/2025:

> **Open Problem 60.** *"How can audit registries be used to provide end-to-end
> verification along the AI value chain?"*
>
> **Open Problem 101.** An auditable log of all actors.

## The answer this module states

`EvidenceArchitecture` already separates what a principal *holds*
(`privateState`) from what it *declares* (`emit`). A value chain in which every
actor files a return is then two different observers:

* `registryCandidate` — the registry: each member's **declared** view, and
  nothing else.
* `consortiumCandidate` — the same actors pooling the **evidence itself**.

`consortium_covers_of_registry_covers` says the registry is never the stronger
of the two: anything a filing settles, the evidence behind the filing settles.
That is the half that makes registries worth building, and it holds for every
coalition without hypotheses.

`not_registry_covers_of_emit_collision` is the other half and is Open Problem
60's obstruction. If two executions produce identical filings from every member
while differing on the hazard, no registry over that coalition settles it —
**however many actors the chain contains**. Enrolling more filers helps only if
some new filing separates the two executions; filers whose filings also agree
leave it unrepaired, because the obstruction is in what a filing discards, not
in how many were collected.

So *end-to-end* is the wrong axis when the coverage failure is per-actor: the
repair is a richer declared interface, not a longer chain.

## What this does not claim

Value-chain actors are not modelled. Who occupies which position, and which
principal observes which part of a real pipeline, is a layer-4 assignment and is
not made here. Nothing in this module says that any real registry schema loses
the information it would need; `emit` is an arbitrary projection and may be
injective, in which case the collision simply does not arise and both candidates
cover exactly the same hazards.

Coverage here is **informational and under truthful reporting**, as
`CandidateObservation.observe` fixes. A registry whose filers may misreport is a
different question and this module does not touch it.
-/

namespace AISafetyAtlas.Oversight.JointObservation

universe u v w

variable {A : EvidenceArchitecture.{u, v}}

/--
**An audit registry over a coalition**: every member files its declared
interface, and the registry is the tuple of those filings.

This is `localCandidate` at a coalition rather than at one principal, which is
the level Open Problem 60 asks about.
-/
@[expose] public def registryCandidate (A : EvidenceArchitecture.{u, v})
    (C : Finset A.Principal) : CandidateObservation A where
  coalition := C
  Output := (i : {p // p ∈ C}) → A.EmittedView i.1
  joint := fun held i => A.emit i.1 (held i)

/--
**The same actors pooling the evidence itself**, rather than their filings.

`privateSingletonCandidate` is this at one principal. Keeping the two candidates
apart is what makes "the registry is insufficient" a statement about the
declared interface rather than about the hazard.
-/
@[expose] public def consortiumCandidate (A : EvidenceArchitecture.{u, v})
    (C : Finset A.Principal) : CandidateObservation A where
  coalition := C
  Output := CoalitionInput A C
  joint := id

@[simp] public theorem registryCandidate_observe
    (C : Finset A.Principal) (σ : A.Execution) :
    (registryCandidate A C).observe σ =
      fun i : {p // p ∈ C} ↦ A.emit i.1 (A.privateState i.1 σ) := rfl

@[simp] public theorem consortiumCandidate_observe
    (C : Finset A.Principal) (σ : A.Execution) :
    (consortiumCandidate A C).observe σ =
      fun i : {p // p ∈ C} ↦ A.privateState i.1 σ := rfl

/--
**A registry is never stronger than the evidence behind it.**

Whatever a set of filings settles, the private evidence those filings were
computed from settles too, by composing the registry's decision rule with
`emit`. No hypothesis: this holds at every coalition and every hazard. It bounds
a registry from above; it says nothing about whether filing is worth requiring.
-/
public theorem consortium_covers_of_registry_covers
    {C : Finset A.Principal} {h : Hazard A}
    (hreg : Covers (registryCandidate A C) h) :
    Covers (consortiumCandidate A C) h := by
  obtain ⟨decideHazard, hdec⟩ := hreg
  exact ⟨fun held ↦ decideHazard (fun i ↦ A.emit i.1 (held i)), hdec⟩

/--
**Open Problem 60's obstruction.** Two executions on which every member files
identically, and which differ on the hazard, refute registry coverage outright.

The coalition is arbitrary, so this says something stronger than it looks:
enlarging the chain repairs it only through a member whose filing separates the
two executions. A new member whose filing agrees across them as well leaves the
enlarged registry still unable to separate them, however many are added. The obstruction lives in what a filing
discards, not in how many filings were gathered — so the repair is a richer
declared interface and not a longer value chain.
-/
public theorem not_registry_covers_of_emit_collision
    {C : Finset A.Principal} {h : Hazard A} {σ τ : A.Execution}
    (hfile : ∀ i : {p // p ∈ C},
      A.emit i.1 (A.privateState i.1 σ) = A.emit i.1 (A.privateState i.1 τ))
    (hhazard : h σ ≠ h τ) :
    ¬ Covers (registryCandidate A C) h := by
  refine Knowledge.not_knowable_of_collision ?_ hhazard
  exact funext hfile

/--
**Both halves together**, which is the shape the question is asked in: the
evidence behind the filings settles the hazard, and the filings do not.

A consumer holding this pair has the precise diagnosis — the chain is not too
short, the interface is too lossy.
-/
public theorem consortium_covers_and_registry_does_not
    {C : Finset A.Principal} {h : Hazard A} {σ τ : A.Execution}
    (hcons : Covers (consortiumCandidate A C) h)
    (hfile : ∀ i : {p // p ∈ C},
      A.emit i.1 (A.privateState i.1 σ) = A.emit i.1 (A.privateState i.1 τ))
    (hhazard : h σ ≠ h τ) :
    Covers (consortiumCandidate A C) h ∧ ¬ Covers (registryCandidate A C) h :=
  ⟨hcons, not_registry_covers_of_emit_collision hfile hhazard⟩

end AISafetyAtlas.Oversight.JointObservation
