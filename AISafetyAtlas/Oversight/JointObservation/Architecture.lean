module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Joint observation — evidence architecture and candidate observations

The public types, quantifier structure, and constructor signatures for the
joint-observation kernel. These were fixed before any proof work began and may not be
silently reshaped: the coalition-restriction and factorization commitments below are
what every downstream result rests on.

## What is modelled

A multi-principal system in which each principal holds **private evidence** about an
execution and exposes a strictly coarser **emitted view** through a declared
interface. An *observation candidate* is a computation over the private evidence of
one **coalition** of principals. The engineering question is which candidates can
decide a hazard.

## The one structural commitment

Coalition access is enforced **by type**, not by a side condition:

* `CoalitionInput A C` is the product of the private fields of the members of `C`;
* a `CandidateObservation` is a function out of that product.

A candidate therefore *cannot* mention the execution, or a principal outside its own
coalition, even accidentally. The rejected alternative — an unrestricted global
product plus a `RespectsCoalition` hypothesis — leaves an assumption that can be
forgotten, weakened, or discharged in the wrong place. Here illegal evidence access
is a type error.

## Mechanism scope (C4)

Everything here is stated under one fixed idealized **truthful informational
mechanism `M0`**: `observe` feeds a candidate the principals' actual private fields.
Here `M0` is a label for that path, not a separate mechanism object: it is exactly
`CandidateObservation.observe`, with `observe_truthful` exposing the convention for
downstream statements.
Nothing in this module establishes strategic incentive compatibility, equilibrium
reporting, or robustness to deception. Later mechanisms may replace `PrivateField`
with a narrower admissible projection; that generalization is deliberately out of
scope.

No survey coverage row is claimed here; this is oversight infrastructure.
-/

namespace AISafetyAtlas.Oversight.JointObservation

universe u v w t

/-! ## Evidence architecture -/

/--
A multi-principal evidence architecture.

`privateState` is the evidence a principal actually holds in an execution; `emit` is
the declared interface projection producing what that principal exposes. Keeping
`PrivateField` and `EmittedView` distinct types, related only through `emit`, is what
makes "the complete existing emitted interface is insufficient" a statement with
content rather than a restatement of the definitions.
-/
public structure EvidenceArchitecture where
  /-- Principals holding evidence. -/
  Principal : Type u
  /-- Executions of the system under study. -/
  Execution : Type u
  /-- Evidence principal `i` actually holds. -/
  PrivateField : Principal → Type v
  /-- What principal `i` exposes through its declared interface. -/
  EmittedView : Principal → Type v
  /-- The evidence principal `i` holds in a given execution. -/
  privateState : (i : Principal) → Execution → PrivateField i
  /-- The declared interface projection. Generally lossy. -/
  emit : (i : Principal) → PrivateField i → EmittedView i

/--
A hazard is a decidable property of executions. `Bool`-valued on purpose: coverage
is about a *decision* being recoverable from an observation, not about a proposition
being true.
-/
public abbrev Hazard (A : EvidenceArchitecture) : Type _ :=
  A.Execution → Bool

/-! ## Coalition-restricted candidates -/

/--
The evidence available to coalition `C`: exactly the private fields of its members,
and nothing else.

This is the pattern `J : (Π i ∈ C, PrivateField i) → Output` from the design note.
-/
public abbrev CoalitionInput
    (A : EvidenceArchitecture)
    (C : Finset A.Principal) : Type _ :=
  (i : {p // p ∈ C}) → A.PrivateField i.1

/--
A candidate observation: a coalition, an output type, and a computation from the
coalition's evidence to that output.

`Output` is a field rather than a parameter so that a family may mix candidates with
heterogeneous outputs without ever requiring `DecidableEq (CandidateObservation A)`.
-/
public structure CandidateObservation (A : EvidenceArchitecture.{u, v}) where
  /-- Principals whose private evidence this candidate may read. -/
  coalition : Finset A.Principal
  /-- What the candidate reports. -/
  Output : Type w
  /-- The candidate's computation. It has no other access to the execution. -/
  joint : CoalitionInput A coalition → Output

/--
What the candidate reports in an execution, **under the fixed truthful mechanism
`M0`**: each coalition member contributes its actual private field.
-/
@[expose] public def CandidateObservation.observe
    {A : EvidenceArchitecture}
    (q : CandidateObservation A)
    (σ : A.Execution) : q.Output :=
  q.joint (fun i => A.privateState i.1 σ)

/--
**Mechanism boundary (C4), definitionally.**

`observe` is truthful reporting and nothing more. This lemma exists to make the
scope of every downstream coverage claim explicit at the point of use: results are
about *informational* coverage under `M0`, not about incentives.
-/
public theorem observe_truthful
    {A : EvidenceArchitecture}
    (q : CandidateObservation A)
    (σ : A.Execution) :
    q.observe σ = q.joint (fun i => A.privateState i.1 σ) :=
  rfl

/-! ## Candidate families -/

/--
An indexed family of candidates.

Indexed rather than a `Finset` of candidates: candidate structures contain functions,
so requiring `DecidableEq (CandidateObservation A)` would be brittle and would
needlessly force homogeneous output types.

Carries **no** `Fintype Index`. It did, and nothing ever read it: `FamilyBlind` is
`∀ i : F.Index, …`, and `Portfolio := Finset F.Index` needs `DecidableEq`, not finiteness.
A structure carrying a constraint no proof consumes is generality that looks present
without being exercised. Consumers that need finiteness should require it where they use
it — `Portfolio.lean`'s example supplies `Fintype` on its own index type for exactly that
reason.
-/
public structure CandidateFamily (A : EvidenceArchitecture.{u, v}) where
  /-- Index of the family. -/
  Index : Type t
  /-- The indexed candidates. -/
  candidate : Index → CandidateObservation.{u, v, w} A

/-! ## The two distinguished constructors

These make emitted views load-bearing. Without them, "local monitoring fails" and
"the existing interface fails" would be claims about arbitrary functions rather than
about the interface a system actually declares. -/

/--
The **local candidate** for principal `i`: the singleton coalition `{i}`, reporting
exactly `i`'s declared emitted view.

This is what a per-principal monitor can see today.
-/
@[expose] public def localCandidate
    (A : EvidenceArchitecture)
    (i : A.Principal) : CandidateObservation A where
  coalition := {i}
  Output := A.EmittedView i
  joint := fun x => A.emit i (x ⟨i, Finset.mem_singleton_self i⟩)

/--
The **private singleton candidate** for principal `i`: the singleton coalition `{i}`,
reporting `i`'s full private field.

Strictly stronger than `localCandidate i`, which is limited to what `i` declares. A
failure here is therefore a statement about the *hazard*, not about the interface: not
even unrestricted access to one principal's evidence suffices, because the hazard is
relational. Keeping the two constructors apart is what stops a reader from concluding
that a positive joint result recovers information the architecture says is absent.
-/
@[expose] public def privateSingletonCandidate
    (A : EvidenceArchitecture)
    (i : A.Principal) : CandidateObservation A where
  coalition := {i}
  Output := A.PrivateField i
  joint := fun x => x ⟨i, Finset.mem_singleton_self i⟩

/--
The family of all local candidates, indexed by principal.

Derived convenience, not part of the frozen signature set: it is `localCandidate`
packaged so that "no local monitor covers the hazard" is one statement about a family
rather than one statement per principal.
-/
@[expose] public def localFamily
    (A : EvidenceArchitecture) : CandidateFamily A where
  Index := A.Principal
  candidate := localCandidate A

/--
The **complete emitted-interface candidate**: the grand coalition, reporting the
tuple of *all* currently emitted views.

This is the strongest observation the declared interface supports before any
architectural change. Combined with the repair boundary, a failure here rules out
arbitrary post-processing of the existing interface, not merely the obvious monitors.
-/
@[expose] public def emittedArchitectureCandidate
    (A : EvidenceArchitecture)
    [Fintype A.Principal] : CandidateObservation A where
  coalition := Finset.univ
  Output := (i : A.Principal) → A.EmittedView i
  joint := fun x i => A.emit i (x ⟨i, Finset.mem_univ i⟩)

end AISafetyAtlas.Oversight.JointObservation
