module

public import AISafetyAtlas.Verification

/-!
# Full access to the code: what it settles, and why Rice is not the reason

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four
layers: *(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Verification` and
`AISafetyAtlas.Computability`, which hold Rice's theorem in two forms. What is
added here is the arrow to a verification question — and, as much, a **fence**
around it.

## The question

Reuel, Bucknall et al., *Open Problems in Technical AI Governance*, TMLR
04/2025:

> **Open Problem 55.** *"How can model properties be verified with full access
> to the model?"*

## What this module states, and the line it does not cross

The natural sentence to reach for is *"no verifier exists even with full
access"*. **That sentence is false**, and this module is built so that it cannot
be read off it.

`FullAccessVerifier P` is a total computable procedure that reads **the code
itself** and decides membership in a set of codes `P`. The same verifier type
appears in both theorems below. Access is held fixed at the maximum; only the
property changes.

* `no_fullAccessVerifier_of_extensional` — if `P` is **extensional** (codes with
  the same behaviour are alike under it) and nontrivial, no such verifier
  exists. Having the source does not help. This is Rice, through
  `AISafetyAtlas.Computability.rice_code_iff`.
* `fullAccessVerifier_exactArtifact` — and for the property *"this code is
  exactly `c₀`"*, a verifier **does** exist, with full access and nothing else.

`exactArtifact_not_extensional` is what joins them: two distinct codes computing
the same function are not alike under code identity, so Rice's hypothesis fails
for it. `access_is_not_what_separates_them` puts both halves side by side at the
same access level, which is the honest statement:

> **Rice bounds the behavioral half of Open Problem 55.** What fails is not
> access; it is extensionality.

## What this module does not claim

**Not that verification with full access is impossible.** The claim is confined
to extensional properties — properties that depend only on the computed
function. Properties of weights, activations, circuit structure, parameter
count, training provenance or the loss landscape are **not** extensional: two
codes computing the same function can differ in all of them, and Rice says
nothing whatever about those.

Those are Open Problems 21 and 22 of the same paper — mechanistic analysis of
model internals, and how far it generalizes — and **this module is not evidence
that they are hard.** Reading it as such would be the precise error it exists to
prevent. `fullAccessVerifier_exactArtifact` is the smallest demonstration that
the non-extensional side is not closed by Rice; it is a demonstration and not a
survey, and nothing here says which non-extensional properties are tractable.

**No real system is modelled.** A `Code` is a Mathlib program code. Whether a
trained model's weights are a program code in the relevant sense, and whether
any property a governance regime would ask about is extensional, are layer-4
assignments and neither is made here.

**Totality is part of the negative claim.** `FullAccessVerifier` demands an
answer on every code, always correct. Procedures that may abandon a case, answer
only on a restricted class, or be sound in one direction only are not ruled out
by anything here.
-/

namespace AISafetyAtlas.Verification.FullAccess

open Nat.Partrec (Code)
open Nat.Partrec.Code

/--
**A property of the artifact as written**: a set of program codes, with no
requirement that it respect behaviour.

Deliberately not `BehavioralProperty`. The point of the module is the gap
between the two, and a syntactic property is what sits on the other side of it.
-/
public abbrev SyntacticProperty := Set Code

/--
**A verifier with full access**: a total computable procedure that reads the
code itself and decides the property, correctly on every code.

The same structure is used for both halves below, which is what makes the
comparison a comparison — access is maximal and fixed, and only the property
varies.
-/
public structure FullAccessVerifier (P : SyntacticProperty) where
  /-- The decision procedure, reading the code. -/
  decide : Code → Bool
  /-- It is computable. -/
  computable_decide : Computable decide
  /-- And correct on every code, in both directions. -/
  correct : ∀ c, (decide c : Prop) ↔ c ∈ P

/-! ## The behavioral half: full access does not help -/

/--
**No full-access verifier for a nontrivial extensional property.**

`hextensional` is Rice's hypothesis, stated where it can be seen: codes
computing the same function are alike under `P`. Given it, and one code in `P`
with one code outside, no total computable procedure decides `P` from the source.

So Open Problem 55's *"with full access"* framing, read as *access is the
bottleneck*, is answered negatively — **for this class of property and no
other.**
-/
public theorem no_fullAccessVerifier_of_extensional (P : SyntacticProperty)
    (hextensional : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ P ↔ cg ∈ P))
    {accepted rejected : Code} (haccepted : accepted ∈ P) (hrejected : rejected ∉ P) :
    ¬ Nonempty (FullAccessVerifier P) := by
  rintro ⟨verifier⟩
  have hcomputable : ComputablePred (fun c : Code => c ∈ P) := by
    refine ComputablePred.computable_iff.mpr
      ⟨verifier.decide, verifier.computable_decide, ?_⟩
    funext c
    exact propext (verifier.correct c).symm
  rcases (AISafetyAtlas.Computability.rice_code_iff P hextensional).mp hcomputable with
    hempty | huniv
  · rw [hempty] at haccepted
    exact haccepted
  · rw [huniv] at hrejected
    exact hrejected (Set.mem_univ rejected)

/-! ## The other half: full access decides plenty -/

/-- **The property of being one particular artifact.** Syntactic, and the
smallest non-extensional property there is. -/
@[expose] public def exactArtifact (c₀ : Code) : SyntacticProperty := {c | c = c₀}

/--
**And a full-access verifier for it exists.** Compare the code with `c₀`.

Primitive recursive, let alone computable. This is not a deep fact and it is not
meant to be: it is the counterexample that stops
`no_fullAccessVerifier_of_extensional` from being read as a claim about access.
-/
public theorem fullAccessVerifier_exactArtifact (c₀ : Code) :
    Nonempty (FullAccessVerifier (exactArtifact c₀)) := by
  have hprim : PrimrecPred (fun c : Code => c = c₀) :=
    Primrec.eq.comp Primrec.id (Primrec.const c₀)
  obtain ⟨check, hcomputable, hcorrect⟩ :=
    ComputablePred.computable_iff.mp hprim.computablePred
  exact ⟨{ decide := check
           computable_decide := hcomputable
           correct := fun c => by
             simp only [exactArtifact, Set.mem_ofPred_eq]
             exact (iff_of_eq (congrFun hcorrect c)).symm }⟩

/--
**Why Rice does not reach it.** Two distinct codes computing the same function
are not alike under code identity, so the extensionality hypothesis fails.

The hypothesis is the whole difference between the two halves, and this makes
that explicit rather than leaving it to the reader.
-/
public theorem exactArtifact_not_extensional {c₀ c₁ : Code}
    (hsameBehaviour : eval c₀ = eval c₁) (hdistinct : c₀ ≠ c₁) :
    ¬ ∀ cf cg : Code, eval cf = eval cg →
      (cf ∈ exactArtifact c₀ ↔ cg ∈ exactArtifact c₀) := by
  intro hextensional
  exact hdistinct ((hextensional c₀ c₁ hsameBehaviour).mp rfl).symm

/--
**Open Problem 55, both halves at the same access level.**

One property of the source is undecidable from the source and another is
decidable from it. The verifier type is identical, the access is identical, and
the only thing that changed is whether the property depends on behaviour alone.

**Rice bounds the behavioral half of Open Problem 55.** The non-extensional
half — which is where analysis of model internals lives — is untouched by any of
this, and none of it is evidence that the non-extensional half is hard.
-/
public theorem access_is_not_what_separates_them
    (P : SyntacticProperty)
    (hextensional : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ P ↔ cg ∈ P))
    {accepted rejected : Code} (haccepted : accepted ∈ P) (hrejected : rejected ∉ P)
    (c₀ : Code) :
    ¬ Nonempty (FullAccessVerifier P) ∧
      Nonempty (FullAccessVerifier (exactArtifact c₀)) :=
  ⟨no_fullAccessVerifier_of_extensional P hextensional haccepted hrejected,
    fullAccessVerifier_exactArtifact c₀⟩

end AISafetyAtlas.Verification.FullAccess
