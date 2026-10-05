module

public import AISafetyAtlas.Sovereignty.Authority

/-!
# What an attestation attests, and the four things it is not

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Authority`, whose `A4`
and `B8` are bare existentials over abstract types and mention no AI system.
What is added here is the reading as **attestations about an AI system**, and
the consequence for how such claims may be combined.

## The question

Assurance about an AI system arrives as attested claims: a signed evaluation
result, a model card, a provenance record, a compliance declaration. Each says
that some property was checked. The recurring move is to treat one such claim as
carrying another — the artifact is signed, therefore what it says is true; the
use was authorized, therefore it was beneficial; the output is private,
therefore it is accurate.

## What is stated

`Record` pairs what an attestation asserts of a claim with whether the claim
holds. Nothing relates the two fields, which is the entire point.

* `attestation_is_not_the_claim` — `A4`: there is an attestation that asserts
  something false. So no signature, however verified, is a proof of the thing
  signed; attestation and truth are different predicates and a verifier
  establishes the first.
* `attested_does_not_transfer` — the same fact in the form the argument is
  actually made: attestation does not imply the claim, *and* the claim does not
  imply attestation. The second direction matters too — an unattested system is
  not thereby non-compliant, which is the failure mode of a registry read as a
  whitelist.
* `properties_are_independent` — `B8`: two attested properties admit all four
  combinations. Every pairing of accuracy, privacy, benefit and authorization
  occurs, so linking any two of them takes an assumption about the system and
  never a relabelling of the record.
* `no_property_implies_another` is that stated as the refusal it licenses: for
  such a pair, neither direction of implication holds.

## What this does not claim

The atlas has **no signature scheme, no evaluation report and no compliance
declaration.** These are statements about *labels*, and their strength is
exactly that they assume nothing: they say that the link has to come from
somewhere, not that no link exists. A concrete scheme in which signing really
does establish truth — because the signer checked, and the check is sound — is
not refuted by anything here. It is required to say what it checked.

Symmetrically, `properties_are_independent` does not say that accuracy and
privacy are unrelated in any real system. It says the relation is not carried by
the fact that both are recorded, so an argument that moves from one to the other
must name the mechanism.

Identifying `attested` with any real attestation, or the labels with any real
pair of properties, is layer 4 and is not done here.
-/

namespace AISafetyAtlas.Sovereignty.Attestation

universe u

/--
An **attestation record** about claims of type `C`.

* `attested c` — a record asserts `c`.
* `holds c` — `c` is the case.

The two fields are unrelated by construction. Any regime in which they are
related supplies that relation as a hypothesis, and naming it is the work.
-/
public structure Record (C : Type u) where
  /-- A record asserts this claim. -/
  attested : C → Prop
  /-- The claim is the case. -/
  holds : C → Prop

/--
**`A4` as an attestation: a record can assert what is not so.**

There is an attestation and a claim it asserts which does not hold. So the two
predicates are not the same predicate, and a proof that a claim was attested is
not, without more, a proof of the claim, because nothing about being a record
relates it to being true.
-/
public theorem attestation_is_not_the_claim :
    ∃ (C : Type) (A : Record C) (c : C), A.attested c ∧ ¬ A.holds c := by
  obtain ⟨Stmt, verify, truth, s, hv, ht⟩ := exists_verified_untrue
  exact ⟨Stmt, ⟨verify, truth⟩, s, hv, ht⟩

/--
**Neither direction transfers**, which is the form in which the mistake is
usually made.

Forwards: an attested claim need not hold — a signed report is not a true report.
Backwards: a claim that holds need not be attested — an unlisted system is not
thereby non-compliant, which is what a registry read as a whitelist assumes.
-/
public theorem attested_does_not_transfer :
    ∃ (C : Type) (A : Record C),
      (¬ ∀ c, A.attested c → A.holds c) ∧ ¬ ∀ c, A.holds c → A.attested c := by
  refine ⟨Bool, ⟨fun c => c = false, fun c => c = true⟩, ?_, ?_⟩
  · exact fun h => by simpa using h false rfl
  · exact fun h => by simpa using h true rfl

/--
**`B8` as attested properties: all four combinations occur.**

Two properties recorded about the same system — accuracy and authorization,
privacy and benefit, provenance and safety — admit every pairing. Neither
presence nor absence of one constrains the other.

The four witnesses are named separately because the useful reading is that each
quadrant is inhabited, not merely that the implication fails somewhere.
-/
public theorem properties_are_independent :
    ∃ (Sys : Type) (p q : Sys → Prop) (neither onlyQ onlyP both : Sys),
      (¬ p neither ∧ ¬ q neither) ∧ (¬ p onlyQ ∧ q onlyQ) ∧
        (p onlyP ∧ ¬ q onlyP) ∧ (p both ∧ q both) :=
  exists_all_four_combinations

/--
**The refusal it licenses.** For such a pair of properties, neither implication
holds, so an argument that moves from one to the other is making an assumption
about the system rather than reading its record.
-/
public theorem no_property_implies_another :
    ∃ (Sys : Type) (p q : Sys → Prop),
      (¬ ∀ s, p s → q s) ∧ ¬ ∀ s, q s → p s := by
  obtain ⟨Sys, p, q, _, onlyQ, onlyP, _, -, hQ, hP, -⟩ := exists_all_four_combinations
  exact ⟨Sys, p, q, fun h => hP.2 (h onlyP hP.1), fun h => hQ.1 (h onlyQ hQ.2)⟩

end AISafetyAtlas.Sovereignty.Attestation
