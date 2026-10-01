# Bridge review — `Sovereignty.Attestation.attestation_is_not_the_claim`

**Row `LAND-SOV-AUTH-001` · module `AISafetyAtlas/Sovereignty/Attestation.lean` · `HUMAN_REVIEW`**

Siblings: [`obedience_does_not_give_authority`](review-obedience-does-not-give-authority.md),
[`properties_are_independent`](review-properties-are-independent.md),
[`power_over_a_matter_does_not_compose`](review-power-over-a-matter-does-not-compose.md).

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem attestation_is_not_the_claim :
    ∃ (C : Type) (A : Record C) (c : C), A.attested c ∧ ¬ A.holds c
```

`Record` pairs what an attestation asserts of a claim with whether the claim
holds. **Nothing relates the two fields, which is the entire point.** `A4` from
`Sovereignty.Authority`.

## What to check

1. **The struct is named `Record`, not `Attestation`** — the obvious name
   produced `Attestation.Attestation`. Cosmetic, but it is the kind of rename
   that makes a later reader think two objects exist.
2. **The strength is that it assumes nothing.** It says the link has to come from
   somewhere, not that no link exists. **A concrete scheme in which signing does
   establish truth — because the signer checked, and the check is sound — is not
   refuted by anything here.** It is required to say what it checked.
3. It is a bare existential over abstract types. Decide whether a bare
   existential earns a `BRIDGE` grade, or whether the AI reading lives entirely
   in the prose. That is the honest question for this one.

## Allowed claim

> Attestation and truth are different predicates. A record can assert what is not
> so, whatever the signature scheme, because nothing about being a record relates
> it to being true — so a proof that a claim was attested is not a proof of the
> claim.

## Forbidden

- **Not** "attestation is worthless." This is about labels *as such*.
- **Not** a claim about any signature scheme, evaluation report, model card or
  compliance declaration. The atlas has none.
- **Not** a cryptographic statement. No adversary, no forgery, no key.
- **Not** the converse on its own — that an unattested system is non-compliant is
  refused by `attested_does_not_transfer` (not graded), and the failure mode is a
  registry read as a whitelist.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Signed model cards prove nothing." | about the label as such; a scheme that says what it checked is untouched |
| "So certification schemes are broken." | nothing here is about any scheme |
| "This is a result about digital signatures." | no cryptography is present |

## Witness

`AISafetyAtlas/Examples/Sovereignty/Governance.lean`.
