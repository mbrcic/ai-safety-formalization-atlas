# Bridge review — `Verification.FullAccess.no_fullAccessVerifier_of_extensional`

**Row `LAND-VERIF-FULLACCESS-001` · module `AISafetyAtlas/Verification/FullAccess.lean` · `HUMAN_REVIEW`**

Siblings: [`fullAccessVerifier_exactArtifact`](review-fullaccessverifier-exactartifact.md),
[`access_is_not_what_separates_them`](review-access-is-not-what-separates-them.md).
Arrow to Reuel, Bucknall et al., TMLR 04/2025, **Open Problem 55**.

**The highest misreading risk of any bridge in the repository.** The sentence
*"no verifier exists even with full access"* is false, and the module is built so
it cannot be read off this theorem.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 on the allowed claim as sharpened. |

## The statement

```lean
public theorem no_fullAccessVerifier_of_extensional (P : SyntacticProperty)
    (hextensional : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ P ↔ cg ∈ P))
    {accepted rejected : Code} (haccepted : accepted ∈ P) (hrejected : rejected ∉ P) :
    ¬ Nonempty (FullAccessVerifier P)
```

`FullAccessVerifier P` is a **total computable** procedure reading the code
itself. Via `Computability.rice_code_iff`.

## What to check

1. **`hextensional` is Rice's hypothesis, written where it can be seen** — not
   hidden in a structure field. A reader can tell exactly which properties are
   covered: those depending only on the computed function.
2. **Totality is part of the negative claim.** A correct answer on **every**
   code. Procedures that abstain, restrict their class, or are sound in one
   direction are not ruled out by anything here.
3. **It must be read beside its sibling**, which builds a verifier at the same
   access level. Signing this one alone is what produces the false sentence.

## Allowed claim

> With full access to the source, no total, computable and always-correct
> procedure decides a nontrivial property that depends only on what the code
> computes. Having the artifact does not help for that class of property.

## Forbidden

- **Not** "verification with full access is impossible." The module contains a
  verifier that works at full access.
- **Not** evidence that interpretability is hard. Weights, activations, circuit
  structure, parameter count and provenance are **non-extensional**; Rice is
  silent on them. Those are Open Problems 21 and 22 and **nothing here bears on
  them.**
- **Not** a claim that any governance-relevant property is extensional.
- **Not** about trained models. A `Code` is a Mathlib program code.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Rice shows white-box verification fails." | the sibling exists at the same access level |
| "So mechanistic interpretability is provably limited." | non-extensional; the hypothesis is not met |
| "Weights are code, so this applies to models." | layer-4 assignment, not made |
| "A sound-but-incomplete scanner is ruled out." | `FullAccessVerifier` is total |

## Witness

`AISafetyAtlas/Examples/Verification/FullAccess.lean`.
