# Bridge review — `Verification.FullAccess.fullAccessVerifier_exactArtifact`

**Row `LAND-VERIF-FULLACCESS-001` · module `AISafetyAtlas/Verification/FullAccess.lean` · `HUMAN_REVIEW`**

Siblings: [`no_fullAccessVerifier_of_extensional`](review-no-fullaccessverifier-of-extensional.md),
[`access_is_not_what_separates_them`](review-access-is-not-what-separates-them.md).

**This is a fence post, not a result**, and the review question is whether a
fence post should carry a `BRIDGE` grade.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem fullAccessVerifier_exactArtifact (c₀ : Code) :
    Nonempty (FullAccessVerifier (exactArtifact c₀))
```

Compare the code with `c₀`. Primitive recursive.

## What to check

1. **It is deliberately trivial.** Its whole job is to stop
   `no_fullAccessVerifier_of_extensional` from being read as a claim about
   access. The mathematics is `Primrec.eq`.
2. **The verifier type is identical to the negative theorem's.** Access is held
   fixed at the maximum in both; only the property changes. **Confirm that
   directly from the two signatures** — if the types differed, the module's
   central claim would collapse.
3. `exactArtifact_not_extensional` is what joins them: two distinct codes
   computing the same function are not alike under code identity, so Rice's
   hypothesis fails for it.

## Allowed claim

> With full access to the source, a total and always-correct procedure exists for
> the property *"this code is exactly `c₀`"*. So full access is not, in general,
> the obstruction — whether a verifier exists depends on the property.

## Forbidden

- **Not** a claim that any useful property is decidable at full access. Code
  identity is the smallest possible example and is not a safety property.
- **Not** a claim about release processes, model hashing or provenance checks.
  That `exactArtifact` resembles an artifact-identity check is suggestive and is
  **not** an assignment made here.
- **Not** evidence that non-extensional properties are tractable in general. It
  is one demonstration, not a survey, and the module says so.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Verification works at full access." | for this property; the sibling shows a class where it does not |
| "So hash-checking the deployed model is formally verified." | no real artifact, no hash, no release process is modelled |
| "Non-extensional properties are decidable." | one example; the module refuses the generalisation explicitly |

## Witness

`AISafetyAtlas/Examples/Verification/FullAccess.lean`.
