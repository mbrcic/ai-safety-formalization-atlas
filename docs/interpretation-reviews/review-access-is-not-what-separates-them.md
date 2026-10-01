# Bridge review — `Verification.FullAccess.access_is_not_what_separates_them`

**Row `LAND-VERIF-FULLACCESS-001` · module `AISafetyAtlas/Verification/FullAccess.lean` · `HUMAN_REVIEW`**

Siblings: [`no_fullAccessVerifier_of_extensional`](review-no-fullaccessverifier-of-extensional.md),
[`fullAccessVerifier_exactArtifact`](review-fullaccessverifier-exactartifact.md).

**This is the declaration that carries the module's actual claim.** The other two
are its halves.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem access_is_not_what_separates_them
    (P : SyntacticProperty)
    (hextensional : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ P ↔ cg ∈ P))
    {accepted rejected : Code} (haccepted : accepted ∈ P) (hrejected : rejected ∉ P)
    (c₀ : Code) :
    ¬ Nonempty (FullAccessVerifier P) ∧
      Nonempty (FullAccessVerifier (exactArtifact c₀))
```

## What to check

1. **One property of the source is undecidable from the source and another is
   decidable from it.** Same verifier type, same access, and the only thing that
   changed is whether the property depends on behaviour alone.
2. **The claim this licenses:** *Rice bounds the behavioral half of Open Problem
   55. What fails is not access; it is extensionality.* Decide whether that
   sentence is one you will put your name to — it is the module's reason to
   exist.
3. **The conjunction is the bridge, the halves are the mathematics.** If you
   reject the other two grades and keep this one, the module still says what it
   means to say; if you reject this one, the module loses its point and becomes
   two unrelated facts about `Code`.

## Allowed claim

> With access held fixed at the maximum, a verifier provably does not exist for
> nontrivial properties depending only on the computed function, and provably
> does exist for a property of the artifact itself. So framing a verification
> question as *"if only we had full access"* mislocates the obstruction for the
> behaviour-only class, and says nothing at all about the rest.

## Forbidden

- **Not** "verification is impossible with full access." The second conjunct is
  the refutation of that sentence and sits inside this very statement.
- **Not** evidence about model internals. Open Problems 21 and 22 are untouched,
  and reading this as bearing on them is the precise error the module exists to
  prevent.
- **Not** a claim that any real property falls on either side.
- **Not** a bound on partial or abstaining procedures.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Formal proof that full model access will not let us verify safety." | the statement contains a verifier that works at full access |
| "Interpretability faces a Rice barrier." | non-extensional; explicitly outside |
| "So access policy does not matter." | the module is about this one class of property, and `Knowledge.Access` is where the informativeness of access levels actually lives |

## Witness

Grounded through the generated `Examples/Registry.lean` only; the two halves have
hand-written instances in `Examples/Verification/FullAccess.lean`. For a
conjunction of two witnessed halves that is thin but not hollow — note it if you
want a direct instance.
