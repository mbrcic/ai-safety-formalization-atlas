# Bridge review — `Knowledge.Access.exists_indistinguishable_behaviour`

**Row `LAND-ACCESS-ORDER-001` · module `AISafetyAtlas/Knowledge/Access.lean` · `HUMAN_REVIEW`**

Siblings: [`whiteBox_determines_blackBox`](review-whitebox-determines-blackbox.md),
[`no_blackBox_methodology`](review-no-blackbox-methodology.md).

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem exists_indistinguishable_behaviour {Y : Type*} [Nonempty Y]
    {property : Weights → Y} (h : ¬ Knowable (blackBox M) property) :
    ∃ ω τ : Weights,
      (∀ i, M.behaviour ω i = M.behaviour τ i) ∧ property ω ≠ property τ
```

## What to check

1. **This is what makes a negative answer usable.** An auditor who cannot settle
   a question from black-box access is handed **the two artifacts that access
   cannot tell apart** — the obstruction becomes inspectable rather than a bare
   failure. That is the practitioner value and the reason it is a separate
   declaration rather than a corollary left in prose.
2. **It is classical**, via `exists_witness_of_not_knowable`, and `[Nonempty Y]`
   is needed. Non-constructive: it asserts the pair exists, it does not compute
   it. **Do not read it as "the auditor can produce the pair."**
3. Behavioural agreement is at **every** input (`∀ i`), which is the strongest
   form of indistinguishability and the right one here.

## Allowed claim

> Where a property is not determined by input-output behaviour, two artifacts
> exist that agree on every input and differ in that property. So the failure of
> black-box access on that question has a concrete shape — a pair — rather than
> being only the absence of a method.

## Forbidden

- **Not** a construction. The pair is asserted to exist, not produced, and no
  procedure finds it.
- **Not** a claim that such a pair exists for any real deployment or any real
  question; conditional on the same unestablished hypothesis as its sibling.
- **Not** an adversarial claim. Nothing says anyone can *build* the second
  artifact, which would be a capability question.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "So we can exhibit two models the API cannot distinguish." | classical existence; nothing computes the pair |
| "An attacker can substitute the twin." | no construction, no capability, no threat model is present |
| "This proves models can hide properties." | conditional on the property being behaviour-undetermined, which is not established |

## Witness

`AISafetyAtlas/Examples/Knowledge/Access.lean`, which exhibits an actual pair —
so the existence statement is not the only thing in the repository asserting one.
