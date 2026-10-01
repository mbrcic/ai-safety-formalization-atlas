# Bridge review — `Knowledge.Access.no_blackBox_methodology`

**Row `LAND-ACCESS-ORDER-001` · module `AISafetyAtlas/Knowledge/Access.lean` · `HUMAN_REVIEW`**

Siblings on this row, signed separately:
[`whiteBox_determines_blackBox`](review-whitebox-determines-blackbox.md),
[`exists_indistinguishable_behaviour`](review-exists-indistinguishable-behaviour.md).
Arrow to Reuel, Bucknall et al., TMLR 04/2025, **Open Problem 37**.

**This is the sharp one of the three.**

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem no_blackBox_methodology {K : Sort*} {Y : Sort*}
    (analysis : (Input → Output) → K)
    {property : Weights → Y}
    (h : ¬ Knowable (blackBox M) property) :
    ¬ Knowable (fun ω => analysis (blackBox M ω)) property :=
  not_knowable_comp analysis h
```

## What to check

1. **`analysis` is arbitrary, and that is the content.** It may probe adaptively,
   aggregate across unboundedly many queries, or run any statistic — it is still
   a function of evidence that was already insufficient. So R#37's answer is a
   property of the **access level**, not of the method.
2. **`Knowable` is exact recovery.** Real auditing is statistical and
   approximate, and nothing here covers it.
3. **The hypothesis is the contestable half.** `¬ Knowable (blackBox M) property`
   says the property is not determined by behaviour. **Nothing establishes that
   for any real question**, and establishing it is the modelling step.
4. `blackBox M` must be **everything** the investigator gets. A side channel left
   out of the model makes the result pessimistic about black-box access.

## Allowed claim

> Where a property of an artifact is not determined by its input-output
> behaviour, no methodology over that behaviour establishes it — not a cleverer
> probe, not more queries, not any statistic of the transcript — because every
> such method is a function of evidence that was already insufficient.

## Forbidden

- **Not** "black-box auditing establishes nothing." It establishes everything
  determined by behaviour, which is a large class.
- **Not** a claim that any particular question is behaviour-undetermined.
- **Not** about approximate or statistical recovery.
- **Not** about misuse risk or model theft (R#38, R#39): those are about what an
  adversary can *do* with access, a capability question and not a
  decoder-existence one.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "API red-teaming is provably insufficient." | needs the target property shown behaviour-undetermined; not done here |
| "More queries will eventually settle it." | the quantifier is over every function of the behaviour, adaptive probing included |
| "So mandate weight access." | says nothing about cost, misuse risk, or whether the question at hand needs it |

## Witness

`AISafetyAtlas/Examples/Knowledge/Access.lean`, negative branch.
