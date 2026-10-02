# Bridge review — `Verification.Containment.harming_undecidable`

**Row `BY-025` · module `AISafetyAtlas/Verification/Containment.lean` · `HUMAN_REVIEW`**

Only bridge on this row. Source: Alfonseca, Cebrian, Fernández Anta, Coviello,
Abeliuk, Rahwan, *Superintelligence Cannot be Contained*, **JAIR 70 (2021)
65–76**, Theorem 1, journal page 71.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem harming_undecidable {Program Data : Type*} [Primcodable Program]
    [Primcodable Data] {harms : Program → Data → Prop}
    (reduction : HarmReduction harms) :
    ¬ Nonempty (HarmDecider harms)
```

`HarmReduction` is print's Assumption 2 reduced to what the proof consumes: a
distinguished program `haltHarm`, a computable packaging of a machine as data,
and the biconditional print derives. `HarmDecider` is total and exact.

## What to check

1. ***HarmHumans* is uninterpreted, and deliberately.** No predicate in the file
   means *harms humans*; `harms` is an arbitrary relation. **The safety reading
   is the bridge, not the theorem.** Print is in the same position — its
   *HarmHumans()* is an opaque operation of the language of `R`.
2. **Narrower than print on one axis.** Print quantifies over every machine `T`
   and input `I`; this fixes `sourceInput` and varies the machine, because that
   is the shape of Mathlib's halting statement. Equivalent as undecidable source
   problems. Same narrowing `Verification.Robot` carries.
3. **Corollary 3 is absent and that is the judgement call.** Print states *"the
   containment problem is incomputable"* and derives it in running prose with no
   reduction. Nothing is claimed for it. Stating the complement of `harms` and
   calling it containment would have invented print's missing step.

## Allowed claim

> If a screening procedure must answer, for every program and every situation,
> exactly whether that program in that situation performs a designated effect,
> and the effect can be appended to an arbitrary computation, then no such
> procedure exists — it would decide halting. The obstruction is about **exact,
> total decision of an arbitrary appended effect**, and it is prior to any
> question about capability.

## Forbidden

- **Not** "superintelligence cannot be contained." Containment in the field's
  sense is isolation — channels, boundaries, a system acting to get out. The
  atlas has none of those. Print itself drops the escape half between pages 68
  and 69, and Theorem 1 is about what remains.
- **Not** print's Corollary 3.
- **Not** about capability. The quantifier is over all programs.
- **Not** a bound on statistical, partial, conservative or abstaining screening.
- **Not** a claim that any real harm predicate satisfies `HarmReduction`.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Proved: you cannot box a superintelligent AI." | no boundary, channel or escape is modelled; the module names both senses of *containment* and carries neither |
| "So safety classifiers are impossible." | classifiers are neither total nor exact and may abstain |
| "This is about advanced systems." | nothing scales with capability |
| "Corollary 3 follows." | derived in prose with no reduction; not formalized |

## Witness

`AISafetyAtlas/Examples/Verification/Containment.lean` inhabits `HarmReduction`,
so the hypothesis is not empty.
