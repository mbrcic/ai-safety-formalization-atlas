# Bridge review — `Knowledge.not_uniformlyActionable_iff_exists_unservable`

**Row `LAND-KNOW-UNIFORM-001` · module `AISafetyAtlas/Knowledge/UniformAction.lean` · `HUMAN_REVIEW`**

Only bridge on this row. **The grade was moved here on 2026-09-16** from
`knowable_iff_uniformlyActionable`, which is `Iff.rfl` — it recorded that the
knowability kernel is the single-acceptable-action case and proved nothing. That
declaration is now a `WRAPPER`; the content is here.

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Accepted 2026-10-04 on the allowed claim as sharpened; existence only, no claim the policy is known or computable. |

## The statement

```lean
public theorem not_uniformlyActionable_iff_exists_unservable {Ω : Sort u} {I : Sort v} {A : Sort w}
    [Nonempty A] (observation : Ω → I) (Good : Ω → A → Prop) :
    ¬ UniformlyActionable observation Good ↔
      ∃ ω, ∀ a, ∃ τ, observation τ = observation ω ∧ ¬ Good τ a
```

`UniformlyActionable` asks whether one rule `I → A` acts acceptably at every
state — the operational question, weaker than whether the observation determines
a *value*. This is its negation with the quantifiers pushed in.

## What to check

1. **It is necessary *and* sufficient**, which is the reason to grade this one.
   The certificate an auditor can demand is a **state whose whole
   indistinguishable neighbourhood rejects every candidate action** — not a
   single awkward pair.
2. **The pairwise certificate is sufficient only, and the module proves the
   converse false.** Three states on one fibre with acceptable sets `{1,2}`,
   `{0,2}`, `{0,1}` are pairwise compatible and jointly empty. **This is the one
   structural difference from the kernel**: `Knowable` fails only through a pair,
   because equality is transitive, and compatibility of acceptable-action sets is
   not. If you check only `ActionConflict`, you can pass a system that has no
   uniform policy.
3. **`Good` is exact and binary.** No cost, no ranking, no partial credit. The
   acceptability standard is an input, not something the theorem supplies.
4. **"The only two repairs"** — a more informative observation
   (`UniformlyActionable.mono`), a more permissive standard (`.mono_good`) — is
   argued in prose from the criterion being an intersection over a fibre. It is
   **not a theorem**. Decide whether the module should say "the only two" at all.

## Allowed claim

> A monitor, reviewer or controller has no uniform policy from its observation
> exactly when some set of states it cannot separate admits no action acceptable
> throughout; otherwise a uniform policy from the observation it already has
> exists, however ambiguous that observation — though nothing says the policy is
> known or computable. When no
> uniform policy exists, the obstruction is exhibitable as a state whose
> indistinguishable neighbourhood defeats every candidate action, and that
> certificate is complete — no other kind of failure occurs.

## Forbidden

- **Not** "you can act safely without understanding the system." `Good` is an
  exact standard given in advance, and nothing says it can be specified or
  checked without understanding.
- **Not** a claim about any controller, policy or deployment. The atlas has none.
- **Not** about cost, optimality or regret.
- **Not** an achievability result. It characterises failure; it does not say a
  uniform policy exists anywhere.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Interpretability is unnecessary — just act well." | the acceptability standard is an input, not a conclusion |
| "We checked every pair, so a uniform policy exists." | the pairwise certificate is sufficient for failure only; the three-state witness is in the Examples |
| "A richer sensor always fixes it." | `mono` gives one direction; no sufficient sensor is claimed to exist |
| "So sensing can be cut wherever ambiguity is harmless." | the criterion is per fibre, and "harmless" is exactly what `Good` has to already encode |

## Witness

`AISafetyAtlas/Examples/Knowledge/UniformAction.lean`, including the three-state
fibre that separates pairwise compatibility from joint emptiness.
