# Bridge review — `Sovereignty.gameFormAcyclic_iff`

**Row `LAND-SOV-STABILITY-001` · module `AISafetyAtlas/Sovereignty/Stability.lean` · `HUMAN_REVIEW`**

Only bridge on this row.

**Updated 2026-09-16, and the verdict question has changed.** When this file was
written, neither of Keiding's theorems was carried and rejection looked like the
answer. **Theorem 3.6 is now proved** — `not_stable_of_cycle`, with
`acyclic_of_stable` its contrapositive — so the condition graded here is no longer a definitional
identity with nothing behind it. It is still `Iff.rfl`; what changed is that the
module it names now draws a conclusion.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem gameFormAcyclic_iff {N : Type u} {X : Type v}
    (G : GameForm.{u, v, w} N X) :
    GameFormAcyclic G ↔ Acyclic (effectivity G) :=
  Iff.rfl
```

Keiding, *Necessary and sufficient conditions for stability of effectivity
functions*, **IJGT 14(2):93–101, 1985**, Definition 3.3 (p. 96).

## What to check

1. **The transcription is free.** Keiding's `E : P(N) → P²(A)` **is** the type of
   `Sovereignty.effectivity` — `Set N → Set (Set X)` — so the condition carries
   over with no new substrate and no translation step to get wrong. That is the
   reason the module exists.
2. **The condition mentions only `E`.** No preference, no utility, no ordering
   appears in Definition 3.3. A purely combinatorial property of a power
   distribution.
3. **Theorem 3.6 is carried; Theorem 3.8 is not.** So "stability" in the row
   title is now half proved: a cycle gives instability, and the converse — acyclic
   gives stability — is still Keiding's vocabulary rather than a theorem here.
   Its proof runs the other way, building a cycle from an empty core, and that
   construction is not transcribed.
4. **Check what the grade is actually on.** This declaration is `Iff.rfl`; the
   content is in `not_stable_of_cycle`. A reasonable verdict is to **move the
   grade** there, the way `LAND-KNOW-UNIFORM-001`'s was moved off its own
   `Iff.rfl` on the same day. Say so in the Note and I re-grade.
5. **A fidelity defect was found and fixed while proving 3.6.** Definition 3.3
   writes `Sᵢ ∈ 2^N`, and p. 94 defines `2^D = P(D) \ {∅}` — so a cycle's
   coalitions are non-empty. The first transcription dropped that, which made
   `Cycle` wider than print and Theorem 3.6 **false**, since the empty coalition
   dominates nothing. `Cycle.Snonempty` carries it now. **Worth checking that the
   field is print's and not a convenience**, because it narrows `Cycle` and so
   widens `Acyclic` — including the `Acyclic` this declaration is about.

## Allowed claim

> Keiding's acyclicity condition is stated at this repository's effectivity
> families, and reading it at a game form's own power distribution is
> definitional. Whether a power distribution can be blocked from every direction
> at once is decided without reference to anyone's preferences.

And, through Theorem 3.6, one consequence does follow:

> A power distribution carrying a cycle — whose forced sets are non-empty — is
> **unstable**: some profile of weak orders over the outcomes leaves every
> outcome dominated by some coalition that can force something all its members
> prefer.

## Forbidden

- **Not** that acyclicity gives stability. That is Theorem 3.8 and it is **not**
  formalized; only the cycle-implies-unstable direction is carried.
- **Not** that any real arrangement is stable or unstable. No AI system, no
  deployment and no governance arrangement is modelled, and instantiating
  `effectivity G` at one is layer 4.
- **Not** a claim about preferences anyone holds. The profile Theorem 3.6
  produces is constructed from the cycle to witness instability; it is not
  offered as a model of what any party wants.
- **Not** an AI-safety claim in its own right — this is a governance-theoretic
  condition, and the bridge grade is on the reading at a game form.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "The atlas characterises when a governance arrangement is stable." | half of it: 3.6 is carried, 3.8 is not, so "stable iff acyclic" is not available |
| "Acyclicity implies a non-empty core." | that is Theorem 3.8, not formalized |
| "Our governance arrangement has a cycle, so it is unstable." | true of the model once `effectivity G` is instantiated at it — and that instantiation is the layer-4 step nobody has taken |
| "The instability profile shows what the parties want." | it is constructed to witness the conclusion, not observed |

## Witness

`AISafetyAtlas/Examples/Sovereignty/Stability.lean` carries `duelCycle` — two
agents, two outcomes, each effective for exactly the outcome the other is blocked
by — and now also `duel_not_stable`, Theorem 3.6 drawn on it, plus
`duel_stable_would_be_acyclic` for the contrapositive and `noEmptySet_duel`
discharging Definition 2.1(i). `acyclic_bot` inhabits the other side, so neither
side of the predicate is vacuous.
