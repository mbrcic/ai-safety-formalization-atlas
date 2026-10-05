# The maintenance floor, and what it is not

**Date.** 2026-09-13. Row `LAND-SOV-CAPABILITY-001`.

## Why this module exists

The verb **preserve** is one of five in this repository's cognitive-sovereignty
reading. **It is not true that it had no formal object** — that is a wider claim
than the tree supports, and it is narrowed here before it propagates:

| Existing object | What it preserves |
|---|---|
| `AISafetyAtlas.Sovereignty.RetainsFamily` (`Mandate.lean`) | what a coalition can force, across a change of game form |
| `AISafetyAtlas.Wireheading.GoalPreservation` | a goal, across self-modification |
| `docs/provenance/cognitive-sovereignty-obligation.md` §on indistinguishability | frames SOV-1 as *"what a principal can preserve"* |

What had **no** object is **capability preservation over time**: a scalar
quantity that decays at a rate, is topped up each period, and must not fall below
a floor. `LAND-SOV-STEERING-001`'s note says the five verbs are "named in the
module docstring as interpretation and are not formalized", and that is true of
the *verb inventory as such*; it is not a statement that nothing preservation-
shaped exists. This module adds the temporal-capability reading and nothing else.

## What came from print, and print's own status

The source is the unpublished governance sketch,
a private note,
§12.1, catalogued as `governance-kernel-sketch-unpublished`. It is **not
published**, is not in the coverage audit, and is not coverage.

**GK1, as printed:**

> Let fallback skill obey the explicitly selected affine recurrence
> `k_{t+1} = a k_t + p_t`. … **Maintenance floor:** if `a>=0`, `k_0>=k_min`, and
> `p_t >= (1-a) k_min` for all `t`, then `k_t >= k_min` for every `t`.

and, immediately after:

> For usual forgetting interpretations add `a<=1`, nonnegative skills, and
> nonnegative practice. **The theorem itself needs only its printed
> assumptions.**

That last sentence is why `Examples.Sovereignty.Capability.expanding_floor` is in
the same commit: it inhabits the antecedent with `a = 2`, so "needs only its
printed assumptions" is a checked claim rather than a quotation. The companion
`floor_fails_without_practice` removes the top-up floor at `a = 1` and the
conclusion fails at the first step, so that hypothesis is load-bearing too.

**GK2, as printed:**

> Assisted task output can rise while fallback output falls. A concrete reference
> case starts at fallback 2 and ends at fallback 1 with borrowed assistance 3:
> assisted output increases to 4 while post-withdrawal capacity falls to 1.

`Examples.Sovereignty.Capability.sketch_case` is those numbers and no others.

## Prior-art search — done before building, this time

| Where | Searched for | Found |
|---|---|---|
| `AISafetyAtlas/`, `registry.yaml` | `recurrence`, `fallback`, `maintenance`, `k_min`, `practice`, `preserve` | Nothing formal. `preserve` occurs once, in `LAND-SOV-STEERING-001`'s note, saying it is **not** formalized |
| leansearch | affine recurrence staying above a lower bound | **`Mathlib.Analysis.SpecificLimits.ArithmeticGeometric`** — real prior art, see below |
| loogle | `arithGeom` and its API | 12 lemmas; only one is a floor |

### The Mathlib lemma that is nearly this, and why it is not used

`div_lt_arithGeom : 0 < a → a ≠ 1 → b / (1 - a) < u₀ → ∀ n, b / (1 - a) < arithGeom a b u₀ n`,
where `arithGeom a b u₀` is the same recurrence with a **constant** forcing term
`b`. With `b = (1 - a) * kmin` and `a ≠ 1` its bound is exactly `kmin`.

It is not reused, on four counts, each of which the source's model needs:

1. **The top-up varies with `t`.** That is the point of the model — the sketch's
   own sentence is that `p_t` "includes genuine practice and can itself be
   increased by well-designed AI assistance". A constant `b` flattens exactly the
   quantity an intervention moves.
2. **The bound is strict.** GK1's is not, and `k_0 = k_min` is the interesting
   boundary case.
3. **`a = 1` and `a = 0` are excluded** by `0 < a` and `a ≠ 1`. GK1 allows both,
   and `a = 1` is the no-decay case a reader will reach for first.
4. **It needs a `Field`.** This needs `[Ring R] [PartialOrder R] [IsOrderedRing R]`.

So the atlas statement is a generalization of a Mathlib statement along four
axes, and that is recorded here rather than left as "nothing found".

## What is an atlas-side decision

**The recurrence is a hypothesis, not a definition.** `AffineCapability k p a` is
a predicate on a trajectory the consumer supplies. The sketch calls the
recurrence "explicitly selected" and says "the recurrence is not an empirical
universal law"; carrying it as a defined function would quietly promote a
modelling choice to a fact.

**`assistedOutput` is the cheapest possible model of observation** — fallback plus
borrowed assistance — and nothing here claims it is the right one. What it buys
is `fallback_not_knowable_from_assistedOutput`, which is one application of
`AISafetyAtlas.Knowledge.not_knowable_of_collision` and is the statement that
matters: **the quantity the floor is about is not the quantity anyone observes.**

`exists_output_rise_with_fallback_fall` is the same failure in order-theoretic
form, constructive, at any two comparable levels.

## Not built, and why

**GK3 is now built** — 2026-09-13, in the same module. It had been costed here
as needing "a game-form embedding that says what *simulated unchanged* means,
which the `Sovereignty` cluster does not currently carry." That costing was
right about the gap and the embedding was built rather than borrowed:

```
structure Enlarges (G G' : GameForm N X) (C : Set N) where
  embed        : ∀ i, G.strategy i → G'.strategy i
  reduce       : ∀ i, i ∉ C → G'.strategy i → G.strategy i
  embed_reduce : ∀ i (h : i ∉ C) (t : G'.strategy i), embed i (reduce i h t) = t
  outcome_embed : ∀ s, G'.outcome (fun i => embed i (s i)) = G.outcome s
```

`Enlarges.forces : Enlarges G G' C → Forces G C A → Forces G' C A`.

**The middle two clauses are the whole theorem.** They say the *complement*
gained nothing. `Examples.Sovereignty.Capability.foe_breaks_forces` exhibits an
`embed` and an `outcome_embed` — the first and last clauses, and the only two a
careless reading would check — under which the guarantee is destroyed, because
one agent outside the coalition acquired an option. So the sentence "more
options cannot hurt" is false as usually said. What is true is that more options
*for the guarantor*, with everyone else fixed, cannot hurt.

`wide_forces_one` and `base_not_forces_one` keep the positive witness honest:
the enlargement there really does add something the baseline could not force.

### The prior art, found after the build

**GK3 is published.** Wooldridge & van der Hoek, *On obligations and normative
ability*, J. Applied Logic **3**:396–420, 2005 — held since 2026-09-13, sha256
`21970069…` — state it as **Proposition 3, item 1, journal page 410**, read from
a rendered page image:

> Let `S` be an AATS, and let `η, η′` be arbitrary non-trivial normative systems
> over `S` such that `η ≼ η′` (i.e., `η` is less restrictive than `η′`). Then:
> (1) `S ⊨ ⟪η′ : C⟫φ → ⟪η : C⟫φ`

Their proof is this proof. By their Proposition 2 (journal page 405),
`η ≼ η′ ⟺ ∀C ⊆ Ag: Σ^{η′}_C ⊆ Σ^η_C` for non-trivial systems, so the witnessing
strategy survives the relaxation; and the set of completions does not depend on
`η` at all, because the semantics at journal page 407,

> `S, q ⊨ ⟪η : C⟫φ` iff `∃σ_C ∈ Σ^η_C`, such that `∀λ ∈ comp(σ_C, q)`, we have
> `S, λ ⊨ φ`.

quantifies over every computation consistent with `σ_C` — and, in their own words
at journal page 409, *"does not put any constraint on the agents outside
coalition `C`, they don't necessarily need to behave according to `η`."*

**That last sentence is GK3's load-bearing hypothesis, and in print it is prose
about the model rather than a clause of the proposition.** It cannot be a clause
there: print varies only *which strategies a fixed AATS permits*, so the
complement's options are fixed by construction and no counterexample of
`foe_breaks_forces`'s kind is expressible.

| | Print, Prop 3(1) | `Enlarges.forces` |
|---|---|---|
| carrier | one AATS; `η` varies | two arbitrary `GameForm`s |
| the embedding | set inclusion `Σ^{η′}_C ⊆ Σ^η_C` | an arbitrary `embed`, injectivity not required |
| the outcome | identical, one `comp` | may differ off the image; `outcome_embed` is a hypothesis |
| the conclusion | path formulae over infinite computations | one shot, a set of outcomes |
| complement fixed | true of the model, unstated | `embed_reduce`, and refuted when dropped |

So: **wider in the carrier, narrower on the temporal axis, and carrying one
statement print has no room for.**

**How this was missed.** The prior-art search recorded above was run against Lean
and Isabelle corpora for the shape of the *recurrence*. GK3's shape is a
monotonicity claim in a modal logic of coalition ability, and nothing pointed the
search at the deontic literature — where the paper was already sitting, held and
unread in this repository, named in Ågotnes et al.'s own bibliography and cited
in `deontic-layer.md` two days earlier. Recorded because the outcome did not
change what was built and that is luck rather than method.

**§12.2's hazard bound** is a separate statement about survival probabilities and
needs a probability layer; it is not in this row.

**And the sketch's own wider object is not this one.** The sentence immediately
after GK1 reads: *"The operational object is not skill alone but fallback
effectivity: what the institution can guarantee when a specified dependency is
withdrawn. Different skill-to-task maps can produce different sovereignty
consequences for the same scalar skill trajectory."* This row carries the
**scalar** recurrence, which is what GK1 is stated over; `assistedOutput` is a
two-component model of observation, not that. GK3 *is* stated at effectivity —
`Enlarges.effectivity_subset` — but at *monotonicity under added options*, not
at what survives withdrawal of a dependency, which is the sketch's operational
object and remains unbuilt. Recorded so the row is not read
as having discharged the sketch's §12 rather than its GK1 and GK2.
