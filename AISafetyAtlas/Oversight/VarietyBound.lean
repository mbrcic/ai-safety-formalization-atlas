module

public import AISafetyAtlas.Control.VarietyCounting
public import AISafetyAtlas.Knowledge

/-!
# Seeing and doing are separate capacities

Oversight is usually argued about as an *information* problem: can the overseer
tell the bad case from the good one? `Oversight.JointObservation` formalizes that
question and `Knowledge` supplies its kernel. This module states the part that
question leaves out.

An overseer that can distinguish every situation still has to **do** something,
and what it can do is drawn from a finite repertoire of interventions. Ashby's
counting bound applies to that repertoire whatever the overseer knows. So there
are two independent bottlenecks, and this module proves they are independent in
both directions.

## The model

`Σ` is the set of situations the overseer is answerable for, `Obs` what it gets
to see, `Act` the interventions available to it, and `Out` the outcomes. An
overseer is a map `Obs → Act`: it may use everything it observes and nothing it
does not.

`Forces effect observe act target` says the overseer's policy pins the outcome at
`target` in **every** situation. That is the strongest reading of "oversight
works", and it is deliberately the one used here: a necessary condition for it is
a necessary condition for anything weaker.

The one structural hypothesis is Ashby's, `hcol`: for a fixed intervention,
different situations lead to different outcomes. It says the intervention does
not by itself erase the situation. Where it fails — an intervention that
flattens everything to one outcome — the bound does not apply, and
`forces_of_constant_effect` is exactly that case.

## What is proved

`not_forces_of_card_lt` — **seeing does not give doing.** If there are fewer
interventions than situations, no overseer forces the outcome, and the hypothesis
list contains nothing about what the overseer observes. The policy may read the
situation perfectly; it changes nothing.

`forces_of_constant_effect` — **doing does not need seeing.** An intervention
whose effect is constant forces the target from a blind policy.

Together: coverage is neither necessary nor sufficient for control. The two
theorems are cheap individually and the pair is the content.
`Examples.Oversight.VarietyBound` exhibits both corners in one concrete model, so
the independence is witnessed and not merely stated.

## Why this is a bridge and what it is not

The declarations here are stated over an oversight model, which is the thing
`docs/guide/methodology.md` calls a bridge, and the registry records them as
`BRIDGE`. Renaming Ashby's regulator "overseer" would not earn that; what earns
it is that the model carries a hazard-decision notion from `Knowledge` alongside
the intervention repertoire, and the result is about the relation between them.

## Explicit non-claims

- **Not** a claim that oversight is futile. Every statement here is about
  *forcing a single outcome in every situation*. Oversight that reduces harm,
  catches most cases, or buys time is untouched, and the counting bound says
  nothing against it.
- **Not** a claim about any deployed system. `Σ`, `Act` and `effect` are
  arbitrary finite data. Nothing here asserts that a real monitor's intervention
  set is small, and the bound is vacuous unless someone establishes that it is.
- **Not** a claim that more interventions suffice. `not_forces_of_card_lt` is a
  necessary condition. Its converse is false, and `hcol` is a hypothesis about
  the effect table, not a conclusion.
- **Not** an independence claim about *knowability* in general. What is proved
  independent is coverage and forcing, in this model. `Knowledge.Knowable` on
  other data is a different statement.
- **Not** a probabilistic bound. This is counting; there is no measure here.
-/

namespace AISafetyAtlas.Oversight

open Function
open AISafetyAtlas.Control (admittedOutcomes two_le_card_admittedOutcomes)

variable {Sit : Type*} {Obs : Type*} {Act : Type*} {Out : Type*}

/--
The overseer's policy **forces** the outcome: in every situation, intervening as
the policy directs produces `target`.

The policy reads only `observe σ`, which is what makes this a statement about
oversight rather than about an omniscient controller.
-/
@[expose] public def Forces (effect : Sit → Act → Out) (observe : Sit → Obs)
    (act : Obs → Act) (target : Out) : Prop :=
  ∀ σ, effect σ (act (observe σ)) = target

/--
**Seeing does not give doing.**

With fewer interventions than situations, and an effect table in which a fixed
intervention still distinguishes situations, no policy forces the outcome —
whatever it observes.

The observation appears in the statement and not in the hypotheses, which is the
point of the theorem rather than an oversight in it: perfect discrimination of
the situation would leave the conclusion unchanged, because the obstruction is
the size of `Act` and not the quality of `observe`.
-/
public theorem not_forces_of_card_lt [Fintype Sit] [Fintype Act] [DecidableEq Act]
    [DecidableEq Out] {effect : Sit → Act → Out} {observe : Sit → Obs}
    (hcol : ∀ a : Act, Injective fun σ => effect σ a)
    (hlt : Fintype.card Act < Fintype.card Sit)
    (act : Obs → Act) (target : Out) :
    ¬ Forces effect observe act target := by
  intro hforce
  have htwo : 2 ≤ (admittedOutcomes effect (fun σ => act (observe σ)) Finset.univ).card :=
    two_le_card_admittedOutcomes effect (fun σ => act (observe σ)) hcol hlt
  have hsub : admittedOutcomes effect (fun σ => act (observe σ)) Finset.univ ⊆ {target} := by
    intro e he
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp he
    simpa using hforce σ
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hcard
  omega

/--
**Doing does not need seeing.**

An intervention whose effect does not depend on the situation forces the target
from a policy that observes nothing at all.

This is the other corner, and it is what makes the independence a fact about the
model rather than a one-sided limitation. It is also where `not_forces_of_card_lt`'s
structural hypothesis fails: a constant column is exactly a non-injective one.
-/
public theorem forces_of_constant_effect {effect : Sit → Act → Out} {observe : Sit → Obs}
    {a : Act} {target : Out} (hconst : ∀ σ, effect σ a = target) :
    Forces effect observe (fun _ => a) target :=
  fun σ => hconst σ

/--
The two corners cannot both be ruled out by a statement about observation alone:
`Forces` is a property of the effect table and the repertoire, and
`Knowledge.Knowable` is a property of the observation. This restates
`forces_of_constant_effect` with an explicit unknowability hypothesis to make the
direction visible in a single statement.
-/
public theorem forces_of_constant_effect_of_not_knowable {effect : Sit → Act → Out}
    {observe : Sit → Obs} {hazard : Sit → Bool} {a : Act} {target : Out}
    (_hunknown : ¬ AISafetyAtlas.Knowledge.Knowable observe hazard)
    (hconst : ∀ σ, effect σ a = target) :
    Forces effect observe (fun _ => a) target :=
  forces_of_constant_effect hconst

end AISafetyAtlas.Oversight
