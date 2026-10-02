module

public import AISafetyAtlas.Sovereignty.Arena
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
- **Not** a claim that more interventions suffice, and **not** a claim that
  counting measures power. `not_forces_of_card_lt` is a necessary condition whose
  converse is false, and `hcol` is a hypothesis about the effect table rather
  than a conclusion. `fewer_acts_can_force_while_more_cannot` exhibits a
  two-intervention repertoire that forces where a four-intervention one cannot;
  what separates them is `collapse`, not size.
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

/-! ## What forcing actually needs: collapse, not count

`not_forces_of_card_lt` is a bound on the *size* of the repertoire, and size is
the wrong quantity. Its hypothesis `hcol` says every intervention is injective in
the situation -- no act flattens the state space -- and that hypothesis is doing
all the work. Drop it and one intervention suffices, whatever the counts:
`forces_of_constant_effect` is that corner already.

So a repertoire's power is not how many acts it holds but how far any one of them
**collapses** the situations onto a single outcome. Two acts, one of which lands
the world on the same point from wherever it started, beat a thousand acts that
each preserve every distinction. This section names the quantity and proves the
two existing theorems are its extremes.
-/

/--
The **collapse** of an intervention: the outcomes it still admits as the
situation varies.

A small collapse is a powerful act. `collapse effect a = {x}` is an act that
lands the world on `x` from wherever it started; a collapse as large as `Sit` is
an act that preserves every distinction the situation makes. This is the quantity
`not_forces_of_card_lt` and `forces_of_constant_effect` sit at opposite ends of.
-/
@[expose] public def collapse (effect : Sit → Act → Out) (a : Act) : Set Out :=
  Set.range fun σ => effect σ a

/-- An intervention is **decisive** for `target` when it collapses every
situation onto it. -/
@[expose] public def Decisive (effect : Sit → Act → Out) (a : Act)
    (target : Out) : Prop :=
  collapse effect a ⊆ {target}

/-- Being decisive is being constant, spelled out. -/
public theorem decisive_iff {effect : Sit → Act → Out} {a : Act} {target : Out} :
    Decisive effect a target ↔ ∀ σ, effect σ a = target := by
  constructor
  · intro h σ; exact h ⟨σ, rfl⟩
  · rintro h _ ⟨σ, rfl⟩; exact h σ

/--
**One decisive act forces, whatever the counts.**

No hypothesis relates `Act` to `Sit`, and the observation is never consulted.
This is `forces_of_constant_effect` in the vocabulary of collapse, and it is the
formal content of the objection that a repertoire of two -- act, or do not --
can beat a repertoire of thousands.
-/
public theorem forces_of_decisive {effect : Sit → Act → Out} {observe : Sit → Obs}
    {a : Act} {target : Out} (h : Decisive effect a target) :
    Forces effect observe (fun _ => a) target :=
  forces_of_constant_effect (decisive_iff.mp h)

/--
**Forcing is exactly collapse along the policy.** The composite act-after-observe
must land every situation on the target; nothing weaker will do, and the
observation enters only by choosing which act is played where.
-/
public theorem forces_iff_composite_constant {effect : Sit → Act → Out}
    {observe : Sit → Obs} {act : Obs → Act} {target : Out} :
    Forces effect observe act target ↔
      ∀ σ, effect σ (act (observe σ)) = target :=
  Iff.rfl

/--
**The counting bound lives at the other end.** `hcol` says no intervention
collapses two distinct situations, which rules out decisiveness outright as soon
as there are two situations to collapse.

So the two theorems do not compete: `not_forces_of_card_lt` is what remains once
decisiveness has been assumed away, and this states the boundary between them
rather than leaving it to the reader.
-/
public theorem not_decisive_of_injective [Nontrivial Sit] {effect : Sit → Act → Out}
    {a : Act} (hinj : Injective fun σ => effect σ a) (target : Out) :
    ¬ Decisive effect a target := by
  intro hdec
  obtain ⟨σ₁, σ₂, hne⟩ := exists_pair_ne Sit
  exact hne (hinj (by
    simp only []
    rw [decisive_iff.mp hdec σ₁, decisive_iff.mp hdec σ₂]))

/-! ## Where power becomes, and whether it stays

Collapse is a property of one effect table, and an effect table is a snapshot.
Power a configuration hands you is power another configuration can take back, so
the repertoire is not the whole substrate; what the substrate does across its
configurations is.

`Γ : K → (Sit → Act → Out)` is that substrate and `k` a configuration it can be
in. `RobustlyForces` is the property of *staying*: the guarantee survives every
configuration, not merely the one you were handed. `HasStructuralPower` in
`AISafetyAtlas.Sovereignty.Separations` is the same move on a game form, and this
is its oversight-side counterpart.
-/

variable {K : Type*}

/-- **Power that stays.** The policy forces the target in every configuration the
substrate can be in, not merely in the present one. -/
@[expose] public def RobustlyForces (Γ : K → Sit → Act → Out) (observe : Sit → Obs)
    (act : Obs → Act) (target : Out) : Prop :=
  ∀ k, Forces (Γ k) observe act target

/-- Staying implies holding: a guarantee across all configurations is a guarantee
in each one. -/
public theorem RobustlyForces.forces {Γ : K → Sit → Act → Out} {observe : Sit → Obs}
    {act : Obs → Act} {target : Out} (h : RobustlyForces Γ observe act target)
    (k : K) : Forces (Γ k) observe act target := h k

/-- **An act that stays decisive is power that stays.** The hypothesis is a
condition on the substrate `Γ`, not on the agent holding the act. -/
public theorem robustlyForces_of_decisive {Γ : K → Sit → Act → Out}
    {observe : Sit → Obs} {a : Act} {target : Out}
    (h : ∀ k, Decisive (Γ k) a target) :
    RobustlyForces Γ observe (fun _ => a) target :=
  fun k => forces_of_decisive (h k)

/-- **Power does not stay if one configuration removes it.** However well the
policy does elsewhere, a single configuration in which it fails is enough. -/
public theorem not_robustlyForces_of_exists_not {Γ : K → Sit → Act → Out}
    {observe : Sit → Obs} {act : Obs → Act} {target : Out}
    (k : K) (h : ¬ Forces (Γ k) observe act target) :
    ¬ RobustlyForces Γ observe act target :=
  fun hall => h (hall k)

/-! ## The same notion as the game-form side

`AISafetyAtlas.Sovereignty.Arena` states forcing for one party against an opaque
residue. This module's `Forces` is that notion with the policy named rather than
quantified: the party settles a policy, the situation is the residue, and
`effect`-after-`observe` resolves them. Making the identification explicit is what
lets the counting and collapse results here be read as results about power rather
than only about oversight.
-/

/-- **The overseer's arena.** The policy is what the overseer settles, the
situation is what it does not. -/
@[expose] public def effectArena (effect : Sit → Act → Out) (observe : Sit → Obs) :
    Sovereignty.Arena (Obs → Act) Sit Out where
  outcome := fun act σ => effect σ (act (observe σ))

/-- **Oversight forcing is arena forcing, once the policy is quantified.** The
only difference between the two statements is that `Forces` names the policy and
`Arena.Forces` asks for one. -/
public theorem exists_forces_iff_arena_forces {effect : Sit → Act → Out}
    {observe : Sit → Obs} {target : Out} :
    (∃ act, Forces effect observe act target) ↔
      (effectArena effect observe).Forces {target} :=
  Iff.rfl

/-- The arena's collapse at a policy is the set of outcomes that policy still
admits, which is `collapse` composed with the policy rather than with a single
act. -/
public theorem arena_collapse_eq {effect : Sit → Act → Out} {observe : Sit → Obs}
    {act : Obs → Act} :
    (effectArena effect observe).collapse act =
      Set.range fun σ => effect σ (act (observe σ)) := rfl

end AISafetyAtlas.Oversight
