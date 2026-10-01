module

public import AISafetyAtlas.Sovereignty.Separations
public import Mathlib.Data.Set.Image

/-!
# Sovereignty as immunity inside a boundary

The separations module says what it is for a coalition to have
**power**: `C` has power over `D` when whether `D` can reach a target is settled
by what `C` commits to. This module states the other notion, and it is not the
negation of that one.

**Power is about influencing what someone else gets. Sovereignty is about
keeping what you get free of everyone else — inside a boundary you claim.** A
country's boundary is its territory; a mind's is its cognition. Outside the
boundary, sovereignty says nothing at all, and that is deliberate: a sovereign
state does not thereby control the weather, and a sovereign mind does not
thereby control what is true.

## The three commitments this makes

**A boundary is a view, not a set of outcomes.** `Boundary` is a map `X → V`
saying what an outcome looks like from inside. Territory is what the outcome
looks like within the borders; cognition is what it looks like at the agent's
own states. Making it a *quotient of outcomes* rather than a *subset* is what
lets an outcome be partly inside and partly outside — which every real boundary
is, since the same world-state has an inside aspect and an outside one. A subset
could not express that.

**Sovereignty is defensive and universally quantified.** `Sovereign` does not
name an adversary. It says the view is unmoved by *every* strategy of *everyone
outside `D`*, which is what "keeping yourself from intrusion" means when you do
not get to choose who tries. There is no coalition parameter, and the absence is
the point: a defensive notion that had to be told whom to defend against would
be a claim about one opponent, not about a boundary.

**It is a fact about the game, not about anyone's intent.** No one need be
trying to intrude. `Sovereign` holds when intrusion is impossible, whoever wants
it and however they play. That is stronger than "nobody in fact intrudes", which
is an equilibrium notion and is not this.

## Where this sits in the literature

None of the three commitments above is novel, and that is deliberate -- each has
an established home, so the modelling can be defended by citation rather than
from first principles.

**Pin status.** All of Ingham and Lovett 2019 and 2022, Peleg 1998, Gaerdenfors
1981, Puppe and Xu 2010 and Basteck and Lojkine 2025 are pinned and were read.
No statement in this file is graded against any of them: this is where the
notions came from, not a transcription, and none of their mathematics is
reproved here.

Ingham and Lovett 2022 state the target as a definition, and it settles three
choices made here rather than merely resembling them:

> *"A's choice whether to φ is dominated to the extent that some B has an
> unconstrained ability to frustrate that choice."*

The object is a **choice**, not an outcome -- which is why the action-set layer
below is the primary reading and not a refinement of the outcome one. The
modality is **ability**, and their 2019 paper quotes Pettit that *"domination
goes with the accessibility of arbitrary interference"* and that improbability
"does not make for inaccessibility", so capacity-not-exercise is theirs and not
an interpretation. And the quantifier is **some B**, so non-domination is a
universal over outsiders -- which is `Sovereign`, negated.

Their *ignorable types* refinement is `SovereignEnv`. A type is ignorable when
its becoming common knowledge "would have no significant practical
consequences", and an ability is *suitably constrained* when every type for whom
frustrating would be rational is ignorable. That is a restriction on which
outsider behaviours are allowed to count, which is exactly what an environment
predicate does.

Gaerdenfors 1981 is where a right becomes an effectivity claim, and three of his
conditions are already in this tree or adjacent to it. A *rights-system* is a set
of pairs: group `G` is entitled to restrict the social state to `X`, which is
`Forces` for a coalition. His **condition on the rights of groups** -- a
supergroup inherits a subgroup's rights -- is `Forces.mono_coalition`. His
**consistency condition** -- disjoint groups are never assigned conflicting
rights -- is `Forces.inter_nonempty_of_disjoint`, which holds here as a
consequence of superadditivity rather than as an imposed axiom. And his
**minimal libertarianism** -- every individual
has *some* proper set it is entitled to -- is the one this file does **not**
have: `Sovereign` says what it is to hold a boundary and asserts of nobody that
they hold a non-trivial one.

Peleg 1998 supplies the other half. A *constitution* induces an **effectivity
function** describing "the distribution of power in a given society as a result
of the assignment of rights", and **game forms that faithfully represent it** are
how rights get exercised. That is `effectivity` and `Forces` here, and his
superadditivity axiom is the neighbouring file's `forces_superadditive`. His
mathematics was not transcribed: it is AMS-glyph and extracts corrupted, so
anything taken from it must be read from rendered pages first.

**Capacity rather than exercise, and defensive** is republican *non-domination*.
Domination there is the *capacity* to interfere, so a party is unfree even if no
one ever interferes; that is exactly why `Sovereign` quantifies over every
outsider strategy and names no adversary. Ingham and Lovett, *Domination and
democratic legislation*, Politics Philosophy and Economics 21(3), 2022, give a
game-theoretic and coalitional treatment; Pettit 2008 and List and Valentini
2016 are the background.

**That commitment has a standing objection and this file answers it rather than
ignoring it.** Carter and Shnayderman, *The impossibility of "freedom as
independence"*, Political Studies Review, 2018, argue that reading
non-interference over sheer possibility instead of probability makes unfreedom
ubiquitous and freedom "a virtually non-existent one". Their argument applies to
`Sovereign` verbatim, and `not_sovereign_of_outsider_moves_view` states it inside
the model. The reply is in that theorem's docstring: their counterexamples are
weighted by how unlikely an interference is, which presumes an environment that
is not searching for the interference that works, and an all-profiles invariant
is the right shape exactly when it is.

**A boundary** is the *protected sphere* of the rights literature, and that
literature is written in this file's own apparatus. Gaerdenfors 1981 defines a
right of a coalition as a set of social states the coalition is entitled to
bring about, which is `Forces` verbatim, and Peleg, *Effectivity functions, game
forms, games, and rights*, Social Choice and Welfare 15, 1998, develops rights as
effectivity functions over game forms. Sen's Paretian liberal is upstream of
both.

**The action-set reading** below is the opportunity-set literature, and it names
the case exactly. Puppe and Xu 2010 call an alternative *essential* when
*"by deleting it, the reduced opportunity set offers less freedom than the
original set"*. So the action removed in `curtailed_but_reach_unchanged` is a
**non-essential** alternative, and the gap between action-level and outcome-level
sovereignty is the essential/non-essential distinction rather than an artefact of
this rendering. They also record that Pattanaik and Xu's 1990 cardinality rule is
the special case in which every alternative is essential in every set containing
it.

One caution from the same paper, and it applies here. Their essentiality-based
ranking is transitive only under very restrictive conditions, which they call an
impossibility flavour. `reach` is a *set* and nothing in this file ranks or
measures it; that restraint is deliberate, and the literature says what it would
cost to give it up.

**The closest single reference, found and read after the three above.** Basteck
and Lojkine, *Power and Freedom in Mechanisms*, arXiv 2512.10112, 2025, make the
same split this file makes and make it in the same shape. They call an agent's
influence on her *own relevant outcomes* her **freedom** and her influence on
outcomes relevant to others her **power over others**; own-relevant outcomes are
a canonical **projection** of the outcome, which is `view` here, motivated by
agents who care about one dimension of an outcome and are indifferent to the
rest. Their **menu** -- the own-relevant outcomes an agent can bring about as her
report varies, given the others' -- is `Curtailment.reach`, and its dependence on
the others is `SovereignEnv`. They quote Dowding and Van Hees 2008 that the
freedom and power literatures grew up independent of one another and that a
framework integrating them is wanted.

Their setting is strategy-proof direct mechanisms with preferences; this file is
bare game forms with none, and its notion is *invariance* of the view rather than
the size of a menu. So the objects are not the same, and the overlap is the
reason to read them rather than a reason to stop.

What appears to be absent from all three is the conjunction: non-domination
stated over a boundary, with the action-set and outcome readings separated. The
survey in the sovereignty literature notes also records that no non-domination
result has been machine-checked anywhere.

## What is proved

`sovereign_iff_factors` is the content: `D` is sovereign over a boundary exactly
when the view of the outcome is a function of `D`'s own strategies alone. That
is the sharp form of "your outcomes inside your boundary are your own business".

`not_hasPowerOver_of_sovereign` is the bridge to the other notion, and it is the
theorem that earns the word: a sovereign `D` is immune to power, *for every
target expressible in its boundary*. Power over `D` at such a target is
impossible, not merely unexercised.

`Examples.Sovereignty.Boundary.splitGame_hasPowerOver_outside` is the converse discipline, and the reason the
bridge above says "expressible in its boundary". A sovereign `D` can still be
subject to power at targets its boundary does not see. Sovereignty is not
immunity; it is immunity **inside a boundary**, and a theorem that forgot the
qualifier would be false.

The four separations in the final section show sovereignty and power are
independent: each of the four combinations is realised.
-/

namespace AISafetyAtlas.Sovereignty

variable {N : Type u} {X : Type v} {V : Type*} {G : GameForm.{u, v, w} N X}

/-! ## The boundary and the notion -/

/--
**Sovereignty inside a boundary.** `D` is sovereign over the view `view` when
changing the strategies of everyone outside `D` never changes what the outcome
looks like inside the boundary.

Stated as invariance rather than as a factorisation because invariance is what
has to be checked and needs no choice; `sovereign_iff_factors` gives the
factorisation.
-/
@[expose] public def Sovereign (G : GameForm.{u, v, w} N X) (D : Set N)
    (view : X → V) : Prop :=
  ∀ s s' : ∀ i, G.strategy i,
    (∀ i : D, s i = s' i) → view (G.outcome s) = view (G.outcome s')

/-- **The content of the definition.** `D` is sovereign over a boundary exactly
when the boundary view of the outcome is a function of `D`'s own strategies.

The forward direction is where the work is and it needs a profile to extend a
partial one, so it asks that every agent have a strategy available. That is not
a restriction on `D`: it says the game is playable. -/
public theorem sovereign_iff_factors [∀ i, Nonempty (G.strategy i)]
    (D : Set N) (view : X → V) :
    Sovereign G D view ↔
      ∃ f : (∀ i : D, G.strategy i) → V,
        ∀ s : ∀ i, G.strategy i, view (G.outcome s) = f (fun i : D => s i) := by
  classical
  constructor
  · intro h
    refine ⟨fun sD ↦ view (G.outcome (fun i ↦
      if hi : i ∈ D then sD ⟨i, hi⟩ else Classical.arbitrary _)), fun s ↦ ?_⟩
    refine h s _ ?_
    rintro ⟨i, hi⟩
    simp [hi]
  · rintro ⟨f, hf⟩ s s' hss'
    rw [hf, hf]
    congr 1
    funext i
    exact hss' i

/-! ## How sovereignty behaves -/

/-- **A coarser boundary is easier to hold.** If `D` is sovereign over what it
sees, it is sovereign over any less detailed reading of the same thing.

Claiming less is never harder, which is the sense in which a boundary can be
drawn conservatively. -/
public theorem Sovereign.comp {D : Set N} {view : X → V} (h : Sovereign G D view)
    {W : Type*} (g : V → W) : Sovereign G D (g ∘ view) := by
  intro s s' hss'
  exact congrArg g (h s s' hss')

/-- **More members, no less sovereignty.** Enlarging the coalition fixes more
coordinates, so it can only make the invariance easier to satisfy.

This is why sovereignty is a claim of a *group*: a federation is at least as
sovereign as any of its members. -/
public theorem Sovereign.mono {D D' : Set N} (hDD' : D ⊆ D') {view : X → V}
    (h : Sovereign G D view) : Sovereign G D' view := by
  intro s s' hss'
  exact h s s' fun i ↦ hss' ⟨i.1, hDD' i.2⟩

/-- **Claiming nothing is free.** Every coalition is sovereign over the trivial
boundary, which is the degenerate case and the reason the notion needs a
boundary argument to say anything. -/
public theorem sovereign_const (D : Set N) (c : V) :
    Sovereign G D (fun _ ↦ c) := fun _ _ _ ↦ rfl

/-- **Everyone together is sovereign over everything.** With no outsiders left
there is nothing to be immune from, so the grand coalition is sovereign over the
finest boundary there is. -/
public theorem sovereign_univ (view : X → V) :
    Sovereign G (Set.univ : Set N) view := by
  intro s s' hss'
  have : s = s' := funext fun i ↦ hss' ⟨i, Set.mem_univ i⟩
  rw [this]

/-- **The empty coalition is sovereign only over nothing.** With no members to
fix, invariance is constancy of the view across the whole game. -/
public theorem sovereign_empty_iff (view : X → V) :
    Sovereign G (∅ : Set N) view ↔
      ∀ s s' : ∀ i, G.strategy i, view (G.outcome s) = view (G.outcome s') := by
  constructor
  · intro h s s'; exact h s s' (fun i ↦ i.2.elim)
  · intro h s s' _; exact h s s'

/--
**One outsider with one alternative move destroys sovereignty.**

If any `j` outside `D` has a strategy `t` whose substitution into some profile
shifts the view at all, then `D` is not sovereign over that view. Nothing here
weighs how likely `j` is to play `t`, because `Sovereign` quantifies over
profiles and not over a distribution on them.

**This is the objection Carter and Shnayderman (2018) raise, stated inside the
model rather than about it.** They argue that reading non-interference over
*sheer possibility* rather than probability makes unfreedom ubiquitous: since at
any moment someone can very easily prevent you from performing every future
action, "no one is ever free to do anything whatsoever". This theorem is that
argument: the antecedent is cheap to satisfy in any game form with a rich enough
strategy space, so `Sovereign` is false almost everywhere. Their sharpest form of
it -- "if the mere possibility of interference is enough to render us unfree,
then the interference itself cannot do anything more to our freedom" -- is the
observation that `Sovereign` is a `Prop`, so a coalition that has lost it cannot
lose more.

They are right about social freedom and it does not make this definition wrong,
because the two are answering different questions. Their positive proposal is to
weigh each possible interference by its conditional probability, and their
counterexamples turn on that weighing: "the very low probability of anyone
actually killing us". That step assumes an environment which is not searching for
the interference that works. Against an optimising adversary the improbable
branch is the one that gets found, which is why safety and security properties
are stated over all traces rather than over likely ones. So `Sovereign` should be
read as a **non-interference invariant**, in the sense verification uses, and not
as a measure of freedom in the sense this literature is arguing about. Note also
that `SovereignEnv` does not answer them: restricting to a set of environments is
List and Valentini's *nearby worlds* qualification, which the paper rebuts
directly on the ground that nearness is not improbability -- the worlds in which
your neighbour interferes are very close ones.
-/
public theorem not_sovereign_of_outsider_moves_view [DecidableEq N]
    {D : Set N} {view : X → V} {j : N} (hj : j ∉ D)
    (s : ∀ i, G.strategy i) (t : G.strategy j)
    (h : view (G.outcome s) ≠ view (G.outcome (Function.update s j t))) :
    ¬ Sovereign G D view := by
  intro hsov
  exact h (hsov s (Function.update s j t) fun i => by
    have : (i : N) ≠ j := fun hij => hj (hij ▸ i.2)
    exact (Function.update_of_ne this t s).symm)

/-! ## Sovereignty against power

The two notions meet here, and the meeting is not a negation.
-/

/--
**A sovereign coalition is immune to power inside its boundary.**

If `D` is sovereign over `view`, then no coalition has power over `D` at any
target of the form `view ⁻¹' B` -- a target the boundary can express. The reason
is immediate once `Sovereign` is read correctly: `ForcesGiven` at such a target
does not depend on `C`'s commitment at all, so the two clauses of `HasPowerOver`
that demand a commitment which forces and one which does not cannot both hold.

This is what licenses the word *sovereignty*. Not that no one tries, and not that
`D` is powerful, but that intrusion inside the boundary is unavailable to
everyone, whatever they play.
-/
public theorem not_hasPowerOver_of_sovereign [∀ i, Nonempty (G.strategy i)]
    {C D : Set N} {view : X → V} (h : Sovereign G D view) (B : Set V) :
    ¬ HasPowerOver G C D (view ⁻¹' B) := by
  classical
  rintro ⟨hCD, ⟨sC, sD, hforce⟩, ⟨sC', hnot⟩⟩
  refine hnot ⟨sD, fun s _ hsD ↦ ?_⟩
  -- A profile playing `sC` on `C` and `sD` on `D`. Disjointness is what makes the
  -- two prescriptions consistent, which is why `HasPowerOver` carries it.
  obtain ⟨t, htC, htD⟩ : ∃ t : ∀ i, G.strategy i,
      (∀ i : C, t i = sC i) ∧ (∀ i : D, t i = sD i) := by
    refine ⟨fun i ↦ if hi : i ∈ C then sC ⟨i, hi⟩
      else if hi' : i ∈ D then sD ⟨i, hi'⟩ else Classical.arbitrary _, ?_, ?_⟩
    · rintro ⟨i, hi⟩; simp [hi]
    · rintro ⟨i, hi⟩
      have hiC : i ∉ C := Set.disjoint_right.mp hCD hi
      simp [hiC, hi]
  have hmem : view (G.outcome t) ∈ B := hforce t htC htD
  have hview : view (G.outcome s) = view (G.outcome t) :=
    h s t fun i ↦ (hsD i).trans (htD i).symm
  rw [Set.mem_preimage, hview]
  exact hmem

/-! ## Sovereignty given how everyone else is arranged

`Sovereign` quantifies over every strategy of every outsider, which is the
worst-case reading. For a *defensive* notion that is the right default -- you do
not get to choose who tries -- but it is not the only question worth asking, and
the same branch already made the point on the other side: `ForcesGivenEnv` exists
because worst-case-over-outsiders "silently fixes the environment to the one
configuration in which every bystander is hostile".

A state can be sovereign while its alliances hold and not sovereign in the worst
case, and both are things one wants to say. `SovereignEnv` restricts the
invariance to profiles the environment admits, and `sovereignEnv_true_iff`
recovers `Sovereign` as the unconstrained instance, exactly as
`forcesGivenEnv_true_iff` does for forcing.
-/

/-- **Sovereignty given an environment.** The view is unmoved by outsiders, among
the profiles `Env` admits. -/
@[expose] public def SovereignEnv (G : GameForm.{u, v, w} N X) (D : Set N)
    (Env : (∀ i, G.strategy i) → Prop) (view : X → V) : Prop :=
  ∀ s s' : ∀ i, G.strategy i,
    Env s → Env s' → (∀ i : D, s i = s' i) → view (G.outcome s) = view (G.outcome s')

/-- The unconstrained environment recovers the worst-case reading exactly. -/
public theorem sovereignEnv_true_iff {D : Set N} {view : X → V} :
    SovereignEnv G D (fun _ ↦ True) view ↔ Sovereign G D view :=
  ⟨fun h s s' hss' ↦ h s s' trivial trivial hss',
    fun h s s' _ _ hss' ↦ h s s' hss'⟩

/-- Worst-case sovereignty is sovereignty in every environment. The converse
fails, which is the point of having both. -/
public theorem Sovereign.sovereignEnv {D : Set N} {view : X → V}
    (h : Sovereign G D view) (Env : (∀ i, G.strategy i) → Prop) :
    SovereignEnv G D Env view := fun s s' _ _ hss' ↦ h s s' hss'

/-- **A narrower environment is easier to be sovereign in.** Ruling out
configurations can only remove ways for the view to move. -/
public theorem SovereignEnv.mono_env {D : Set N} {view : X → V}
    {Env Env' : (∀ i, G.strategy i) → Prop} (hsub : ∀ s, Env' s → Env s)
    (h : SovereignEnv G D Env view) : SovereignEnv G D Env' view :=
  fun s s' hs hs' hss' ↦ h s s' (hsub s hs) (hsub s' hs') hss'

/-! ## Sovereignty is not the dual of power, it *contains* power

The tempting reading is that power and sovereignty are opposites: one aggressive,
one defensive. They are not opposites, and the theorem below says why. Power is a
**capability**, and holding a boundary is one of the things a capability is for.
The same capability can be turned outward instead, which is why
`Examples.Sovereignty.Boundary.splitGame_sovereign_and_powerful` is not a
paradox.

So the relation is containment rather than duality: **sovereignty over a
boundary is exclusive power over that boundary** -- `D` has it
(`Sovereign.forces_own_view`) and nobody else can move it
(`not_hasPowerOver_of_sovereign`). Neither half alone is sovereignty. A party
that could set its own view but whose setting could be overridden has the
capability and not the boundary; a party nothing can move but which cannot move
it either is inert, not sovereign.
-/

/--
**A sovereign coalition holds the power over its own boundary.**

Whatever `D` in fact plays, it thereby forces the view to the value it produced:
sovereignty is not merely that others cannot move the view, but that `D`'s own
choice fixes it. This is the "power is the capability sovereignty is made of"
half, and with `not_hasPowerOver_of_sovereign` it is the exclusivity.
-/
public theorem Sovereign.forces_own_view {D : Set N} {view : X → V}
    (h : Sovereign G D view) (s : ∀ i, G.strategy i) :
    Forces G D (view ⁻¹' {view (G.outcome s)}) :=
  ⟨fun i ↦ s i, fun s' hs' ↦ h s' s (fun i ↦ hs' i)⟩

/--
**Nobody outside can move the boundary, in the plain sense.**

`not_hasPowerOver_of_sovereign` refutes a specific notion -- whether `C`'s
commitment settles `D`'s reach. This is the simpler statement standing behind
it: an outsider coalition can force a boundary target only when that target
already holds at every profile. So an outsider's forcing power over the boundary
is vacuous, which is what makes `D`'s power over it *exclusive* rather than
merely uncontested.
-/
public theorem Sovereign.outsider_forces_trivially {C D : Set N} {view : X → V}
    (h : Sovereign G D view) (hCD : Disjoint C D) {B : Set V}
    (hforce : Forces G C (view ⁻¹' B)) (s : ∀ i, G.strategy i) :
    view (G.outcome s) ∈ B := by
  classical
  obtain ⟨sC, hsC⟩ := hforce
  -- Agree with `C`'s forcing commitment, and with `s` everywhere else.
  obtain ⟨t, htC, htD⟩ : ∃ t : ∀ i, G.strategy i,
      (∀ i : C, t i = sC i) ∧ ∀ i : D, t i = s i := by
    refine ⟨fun i ↦ if hi : i ∈ C then sC ⟨i, hi⟩ else s i, ?_, ?_⟩
    · rintro ⟨i, hi⟩; simp [hi]
    · rintro ⟨i, hi⟩
      have hiC : i ∉ C := Set.disjoint_right.mp hCD hi
      simp [hiC]
  have hmem : view (G.outcome t) ∈ B := hsC t htC
  have : view (G.outcome s) = view (G.outcome t) := h s t fun i ↦ (htD i).symm
  rw [this]
  exact hmem

/-! ## Dictation: putting the state where you want it

Power in the sense that matters is not holding a large repertoire. It is being
able to **put the state where you like**, so that everyone else takes what
follows as a consequence rather than as a choice. This section states that, and
states the law that stops two parties doing it at once.

`Dictates` is the exact mirror of `Sovereign`. Sovereignty says *outsiders*
cannot move what the boundary shows. Dictation says *this coalition alone* fixes
what it shows. Same equation, different side: sovereignty is a view that nobody
outside can move, dictation is a view that this coalition has already moved.
-/

/--
**`C` dictates the view.** It has a commitment after which what the view shows is
settled, whatever anyone else plays.

Note what this does *not* say: not that `C` gets the outcome it wants, and not
that `C` controls the whole outcome. Only that the boundary's reading is `C`'s to
set, so everyone else receives it rather than choosing it.
-/
@[expose] public def Dictates (G : GameForm.{u, v, w} N X) (C : Set N)
    (view : X → V) : Prop :=
  ∃ sC : ∀ i : C, G.strategy i,
    ∀ s s' : ∀ i, G.strategy i,
      (∀ i : C, s i = sC i) → (∀ i : C, s' i = sC i) →
        view (G.outcome s) = view (G.outcome s')

/-- **Dictating is forcing a value of the view.** The two readings agree, which is
what lets the forcing laws apply to dictation. -/
public theorem dictates_iff_exists_forces_value [∀ i, Nonempty (G.strategy i)]
    {C : Set N} {view : X → V} :
    Dictates G C view ↔ ∃ v : V, Forces G C (view ⁻¹' {v}) := by
  classical
  constructor
  · rintro ⟨sC, hsC⟩
    refine ⟨view (G.outcome fun i ↦ if hi : i ∈ C then sC ⟨i, hi⟩ else Classical.arbitrary _),
      sC, fun s hs ↦ ?_⟩
    exact hsC s _ hs fun i ↦ by simp [i.2]
  · rintro ⟨v, sC, hsC⟩
    exact ⟨sC, fun s s' hs hs' ↦ by rw [hsC s hs, hsC s' hs']⟩

/-- **Sovereignty over your own boundary is already dictation of it.** If nothing
outside `C` can move the view, then `C`'s own commitment settles it. This is one
direction of the containment between power and sovereignty: keeping a boundary
requires being able to set it. -/
public theorem Sovereign.dictates [∀ i, Nonempty (G.strategy i)] {C : Set N}
    {view : X → V} (h : Sovereign G C view) : Dictates G C view := by
  classical
  exact ⟨fun _ ↦ Classical.arbitrary _,
    fun s s' hs hs' ↦ h s s' fun i ↦ (hs i).trans (hs' i).symm⟩

/--
**The overcoming law: two separated parties cannot both put the state where they
like, when they like different things.**

If `C` forces the view to `v` and a disjoint `D` forces it to `w`, then `v = w`.
Nobody has to lose a contest for this to hold -- the game form has no contest in
it -- but it means at most one *value* can be dictated, so at most one side's
preference can be the one the view ends up showing.

This is `Forces.inter_nonempty_of_disjoint`, which is Gaerdenfors' consistency
condition, read as a statement about power rather than about rights.
-/
public theorem eq_of_dictate_disjoint [∀ i, Nonempty (G.strategy i)]
    {C D : Set N} {view : X → V} {v w : V} (hCD : Disjoint C D)
    (hC : Forces G C (view ⁻¹' {v})) (hD : Forces G D (view ⁻¹' {w})) :
    v = w := by
  obtain ⟨x, hxv, hxw⟩ := Forces.inter_nonempty_of_disjoint hCD hC hD
  exact (Set.mem_preimage.mp hxv).symm.trans (Set.mem_preimage.mp hxw)

/--
**Everyone else is a taker.** If `C` dictates the view to `v`, then anything a
disjoint `D` can force about the view has to admit `v`. `D` still acts, and may
force plenty; it simply cannot force anything that rules out what `C` chose.

This is the sense in which the weaker party "gets what it gets as a
consequence": its achievable descriptions of the boundary are exactly those
compatible with the dictated value.
-/
public theorem mem_of_forces_of_dictated [∀ i, Nonempty (G.strategy i)]
    {C D : Set N} {view : X → V} {v : V} {B : Set V} (hCD : Disjoint C D)
    (hC : Forces G C (view ⁻¹' {v})) (hD : Forces G D (view ⁻¹' B)) :
    v ∈ B := by
  obtain ⟨x, hxv, hxB⟩ := Forces.inter_nonempty_of_disjoint hCD hC hD
  exact (Set.mem_preimage.mp hxv) ▸ Set.mem_preimage.mp hxB

/-- **A dictator with two options destroys everyone else's sovereignty.** If `C`
can force the view to either of two distinct values, then no coalition disjoint
from `C` is sovereign over it. Dictation and outside sovereignty over the same
boundary are incompatible. -/
public theorem not_sovereign_of_dictates_two [∀ i, Nonempty (G.strategy i)]
    {C D : Set N} {view : X → V} {v w : V} (hCD : Disjoint C D) (hvw : v ≠ w)
    (hv : Forces G C (view ⁻¹' {v})) (hw : Forces G C (view ⁻¹' {w})) :
    ¬ Sovereign G D view := by
  classical
  intro hsov
  obtain ⟨sv, hsv⟩ := hv
  obtain ⟨sw, hsw⟩ := hw
  obtain ⟨p, hpC, hpOut⟩ : ∃ p : ∀ i, G.strategy i,
      (∀ i : C, p i = sv i) ∧ ∀ i, i ∉ C → p i = Classical.arbitrary _ := by
    refine ⟨fun i ↦ if hi : i ∈ C then sv ⟨i, hi⟩ else Classical.arbitrary _, ?_, ?_⟩
    · rintro ⟨i, hi⟩; simp [hi]
    · intro i hi; simp [hi]
  obtain ⟨q, hqC, hqOut⟩ : ∃ q : ∀ i, G.strategy i,
      (∀ i : C, q i = sw i) ∧ ∀ i, i ∉ C → q i = Classical.arbitrary _ := by
    refine ⟨fun i ↦ if hi : i ∈ C then sw ⟨i, hi⟩ else Classical.arbitrary _, ?_, ?_⟩
    · rintro ⟨i, hi⟩; simp [hi]
    · intro i hi; simp [hi]
  have hpq : ∀ i : D, p i = q i := by
    rintro ⟨i, hi⟩
    have hiC : i ∉ C := Set.disjoint_right.mp hCD hi
    rw [hpOut i hiC, hqOut i hiC]
  have hvp : view (G.outcome p) = v := hsv p hpC
  have hwq : view (G.outcome q) = w := hsw q hqC
  apply hvw
  rw [← hvp, ← hwq]
  exact hsov p q hpq

/-- **Exact power over a view value is dictation of the view.** `ActualPower`
asks for a commitment whose outcomes are exactly the target; taking the target to
be one value of the view, that is dictation. This is the join between the
strongest forcing notion in the neighbouring file and this one. -/
public theorem ActualPower.dictates [∀ i, Nonempty (G.strategy i)] {C : Set N}
    {view : X → V} {v : V} (h : ActualPower G C (view ⁻¹' {v})) :
    Dictates G C view :=
  dictates_iff_exists_forces_value.mpr ⟨v, h.forces⟩

/--
**A dictator with two options has power over everyone else.**

If `C` can put the view at either of two distinct values, then `C` has power over
any disjoint `D` at the target `view ⁻¹' {v}`: one commitment leaves `D` bound to
land there whatever it plays, and the other leaves it unable to. `D`'s ability to
reach that description of the boundary is `C`'s to grant or withhold.

Together with `not_sovereign_of_dictates_two` this is the whole asymmetry: the
same two commitments that destroy `D`'s sovereignty give `C` power over `D`. That
is what makes dictation a relation and not merely a capacity.
-/
public theorem hasPowerOver_of_dictates_two [∀ i, Nonempty (G.strategy i)]
    {C D : Set N} {view : X → V} {v w : V} (hCD : Disjoint C D) (hvw : v ≠ w)
    (hv : Forces G C (view ⁻¹' {v})) (hw : Forces G C (view ⁻¹' {w})) :
    HasPowerOver G C D (view ⁻¹' {v}) := by
  classical
  obtain ⟨sv, hsv⟩ := hv
  obtain ⟨sw, hsw⟩ := hw
  refine ⟨hCD, ⟨sv, ⟨fun _ ↦ Classical.arbitrary _, fun s hsC _ ↦ hsv s hsC⟩⟩, ⟨sw, ?_⟩⟩
  rintro ⟨sD, hsD⟩
  obtain ⟨t, htC, htD⟩ : ∃ t : ∀ i, G.strategy i,
      (∀ i : C, t i = sw i) ∧ (∀ i : D, t i = sD i) := by
    refine ⟨fun i ↦ if hi : i ∈ C then sw ⟨i, hi⟩
      else if hj : i ∈ D then sD ⟨i, hj⟩ else Classical.arbitrary _, ?_, ?_⟩
    · rintro ⟨i, hi⟩; simp [hi]
    · rintro ⟨i, hi⟩
      have hiC : i ∉ C := Set.disjoint_right.mp hCD hi
      simp [hiC, hi]
  have h1 : view (G.outcome t) = v := hsD t htC htD
  have h2 : view (G.outcome t) = w := hsw t htC
  exact hvw (h1.symm.trans h2)

/-! ## Losing a boundary is losing actions, not only outcomes

The outcome-level notion above is the clearer picture, and it is not the whole
one. When a boundary is actually overrun, what typically happens first is that
the holder's **available actions shrink** -- a border closes, a channel is cut, a
topic becomes unthinkable -- rather than that its actions stay available and stop
working. An account that only watched outcomes would call those two the same
whenever the removed actions happened to be ones that changed nothing.

`Curtailment` is the minimal object that can tell them apart: an outsider's
choice `e` fixes which actions the holder may take, and the outcome depends on
the action alone. `reach_mono` is the direction that always holds -- fewer
actions can only mean fewer outcomes -- and
`Examples.Sovereignty.Boundary.curtailed_but_reach_unchanged` is the separation:
an action set can be cut with no outcome consequence at all, so
**action-level sovereignty is strictly stronger than outcome-level**.

This is deliberately not a `GameForm`. Availability of `i`'s actions as a
function of the full profile is circular, and resolving that is a design question
-- staging, or a game family indexed by configuration as `HasStructuralPower`
does -- which this file does not settle.
-/

/-- An outsider's choice `e` fixes which of the holder's actions are available;
the outcome depends on the action alone. -/
public structure Curtailment (E : Type*) (Act : Type*) (X : Type*) where
  /-- Which actions the holder may take, given the outsider's choice. -/
  available : E → Set Act
  /-- What an action produces. -/
  outcome : Act → X

namespace Curtailment

variable {E Act Y : Type*}

/-- The outcomes the holder can still bring about. -/
@[expose] public def reach (M : Curtailment E Act Y) (e : E) : Set Y :=
  M.outcome '' M.available e

/-- **Fewer actions, no more outcomes.** The direction that always holds. -/
public theorem reach_mono (M : Curtailment E Act Y) {e e' : E}
    (h : M.available e' ⊆ M.available e) : M.reach e' ⊆ M.reach e :=
  Set.image_mono h

/-- **Action-level sovereignty.** The holder's options do not depend on the
outsider at all. -/
@[expose] public def Uncurtailed (M : Curtailment E Act Y) : Prop :=
  ∀ e e' : E, M.available e = M.available e'

/-- **Outcome-level sovereignty.** What the holder can bring about does not
depend on the outsider. -/
@[expose] public def ReachInvariant (M : Curtailment E Act Y) : Prop :=
  ∀ e e' : E, M.reach e = M.reach e'

/-- Keeping every action keeps every outcome. The converse fails, which is the
point -- see `curtailed_but_reach_unchanged`. -/
public theorem reachInvariant_of_uncurtailed {M : Curtailment E Act Y}
    (h : M.Uncurtailed) : M.ReachInvariant :=
  fun e e' ↦ by rw [reach, reach, h e e']

end Curtailment

/-! ## Sovereignty is immunity *inside a boundary*, and not immunity

A sovereign `D` may still be subject to power at targets its boundary does not
express, and that is the content of *"within some boundaries"* rather than a
defect. A state sovereign over its territory is still subject to the price of
wheat; a mind sovereign over its own cognition is still subject to what the
world in fact contains.

Stating that needs a game where both hold at once, so it is a theorem about a
witness rather than a general fact, and it lives in
the boundary examples module with the four combinations of
sovereignty and power.
-/

end AISafetyAtlas.Sovereignty
