module

public import AISafetyAtlas.Sovereignty.Arena
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Insert
public import Mathlib.Logic.Nonempty
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets

/-!
# Forcing, and what it does not distinguish

Countermodels and separations for the obligation stated in
[`cognitive-sovereignty-obligation.md`](../../docs/provenance/cognitive-sovereignty-obligation.md).

**This is not a foundation.** Every definition here exists to state a theorem in
this file, and nothing outside is meant to build on `GameForm`.

**Amended 2026-09-11: the two further claims this paragraph used to make are
false, and both were about provenance rather than mathematics.** It read *"not a
foundation and not coverage ... and no registry row is claimed"*. It **is**
coverage, of a source it was not written to cover: `GameForm` is Peleg's
Definition 3.2, `Forces` and `effectivity` are his Definition 3.3, and
`forces_univ`, `Forces.mono`, `Forces.mono_coalition` and `forces_superadditive`
are four conditions he *imposes* on an effectivity function and this file
*derives* — which is precisely why `forces_superadditive` can carry the
conclusion it does. That is graded in section 21 of
`docs/provenance/source-coverage-audit.md` (7 Yes, 4 Partial, 16 No, 2 Beyond),
and `LAND-SOV-POWER-001` now hosts this module and
`AISafetyAtlas.Sovereignty.Mandate`. The separations themselves are still not
coverage of anything, and are graded `Beyond` there. The `ActualPower` section
below renders Chen, Ju and Ågotnes and has **no** section in that file yet. The note reaches three prose conclusions and one
retraction, and each is a claim a reader has to take on trust while it stays
prose. This file discharges four of them mechanically:

* `forces_superadditive` — superadditivity is a **theorem about every game
  form**, not a condition a game can fail. Together with `dominated_forces_univ`
  (a game form in which the pressured player forces no proper subset) it settles
  that the axiom carries no information about domination.
* `forces_of_forces_singletons` — forcing every singleton forces every non-empty
  target, so widening the target set is a corollary rather than a missing
  capability.
* `retainsAgainst_imp_retainsWith`, and the three `not_` results beside it — the
  note's three readings of *who acts for the principal* are genuinely three
  obligations. One implication holds and nothing else does.
* `minCard_cannot_separate` — a principal in a system pinned to one outcome and
  a principal who can select any outcome both force a singleton. The retracted
  measure is retracted for a checkable reason.

The `Forces` here is α-forcing: the coalition moves first and the guarantee is
against **every** completion. No payoff for the complement appears, and none is
needed — see the note's §3.

Two further sections answer questions the note raised and could not settle.

**`ActualPower`** is the literature's other notion of coalition power (Chen, Ju &
Ågotnes, arXiv:2607.10567; *basic powers* in van Benthem's terminology), and it
places `forces_of_forces_singletons` correctly. That theorem is not an artefact of
this development: `α`-forcing is upward closed by construction, and the resulting
inability to tell an exactly-hit target from a merely-landed-in one is the known
objection to `α`-effectivity. `pinned_not_actualPower_pair` exhibits the
separation.

**`MForces`** is forcing when the principal may condition only on what a channel
reveals. `mforces_of_factors` is the monotonicity a claim about mediated
sovereignty needs — coarsening the channel never gains — and `matchGame_forces`
with `matchGameBlind_not_forces` shows the loss is real at some channel rather
than merely permitted by the statement.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/--
A game form: a strategy space per agent, and a map from complete strategy
profiles to outcomes.

The outcome type `X` is deliberately separate from the profile. Identifying the
two — taking outcomes to *be* profiles — trivialises everything below, and is the
gap the note's §5 records against EconCSLib's strategic-game structure, which
carries strategy spaces and a payoff map and no outcome type of its own.

**Where this sits in the literature's taxonomy.** Chen, Ju & Ågotnes
(arXiv:2607.10567) Definition 9 separates three assumptions built into the
standard model — **seriality** (every coalition has an available action at every
state), **independence** (disjoint coalitions' choices always combine), and
**determinism** (the grand coalition's outcome set is always a singleton) —
giving eight frame classes. `GameForm` has all three: strategies are
arbitrary dependent functions, so choices on disjoint coalitions combine and
independence holds by construction; `outcome` is a function, so determinism holds;
and seriality holds whenever the strategy types are inhabited. It is therefore an
**SID-frame**, the most restrictive of the eight and the one Pauly's original
representation theorem assumes. Everything below is a statement about that class
only.

**Print's own carrier lives in `AISafetyAtlas.Sovereignty.ConcurrentGameFrame`**,
added 2026-09-20, and `gameFrame` is the embedding that places this one. Its
state set is the **outcome type** with state-independent dynamics, not a single
state: this paragraph used to say *"at a single state"*, and with a one-point
state set every alpha power would be trivial.
-/
public structure GameForm (N : Type u) (X : Type v) where
  /-- Each agent's strategy space. -/
  strategy : N → Type w
  /-- The outcome produced by a complete profile. -/
  outcome : (∀ i, strategy i) → X

variable {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}

/--
**α-forcing.** Coalition `C` has a joint choice such that *every* profile
agreeing with it on `C` lands the outcome in `A`.

Stated by agreement rather than by merging a coalition choice with a complement
choice: it needs no decidable membership and no splitting lemma, and the two
formulations have the same content.
-/
@[expose] public def Forces (G : GameForm.{u, v, w} N X) (C : Set N) (A : Set X) : Prop :=
  ∃ sC : ∀ i : C, G.strategy i,
    ∀ s : ∀ i, G.strategy i, (∀ i : C, s i = sC i) → G.outcome s ∈ A

/-- The effectivity family of a coalition: everything it can force. -/
@[expose] public def effectivity (G : GameForm.{u, v, w} N X) (C : Set N) : Set (Set X) :=
  {A | Forces G C A}

/--
**Forcing is decidable on a finite game form.** Every quantifier in `Forces`
ranges over a finite type once the agents, their strategy spaces and the
coalition are finite and membership in the target is decidable, so
`Fintype.decidableExistsFintype` and `Fintype.decidableForallFintype` settle it
and `by decide` closes a forcing claim on a worked model.

This is infrastructure, not a result: it lets an example *exhibit* a forcing
claim without hand-building the joint choice and checking the complement
pointwise. Nothing about the unbounded case changes.
-/
public instance decidableForces {N : Type u} {X : Type v}
    (G : GameForm.{u, v, w} N X) [Fintype N] [DecidableEq N]
    [∀ i : N, Fintype (G.strategy i)]
    [∀ (i : N) (a b : G.strategy i), Decidable (a = b)]
    (C : Set N) [∀ i : N, Decidable (i ∈ C)] (A : Set X) [∀ x : X, Decidable (x ∈ A)] :
    Decidable (Forces G C A) := by
  unfold Forces
  infer_instance

/--
**The outcomes still possible once coalition `C` has committed to `sC`.**

Print's "set of possible outcomes" of a joint action, at a SID frame: range
over the completions of `sC`. Determinism makes each *complete* profile a
singleton; a proper coalition's joint action still leaves a set, because the
complement has not yet moved.
-/
@[expose] public def outcomesOf (G : GameForm.{u, v, w} N X) (C : Set N)
    (sC : ∀ i : C, G.strategy i) : Set X :=
  {x | ∃ s : ∀ i, G.strategy i, (∀ i : C, s i = sC i) ∧ G.outcome s = x}

/-- Forcing `A` is having a joint action whose possible outcomes all lie in `A`. -/
public theorem forces_iff_outcomesOf_subset {C : Set N} {A : Set X} :
    Forces G C A ↔ ∃ sC, outcomesOf G C sC ⊆ A := by
  constructor
  · rintro ⟨sC, hsC⟩
    exact ⟨sC, fun _x ⟨s, hs, heq⟩ => heq ▸ hsC s hs⟩
  · rintro ⟨sC, hsub⟩
    exact ⟨sC, fun s hs => hsub ⟨s, hs, rfl⟩⟩

/-- Forcing is upward closed in the target. -/
public theorem Forces.mono {C : Set N} {A B : Set X}
    (h : Forces G C A) (hAB : A ⊆ B) : Forces G C B := by
  obtain ⟨sC, hsC⟩ := h
  exact ⟨sC, fun s hs => hAB (hsC s hs)⟩

/-- **Safety.** Every coalition forces the whole outcome space. -/
public theorem forces_univ [∀ i, Nonempty (G.strategy i)] (C : Set N) :
    Forces G C (Set.univ) :=
  ⟨fun _ => Classical.arbitrary _, fun _ _ => Set.mem_univ _⟩

/--
**Fact 1, item 1 (Chen, Ju & Ågotnes), at SID frames.** Extending a joint
action to a larger coalition can only shrink the set of possible outcomes.

Print's statement is about those sets, not about effectivity families.
`Forces.mono_coalition` is the effectivity-level consequence; this is the
statement itself. At print's own carrier it is
`IsGCGF.out_anti_coalition`, and this is that theorem's `SID` instance. It is not a degeneracy: a proper coalition's outcome set is
typically not a singleton, and `vetoGame_outcomesOf_strict` shows the inclusion
can be proper.
-/
public theorem outcomesOf_anti_coalition {C D : Set N}
    (hCD : C ⊆ D) (sC : ∀ i : C, G.strategy i) (sD : ∀ i : D, G.strategy i)
    (hagree : ∀ i : C, sD ⟨i, hCD i.2⟩ = sC i) :
    outcomesOf G D sD ⊆ outcomesOf G C sC := by
  intro x hx
  obtain ⟨s, hsD, rfl⟩ := hx
  refine ⟨s, fun i => ?_, rfl⟩
  have := hsD ⟨i, hCD i.2⟩
  rw [this, hagree i]

/-- Forcing is monotone in the coalition: a larger coalition forces at least as much. -/
public theorem Forces.mono_coalition [∀ i, Nonempty (G.strategy i)] {C D : Set N} {A : Set X}
    (h : Forces G C A) (hCD : C ⊆ D) : Forces G D A := by
  classical
  obtain ⟨sC, hsC⟩ := h
  refine ⟨fun i => if hi : (i : N) ∈ C then sC ⟨i, hi⟩ else Classical.arbitrary _, ?_⟩
  intro s hs
  refine hsC s fun i => ?_
  have hiD : (i : N) ∈ D := hCD i.2
  have := hs ⟨i, hiD⟩
  simpa [dif_pos i.2] using this

/--
**Superadditivity is a theorem here, because `GameForm` assumes what makes it
one.**

Disjoint coalitions that separately force `A` and `B` jointly force `A ∩ B`, for
every `GameForm`. Nothing has to be assumed *in this development* and nothing can
fail it, which is exactly why it says nothing about how much either coalition
retains — see `dominated_forces_univ`.

The qualification matters, and an earlier draft of this docstring omitted it.
Chen, Ju & Ågotnes (arXiv:2607.10567) Definition 9 isolates the assumption doing
the work: a general concurrent game frame is **independent** when, for disjoint
`C` and `D`, `σ_C ∈ av_C(s)` and `σ_D ∈ av_D(s)` imply `σ_C ∪ σ_D ∈ av_{C∪D}(s)` —
disjoint coalitions can always combine their choices. `GameForm` builds that in:
strategies are arbitrary dependent functions, so any two choices on disjoint sets
combine, and the proof below is exactly that combination. Their paper separates
seriality, independence and determinism into eight frame classes precisely so that
independence can be dropped, and superadditivity is not *guaranteed* in the
classes that do not impose it.

**That qualification is corrected 2026-09-11 and it used to read "not
available".** Print is explicit that the eight labels *"record which frame
conditions are imposed; they do not record which conditions are required to
fail"*, that the classes *"are not intended to be disjoint"*, and that a class
not imposing independence means the labels without it rather than *"the class of
frames in which independence fails"*. So dropping the label does not make
superadditivity unavailable; it makes it a real condition again, which frames in
those classes may still satisfy.

So the honest reading of this theorem is narrower than "true of every game form":
**within the standard class, superadditivity is forced and therefore carries no
information about domination.** Outside it, it is a real condition.

**And it is a condition that fails, 2026-09-20.**
`AISafetyAtlas.Examples.Sovereignty.exists_gcgf_not_superadditive` is a general
concurrent game frame with two disjoint coalitions, each effective for a state,
whose union is effective for neither intersection — so "not guaranteed" above is
now "false at some frame" rather than a possibility left open. The carrier is
`AISafetyAtlas.Sovereignty.ConcurrentGameFrame`.
-/
public theorem forces_superadditive {C D : Set N} {A B : Set X}
    (hCD : Disjoint C D) (hA : Forces G C A) (hB : Forces G D B) :
    Forces G (C ∪ D) (A ∩ B) := by
  classical
  obtain ⟨sC, hsC⟩ := hA
  obtain ⟨sD, hsD⟩ := hB
  refine ⟨fun i => if hi : (i : N) ∈ C then sC ⟨i, hi⟩ else sD ⟨i, i.2.resolve_left hi⟩, ?_⟩
  intro s hs
  constructor
  · refine hsC s fun i => ?_
    have := hs ⟨i, Or.inl i.2⟩
    simpa [dif_pos i.2] using this
  · refine hsD s fun i => ?_
    have hiC : (i : N) ∉ C := fun hc => (hCD.le_bot ⟨hc, i.2⟩ : (i : N) ∈ (⊥ : Set N))
    have := hs ⟨i, Or.inr i.2⟩
    simpa [dif_neg hiC] using this

/--
**Disjoint coalitions cannot be effective for incompatible targets.**

If `C` forces `A` and a disjoint `D` forces `B`, then `A` and `B` must intersect:
the profile that combines the two witness strategies produces an outcome lying in
both. Contrapositively, no two disjoint coalitions can hold rights to disjoint
sets of outcomes.

This is Gaerdenfors' (1981) **consistency condition** on a rights-system, the
requirement that the rights of disjoint groups never conflict. Here it is not a
condition to impose but a consequence of `forces_superadditive`, for the same
reason that theorem is free: `GameForm` makes disjoint coalitions' choices
combinable by construction. What it rules out is a reading of `Forces` on which
two separated parties could each guarantee outcomes the other excludes.
-/
public theorem Forces.inter_nonempty_of_disjoint [∀ i, Nonempty (G.strategy i)]
    {C D : Set N} {A B : Set X}
    (hCD : Disjoint C D) (hA : Forces G C A) (hB : Forces G D B) :
    (A ∩ B).Nonempty := by
  classical
  obtain ⟨sU, hsU⟩ := forces_superadditive hCD hA hB
  refine ⟨G.outcome fun i => if hi : i ∈ C ∪ D then sU ⟨i, hi⟩ else Classical.arbitrary _, ?_⟩
  exact hsU _ fun i => by simp

/--
**Forcing, with a total profile as the witness.**

`Forces` witnesses a coalition's commitment by a function on the subtype `↥C`,
which is the faithful reading. For proofs that combine commitments across
different coalitions that subtype is a nuisance: the strategy's *type* mentions
the coalition, so replacing one coalition by another is a dependent rewrite.

This says the same thing with a full profile as the witness, of which only the
values on `C` matter. Nothing changes about the notion; the type of the witness
stops depending on `C`.
-/
public theorem forces_iff_exists_total [∀ i, Nonempty (G.strategy i)] {C : Set N}
    {A : Set X} :
    Forces G C A ↔
      ∃ t : ∀ i, G.strategy i, ∀ s : ∀ i, G.strategy i,
        (∀ i ∈ C, s i = t i) → G.outcome s ∈ A := by
  classical
  constructor
  · rintro ⟨sC, hsC⟩
    refine ⟨fun k => if hk : k ∈ C then sC ⟨k, hk⟩ else Classical.arbitrary _,
      fun s hs => hsC s fun k => ?_⟩
    rw [hs k k.2]
    simp only [dif_pos k.2]
  · rintro ⟨t, ht⟩
    exact ⟨fun k => t k, fun s hs => ht s fun k hk => hs ⟨k, hk⟩⟩

/--
**Superadditivity over a whole family, not just a pair.**

Pairwise disjoint coalitions that each force a target jointly force the
intersection of those targets. `forces_superadditive` is the two-coalition case,
and the index type here is arbitrary, so the family need not be finite -- wider
than the partition-shaped use it was written for.

This is the law Pauly's Theorem 3.2 needs at its central claim. Constructing a
game form from an abstract playable effectivity function partitions the players
into blocks that agree on what to force and takes the intersection of what the
blocks force; that the intersection is forced by the union of the blocks is what
makes it non-empty. See `AISafetyAtlas.Sovereignty.Playability`.
-/
public theorem forces_iInter_of_pairwiseDisjoint [∀ i, Nonempty (G.strategy i)]
    {ι : Sort*} {C : ι → Set N} {A : ι → Set X}
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hforce : ∀ i, Forces G (C i) (A i)) :
    Forces G (⋃ i, C i) (⋂ i, A i) := by
  classical
  choose t ht using fun i => forces_iff_exists_total.mp (hforce i)
  have hidx : ∀ (k : N) (hk : k ∈ ⋃ i, C i) (i : ι), k ∈ C i →
      (Set.mem_iUnion.mp hk).choose = i := by
    intro k hk i hi
    by_contra hne
    exact (hdisj _ i hne).le_bot ⟨(Set.mem_iUnion.mp hk).choose_spec, hi⟩
  refine forces_iff_exists_total.mpr
    ⟨fun k => if hk : k ∈ ⋃ i, C i then t (Set.mem_iUnion.mp hk).choose k
      else Classical.arbitrary _, fun s hs => ?_⟩
  refine Set.mem_iInter.mpr fun i => ?_
  refine ht i s fun k hk => ?_
  have hkU : k ∈ ⋃ i, C i := Set.mem_iUnion.mpr ⟨i, hk⟩
  rw [hs k hkU]
  simp only [dif_pos hkU, hidx k hkU i hk]

/--
**No family of separated coalitions can hold incompatible guarantees.** The
targets of pairwise disjoint coalitions always share an outcome.

`Forces.inter_nonempty_of_disjoint` is the two-coalition case. As a law about
power: however the parties are separated, what each of them can guarantee must be
jointly satisfiable, so a conflict of guarantees is not something a game form can
exhibit.
-/
public theorem iInter_nonempty_of_pairwiseDisjoint [∀ i, Nonempty (G.strategy i)]
    {ι : Sort*} {C : ι → Set N} {A : ι → Set X}
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hforce : ∀ i, Forces G (C i) (A i)) :
    (⋂ i, A i).Nonempty := by
  classical
  obtain ⟨t, ht⟩ := forces_iff_exists_total.mp
    (forces_iInter_of_pairwiseDisjoint hdisj hforce)
  exact ⟨G.outcome t, ht t fun _ _ => rfl⟩

/--
**Widening the target is free.** A coalition that forces every singleton forces
every non-empty set.

This is why "`A` an arbitrary set rather than a singleton" is not a missing
capability of `AISafetyAtlas.Control.exists_strategy_forcing`: it follows by
choosing an element. The generalisation that is not free is dropping that
theorem's hypotheses.
-/
public theorem forces_of_forces_singletons {C : Set N}
    (h : ∀ x : X, Forces G C {x}) {A : Set X} (hA : A.Nonempty) : Forces G C A := by
  obtain ⟨a, ha⟩ := hA
  exact (h a).mono (Set.singleton_subset_iff.2 ha)

/-! ## Capability is not power: what `C` can do to what `D` can do -/

/--
**Residual capability.** What `D` can still force once `C` has committed to `sC`.

`Forces` is one coalition against the worst case, which is a coalition against
*nature*. Nothing in it is relational: it never mentions a second party's
prospects. This is the object that does.
-/
@[expose] public def ForcesGiven (G : GameForm.{u, v, w} N X) (C : Set N)
    (sC : ∀ i : C, G.strategy i) (D : Set N) (A : Set X) : Prop :=
  ∃ sD : ∀ i : D, G.strategy i,
    ∀ s : ∀ i, G.strategy i,
      (∀ i : C, s i = sC i) → (∀ i : D, s i = sD i) → G.outcome s ∈ A

/-- `D`'s effectivity family in the residual game after `C` has moved. -/
@[expose] public def effectivityGiven (G : GameForm.{u, v, w} N X) (C : Set N)
    (sC : ∀ i : C, G.strategy i) (D : Set N) : Set (Set X) :=
  {A | ForcesGiven G C sC D A}

/--
**`C` has power over `D` with respect to `A`** when whether `D` gets `A` is up to
`C`: some commitment by `C` leaves `A` within `D`'s reach and some other
commitment puts it out of reach.

This is a *capacity* claim about `C` and it is *relational* by construction — it
cannot be stated without a second party whose prospects vary. No payoff for `D`
appears, so this is power as ability rather than as harm; whether `D` minds is a
further question and deliberately not this one.

**Disjointness is part of the definition, not a stylistic precondition.**
`forcesGiven_vacuous_of_overlap` shows that a shared agent lets `D` contradict
`C`'s choice at that agent, leaving no profile to quantify over, so `D` vacuously
"forces" every target including `∅`. Without the `Disjoint C D` conjunct, power
claims over overlapping coalitions would be noise.

**`D` moves second.** `ForcesGiven` fixes `sC` before `D` chooses, so this is the
sequential reading: `C` commits and `D` best-responds. The simultaneous reading
(`∃ sD` outside `∀ sC`) is a different and weaker capability for `D`. Committing
first is what having power looks like, but it is a modelling choice and is
recorded as one.
-/
@[expose] public def HasPowerOver (G : GameForm.{u, v, w} N X) (C D : Set N)
    (A : Set X) : Prop :=
  Disjoint C D ∧
    (∃ sC : ∀ i : C, G.strategy i, ForcesGiven G C sC D A) ∧
    (∃ sC : ∀ i : C, G.strategy i, ¬ ForcesGiven G C sC D A)

/--
**`C` moves the whole of `D`'s reach, not one target.** `HasPowerOver` is
pointwise in `A`; the underlying object is the map `sC ↦ effectivityGiven G C sC D`,
and `C` has power over `D` at some target exactly when that map is non-constant.

So the answer to "outcomes or capability" is: both, one level apart. Capability is
a set of outcomes; power moves a set of sets of outcomes. **The levels do not
regress**, because `C` and `D` act in the *same* game and feed the *same* outcome
function — power is a derived predicate on one game, not a second game played over
capability sets. Second-order power (`C` over `D`'s power over `E`) is expressed by
taking three coalitions, not by taking a further type.
-/
public theorem hasPowerOver_iff_effectivityGiven_ne {C D : Set N} (hCD : Disjoint C D) :
    (∃ A : Set X, HasPowerOver G C D A) ↔
      ∃ sC sC' : ∀ i : C, G.strategy i,
        effectivityGiven G C sC D ≠ effectivityGiven G C sC' D := by
  constructor
  · rintro ⟨A, -, ⟨sC, hsC⟩, sC', hsC'⟩
    refine ⟨sC, sC', fun hEq => hsC' ?_⟩
    have : A ∈ effectivityGiven G C sC D := hsC
    rwa [hEq] at this
  · rintro ⟨sC, sC', hne⟩
    by_contra hno
    push Not at hno
    refine hne (Set.ext fun A => ?_)
    have h := hno A
    constructor
    · intro hA
      by_contra hA'
      exact absurd ⟨hCD, ⟨sC, hA⟩, sC', hA'⟩ h
    · intro hA
      by_contra hA'
      exact absurd ⟨hCD, ⟨sC', hA⟩, sC, hA'⟩ h

/-- Committing more of the profile can only help the remaining coalition: what `D`
forces outright, it still forces after `C` has moved. -/
public theorem forcesGiven_of_forces {C D : Set N} {A : Set X}
    (h : Forces G D A) (sC : ∀ i : C, G.strategy i) : ForcesGiven G C sC D A := by
  obtain ⟨sD, hsD⟩ := h
  exact ⟨sD, fun s _ hD => hsD s hD⟩

/--
**Power over someone requires that they lack the capability.**

If `D` can force `A` on its own, no commitment by `C` can take it away, so `C` has
no power over `D` at `A`. Capability is what power acts on, and where capability
is complete there is nothing for power to do.
-/
public theorem not_hasPowerOver_of_forces {C D : Set N} {A : Set X}
    (h : Forces G D A) : ¬ HasPowerOver G C D A := by
  rintro ⟨-, -, sC, hsC⟩
  exact hsC (forcesGiven_of_forces h sC)

/-! ### A game form where power is real -/

/-- Two players, each holding a veto: the outcome is good only if both choose so. -/
@[expose] public def vetoGame : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Bool
  outcome s := s false && s true

/-- Neither player can force the good outcome alone — neither has the capability. -/
public theorem vetoGame_not_forces :
    ¬ Forces vetoGame {true} {true} := by
  rintro ⟨sD, hsD⟩
  have h := hsD (fun b => cond b (sD ⟨true, rfl⟩) false) (by
    rintro ⟨b, hb⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    rfl)
  simp only [vetoGame, Set.mem_singleton_iff] at h
  exact Bool.noConfusion h

/--
**But each has power over the other.** Whether the second player can reach the
good outcome is settled by the first player's commitment.

Together with `vetoGame_not_forces` this is the separation the distinction needs:
no capability, and yet power. Power is not a coalition's own reach — it is the
dependence of one party's reach on another's choice.
-/
public theorem vetoGame_hasPowerOver :
    HasPowerOver vetoGame {false} {true} {true} := by
  refine ⟨by simp, ?_, ?_⟩
  · refine ⟨fun _ => true, fun _ => true, fun s hC hD => ?_⟩
    have h0 : s false = true := hC ⟨false, rfl⟩
    have h1 : s true = true := hD ⟨true, rfl⟩
    simp [vetoGame, h0, h1]
  · refine ⟨fun _ => false, ?_⟩
    rintro ⟨sD, hsD⟩
    have h := hsD (fun b => cond b (sD ⟨true, rfl⟩) false)
      (by rintro ⟨b, hb⟩; simp only [Set.mem_singleton_iff] at hb; subst hb; rfl)
      (by rintro ⟨b, hb⟩; simp only [Set.mem_singleton_iff] at hb; subst hb; rfl)
    simp only [vetoGame, Set.mem_singleton_iff] at h
    exact Bool.noConfusion h

/-- One player committing `true` still leaves both outcomes open: the other
player has not yet moved. -/
public theorem vetoGame_outcomesOf_one :
    outcomesOf vetoGame ({false} : Set Bool) (fun _ => true) = (Set.univ : Set Bool) := by
  ext b
  constructor
  · intro; trivial
  · intro
    refine ⟨fun i => cond i b true, ?_, ?_⟩
    · rintro ⟨i, hi⟩
      simp only [Set.mem_singleton_iff] at hi
      subst hi
      rfl
    · simp [vetoGame]

/-- Both committing `true` leaves only `true`. -/
public theorem vetoGame_outcomesOf_both :
    outcomesOf vetoGame (Set.univ : Set Bool) (fun _ => true) = ({true} : Set Bool) := by
  ext b
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hf : s false = true := hs ⟨false, trivial⟩
    have ht : s true = true := hs ⟨true, trivial⟩
    simp [vetoGame, hf, ht]
  · rintro rfl
    exact ⟨fun _ => true, fun _ => rfl, rfl⟩

/-- **Fact 1 is not a degeneracy at SID frames.** Extending `{false}` to
everybody strictly shrinks the outcome set: `{true} ⊂ univ`. -/
public theorem vetoGame_outcomesOf_strict :
    outcomesOf vetoGame (Set.univ : Set Bool) (fun _ => true) ⊂
      outcomesOf vetoGame ({false} : Set Bool) (fun _ => true) := by
  rw [vetoGame_outcomesOf_both, vetoGame_outcomesOf_one]
  refine ⟨fun _ _ => trivial, ?_⟩
  intro h
  have : false ∈ ({true} : Set Bool) := h (Set.mem_univ false)
  simp at this

/--
**Trap: overlapping coalitions make `ForcesGiven` vacuous**, so `C` and `D` must be
disjoint for any of this to mean anything.

If some agent is in both, `D` can pick a choice contradicting `C`'s at that agent;
then no profile satisfies both agreement conditions and the universal statement
holds emptily — `D` "forces" even the empty target. The witness below is concrete
rather than general because that is enough to document a trap.
-/
public theorem forcesGiven_vacuous_of_overlap :
    ForcesGiven vetoGame {false} (fun _ => true) {false} (∅ : Set Bool) := by
  refine ⟨fun _ => false, fun s hC hD => ?_⟩
  have h1 : s false = true := hC ⟨false, rfl⟩
  have h2 : s false = false := hD ⟨false, rfl⟩
  exact absurd (h1.symm.trans h2) Bool.noConfusion

/-! ## A game form in which one player names the outcome -/

/--
Two players — `false` is the pressured party, `true` the pusher — and the pusher
names the outcome outright.

The specification matters. A game form that merely *ignores* the pressured
player's strategy leaves it forcing `{A | Set.range G.outcome ⊆ A}`, which is
`{Set.univ}` only when the pusher can reach every outcome. Here the pusher's
strategy space **is** `X`, so it can.
-/
@[expose] public def dominatedForm (X : Type v) : GameForm.{0, v, v} Bool X where
  strategy _ := X
  outcome s := s true

/-- The pusher forces every non-empty target. -/
public theorem pusher_forces_singleton (x : X) :
    Forces (dominatedForm X) {true} {x} :=
  ⟨fun _ => x, fun _ hs => hs ⟨true, rfl⟩⟩

/--
**The pressured player forces no proper subset of `X`.**

Its effectivity family is `{Set.univ}` — the safety condition alone — while
`forces_superadditive` holds for this game form as it holds for every other.
Superadditivity therefore holds under complete domination, which is the note's
§4 countermodel, machine-checked.
-/
public theorem dominated_forces_univ {A : Set X} (h : Forces (dominatedForm X) {false} A) :
    A = Set.univ := by
  obtain ⟨sC, hsC⟩ := h
  refine Set.eq_univ_of_forall fun x => ?_
  exact hsC (fun b => cond b x (sC ⟨false, rfl⟩)) (by
    rintro ⟨b, hb⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    rfl)

/-! ## The three readings of "who acts for the principal" -/

/--
**Reading 1 — the delegate joins the principal's coalition.** The guarantee
assumes the delegate's cooperation, so this measures the principal-plus-agent
bloc against outsiders.
-/
@[expose] public def RetainsWith (G : GameForm.{u, v, w} N X) (p d : N) (A : Set X) : Prop :=
  Forces G {p, d} A

/--
**Reading 2 — the delegate sits in the complement.** The guarantee has to survive
the delegate's own deviation. This is the strongest reading, and the one closest
to the note's "shadow sovereignty".
-/
@[expose] public def RetainsAgainst (G : GameForm.{u, v, w} N X) (p : N) (A : Set X) : Prop :=
  Forces G {p} A

/--
**Reading 3 — the delegate's policy is fixed by the game form.** Nobody forces;
the question is which targets the fixed policy lands in.
-/
@[expose] public def RetainsUnder (G : GameForm.{u, v, w} N X) (d : N)
    (σd : G.strategy d) (A : Set X) : Prop :=
  ∀ s : ∀ i, G.strategy i, s d = σd → G.outcome s ∈ A

/-! ### Deciding the three readings on a finite model

Each reading is `Forces` at a named coalition or a pinned strategy, so
`decidableForces` settles the first two and the third is a bounded universal.
With these, a worked model discharges a reading by `decide` instead of by
exhibiting the joint choice and checking the complement by hand.
-/

public instance decidableRetainsWith {N : Type u} {X : Type v}
    (G : GameForm.{u, v, w} N X) [Fintype N] [DecidableEq N]
    [∀ i : N, Fintype (G.strategy i)]
    [∀ (i : N) (a b : G.strategy i), Decidable (a = b)]
    (p d : N) (A : Set X) [∀ x : X, Decidable (x ∈ A)] :
    Decidable (RetainsWith G p d A) :=
  inferInstanceAs (Decidable (Forces G {p, d} A))

public instance decidableRetainsAgainst {N : Type u} {X : Type v}
    (G : GameForm.{u, v, w} N X) [Fintype N] [DecidableEq N]
    [∀ i : N, Fintype (G.strategy i)]
    [∀ (i : N) (a b : G.strategy i), Decidable (a = b)]
    (p : N) (A : Set X) [∀ x : X, Decidable (x ∈ A)] :
    Decidable (RetainsAgainst G p A) :=
  inferInstanceAs (Decidable (Forces G {p} A))

public instance decidableRetainsUnder {N : Type u} {X : Type v}
    (G : GameForm.{u, v, w} N X) [Fintype N] [DecidableEq N]
    [∀ i : N, Fintype (G.strategy i)]
    [∀ (i : N) (a b : G.strategy i), Decidable (a = b)]
    (d : N) (σd : G.strategy d) (A : Set X) [∀ x : X, Decidable (x ∈ A)] :
    Decidable (RetainsUnder G d σd A) :=
  inferInstanceAs (Decidable (∀ s : ∀ i, G.strategy i, s d = σd → G.outcome s ∈ A))

/-- **The one implication.** Surviving the delegate's deviation is stronger than
being able to act with it. -/
public theorem retainsAgainst_imp_retainsWith [∀ i, Nonempty (G.strategy i)] {p d : N}
    {A : Set X} (h : RetainsAgainst G p A) : RetainsWith G p d A :=
  h.mono_coalition (by simp)

/--
The delegate-decides game: `false` is the principal, `true` the delegate, and the
delegate names a `Bool` outcome.
-/
@[expose] public def delegateDecides : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Bool
  outcome s := s true

/-- With the delegate inside the coalition, the principal's target is forced. -/
public theorem retainsWith_delegateDecides :
    RetainsWith delegateDecides false true {true} :=
  ⟨fun _ => true, fun _ hs => hs ⟨true, by simp⟩⟩

/-- **Reading 1 does not imply reading 2.** The delegate can simply deviate. -/
public theorem not_retainsAgainst_delegateDecides :
    ¬ RetainsAgainst delegateDecides false {true} := by
  rintro ⟨sC, hsC⟩
  have h := hsC (fun b => cond b false (sC ⟨false, rfl⟩)) (by
    rintro ⟨b, hb⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    rfl)
  simp only [Set.mem_singleton_iff] at h
  exact Bool.noConfusion h

/-- **Reading 3 does not imply reading 2** — the fixed policy may land the target
while the principal alone forces nothing. -/
public theorem retainsUnder_delegateDecides :
    RetainsUnder delegateDecides true true {true} :=
  fun _ hs => hs

/-- **Reading 1 does not imply reading 3** — it depends on which policy is fixed. -/
public theorem not_retainsUnder_delegateDecides :
    ¬ RetainsUnder delegateDecides true false {true} := by
  intro h
  have := h (fun _ => false) rfl
  simp only [Set.mem_singleton_iff] at this
  exact Bool.noConfusion this

/-! ## Why minimum forceable cardinality is not a retention measure -/

/-- A game form pinned to a single outcome, whatever anyone does. -/
@[expose] public def pinnedForm (x₀ : X) : GameForm.{0, v, v} Bool X where
  strategy _ := PUnit.{v + 1}
  outcome _ := x₀

/-- A game form in which the principal names the outcome. -/
@[expose] public def principalDecides (X : Type v) : GameForm.{0, v, v} Bool X where
  strategy _ := X
  outcome s := s false

/-- In the pinned game the principal forces a singleton — the one it is pinned to. -/
public theorem pinned_forces_singleton (x₀ : X) :
    Forces (pinnedForm x₀) {false} {x₀} :=
  ⟨fun _ => PUnit.unit, fun _ _ => rfl⟩

/-- In the pinned game the principal forces **no other** singleton. -/
public theorem pinned_not_forces_other {x₀ x : X} (hx : x ≠ x₀) :
    ¬ Forces (pinnedForm x₀) {false} {x} := by
  rintro ⟨sC, hsC⟩
  exact hx (hsC (fun _ => PUnit.unit) (fun _ => rfl)).symm

/-- When the principal decides, it forces every singleton. -/
public theorem principalDecides_forces_singleton (x : X) :
    Forces (principalDecides X) {false} {x} :=
  ⟨fun _ => x, fun _ hs => hs ⟨false, rfl⟩⟩

/--
**The retracted measure, retracted for a checkable reason.**

Both principals force a singleton, so the minimum cardinality of a forceable set
is `1` in both games — and any function of that number, `log` included, agrees on
them. Yet one can select every outcome and the other is pinned to one. Minimum
forceable cardinality measures *precision*, not *choice*.
-/
public theorem minCard_cannot_separate (x₀ : X) (x : X) (hx : x ≠ x₀) :
    (∃ y : X, Forces (pinnedForm x₀) {false} {y}) ∧
      (∃ y : X, Forces (principalDecides X) {false} {y}) ∧
      (¬ Forces (pinnedForm x₀) {false} {x}) ∧
      Forces (principalDecides X) {false} {x} :=
  ⟨⟨x₀, pinned_forces_singleton x₀⟩, ⟨x, principalDecides_forces_singleton x⟩,
    pinned_not_forces_other hx, principalDecides_forces_singleton x⟩

/-! ## Actual power: the same action, and nothing to spare -/

/--
**Actual power** (Chen, Ju & Ågotnes, arXiv:2607.10567; *basic powers* in van
Benthem's terminology). Print's condition, in two clauses: the coalition has an
action such that *(1)* the action forces the outcome into the set, and *(2)*
**every** outcome in the set is compatible with that action.

Clause (2) is the whole difference. `Forces` is `α`-power and is upward closed —
`Forces.mono` — so it cannot distinguish a target a coalition hits exactly from a
target it merely lands inside.

**Corrected 2026-09-11: where that objection is written down.** This docstring
used to quote, right after the citation above, the sentence *"can obscure
relevant information about the power structure in the game: we don't know whether
two sets a coalition has the power to enforce correspond to the same or different
joint actions."* **That sentence is not in arXiv:2607.10567.** It is in the
authors' companion paper over *two-agent* frames, arXiv:2603.04160v2, and there
it is prefaced *"as pointed out by [BBE19]"* — so it is a third source's
objection, reported. Both files are pinned in the literature directory under
names whose `v1`/`v2` are **not** version numbers: they are two different arXiv
submissions. What arXiv:2607.10567 itself supplies is Definition 5, and that is
what this declaration renders. Graded in section 23 of
`docs/provenance/source-coverage-audit.md`.
-/
@[expose] public def ActualPower (G : GameForm.{u, v, w} N X) (C : Set N) (A : Set X) : Prop :=
  ∃ sC : ∀ i : C, G.strategy i,
    (∀ s : ∀ i, G.strategy i, (∀ i : C, s i = sC i) → G.outcome s ∈ A) ∧
    (∀ x ∈ A, ∃ s : ∀ i, G.strategy i, (∀ i : C, s i = sC i) ∧ G.outcome s = x)

/-- Actual power is the stronger notion: clause (1) alone is `α`-forcing. -/
public theorem ActualPower.forces {C : Set N} {A : Set X}
    (h : ActualPower G C A) : Forces G C A := by
  obtain ⟨sC, hforce, _⟩ := h
  exact ⟨sC, hforce⟩

/-- Actual power is hitting a set *exactly*: some joint action whose possible
outcomes are `A` and nothing else. The two clauses of `ActualPower` are the two
inclusions. -/
public theorem actualPower_iff {C : Set N} {A : Set X} :
    ActualPower G C A ↔ ∃ sC, outcomesOf G C sC = A := by
  constructor
  · rintro ⟨sC, hforce, hcompat⟩
    refine ⟨sC, Set.Subset.antisymm ?_ ?_⟩
    · intro x ⟨s, hs, heq⟩
      exact heq ▸ hforce s hs
    · intro x hx
      obtain ⟨s, hs, heq⟩ := hcompat x hx
      exact ⟨s, hs, heq⟩
  · rintro ⟨sC, hA⟩
    refine ⟨sC, fun s hs => ?_, fun x hx => ?_⟩
    · have : G.outcome s ∈ outcomesOf G C sC := ⟨s, hs, rfl⟩
      exact hA ▸ this
    · have : x ∈ outcomesOf G C sC := hA ▸ hx
      exact this

/-- The pinned principal has actual power over the outcome it is pinned to. -/
public theorem pinned_actualPower_singleton (x₀ : X) :
    ActualPower (pinnedForm x₀) {false} {x₀} :=
  ⟨fun _ => PUnit.unit, fun _ _ => rfl,
    fun _x hx => ⟨fun _ => PUnit.unit, fun _ => rfl, hx.symm⟩⟩

/--
**Actual power is not upward closed**, and this is the separation that matters.

The pinned principal `α`-forces `{x₀, x}` — by `Forces.mono`, since it forces
`{x₀}` — but has no *actual* power over it, because `x` is not compatible with any
action it has. So `Forces` and `ActualPower` come apart on exactly the sets where
monotonicity is doing the work.
-/
public theorem pinned_not_actualPower_pair {x₀ x : X} (hx : x ≠ x₀) :
    ¬ ActualPower (pinnedForm x₀) {false} {x₀, x} := by
  rintro ⟨sC, -, hcompat⟩
  obtain ⟨s, -, hs⟩ := hcompat x (Or.inr rfl)
  exact hx hs.symm

/-- …while `α`-forcing the same pair is free. -/
public theorem pinned_forces_pair (x₀ : X) (_x : X) :
    Forces (pinnedForm x₀) {false} {x₀, _x} :=
  (pinned_forces_singleton x₀).mono (Set.singleton_subset_iff.2 (Or.inl rfl))

/-! ## Power depends on how everyone else is arranged -/

/--
**Forcing against a constrained environment.** `D`'s reach once `C` has committed,
when the profiles that may actually arise are limited to those `Env` admits.

`ForcesGiven` quantifies over *every* completion, which silently treats the
parties outside `C ∪ D` as maximally hostile to `D`. That is one environment among
many and rarely the interesting one: a bystander is not an adversary, and an ally
of `C` is not a neutral. `Env` is where alignment, indifference and support live.

**Prior art, not verified against sources.** Making a coalition's prospects depend
on the arrangement of the remaining parties is the move behind **partition
function form games** (Thrall & Lucas, *N-person games in partition function
form*, Naval Research Logistics Quarterly 10, 1963), where a coalition's worth is
`v(S; P)` for a partition `P` of the others rather than `v(S)` alone — the
standard formalism for coalitional externalities. This is the effectivity-function
analogue of that move, and whether the specific combination has been published is
**unchecked**; nothing here claims novelty. Grossi & Turrini, *Dependence in Games
and Dependence Games* (JAAMAS 25, 2012) is a second neighbour. Note that `α`
versus `β` effectivity is a *different* axis — a change of quantifier order, not a
restriction on which profiles arise.
-/
@[expose] public def ForcesGivenEnv (G : GameForm.{u, v, w} N X) (C : Set N)
    (sC : ∀ i : C, G.strategy i) (D : Set N)
    (Env : (∀ i, G.strategy i) → Prop) (A : Set X) : Prop :=
  ∃ sD : ∀ i : D, G.strategy i,
    ∀ s : ∀ i, G.strategy i,
      (∀ i : C, s i = sC i) → (∀ i : D, s i = sD i) → Env s → G.outcome s ∈ A

/-- The unconstrained environment recovers the worst-case reading exactly. -/
public theorem forcesGivenEnv_true_iff {C D : Set N}
    {sC : ∀ i : C, G.strategy i} {A : Set X} :
    ForcesGivenEnv G C sC D (fun _ => True) A ↔ ForcesGiven G C sC D A := by
  constructor
  · rintro ⟨sD, hsD⟩
    exact ⟨sD, fun s hC hD => hsD s hC hD trivial⟩
  · rintro ⟨sD, hsD⟩
    exact ⟨sD, fun s hC hD _ => hsD s hC hD⟩

/-- A narrower environment is easier to force against: fewer completions have to
be answered. -/
public theorem ForcesGivenEnv.mono_env {C D : Set N} {sC : ∀ i : C, G.strategy i}
    {Env Env' : (∀ i, G.strategy i) → Prop} {A : Set X}
    (h : ForcesGivenEnv G C sC D Env' A) (hsub : ∀ s, Env s → Env' s) :
    ForcesGivenEnv G C sC D Env A := by
  obtain ⟨sD, hsD⟩ := h
  exact ⟨sD, fun s hC hD hEnv => hsD s hC hD (hsub s hEnv)⟩

/-- Power over `D`, relative to an environment. -/
@[expose] public def HasPowerOverEnv (G : GameForm.{u, v, w} N X) (C D : Set N)
    (Env : (∀ i, G.strategy i) → Prop) (A : Set X) : Prop :=
  Disjoint C D ∧
    (∃ sC : ∀ i : C, G.strategy i, ForcesGivenEnv G C sC D Env A) ∧
    (∃ sC : ∀ i : C, G.strategy i, ¬ ForcesGivenEnv G C sC D Env A)

/-! ### Whether `C` has power over `D` can turn entirely on a third party -/

/-- Party `1` gets its aim unless `0` and `2` both move against it. -/
@[expose] public def triadOutcome (a b c : Bool) : Bool := b && !(a && c)

@[simp] public theorem triadOutcome_false_left (b c : Bool) :
    triadOutcome false b c = b := by simp [triadOutcome]

@[simp] public theorem triadOutcome_false_right (a b : Bool) :
    triadOutcome a b false = b := by simp [triadOutcome]

@[simp] public theorem triadOutcome_true_true (b : Bool) :
    triadOutcome true b true = false := by cases b <;> rfl

/--
Three parties. `1` reaches its aim unless `0` and `2` move against it **together**
— neither can block it alone.
-/
@[expose] public def triadGame : GameForm.{0, 0, 0} (Fin 3) Bool where
  strategy _ := Bool
  outcome s := triadOutcome (s 0) (s 1) (s 2)

/-- The third party stands with `0`. -/
@[expose] public def aligned : (∀ i, triadGame.strategy i) → Prop := fun s => s 2 = true

/-- The third party stays out. -/
@[expose] public def neutral : (∀ i, triadGame.strategy i) → Prop := fun s => s 2 = false

/-- With the third party aligned against it, `1`'s reach is settled by `0`. -/
public theorem triad_power_when_aligned :
    HasPowerOverEnv triadGame {0} {1} aligned {true} := by
  refine ⟨by simp, ⟨fun _ => false, fun _ => true, fun s hC hD _ => ?_⟩, ?_⟩
  · have h0 : s 0 = false := hC ⟨0, rfl⟩
    have h1 : s 1 = true := hD ⟨1, rfl⟩
    show triadOutcome (s 0) (s 1) (s 2) ∈ ({true} : Set Bool)
    rw [h0, h1]
    exact triadOutcome_false_left _ _
  · refine ⟨fun _ => true, ?_⟩
    rintro ⟨sD, hsD⟩
    have h := hsD (fun i : Fin 3 => if i = 1 then sD ⟨1, rfl⟩ else true)
      (fun i => by
        have hi : (i : Fin 3) = 0 := i.2
        rw [hi]; rfl)
      (fun i => by
        rcases i with ⟨v, hv⟩
        simp only [Set.mem_singleton_iff] at hv
        subst hv
        rfl)
      rfl
    have hval : triadGame.outcome (fun i : Fin 3 => if i = 1 then sD ⟨1, rfl⟩ else true)
        = false := by
      show triadOutcome true (sD ⟨1, rfl⟩) true = false
      exact triadOutcome_true_true _
    rw [hval] at h
    exact Bool.noConfusion h

/-- With the third party out, `0` cannot touch `1`'s reach at all. -/
public theorem triad_no_power_when_neutral :
    ¬ HasPowerOverEnv triadGame {0} {1} neutral {true} := by
  rintro ⟨-, -, sC, hno⟩
  refine hno ⟨fun _ => true, fun s _ hD hE => ?_⟩
  have h1 : s 1 = true := hD ⟨1, rfl⟩
  have h2 : s 2 = false := hE
  show triadOutcome (s 0) (s 1) (s 2) ∈ ({true} : Set Bool)
  rw [h1, h2]
  exact triadOutcome_false_right _ _

/--
**Power is not a two-place fact.** The same game, the same two parties, the same
target — and `0` has power over `1` exactly when the third party takes a side.

This is why `HasPowerOver`'s worst-case reading is the wrong default for most
situations one would want to describe: it silently fixes the environment to the
one configuration in which every bystander is hostile.
-/
public theorem power_depends_on_environment :
    HasPowerOverEnv triadGame {0} {1} aligned {true} ∧
      ¬ HasPowerOverEnv triadGame {0} {1} neutral {true} :=
  ⟨triad_power_when_aligned, triad_no_power_when_neutral⟩

/-! ## Structural power: choosing which game is played -/

/--
**Structural power.** A party that selects the configuration `k` — the rules, the
law, the custom, the interface — rather than moving inside a fixed game.

`HasPowerOver` is power *within* a `GameForm`: `C` picks a strategy, everyone else
still has theirs. Much of what is ordinarily called power is not that. A state
does not out-manoeuvre a citizen inside a fixed game; it sets which game there is.
A legal system, a labour market, a custom that removes options from one party —
all of them act on `strategy` and `outcome`, not within them.
-/
@[expose] public def HasStructuralPower {K : Type*} (Γ : K → GameForm.{u, v, w} N X)
    (D : Set N) (A : Set X) : Prop :=
  (∃ k, Forces (Γ k) D A) ∧ (∃ k, ¬ Forces (Γ k) D A)

/-- In a fixed-outcome game, what the second party can force does not depend on
what the first party chose. -/
public theorem forcesGiven_pinned_iff {x₀ : X} {C D : Set Bool}
    {sC : ∀ i : C, (pinnedForm x₀).strategy i} {A : Set X} :
    ForcesGiven (pinnedForm x₀) C sC D A ↔ x₀ ∈ A := by
  constructor
  · rintro ⟨sD, hsD⟩
    exact hsD (fun _ => PUnit.unit) (fun _ => rfl) (fun _ => rfl)
  · intro h
    exact ⟨fun _ => PUnit.unit, fun _ _ _ => h⟩

/-- **Nobody has power over anybody inside a fixed-outcome game.** -/
public theorem not_hasPowerOver_pinned (x₀ : X) (C D : Set Bool) (A : Set X) :
    ¬ HasPowerOver (pinnedForm x₀) C D A := by
  rintro ⟨-, ⟨sC, hyes⟩, sC', hno⟩
  exact hno (forcesGiven_pinned_iff.2 (forcesGiven_pinned_iff.1 hyes))

/-- Two configurations of the same party's situation, differing only in what the
world is set up to deliver. -/
@[expose] public def configFamily (x₀ x₁ : X) : Bool → GameForm.{0, v, v} Bool X :=
  fun b => pinnedForm (cond b x₁ x₀)

/--
**Structural power is not reducible to power within a game.**

Whoever selects the configuration settles whether the party `{false}` reaches
`x₁`. Yet in *each* configuration separately, **nobody has `HasPowerOver` anybody
at all**: both are fixed-outcome games, so no one's choice moves anyone's reach.

A model that quantifies power only inside a fixed game form therefore scores this
party as entirely free from interference while its options are being set
elsewhere. That is the shape of legal, cultural and market power — the state, the
custom, the labour market do not out-manoeuvre anyone inside a fixed game, they
settle which game there is — and it is invisible to `HasPowerOver` by
construction.
-/
public theorem structuralPower_not_within_game {x₀ x₁ : X} (hx : x₁ ≠ x₀) :
    HasStructuralPower (configFamily x₀ x₁) {false} {x₁} ∧
      ∀ (k : Bool) (C D : Set Bool) (A : Set X),
        ¬ HasPowerOver (configFamily x₀ x₁ k) C D A :=
  ⟨⟨⟨true, pinned_forces_singleton x₁⟩, ⟨false, pinned_not_forces_other hx⟩⟩,
   fun k => by cases k <;> exact not_hasPowerOver_pinned _⟩


/-! ## Power that stays, and the structural notion as its failure

`HasStructuralPower` above says a coalition's forcing depends on which
configuration the substrate is in. Read the other way round, that is precisely
the failure of *staying*: the coalition forces somewhere and not everywhere. This
section names the staying property so the structural notion can be stated as its
negation rather than as an unrelated definition.

`AISafetyAtlas.Oversight.RobustlyForces` is the same move on an effect table
rather than on a game form; the two are deliberately parallel.
-/

/-- **Power that stays.** The coalition forces the target in every configuration
the substrate can be in, not merely in the one it was handed. -/
@[expose] public def RobustlyForces {K : Type*} (Γ : K → GameForm.{u, v, w} N X)
    (D : Set N) (A : Set X) : Prop :=
  ∀ k, Forces (Γ k) D A

/-- Staying implies holding in each configuration. -/
public theorem RobustlyForces.forces {K : Type*} {Γ : K → GameForm.{u, v, w} N X}
    {D : Set N} {A : Set X} (h : RobustlyForces Γ D A) (k : K) :
    Forces (Γ k) D A := h k

/--
**Structural power is power that becomes without staying.** A coalition has
structural power exactly when it forces in some configuration and does not force
robustly.

This is a restatement rather than a new fact, and that is the point: the two
clauses of `HasStructuralPower` were doing the work of "becomes" and "does not
stay" without saying so.
-/
public theorem hasStructuralPower_iff_not_robustly {K : Type*}
    {Γ : K → GameForm.{u, v, w} N X} {D : Set N} {A : Set X} :
    HasStructuralPower Γ D A ↔
      (∃ k, Forces (Γ k) D A) ∧ ¬ RobustlyForces Γ D A := by
  constructor
  · rintro ⟨hyes, k, hno⟩; exact ⟨hyes, fun hall => hno (hall k)⟩
  · rintro ⟨hyes, hnot⟩
    refine ⟨hyes, ?_⟩
    by_contra hcon
    exact hnot fun k => not_not.mp fun hk => hcon ⟨k, hk⟩

/-! ## Mediation: forcing when the choice may depend on the world only through a channel -/

/--
**A mediated decision problem.** The world is in some state `w : W`; the principal
does not see `w`, only `obs w : O`; it then acts, and `result` determines the
outcome from the state and the act.

This is the shape a game form cannot express, because a game form's strategies are
bare choices with nothing to condition on. Mediation is exactly the presence of
something to condition on, and a restriction on what that something reveals.
`AISafetyAtlas.Control.FactorsThrough` is the same idea inside Ashby's regulator
diagram: a response that depends on the world only through a channel.
-/
public structure MediatedForm (W O Act X : Type*) where
  /-- What the principal gets to see about the state. -/
  obs : W → O
  /-- The outcome, as a function of the true state and the act taken. -/
  result : W → Act → X

variable {W O O' Act : Type*}

/--
**Forcing under mediation.** The principal has a *plan* — a map from what it sees
to what it does — landing the outcome in `A` whatever the state is.

The plan quantifies existentially and the state universally, so this is `α`-forcing
with the strategy set cut down to the channel-measurable plans.
-/
@[expose] public def MForces (M : MediatedForm W O Act X) (A : Set X) : Prop :=
  ∃ p : O → Act, ∀ w : W, M.result w (p (M.obs w)) ∈ A

/-- Forcing under mediation is upward closed in the target, as `α`-forcing is. -/
public theorem MForces.mono {M : MediatedForm W O Act X} {A B : Set X}
    (h : MForces M A) (hAB : A ⊆ B) : MForces M B := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun w => hAB (hp w)⟩

/--
**Coarsening the channel never gains, and refining never loses.**

If the coarse channel `obs'` factors through the fine one — `obs' = k ∘ obs`, so
`obs'` tells the principal no more than `obs` does — then anything forceable under
`obs'` is forceable under `obs`. Contrapositively, a mediator that coarsens what a
principal can see can only shrink what that principal can guarantee.

This is the monotonicity the sovereignty claim needs, and it holds for every
`result`: no assumption about the world's intentions is required, because the
universal quantifier over `w` already covers an adversarial state.
-/
public theorem mforces_of_factors {obs : W → O} {obs' : W → O'} {k : O → O'}
    (hk : obs' = k ∘ obs) {result : W → Act → X} {A : Set X}
    (h : MForces ⟨obs', result⟩ A) : MForces ⟨obs, result⟩ A := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p ∘ k, fun w => ?_⟩
  have := hp w
  simp only [hk, Function.comp_apply] at this ⊢
  exact this

/-! ### The loss is real, not merely possible -/

/-- Match the state: the outcome is `true` exactly when the act equals the state. -/
@[expose] public def matchGame : MediatedForm Bool Bool Bool Bool where
  obs := id
  result w a := decide (a = w)

/-- The same problem with the channel destroyed: the principal sees nothing. -/
@[expose] public def matchGameBlind : MediatedForm Bool Unit Bool Bool where
  obs := fun _ => ()
  result w a := decide (a = w)

/-- **Seeing the state, the principal forces the good outcome.** -/
public theorem matchGame_forces : MForces matchGame {true} :=
  ⟨id, fun w => by simp [matchGame]⟩

/--
**Blind, it cannot.** Whatever constant act the plan commits to, the state that
differs from it defeats the plan.

Together with `matchGame_forces` this shows the coarsening in `mforces_of_factors`
is strict at some channel — the theorem is not vacuous, and "sovereignty lost to
mediation" names a real difference rather than a bookkeeping one.
-/
public theorem matchGameBlind_not_forces : ¬ MForces matchGameBlind {true} := by
  rintro ⟨p, hp⟩
  have := hp (!(p ()))
  simp [matchGameBlind] at this

/-- The blind channel is a coarsening of the seeing one, via the map to `Unit`. -/
public theorem matchGameBlind_factors :
    (matchGameBlind.obs) = (fun _ => ()) ∘ matchGame.obs := rfl

/-! ## Both notions are arenas

`AISafetyAtlas.Sovereignty.Arena` states forcing for one party against an opaque
residue. The two forcing notions in this file are that notion at two different
splits: for a game form the residue is the complementary coalition, for a
mediated form it is the state of the world. Neither bridge does any work -- that
is the claim being made.
-/

open scoped Classical in
/-- **A coalition's arena.** `C` settles its own strategies, the complement
settles the rest, and the game form resolves them. -/
@[expose] public noncomputable def gameArena (G : GameForm.{u, v, w} N X) (C : Set N) :
    Arena (∀ i : C, G.strategy i) (∀ i : ↥(Cᶜ), G.strategy i) X where
  outcome := fun c r => G.outcome fun i => if hi : i ∈ C then c ⟨i, hi⟩ else r ⟨i, hi⟩

/-- **α-forcing is arena forcing at the coalition split.** -/
public theorem forces_iff_gameArena_forces {C : Set N} {A : Set X} :
    Forces G C A ↔ (gameArena G C).Forces A := by
  classical
  constructor
  · rintro ⟨sC, hsC⟩
    exact ⟨sC, fun r => hsC _ fun i => dif_pos i.2⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, fun s hs => ?_⟩
    have : (fun i => if hi : i ∈ C then c ⟨i, hi⟩ else (fun j : ↥(Cᶜ) => s j) ⟨i, hi⟩) = s := by
      funext i
      by_cases hi : i ∈ C
      · simp [hi, (hs ⟨i, hi⟩).symm]
      · simp [hi]
    have h := hc fun j : ↥(Cᶜ) => s j
    simpa [gameArena, this] using h

/-- **A mediated form is already an arena.** The principal settles a policy, the
world settles a state. -/
@[expose] public def MediatedForm.toArena (M : MediatedForm W O Act X) :
    Arena (O → Act) W X where
  outcome := fun p w => M.result w (p (M.obs w))

/-- **Mediated forcing is arena forcing, definitionally.** -/
public theorem mforces_iff_toArena_forces {M : MediatedForm W O Act X} {A : Set X} :
    MForces M A ↔ M.toArena.Forces A := Iff.rfl

end AISafetyAtlas.Sovereignty
