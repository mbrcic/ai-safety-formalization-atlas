module

public import AISafetyAtlas.Knowledge
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Fintype.Card

/-!
# Acting well without knowing which state you are in

`Knowable` asks whether an observation determines a *value*. This module asks
the weaker and more operational question: whether it determines a *good enough
action*. A controller that cannot tell two states apart does not have to
identify them — it only has to find one action acceptable in both.

The answer is a boundary rather than a bound. A uniform rule `I → A` exists
exactly when every realized observation value admits one action acceptable
throughout its fibre:

`UniformlyActionable` ↔ `FibrewiseAgreeable`
  ↔ `∀ i ∈ range observation, (⋂ ω ∈ fibre i, {a | Good ω a}).Nonempty`

| Layer | Name | What it fixes |
|---|---|---|
| **Model** | `UniformlyActionable` | One rule from observations to actions, acceptable at every state |
| **Model** | `FibrewiseAgreeable` | Per state, an action acceptable at everything sharing its observation |
| **Law** | `uniformlyActionable_iff_fibrewiseAgreeable` | The two are the same, given a nonempty action type |
| **Law** | `uniformlyActionable_iff_iInter_nonempty` | The same boundary in set form, at `Type` |
| **Bridge** | `knowable_iff_uniformlyActionable` | `Knowable` is the case where exactly one action is acceptable |
| **Certificate** | `not_uniformlyActionable_iff_exists_unservable` | The negation, with the quantifiers pushed in |
| **Certificate** | `ActionConflict`, `not_uniformlyActionable_of_conflict` | A **sufficient** obstruction: one indistinguishable pair with no shared action |
| **Repair** | `UniformlyActionable.mono` | A more informative observation keeps the rule |
| **Repair** | `UniformlyActionable.mono_good` | A more permissive acceptability keeps the rule |

The last two are the only two repairs there are, and the statement says why:
the criterion is an intersection over a fibre, so it is improved by shrinking
fibres or by enlarging the sets intersected. Nothing else moves it.

## What the pairwise certificate does and does not give

`ActionConflict` — two states with the same observation and no action
acceptable at both — refutes a uniform rule. Its converse is **false**. Three
states on one fibre whose acceptable sets are `{1,2}`, `{0,2}`, `{0,1}` are
pairwise compatible and jointly empty, so no `ActionConflict` exists and no
uniform rule does either. `AISafetyAtlas.Examples.Knowledge.UniformAction`
carries that witness, which is why the necessary certificate here is the empty
fibre of `not_uniformlyActionable_iff_exists_unservable` rather than a pair.

This is the one structural difference from the kernel. `Knowable` fails only
through a *pair* — `exists_witness_of_not_knowable` produces one — because
equality is transitive. Compatibility of acceptable-action sets is not.

## Neighbours

`AISafetyAtlas.Sovereignty.demandwise_iff_exists_selector` has the same
logical shape, a uniform witness against a family, but it is indexed by the
**demand** a coalition must serve, not by what an observer can see. It has no
notion of a fibre and no obstruction on one; the two do not instantiate each
other.

`Knowledge.Ambiguity` counts what a fibre leaves open. This module asks whether
what is left open matters, and an ambiguous fibre is harmless here whenever the
states in it agree on some action.

The existence half uses choice, once, and it is not an efficiency claim: the
rule is selected, not computed. A finite consumer that wants a computed rule
searches the actions.
-/

namespace AISafetyAtlas.Knowledge

universe u v w x

/-! ## The two forms -/

/--
A **uniform decision rule**: one map from observations to actions whose output
is acceptable at every state, without ever learning the state.
-/
@[expose] public def UniformlyActionable {Ω : Sort u} {I : Sort v} {A : Sort w}
    (observation : Ω → I) (Good : Ω → A → Prop) : Prop :=
  ∃ rule : I → A, ∀ ω, Good ω (rule (observation ω))

/--
The **fibrewise criterion**: at each state there is an action acceptable
throughout the set of states sharing its observation.

Stated per state rather than per observation value, so that it needs no
`Set` and no realizability side condition — the fibre through `ω` is realized
by construction.
-/
@[expose] public def FibrewiseAgreeable {Ω : Sort u} {I : Sort v} {A : Sort w}
    (observation : Ω → I) (Good : Ω → A → Prop) : Prop :=
  ∀ ω, ∃ a, ∀ τ, observation τ = observation ω → Good τ a

/-! ## The boundary -/

/--
**The uniform decision boundary.** A rule exists exactly when every fibre
admits a common acceptable action.

`Nonempty A` is what supplies the rule's value at observations nothing
realizes; it is not needed in the forward direction. Compare
`knowable_iff_no_collision`, which carries `Nonempty Y` for the same reason.
-/
public theorem uniformlyActionable_iff_fibrewiseAgreeable {Ω : Sort u} {I : Sort v} {A : Sort w}
    [Nonempty A] (observation : Ω → I) (Good : Ω → A → Prop) :
    UniformlyActionable observation Good ↔ FibrewiseAgreeable observation Good := by
  classical
  unfold UniformlyActionable FibrewiseAgreeable
  constructor
  · rintro ⟨rule, hrule⟩ ω
    refine ⟨rule (observation ω), fun τ hτ => ?_⟩
    have h := hrule τ
    rwa [hτ] at h
  · intro h
    have key : ∀ i : I, ∃ a : A, ∀ τ, observation τ = i → Good τ a := by
      intro i
      by_cases hi : ∃ ω, observation ω = i
      · obtain ⟨ω, rfl⟩ := hi
        exact h ω
      · exact ⟨Classical.arbitrary A, fun τ hτ => absurd ⟨τ, hτ⟩ hi⟩
    exact ⟨fun i => Classical.choose (key i), fun ω => Classical.choose_spec (key (observation ω)) ω rfl⟩

/--
**The same boundary in the form it is usually stated**: over the realized
observation values, the acceptable-action sets of a fibre have a common point.

At `Type`, because `Set` lives there. The quantifier is over `Set.range`, so
unrealized observation values impose nothing — which is exactly what lets the
rule be arbitrary on them.
-/
public theorem uniformlyActionable_iff_iInter_nonempty {Ω : Type u} {I : Type v} {A : Type w}
    [Nonempty A] (observation : Ω → I) (Good : Ω → A → Prop) :
    UniformlyActionable observation Good ↔
      ∀ i ∈ Set.range observation,
        (⋂ ω ∈ {ω | observation ω = i}, {a | Good ω a}).Nonempty := by
  rw [uniformlyActionable_iff_fibrewiseAgreeable observation Good]
  constructor
  · rintro h i ⟨ω, rfl⟩
    obtain ⟨a, ha⟩ := h ω
    exact ⟨a, Set.mem_iInter₂.mpr fun τ hτ => ha τ hτ⟩
  · intro h ω
    obtain ⟨a, ha⟩ := h (observation ω) ⟨ω, rfl⟩
    exact ⟨a, fun τ hτ => Set.mem_iInter₂.mp ha τ hτ⟩

/-! ## The kernel is the single-action case -/

/--
**`Knowable` is this question with exactly one acceptable action per state.**

Definitional: a decoder is the rule for the acceptability relation
`Good ω y ↔ property ω = y`. So the boundary above generalizes
`knowable_iff_no_collision`, and the generalization is where the slack lives —
an observation can fail to determine the property and still determine an
acceptable action.
-/
public theorem knowable_iff_uniformlyActionable {Ω : Sort u} {I : Sort v} {Y : Sort w}
    (observation : Ω → I) (property : Ω → Y) :
    Knowable observation property ↔
      UniformlyActionable observation (fun ω y => property ω = y) :=
  Iff.rfl

/-! ## Certificates -/

/--
**The negation, with the quantifiers pushed in.** No uniform rule exists
exactly when some state's fibre defeats every action: for each candidate,
something indistinguishable from that state rejects it.

This is the certificate that is both necessary and sufficient. The pairwise
`ActionConflict` below is only sufficient.
-/
public theorem not_uniformlyActionable_iff_exists_unservable {Ω : Sort u} {I : Sort v} {A : Sort w}
    [Nonempty A] (observation : Ω → I) (Good : Ω → A → Prop) :
    ¬ UniformlyActionable observation Good ↔
      ∃ ω, ∀ a, ∃ τ, observation τ = observation ω ∧ ¬ Good τ a := by
  classical
  rw [uniformlyActionable_iff_fibrewiseAgreeable observation Good]
  unfold FibrewiseAgreeable
  push Not
  rfl

/--
An **action conflict**: two states the observation cannot separate, with no
action acceptable at both.

The analogue of `IndistinguishabilityWitness`, and deliberately not claimed to
be complete. See the module docstring: acceptable-action sets can be pairwise
compatible and jointly empty, so a fibre can defeat every rule without
containing such a pair.
-/
public structure ActionConflict {Ω : Sort u} {I : Sort v} {A : Sort w}
    (observation : Ω → I) (Good : Ω → A → Prop) where
  /-- One side of the indistinguishable pair. -/
  left : Ω
  /-- The other side. -/
  right : Ω
  /-- The observation cannot tell them apart. -/
  sameObservation : observation left = observation right
  /-- And no action serves both. -/
  noSharedAction : ∀ a, ¬ (Good left a ∧ Good right a)

/-- **A conflict refutes every uniform rule.** Constructive. -/
public theorem not_uniformlyActionable_of_conflict {Ω : Sort u} {I : Sort v} {A : Sort w}
    {observation : Ω → I} {Good : Ω → A → Prop}
    (c : ActionConflict observation Good) :
    ¬ UniformlyActionable observation Good := by
  rintro ⟨rule, hrule⟩
  refine c.noSharedAction (rule (observation c.left)) ⟨hrule c.left, ?_⟩
  have h := hrule c.right
  rwa [← c.sameObservation] at h

/-! ## The two repairs -/

/--
**Repair one: look harder.** A more informative observation keeps every rule
the coarser one had, because the fibres only shrink.

Constructive, and the exact analogue of `Knowable.mono`: the rule is composed
with the recovery map, not reassembled.
-/
public theorem UniformlyActionable.mono {Ω : Sort u} {I : Sort v} {J : Sort x} {A : Sort w}
    {finer : Ω → J} {coarser : Ω → I} {Good : Ω → A → Prop}
    (hd : Determines finer coarser)
    (h : UniformlyActionable coarser Good) :
    UniformlyActionable finer Good := by
  obtain ⟨k, hk⟩ := hd
  obtain ⟨rule, hrule⟩ := h
  refine ⟨fun j => rule (k j), fun ω => ?_⟩
  have h := hrule ω
  rwa [hk ω] at h

/--
**Repair two: accept more.** Widening acceptability keeps every rule, because
the sets intersected only grow.
-/
public theorem UniformlyActionable.mono_good {Ω : Sort u} {I : Sort v} {A : Sort w}
    {observation : Ω → I} {Good Good' : Ω → A → Prop}
    (h : UniformlyActionable observation Good)
    (hle : ∀ ω a, Good ω a → Good' ω a) :
    UniformlyActionable observation Good' := by
  obtain ⟨rule, hrule⟩ := h
  exact ⟨rule, fun ω => hle ω _ (hrule ω)⟩

/--
**An action acceptable everywhere ends the question.** The degenerate repair,
recorded because it is the one a designer reaches for: supply a fallback that
is safe in every state and no observation is needed at all.
-/
public theorem uniformlyActionable_of_universal {Ω : Sort u} {I : Sort v} {A : Sort w}
    {observation : Ω → I} {Good : Ω → A → Prop} {a : A}
    (ha : ∀ ω, Good ω a) :
    UniformlyActionable observation Good :=
  ⟨fun _ => a, fun ω => ha ω⟩

/--
**Full observability is not what is needed.** If the observation is injective
then a rule exists as soon as every state has *some* acceptable action — but
`uniformlyActionable_of_universal` shows a rule can exist with no observation
at all, so injectivity is sufficient and nowhere near necessary.
-/
public theorem uniformlyActionable_of_injective {Ω : Sort u} {I : Sort v} {A : Sort w}
    [Nonempty A] {observation : Ω → I} {Good : Ω → A → Prop}
    (hinj : Function.Injective observation)
    (h : ∀ ω, ∃ a, Good ω a) :
    UniformlyActionable observation Good := by
  rw [uniformlyActionable_iff_fibrewiseAgreeable observation Good]
  intro ω
  obtain ⟨a, ha⟩ := h ω
  exact ⟨a, fun τ hτ => by rw [hinj hτ]; exact ha⟩

/-! ## When the pairwise certificate *is* complete -/

/--
**Pairwise agreement on every fibre**: any two states the observation confuses
share some acceptable action.

This is the negation of `ActionConflict` quantified over the whole fibre, and it
is the hypothesis the control literature works with. `UniformlyActionable` is
strictly stronger in general -- see `Examples.Knowledge.UniformAction` -- and the
theorem below says exactly when the gap closes.
-/
@[expose] public def PairwiseAgreeable {Ω : Sort u} {I : Sort v} {A : Sort w}
    (observation : Ω → I) (Good : Ω → A → Prop) : Prop :=
  ∀ ω τ, observation τ = observation ω → ∃ a, Good ω a ∧ Good τ a

/-- A uniform rule agrees pairwise: the rule's own output serves both states. -/
public theorem PairwiseAgreeable.of_uniformlyActionable {Ω : Sort u} {I : Sort v} {A : Sort w}
    {observation : Ω → I} {Good : Ω → A → Prop}
    (h : UniformlyActionable observation Good) :
    PairwiseAgreeable observation Good := by
  obtain ⟨rule, hrule⟩ := h
  refine fun ω τ hτ => ⟨rule (observation ω), hrule ω, ?_⟩
  have := hrule τ
  rwa [hτ] at this

/--
**Two actions are enough for the pairwise certificate to be complete.**

With at most two actions available, pairwise agreement on a fibre forces a
common acceptable action, so `ActionConflict` becomes a *characterization* of
failure rather than merely a sufficient obstruction.

This is the Helly property at Helly number two: nonempty subsets of a
two-element set that pairwise intersect all share a point.

**Why it is the right hypothesis, and where it comes from.** Lin and Wonham
(*On Observability of Discrete-Event Systems*, Information Sciences 44:173-198,
1988) state observability as a *pairwise* relation, *ker P ≤ act_K* (p. 177),
and their Theorem 2.1 (p. 181) is nonetheless an iff. Their p. 178 notes
*act_K* is only a **tolerance relation** -- reflexive and symmetric, not
transitive -- which is precisely the shape that makes a pairwise condition look
too weak. It is not too weak there, and p. 179 says why: the supervisor is built
as `ψ : Σ × X → {0,1}`, one **binary** decision per event, with observability
used only to prove `Σ⁰ₓ ∩ Σ¹ₓ = ∅`. Two actions per decision. That is this
theorem.

The bound is sharp at three:
`Examples.Knowledge.UniformAction.triple_pairwiseAgreeable` exhibits a
pairwise-agreeable fibre with no uniform rule, over three actions.
-/
public theorem uniformlyActionable_of_pairwiseAgreeable_of_card_le_two
    {Ω : Type u} {I : Type v} {A : Type w} [Fintype A] [DecidableEq A] [Nonempty A]
    (hcard : Fintype.card A ≤ 2)
    {observation : Ω → I} {Good : Ω → A → Prop}
    (h : PairwiseAgreeable observation Good) :
    UniformlyActionable observation Good := by
  classical
  rw [uniformlyActionable_iff_fibrewiseAgreeable observation Good]
  intro ω
  obtain ⟨a, ha, -⟩ := h ω ω rfl
  by_cases hall : ∀ τ, observation τ = observation ω → Good τ a
  · exact ⟨a, hall⟩
  · push Not at hall
    obtain ⟨τ₀, hτ₀, hng⟩ := hall
    obtain ⟨b, -, hbτ₀⟩ := h ω τ₀ hτ₀
    have hab : a ≠ b := by rintro rfl; exact hng hbτ₀
    -- With at most two elements, every action is `a` or `b`.
    have key : ∀ c : A, c = a ∨ c = b := by
      intro c
      by_contra hc
      push Not at hc
      have hins : ({c, a, b} : Finset A).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hc.1, hc.2]),
            Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
      have := Finset.card_le_univ ({c, a, b} : Finset A)
      rw [hins] at this
      omega
    refine ⟨b, fun τ hτ => ?_⟩
    obtain ⟨c, hcτ₀, hcτ⟩ := h τ₀ τ (hτ.trans hτ₀.symm)
    rcases key c with rfl | rfl
    · exact absurd hcτ₀ hng
    · exact hcτ

end AISafetyAtlas.Knowledge
