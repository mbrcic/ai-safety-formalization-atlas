module

public import AISafetyAtlas.Knowledge.Ambiguity
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod

/-!
# Self-reference: when the model is part of what it models

Every earlier layer treats the observation as an arbitrary map. Each says so in
its non-claims: *nothing here makes `observe` a projection of a state containing
the observer*. This module is where that stops being true.

## The one structural commitment

The observer's model is a **component of the global state**. Write the state as
`Model × Rest`: the observer's current model, together with everything else. The
observer reads `Prod.fst` — its own model, and nothing more. That is what
"embedded" means here, and it is the whole difference from
`Knowledge.Embedded`, where the restriction map is arbitrary data supplied by the
modeller.

Self-reference is then not an extra axiom. It is forced: the target `id` includes
the `Model` component, so a complete self-model must model *itself*.

## The result

`selfComplete_iff_subsingleton_rest`: an embedded observer completely knows the
state it is in **iff there is nothing else in the state**. Finitely,
`card_rest_le_one_of_selfComplete` turns that into a counting statement — a
complete self-model forces `|Rest| ≤ 1`.

Read as a design law: a system whose self-model is part of its own state buys
completeness only by having nothing to be complete about. That is not a
resource-bound argument and does not need one; it is forced by the
map-is-part-of-territory structure alone.

## What this is not

Not Breuer's theorem — that is `Knowledge.Embedded`, which models the apparatus
with an inference map and meshing, grades against the paper, and does not assume
a product decomposition.

Not a regress or hierarchy argument. Nothing here iterates "a model of the model
of the model". The obstruction is one level deep and finite.

Not resource-bounded. `Rest` may be any type; there is no budget, no cost, and no
count of processes.

Not dynamic. There is no transition system, so nothing here says the state
*changes* while being modelled. Composing this with `Knowledge.Temporal` is the
obvious next step and is deliberately not taken here.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `SelfState` | Global state as the observer's model together with the rest |
| **Model** | `selfRead` | What an embedded observer can read: its own model |
| **Model** | `SelfComplete` | The observer knows the whole state it is in |
| **Law** | `selfComplete_iff_subsingleton_rest` | Complete self-knowledge ⟺ nothing else exists |
| **Bound** | `card_rest_le_one_of_selfComplete` | Finitely: a complete self-model forces `|Rest| ≤ 1` |
| **Boundary** | `not_selfComplete_of_two_rest` | Two distinct remainders refute completeness |

## Explicit non-claims

`Model` and `Rest` are arbitrary types; nothing interprets them as memory,
computation, or belief. No AI-system reading — self-monitoring, introspection,
wireheading detection — follows without a separate reviewed bridge. In
particular, nothing here concerns consciousness: incompleteness of a self-model
is a statement about a projection, and every partially observed embedded system
has it, which is exactly why it cannot be evidence of anything phenomenal.

No survey coverage row is claimed here; this is workbench infrastructure.

Not `AISafetyAtlas.SelfAwareness`. That module carries the same registry group
and a different obstruction: a cost law over composites rather than a projection
of the state onto the model component. Neither imports the other.
-/

namespace AISafetyAtlas.Knowledge.SelfReference

universe u v

/-- The global state of a system that contains its own observer: the observer's
model, together with everything else. -/
public abbrev SelfState (Model : Type u) (Rest : Type v) : Type (max u v) :=
  Model × Rest

/-- What an embedded observer can read — its own model, and nothing else.

This is the self-referential step. `selfRead` is not supplied by a modeller; it
is the projection onto the component of the state that *is* the observer. -/
@[expose] public def selfRead {Model : Type u} {Rest : Type v} :
    SelfState Model Rest → Model :=
  Prod.fst

/-- The observer completely knows the state it is embedded in: the whole state
factors through its own model. -/
@[expose] public def SelfComplete (Model : Type u) (Rest : Type v) : Prop :=
  Knowable (selfRead : SelfState Model Rest → Model) id

/-! ## The characterization -/

/--
**A self-model is complete exactly when there is nothing else to model.**

Left to right is the obstruction: reading only your own model cannot separate two
states differing elsewhere. Right to left is the degenerate case that keeps the
statement honest — with a subsingleton remainder the projection *is* injective
and completeness genuinely holds, so this is a characterization and not a one-way
impossibility dressed up as one.

Both instances are load-bearing and neither is decoration. `knowable_id_iff_injective`
needs `[Nonempty Ω]`, and here `Ω` is `Model × Rest`, so it is inhabited only when
both components are; `Nonempty Model` is additionally what the forward direction
uses to build the colliding pair.
-/
public theorem selfComplete_iff_subsingleton_rest
    {Model : Type u} {Rest : Type v} [Nonempty Model] [Nonempty Rest] :
    SelfComplete Model Rest ↔ Subsingleton Rest := by
  rw [SelfComplete, knowable_id_iff_injective]
  constructor
  · intro hinj
    refine ⟨fun r₁ r₂ => ?_⟩
    obtain ⟨m⟩ := ‹Nonempty Model›
    have := hinj (a₁ := (m, r₁)) (a₂ := (m, r₂)) rfl
    exact congrArg Prod.snd this
  · intro hsub s₁ s₂ hread
    obtain ⟨m₁, r₁⟩ := s₁
    obtain ⟨m₂, r₂⟩ := s₂
    have hm : m₁ = m₂ := hread
    have hr : r₁ = r₂ := Subsingleton.elim _ _
    simp [hm, hr]

/-- Two distinct remainders refute completeness. Axiom-free: it exhibits the
colliding pair rather than reasoning about injectivity. -/
public theorem not_selfComplete_of_two_rest
    {Model : Type u} {Rest : Type v} (m : Model) {r₁ r₂ : Rest} (hne : r₁ ≠ r₂) :
    ¬ SelfComplete Model Rest :=
  not_knowable_of_collision
    (observation := (selfRead : SelfState Model Rest → Model))
    (ω₁ := (m, r₁)) (ω₂ := (m, r₂)) rfl
    (fun heq => hne (congrArg Prod.snd heq))

/-! ## The counting form -/

/--
**Finitely: a complete self-model forces the rest of the state to be trivial.**

The proof is the counting obstruction of `Knowledge.Ambiguity`, not a fresh
argument: the state has `|Model| * |Rest|` values and the observer's reading has
at most `|Model|`, so completeness is a cardinality inequality that only
`|Rest| ≤ 1` can satisfy.
-/
public theorem card_rest_le_one_of_selfComplete
    {Model : Type u} {Rest : Type v}
    [Fintype Model] [Fintype Rest] [DecidableEq Model] [DecidableEq Rest]
    [Nonempty Model]
    (h : SelfComplete Model Rest) :
    Fintype.card Rest ≤ 1 := by
  -- The whole state is the target, so its image is everything: `|Model| * |Rest|`.
  have hstate : (Finset.univ.image (id : SelfState Model Rest → _)).card
      = Fintype.card Model * Fintype.card Rest := by
    rw [Finset.image_id, Finset.card_univ]
    exact Fintype.card_prod Model Rest
  -- The observer's reading lands in `Model`, so its image has at most `|Model|`.
  have hread : (Finset.univ.image (selfRead : SelfState Model Rest → Model)).card
      ≤ Fintype.card Model := by
    simpa using Finset.card_le_univ
      (Finset.univ.image (selfRead : SelfState Model Rest → Model))
  -- The counting obstruction closes the gap.
  have hmul : Fintype.card Model * Fintype.card Rest ≤ Fintype.card Model * 1 := by
    rw [Nat.mul_one, ← hstate]
    exact le_trans (card_image_le_of_knowable h) hread
  exact Nat.le_of_mul_le_mul_left hmul Fintype.card_pos

end AISafetyAtlas.Knowledge.SelfReference
