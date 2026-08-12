module

public import AISafetyAtlas.Knowledge.Ambiguity
public import AISafetyAtlas.Knowledge.Temporal
public import Mathlib.Data.Finset.Prod

/-!
# Accumulation: what a fixed observation loses about a whole window

`Knowledge.Ambiguity` counts what one observation leaves open about **one**
target. Asking about a *window* of times means asking about the tuple of targets
across it, and the question becomes how ambiguity behaves as the window grows.

## The two bounds

Pairing two targets can only make things worse, and at worst multiplies:

```
ambiguity r f i  ≤  ambiguity r ⟨f, g⟩ i  ≤  ambiguity r f i * ambiguity r g i
```

The left bound is the accumulation statement — **widening the window never
reduces ambiguity** — and it is what licenses reading a per-step shortfall as
something that persists rather than washing out. The right bound is its ceiling:
ambiguity about a window is never worse than the product of the per-step
ambiguities, so nothing blows up faster than independently.

The bounds themselves are not time-indexed: a "window" is any finite tuple of
targets, and `f := target s₁`, `g := target s₂` from `Knowledge.Temporal` is one
instantiation among others.

## The other direction: evidence time

Widening the window is one axis. The other is *when the observation is read*.
Under `Knowledge.Temporal.EvidenceMonotone` — later evidence determines earlier —
ambiguity moves the opposite way:

```
ambiguity (observe t') f (observe t' ω)  ≤  ambiguity (observe t) f (observe t ω)      for t ≤ t'
```

So the two axes pull against each other, and
`ambiguity_le_pairTarget_of_evidenceMonotone` states both at once: one step read
late is never more ambiguous than the whole window read early. That inequality is
the module's reason to depend on `Knowledge.Temporal` rather than merely mention
it.

Note what this does **not** give. It bounds ambiguity about a *fixed* target as
evidence accumulates. It says nothing about a target that moves with time, which
is the case an impossibility result cares about and which needs dynamics.

## What is *not* proved here

That ambiguity **grows** — strictly, or exponentially — is not a theorem of this
module and could not be. Growth depends on whether each new step introduces a
distinction the observation cannot see, which is a statement about dynamics, and
there is no transition system anywhere in this layer. What is proved is that
growth is *possible and bounded*: the shortfall never shrinks, and never exceeds
the product.

`AISafetyAtlas.Examples.Knowledge.Accumulation` exhibits a model where the bound
on the left is strict and ambiguity doubles per step, reaching `2 ^ k`. That is an
example, not a general law, and the module says so at the point of statement.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `pairTarget` | The joint target: two questions asked at once |
| **Bound** | `ambiguity_le_pairTarget_left` | Widening the window never reduces ambiguity |
| **Bound** | `ambiguity_le_pairTarget_right` | The same on the other component |
| **Bound** | `ambiguity_pairTarget_le_mul` | A window is never worse than the product of its steps |
| **Boundary** | `not_knowable_pairTarget_of_not_knowable` | An unknowable step makes the whole window unknowable |
| **Bound** | `ambiguity_le_of_evidenceMonotone` | Later evidence never increases ambiguity |
| **Bound** | `ambiguity_le_pairTarget_of_evidenceMonotone` | One step read late ≤ the whole window read early |

## Explicit non-claims

Finite counting only — no probability, no entropy, no rate. In particular this is
not an information-accumulation *rate* result: rates need a distribution, and
this layer commits to none. No AI-system reading follows without a separate
reviewed bridge.

No survey coverage row is claimed here; this is workbench infrastructure.
-/

namespace AISafetyAtlas.Knowledge

universe u v w w'

variable {Ω : Type u} {I : Type v} {Y : Type w} {Z : Type w'}

/-- Two targets asked at once: the joint question a window poses. -/
@[expose] public def pairTarget (f : Ω → Y) (g : Ω → Z) : Ω → Y × Z :=
  fun ω => (f ω, g ω)

/-! ## Widening never helps -/

/--
**Accumulation.** Asking about a window is at least as ambiguous as asking about
one of its steps: the step's answer is a projection of the window's.

This is the direction that matters. It says a shortfall recorded at one time does
not wash out when you ask a larger question — the reason "ambiguity accumulates"
is a legitimate reading rather than a hope.
-/
public theorem ambiguity_le_pairTarget_left
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] [DecidableEq Z]
    (r : Ω → I) (f : Ω → Y) (g : Ω → Z) (i : I) :
    ambiguity r f i ≤ ambiguity r (pairTarget f g) i := by
  have himg : (fibre r i).image f
      = ((fibre r i).image (pairTarget f g)).image Prod.fst := by
    rw [Finset.image_image]
    rfl
  rw [ambiguity, ambiguity, himg]
  exact Finset.card_image_le

/-- The same bound on the second component. -/
public theorem ambiguity_le_pairTarget_right
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] [DecidableEq Z]
    (r : Ω → I) (f : Ω → Y) (g : Ω → Z) (i : I) :
    ambiguity r g i ≤ ambiguity r (pairTarget f g) i := by
  have himg : (fibre r i).image g
      = ((fibre r i).image (pairTarget f g)).image Prod.snd := by
    rw [Finset.image_image]
    rfl
  rw [ambiguity, ambiguity, himg]
  exact Finset.card_image_le

/-! ## And never blows up faster than independently -/

/--
**The ceiling.** A window is never more ambiguous than the product of its steps:
every consistent window-answer is a pair of consistent step-answers.

Together with the bounds above this brackets accumulation between "never
decreases" and "at most multiplies".
-/
public theorem ambiguity_pairTarget_le_mul
    [Fintype Ω] [DecidableEq I] [DecidableEq Y] [DecidableEq Z]
    (r : Ω → I) (f : Ω → Y) (g : Ω → Z) (i : I) :
    ambiguity r (pairTarget f g) i ≤ ambiguity r f i * ambiguity r g i := by
  have hsub : (fibre r i).image (pairTarget f g)
      ⊆ ((fibre r i).image f) ×ˢ ((fibre r i).image g) := by
    intro p hp
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem f hω, Finset.mem_image_of_mem g hω⟩
  calc ambiguity r (pairTarget f g) i
      ≤ (((fibre r i).image f) ×ˢ ((fibre r i).image g)).card :=
        Finset.card_le_card hsub
    _ = ambiguity r f i * ambiguity r g i := Finset.card_product _ _

/-! ## The other axis: reading later

Widening a window costs ambiguity; waiting for evidence recovers it. Both
statements are about the same quantity, so they belong together. -/

/--
**Later evidence never increases ambiguity.** Under `Temporal.EvidenceMonotone`, the
observation at `t'` determines the one at `t ≤ t'`, so the later fibre through a
history is contained in the earlier one and can only carry fewer target values.

This is `ambiguity_le_of_comp` read along time: the earlier observation *is* a
post-processing of the later one, and post-processing never resolves anything.
-/
public theorem ambiguity_le_of_evidenceMonotone
    {T : Type*} [Preorder T] {E : T → Type*} [Fintype Ω] [DecidableEq Y]
    (observe : ∀ t, Ω → E t) (f : Ω → Y) {t t' : T}
    [DecidableEq (E t)] [DecidableEq (E t')]
    (cumulative : Temporal.EvidenceMonotone observe) (later : t ≤ t') (ω : Ω) :
    ambiguity (observe t') f (observe t' ω) ≤ ambiguity (observe t) f (observe t ω) := by
  obtain ⟨k, hk⟩ := cumulative later
  have hcomp : (fun ω' => k (observe t' ω')) = observe t := (funext hk).symm
  have hbound := ambiguity_le_of_comp (observe t') f k (observe t' ω)
  rw [hcomp, ← hk ω] at hbound
  exact hbound

/--
**Both axes at once.** One step of a window, read at the later time, is never
more ambiguous than the whole window read at the earlier one.

Widening pushes ambiguity up and waiting pushes it down; this is the composite,
and it is the form a consumer applies when asking whether delay buys back what
scope costs.
-/
public theorem ambiguity_le_pairTarget_of_evidenceMonotone
    {T : Type*} [Preorder T] {E : T → Type*}
    [Fintype Ω] [DecidableEq Y] [DecidableEq Z]
    (observe : ∀ t, Ω → E t) (f : Ω → Y) (g : Ω → Z) {t t' : T}
    [DecidableEq (E t)] [DecidableEq (E t')]
    (cumulative : Temporal.EvidenceMonotone observe) (later : t ≤ t') (ω : Ω) :
    ambiguity (observe t') f (observe t' ω)
      ≤ ambiguity (observe t) (pairTarget f g) (observe t ω) :=
  le_trans
    (ambiguity_le_of_evidenceMonotone observe f cumulative later ω)
    (ambiguity_le_pairTarget_left (observe t) f g (observe t ω))

/-! ## Consequence for knowability -/

/--
One unknowable step makes the whole window unknowable. The contrapositive of the
projection bound, and the form a consumer applies: you cannot recover a window by
asking for more of it.
-/
public theorem not_knowable_pairTarget_of_not_knowable
    {f : Ω → Y} {g : Ω → Z} {r : Ω → I}
    (h : ¬ Knowable r f) : ¬ Knowable r (pairTarget f g) := by
  intro hk
  exact h (Knowable.mono (finer := r) ⟨id, fun _ => rfl⟩
    (by obtain ⟨d, hd⟩ := hk; exact ⟨fun j => (d j).1, fun ω => congrArg Prod.fst (hd ω)⟩))

end AISafetyAtlas.Knowledge
