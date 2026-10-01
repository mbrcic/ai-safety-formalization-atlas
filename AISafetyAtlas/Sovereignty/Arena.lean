module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Image

/-!
# Power without a game form

Every forcing notion in this repository has the same shape. A party settles some
part of the situation, everything it does not settle is settled by something
else, and the two together resolve to an outcome. Forcing is then: *there is a
choice of my part such that, whatever the rest turns out to be, the outcome lies
in the target.*

That shape does not need agents, coalitions, strategies or a graph. It needs a
map `Ctl → Res → X`. This module states power at that level, so that the
game-form notion, the mediated notion and the oversight notion are instances
rather than three parallel developments.

## What generalizes and what does not

**Power-to generalizes.** `Forces`, `collapse`, `Decisive`, `Sovereign` and
`Dictates` are all statements about one party against a residue, and they are
stated here once.

**Power-over does not.** `HasPowerOver` compares what one party can force *across
another party's commitments*, and that needs the residue to be structured -- to
have a distinguished sub-party inside it. An arena deliberately does not carry
that structure: `Res` is an opaque lump. So the relational theory stays in
`AISafetyAtlas.Sovereignty.Separations`, where coalitions exist, and this module
is the unary theory underneath it.

## The pair the whole module turns on

`Sovereign` and `Dictates` are the same predicate under different quantifiers:
sovereignty is "the residue cannot move the view, **whatever** I choose",
dictation is "the residue cannot move the view, for **some** choice of mine".
That is `∀` against `∃` over one condition, which is the precise form of the
relationship between defending a boundary and setting one.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {Ctl : Type u} {Res : Type v} {X : Type w} {V : Type*}

/--
An **arena**: what one party settles (`Ctl`), what it does not (`Res`), and how
the two resolve.

`Res` is everything outside the party's control, taken as a single opaque type.
It may be other agents, a state of the world, a coarsening of either, or all of
these at once; the theory below never asks.
-/
public structure Arena (Ctl : Type u) (Res : Type v) (X : Type w) where
  /-- How a control choice and a residue resolve to an outcome. -/
  outcome : Ctl → Res → X

variable {A : Arena Ctl Res X}

/--
The **collapse** of a control choice: the outcomes still admitted once it is
made.

Small collapse is power. `A.collapse c = {x}` is a choice that lands the world on
`x` from wherever it started; a collapse as large as the whole residue allows is
a choice that settles nothing. `AISafetyAtlas.Oversight.collapse` is the same
quantity on an effect table.
-/
@[expose] public def Arena.collapse (A : Arena Ctl Res X) (c : Ctl) : Set X :=
  Set.range (A.outcome c)

/-- **Forcing.** Some control choice keeps every residue inside the target. -/
@[expose] public def Arena.Forces (A : Arena Ctl Res X) (S : Set X) : Prop :=
  ∃ c : Ctl, ∀ r : Res, A.outcome c r ∈ S

/-- **Forcing is collapsing into the target**, and this is the whole content of
the notion: to force is to have a choice whose collapse fits inside `S`. -/
public theorem Arena.forces_iff_exists_collapse_subset {S : Set X} :
    A.Forces S ↔ ∃ c, A.collapse c ⊆ S := by
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by rintro _ ⟨r, rfl⟩; exact hc r⟩
  · rintro ⟨c, hc⟩; exact ⟨c, fun r => hc ⟨r, rfl⟩⟩

/-- Forcing is upward closed in the target. -/
public theorem Arena.Forces.mono {S T : Set X} (h : A.Forces S) (hST : S ⊆ T) :
    A.Forces T := by
  obtain ⟨c, hc⟩ := h; exact ⟨c, fun r => hST (hc r)⟩

/-- Every arena with a choice available forces the whole outcome space. -/
public theorem Arena.forces_univ [Nonempty Ctl] : A.Forces (Set.univ : Set X) :=
  ⟨Classical.arbitrary _, fun _ => Set.mem_univ _⟩

/-- **Reading the outcome through a boundary.** Composing with a view gives the
arena of what that view shows. -/
@[expose] public def Arena.map (A : Arena Ctl Res X) (f : X → V) : Arena Ctl Res V :=
  ⟨fun c r => f (A.outcome c r)⟩

@[simp] public theorem Arena.map_outcome (f : X → V) (c : Ctl) (r : Res) :
    (A.map f).outcome c r = f (A.outcome c r) := rfl

/--
A control choice is **decisive** when the residue cannot move the outcome: having
made it, what happens is settled.
-/
@[expose] public def Arena.Decisive (A : Arena Ctl Res X) (c : Ctl) : Prop :=
  ∀ r r' : Res, A.outcome c r = A.outcome c r'

/-- Decisiveness is collapse to at most one point. -/
public theorem Arena.decisive_iff_collapse_subsingleton {c : Ctl} :
    A.Decisive c ↔ (A.collapse c).Subsingleton := by
  constructor
  · rintro h _ ⟨r, rfl⟩ _ ⟨r', rfl⟩; exact h r r'
  · intro h r r'; exact h ⟨r, rfl⟩ ⟨r', rfl⟩

/-- A decisive choice forces the singleton it lands on. -/
public theorem Arena.forces_singleton_of_decisive [Nonempty Res] {c : Ctl}
    (h : A.Decisive c) (r₀ : Res) : A.Forces {A.outcome c r₀} :=
  ⟨c, fun r => h r r₀⟩

/-! ## Defending a boundary and setting one

The two notions below differ in one quantifier, and everything about how power
and sovereignty relate is in that difference.
-/

/--
**Sovereignty over a boundary.** Whatever the party chooses, the residue cannot
move what the view shows: the view depends on the party's own choice and on
nothing else.
-/
@[expose] public def Arena.Sovereign (A : Arena Ctl Res X) (view : X → V) : Prop :=
  ∀ c : Ctl, (A.map view).Decisive c

/--
**Dictation of a boundary.** *Some* choice settles what the view shows.

Sovereignty is this for every choice; dictation is this for one. Sovereignty says
the residue never has a say; dictation says the party can arrange for it not to.
-/
@[expose] public def Arena.Dictates (A : Arena Ctl Res X) (view : X → V) : Prop :=
  ∃ c : Ctl, (A.map view).Decisive c

/-- **Defending a boundary requires being able to set it.** Sovereignty is the
universal form and dictation the existential one, so with any choice available at
all the first gives the second. This is the containment between sovereignty and
power, at its most general. -/
public theorem Arena.Sovereign.dictates [Nonempty Ctl] {view : X → V}
    (h : A.Sovereign view) : A.Dictates view :=
  ⟨Classical.arbitrary _, h _⟩

/-- Sovereignty over a coarser boundary is easier. -/
public theorem Arena.Sovereign.comp {view : X → V} {V' : Type*} (h : A.Sovereign view)
    (f : V → V') : A.Sovereign (f ∘ view) :=
  fun c r r' => congrArg f (h c r r')

/-- Every arena is sovereign over a constant boundary, which is why a boundary
that shows nothing is no achievement. -/
public theorem Arena.sovereign_const (b : V) : A.Sovereign (fun _ => b) :=
  fun _ _ _ => rfl

/-- **One residue that moves the view refutes sovereignty.** No weighting of how
likely that residue is enters, which is what makes `Sovereign` an invariant
rather than a measure. -/
public theorem Arena.not_sovereign_of_residue_moves {view : X → V} (c : Ctl)
    (r r' : Res) (h : view (A.outcome c r) ≠ view (A.outcome c r')) :
    ¬ A.Sovereign view :=
  fun hsov => h (hsov c r r')

/-- **Sovereignty is decisiveness of every choice, in the view.** Stated so the
collapse vocabulary applies to boundaries unchanged. -/
public theorem Arena.sovereign_iff_forall_collapse_subsingleton {view : X → V} :
    A.Sovereign view ↔ ∀ c, ((A.map view).collapse c).Subsingleton :=
  forall_congr' fun _ => Arena.decisive_iff_collapse_subsingleton

end AISafetyAtlas.Sovereignty
