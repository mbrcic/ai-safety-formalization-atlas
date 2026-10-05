module

public import AISafetyAtlas.Knowledge
public import AISafetyAtlas.Sovereignty.Separations
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.Abel

/-!
# A maintenance floor, and why assisted output does not report it

Two statements about a capability that decays and is topped up.

**What is new here, stated narrowly.** The verb *preserve* — one of the five in
this repository's cognitive-sovereignty reading — already has objects in the
tree: `AISafetyAtlas.Sovereignty.RetainsFamily` is preservation of what a
coalition can force across a change of game, and
`AISafetyAtlas.Wireheading.GoalPreservation` is preservation of a goal across
self-modification. What had no object is **capability preservation over time**:
a quantity that decays, is topped up, and must not fall below a floor. That is
what this module adds, and nothing wider.

## The model, and its status

`AffineCapability k p a` says a capability trajectory obeys `k (t+1) = a * k t + p t`:
retention `a`, top-up `p t`. **This is a selected model, not a law.** The source
sketch says so itself — *"the recurrence is not an empirical universal law"* —
and no published result is claimed for it here. What is claimed is the
implication, which is an induction.

`maintenanceFloor_of_practice_floor` is that implication: if retention is
nonnegative, the trajectory starts at or above the floor, and each top-up is at
least `(1 - a) * kmin`, then the trajectory never falls below `kmin`.

**It is stated at exactly the hypotheses it needs.** No `a ≤ 1`, no `0 ≤ k`, no
`0 ≤ p` — a forgetting reading would add all three, and the theorem does not use
them. `Examples.Sovereignty.Capability.expanding_floor` inhabits the antecedent
with `a = 2`, so that this is a checked claim and not a remark.

## What is near it in Mathlib, and why it is not reused

`Mathlib.Analysis.SpecificLimits.ArithmeticGeometric` has *arithGeom a b u₀*, the
same recurrence with a **constant** forcing term, and *div_lt_arithGeom* is the
corresponding floor: *0 < a → a ≠ 1 → b / (1 - a) < u₀ → ∀ n, b / (1 - a) < arithGeom a b u₀ n*.
That is this statement's nearest relative and it cannot be used here, on four
counts: the top-up varies with `t` (which is the whole point of the model — the
top-up is what an assistant changes), the bound is strict, `a = 1` and `a = 0`
are excluded, and it needs a field. This one needs an ordered ring and allows
all three of those cases.

## The second statement, and why it is the interesting one

A capability that is being assisted is not observed directly; what is observed is
**output**. `assistedOutput` is the cheapest model of that — fallback capability
plus borrowed assistance — and `fallback_not_knowable_from_assistedOutput` says
the fallback capability is **not `Knowable` from it**, by a collision against
`AISafetyAtlas.Knowledge`.

So the two statements point in opposite directions and that is the point: a
maintenance floor is a fact about a trajectory nobody can read off the thing they
are actually looking at. `Examples.Sovereignty.Capability.sketch_case` is the
source's own arithmetic — output rising from 2 to 4 while fallback falls from 2
to 1.

## The third statement: optionality

`Enlarges` and `Enlarges.forces` are the sketch's third claim — *adding optional
strategies, with the old semantics simulated unchanged, cannot destroy an
existing guarantee*. It is monotonicity of `AISafetyAtlas.Sovereignty.Forces`
under enlargement of one coalition's strategy sets, and the object it needed —
a map between two game forms — is built here rather than borrowed, because the
`Sovereignty` cluster carries game forms and no morphism between them.

**One clause carries the whole theorem**, and it is the one about everybody
else: `embed_reduce` says the *complement* gained nothing.
`Examples.Sovereignty.Capability.foe_breaks_forces` drops exactly that clause,
keeps the embedding and the unchanged semantics, and loses the guarantee. So
"more options cannot hurt" is false as usually said and true as stated here.
-/

namespace AISafetyAtlas.Sovereignty

open AISafetyAtlas.Knowledge

universe u v w

/-! ## The affine capability model -/

/--
The trajectory `k` obeys the affine recurrence with retention `a` and top-ups `p`.

A **selected** model, carried as a hypothesis on a trajectory rather than as a
defined function, so that a consumer may supply any `k` it can show satisfies it.
-/
@[expose] public def AffineCapability {R : Type u} [Mul R] [Add R]
    (k p : ℕ → R) (a : R) : Prop :=
  ∀ t, k (t + 1) = a * k t + p t

/-- The trajectory never falls below `kmin`. -/
@[expose] public def MaintenanceFloor {R : Type u} [LE R] (k : ℕ → R) (kmin : R) : Prop :=
  ∀ t, kmin ≤ k t

/--
**The maintenance floor.** Nonnegative retention, a start at or above the floor,
and top-ups of at least `(1 - a) * kmin` keep the trajectory at or above `kmin`
forever.

The induction step is the whole content: multiply the previous bound by a
nonnegative `a` and add the top-up floor.
-/
public theorem maintenanceFloor_of_practice_floor {R : Type u}
    [Ring R] [PartialOrder R] [IsOrderedRing R]
    {k p : ℕ → R} {a kmin : R}
    (hrec : AffineCapability k p a) (ha : 0 ≤ a) (h0 : kmin ≤ k 0)
    (hp : ∀ t, (1 - a) * kmin ≤ p t) :
    MaintenanceFloor k kmin := by
  intro t
  induction t with
  | zero => exact h0
  | succ n ih =>
      have h1 : a * kmin ≤ a * k n := mul_le_mul_of_nonneg_left ih ha
      have h2 := add_le_add h1 (hp n)
      rw [hrec n]
      calc kmin = a * kmin + (1 - a) * kmin := by rw [sub_mul, one_mul]; abel
        _ ≤ a * k n + p n := h2

/--
**The floor is exactly the floor at the start.** A trajectory with a maintenance
floor starts at or above it — recorded so that the hypothesis `h0` of the theorem
above is visibly not decoration.
-/
public theorem MaintenanceFloor.le_zero {R : Type u} [LE R] {k : ℕ → R} {kmin : R}
    (h : MaintenanceFloor k kmin) : kmin ≤ k 0 := h 0

/-! ## Output is not capability -/

/--
**Assisted output**: what the fallback capability produces together with whatever
assistance is borrowed. A state is the pair, and this is what an outside observer
sees.
-/
@[expose] public def assistedOutput {R : Type u} [Add R] (state : R × R) : R :=
  state.1 + state.2

/-- The fallback capability of a state: the first component. -/
@[expose] public def fallbackCapability {R : Type u} (state : R × R) : R :=
  state.1

/--
**Assisted output does not report fallback capability.** For any two distinct
capability levels there are two states with the same assisted output and
different fallback, so no decoder on output recovers the fallback.

This is `AISafetyAtlas.Knowledge.not_knowable_of_collision` at the pair
`(x, 0)` and `(y, x - y)`, which is the general form of the source's arithmetic
example.
-/
public theorem fallback_not_knowable_from_assistedOutput {R : Type u} [Ring R]
    {x y : R} (hxy : x ≠ y) :
    ¬ Knowable (assistedOutput (R := R)) (fallbackCapability (R := R)) := by
  refine not_knowable_of_collision (ω₁ := (x, 0)) (ω₂ := (y, x - y)) ?_ hxy
  show x + 0 = y + (x - y)
  abel

/--
**And the monotone reading fails too.** Wherever two capability levels are
comparable there are two states whose assisted output strictly *rises* while
fallback capability strictly *falls*.

Constructive: the second state borrows twice the gap it has lost.
-/
public theorem exists_output_rise_with_fallback_fall {R : Type u}
    [Ring R] [PartialOrder R] [IsOrderedRing R] {lo hi : R} (h : lo < hi) :
    ∃ s t : R × R,
      assistedOutput s < assistedOutput t ∧
        fallbackCapability t < fallbackCapability s := by
  refine ⟨(hi, 0), (lo, (hi - lo) + (hi - lo)), ?_, h⟩
  show hi + 0 < lo + ((hi - lo) + (hi - lo))
  have hgap : 0 < hi - lo := sub_pos.mpr h
  have hstep : hi + 0 < hi + (hi - lo) := by
    rw [add_zero]
    exact lt_add_of_pos_right hi hgap
  calc hi + 0 < hi + (hi - lo) := hstep
    _ = lo + ((hi - lo) + (hi - lo)) := by abel


/-! ## Optionality, and the clause that carries the weight -/

/--
**An optionality enlargement, at a coalition.**

`G'` offers coalition `C` at least what `G` did, offers everyone else *exactly*
what `G` did, and computes the old outcome from the old options. This is the
smallest object that can state the sketch's *"the old semantics simulated
unchanged"*, and it is built here rather than borrowed: the `Sovereignty`
cluster carries game forms but no map between two of them.
-/
public structure Enlarges {N : Type u} {X : Type v}
    (G G' : GameForm.{u, v, w} N X) (C : Set N) where
  /-- Every old option is still available. -/
  embed : ∀ i, G.strategy i → G'.strategy i
  /-- **Outside the coalition nothing was added**: every new option is an old one. -/
  reduce : ∀ i, i ∉ C → G'.strategy i → G.strategy i
  /-- And there `reduce` is a section of `embed`, so the two option sets agree. -/
  embed_reduce : ∀ i (h : i ∉ C) (t : G'.strategy i), embed i (reduce i h t) = t
  /-- **The old semantics, simulated unchanged.** -/
  outcome_embed : ∀ s : ∀ i, G.strategy i,
    G'.outcome (fun i => embed i (s i)) = G.outcome s

namespace Enlarges

variable {N : Type u} {X : Type v} {G G' : GameForm.{u, v, w} N X} {C : Set N}

/--
**GK3.** Adding optional strategies to a coalition, with the old semantics
simulated unchanged, cannot destroy a guarantee that coalition already had.

The proof is the only thing it can be: play the old witness through `embed`, and
read any new complete profile back as an old one — which is possible exactly
because `embed_reduce` says the complement gained nothing.
-/
public theorem forces {A : Set X} (E : Enlarges G G' C) (h : Forces G C A) :
    Forces G' C A := by
  classical
  obtain ⟨sC, hsC⟩ := h
  refine ⟨fun i => E.embed i (sC i), ?_⟩
  intro t ht
  have key : ∀ hold : ∀ i, G.strategy i, (∀ i, E.embed i (hold i) = t i) →
      (∀ i : C, hold i = sC i) → G'.outcome t ∈ A := by
    intro hold hlift hagree
    have hout := E.outcome_embed hold
    rw [funext hlift] at hout
    rw [hout]
    exact hsC hold hagree
  refine key (fun i => if hi : i ∈ C then sC ⟨i, hi⟩ else E.reduce i hi (t i)) ?_ ?_
  · intro i
    by_cases hi : i ∈ C
    · rw [dif_pos hi]
      exact (ht ⟨i, hi⟩).symm
    · rw [dif_neg hi]
      exact E.embed_reduce i hi (t i)
  · intro i
    rw [dif_pos i.2]

/-- The same statement at the effectivity family: optionality can only grow it. -/
public theorem effectivity_subset (E : Enlarges G G' C) :
    effectivity G C ⊆ effectivity G' C :=
  fun _ h => E.forces h

end Enlarges

end AISafetyAtlas.Sovereignty
