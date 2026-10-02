module

public import AISafetyAtlas.Sovereignty.Independence
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# The corner that cannot escape, on three worlds

`AISafetyAtlas.Sovereignty.Independence` states List and Valentini's two-by-two
and the two conditionals Carter and Shnayderman argue. Both conditionals are
implications, and an implication says nothing until something satisfies its
antecedent. This file inhabits them, and separates the two theses.

Three worlds are enough, and they are the paper's own three cases:

* `w0`, the actual world, where nobody is constrained;
* `w1`, the everyday lethal world -- the kitchen knife, the car, the train
  platform. The constraint is real. Inside a republican state it is **punished**,
  so on Pettit's conception it is non-arbitrary and exempt;
* `w2`, the takeover world, where a group *"acquires the means ... to take over
  the state and thereby possess more or less absolute arbitrary power"*. Here the
  constraint carries impunity, so it is **not** exempt.

`everyday` takes `w0` and `w1` as relevant; `withTakeover` adds `w2`. The
difference between them is exactly the difference between the paper's two theses.

`matrix` is the other thing print is owed. The two implications that order the
two-by-two are consistent with all four conceptions collapsing to one cell.
Five actions on two worlds make the four extensions pairwise distinct, so
moralization and robustness are independent parameters rather than two names
for one predicate.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- Two agents and two actions, so no quantifier below is degenerate. -/
public abbrev Agent := Bool
/-- The actions an agent might be free to perform. -/
public abbrev Act := Bool

/-- `w0` actual, `w1` everyday lethal and punished, `w2` takeover with impunity. -/
public abbrev World := Fin 3

/-- Every world but the actual one carries a lethal constraint, on every agent
and every action: print's *"no one is ever free to do anything whatsoever"* is
about death preventing every action. -/
@[expose] public def lethal (w : World) (_ : Agent) (_ : Act) : Prop := w ≠ 0

/-- The everyday constraint is punished, hence non-arbitrary, hence exempt on a
moralized conception. The takeover constraint carries impunity and is not. -/
@[expose] public def punished (w : World) (_ : Agent) (_ : Act) : Prop := w = 1

/-- **The everyday setting**: the actual world and the everyday lethal one. -/
@[expose] public def everyday : Setting Agent Act World where
  actual := 0
  relevant := {0, 1}
  actual_mem := by simp
  constrains := lethal
  permitted := punished

/-- **The setting with the takeover world**, which is the extra possibility
Pettit's conception cannot exempt. -/
@[expose] public def withTakeover : Setting Agent Act World where
  actual := 0
  relevant := Set.univ
  actual_mem := trivial
  constrains := lethal
  permitted := punished

/-! ## The everyday setting: three conceptions hold, one is empty -/

/-- Case 1 holds: in the actual world nobody is constrained, so Berlin's liberal
freedom is untouched. **This is the liberal way out.** -/
public theorem everyday_liberalFree (i : Agent) (a : Act) :
    everyday.LiberalFree i a := by
  intro w hw hc
  have : w = 0 := by simpa [Setting.worlds, everyday] using hw
  exact hc.1 (by simp [this])

/-- Case 2 holds, for the same reason. -/
public theorem everyday_moralizedLiberalFree (i : Agent) (a : Act) :
    everyday.MoralizedLiberalFree i a :=
  everyday.free_of_free_not_moralized (everyday_liberalFree i a)

/-- Case 4 holds: the everyday constraint is punished, so on Pettit's conception
it is not arbitrary and does not count. **This is the republican way out.** -/
public theorem everyday_republicanFree (i : Agent) (a : Act) :
    everyday.RepublicanFree i a := by
  intro w hw hc
  have hw' : w = 0 ∨ w = 1 := by simpa [Setting.worlds, everyday] using hw
  rcases hw' with h | h
  · exact hc.1 (by simp [h])
  · exact hc.2 rfl (by simp [everyday, punished, h])

/-- **Case 3 fails, at every agent and every action.** The everyday world is
relevant and the constraint counts, because a non-moralized conception has no
exemption to apply. -/
public theorem everyday_not_independenceFree (i : Agent) (a : Act) :
    ¬ everyday.IndependenceFree i a := by
  refine everyday.not_independenceFree_of_universal_threat ?_ i a
  exact fun _ _ => ⟨1, by simp [everyday], by simp [everyday, lethal]⟩

/--
**Freedom as independence is the trapped corner of print's own matrix.**

One setting, and in it: Berlin's liberal freedom holds, moralized liberal freedom
holds, Pettit's republican freedom holds, and List and Valentini's freedom as
independence holds of nobody for anything. The two escapes Carter and Shnayderman
name -- drop robustness, or add the moralized exemption -- are exactly the two
parameters, and case 3 is the corner that has taken neither.
-/
public theorem independence_is_the_trapped_corner :
    (∀ i a, everyday.LiberalFree i a) ∧
    (∀ i a, everyday.MoralizedLiberalFree i a) ∧
    (∀ i a, everyday.RepublicanFree i a) ∧
    (∀ i a, ¬ everyday.IndependenceFree i a) :=
  ⟨everyday_liberalFree, everyday_moralizedLiberalFree,
   everyday_republicanFree, everyday_not_independenceFree⟩

/-! ## Adding the takeover world: the republican thesis too -/

/-- With the takeover world relevant, **republican freedom fails as well** --
Carter and Shnayderman's first thesis. The constraint there carries impunity, so
Pettit's exemption has nothing to apply to. -/
public theorem withTakeover_not_republicanFree (i : Agent) (a : Act) :
    ¬ withTakeover.RepublicanFree i a := by
  refine withTakeover.not_republicanFree_of_impermissible_threat ?_ i a
  exact fun _ _ => ⟨2, trivial, by simp [withTakeover, lethal], by simp [withTakeover, punished]⟩

/-- And so does independence, a fortiori. -/
public theorem withTakeover_not_independenceFree (i : Agent) (a : Act) :
    ¬ withTakeover.IndependenceFree i a := fun h =>
  withTakeover_not_republicanFree i a (withTakeover.republicanFree_of_independenceFree h)

/-- **Liberal freedom survives even the takeover world**, because it never looks
past the actual one. That is the whole content of the robustness parameter. -/
public theorem withTakeover_liberalFree (i : Agent) (a : Act) :
    withTakeover.LiberalFree i a := by
  intro w hw hc
  have : w = 0 := by simpa [Setting.worlds, withTakeover] using hw
  exact hc.1 (by simp [this])

/--
**The two theses differ in scope, and the difference is witnessed.**

Republican freedom survives `everyday` and fails in `withTakeover`; freedom as
independence fails in both. That is Carter and Shnayderman's *"this entailment
depends not only on the particular case of a threat to any regime ...; it depends
also on the countless threats which everyone constantly faces in everyday
situations"*.
-/
public theorem theses_differ_in_scope :
    (∀ i a, everyday.RepublicanFree i a) ∧
    (∀ i a, ¬ withTakeover.RepublicanFree i a) ∧
    (∀ i a, ¬ everyday.IndependenceFree i a) ∧
    (∀ i a, ¬ withTakeover.IndependenceFree i a) :=
  ⟨everyday_republicanFree, withTakeover_not_republicanFree,
   everyday_not_independenceFree, withTakeover_not_independenceFree⟩

/-! ## The two-by-two has four cells

`everyday` and `withTakeover` separate the theses. They do not separate the
four conceptions from each other: in `everyday`, cases 1, 2 and 4 hold of
every action and case 3 of none, so three cells coincide. Print's claim is
that moralization and robustness are *independent*, hence that the matrix is
a genuine two-by-two. `matrix` is a setting in which the four extensions are
four different sets.
-/

/-- Constrained in the actual world (`a.val ≤ 1`) or in the other relevant
world (`a.val = 2` or `3`). Action `4` is never constrained. -/
@[expose] public def matrixConstrains (w : Fin 2) (_ : Unit) (a : Fin 5) : Prop :=
  (a.val ≤ 1 ∧ w = 0) ∨ ((a.val = 2 ∨ a.val = 3) ∧ w = 1)

/-- Actions `1` and `3` are permitted; the rest are not. -/
@[expose] public def matrixPermitted (_ : Fin 2) (_ : Unit) (a : Fin 5) : Prop :=
  a.val = 1 ∨ a.val = 3

/--
**Print's two-by-two, inhabited at every cell.**

Two worlds, five actions. The actual world is `0`; both worlds are relevant.
Actions `0` and `1` are constrained only in the actual world, `2` and `3` only
in the other, `4` never; `1` and `3` are permitted, the rest not. That is one
constraint-pattern per combination of (actual vs counterfactual) with
(permitted vs not), plus an unconstrained action so the strongest cell is not
empty.
-/
@[expose] public def matrix : Setting Unit (Fin 5) (Fin 2) where
  actual := 0
  relevant := Set.univ
  actual_mem := trivial
  constrains := matrixConstrains
  permitted := matrixPermitted

/-- Liberal freedom holds exactly off the actual-world constraints. -/
public theorem matrix_liberalFree_iff (a : Fin 5) :
    matrix.LiberalFree () a ↔ 2 ≤ a.val := by
  fin_cases a <;> simp [Setting.LiberalFree, Setting.Free, Setting.worlds,
    Setting.Counts, matrix, matrixConstrains, matrixPermitted]

/-- Moralized liberal freedom fails only at the actual, impermissible constraint. -/
public theorem matrix_moralizedLiberalFree_iff (a : Fin 5) :
    matrix.MoralizedLiberalFree () a ↔ a.val ≠ 0 := by
  fin_cases a <;> simp [Setting.MoralizedLiberalFree, Setting.Free, Setting.worlds,
    Setting.Counts, matrix, matrixConstrains, matrixPermitted]

/-- Freedom as independence holds only of the unconstrained action. -/
public theorem matrix_independenceFree_iff (a : Fin 5) :
    matrix.IndependenceFree () a ↔ a.val = 4 := by
  fin_cases a <;> simp [Setting.IndependenceFree, Setting.Free, Setting.worlds,
    Setting.Counts, matrix, matrixConstrains, matrixPermitted]

/-- Republican freedom fails at the two impermissible constraints. -/
public theorem matrix_republicanFree_iff (a : Fin 5) :
    matrix.RepublicanFree () a ↔ a.val = 1 ∨ 3 ≤ a.val := by
  fin_cases a <;> simp [Setting.RepublicanFree, Setting.Free, Setting.worlds,
    Setting.Counts, matrix, matrixConstrains, matrixPermitted]

/--
**Moralization and robustness are independent parameters.**

The four conceptions, read as sets of actions this setting counts as free, are

* liberal: `{2, 3, 4}`
* moralized liberal: `{1, 2, 3, 4}`
* independence: `{4}`
* republican: `{1, 3, 4}`

No two are equal, so the two-by-two has four cells. Each pairwise difference
is a single action: `1` is the moralization gap at the actual world, `2` is
the robustness gap on an impermissible counterfactual constraint, `3` is the
robustness gap on a permitted one.
-/
public theorem four_corners_distinct :
    (∃ a, matrix.LiberalFree () a ∧ ¬ matrix.IndependenceFree () a) ∧
    (∃ a, matrix.RepublicanFree () a ∧ ¬ matrix.IndependenceFree () a) ∧
    (∃ a, matrix.MoralizedLiberalFree () a ∧ ¬ matrix.LiberalFree () a) ∧
    (∃ a, matrix.MoralizedLiberalFree () a ∧ ¬ matrix.RepublicanFree () a) ∧
    (∃ a, matrix.LiberalFree () a ∧ ¬ matrix.RepublicanFree () a) ∧
    (∃ a, matrix.RepublicanFree () a ∧ ¬ matrix.LiberalFree () a) := by
  refine ⟨⟨2, ?_, ?_⟩, ⟨1, ?_, ?_⟩, ⟨1, ?_, ?_⟩, ⟨2, ?_, ?_⟩, ⟨2, ?_, ?_⟩, ⟨1, ?_, ?_⟩⟩
    <;> simp [matrix_liberalFree_iff, matrix_moralizedLiberalFree_iff,
      matrix_independenceFree_iff, matrix_republicanFree_iff]

/-- **The strongest thesis implies the weakest, at the corner that satisfies
it.**

`matrix_independenceFree_iff` puts independence-freedom at exactly one action,
and `four_corners_distinct` shows the implication is strict in the other
direction -- action `2` is liberally free and not independence-free. So the
ordering between the two theses is a real ordering here rather than a
coincidence of an empty antecedent. -/
public theorem matrix_liberalFree_of_independenceFree :
    matrix.LiberalFree () (4 : Fin 5) :=
  Setting.liberalFree_of_independenceFree matrix
    ((matrix_independenceFree_iff 4).mpr rfl)

end AISafetyAtlas.Examples.Sovereignty
