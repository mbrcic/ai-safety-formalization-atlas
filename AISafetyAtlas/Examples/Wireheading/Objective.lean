module

public import AISafetyAtlas.Wireheading.Objective
-- `norm_num` does not resolve through this file's atlas-only import chain: the
-- goals below are `(2 : ℝ) = 1 + 1` and `3 * 2 = 6`, which it closes instantly
-- under a direct Mathlib import and not at all without one. Same module-system
-- exposure gap recorded in STATE.md for `Fintype (Fin 4 × Fin 4)`.
public import Mathlib.Tactic.NormNum

/-!
# The congruence lemma, at the cheapest possible objective

`optimal_decisions_congr` is record congruence: its proof never unfolds
`value`. Grounding it needs nothing but an objective to be congruent with
itself -- the smallest witness that is not vacuous in its own type.
-/

namespace AISafetyAtlas.Examples.Wireheading.Objective

open AISafetyAtlas.Wireheading

/-- The constant-zero objective on the one-point history type. -/
public def trivialObjective : Objective Unit where
  utility := fun _ => 0
  horizon := fun _ _ => 0

/-- **The congruence lemma, at an objective congruent with itself.** Both
sides of the conclusion are then the same set by `rfl`, but they are reached
through the theorem's own hypotheses rather than assumed. -/
public theorem trivialObjective_optimal_decisions_congr :
    {d : Unit | trivialObjective.IsOptimal (fun _ _ => ()) Set.univ 0 0 d} =
      {d : Unit | trivialObjective.IsOptimal (fun _ _ => ()) Set.univ 0 0 d} :=
  Objective.optimal_decisions_congr trivialObjective trivialObjective rfl rfl
    (fun _ _ => ()) Set.univ 0 0

/-! ## `value_congr`, at two objectives that are not the same term

Witnessing a congruence lemma by handing it one object twice and `rfl` proves
only that the statement elaborates: the conclusion is then `rfl` as well, and the
lemma's hypotheses carry nothing. The pair below is written two different ways,
so `utility_eq` and `horizon_eq` are proved rather than assumed, and the value
they agree on is a non-zero sum.
-/

/-- Reward `1` for `true`, `0` for `false`, over a two-step horizon. -/
@[expose] public def payTrue : Objective Bool where
  utility := fun b => if b then 1 else 0
  horizon := fun _ _ => 2

/-- The same objective, written so that neither field is syntactically the
other's. -/
@[expose] public def payTrue' : Objective Bool where
  utility := fun b => if b then 0 + 1 else 1 - 1
  horizon := fun _ _ => 1 + 1

public theorem payTrue_utility_eq : payTrue.utility = payTrue'.utility := by
  funext b; cases b <;> simp [payTrue, payTrue']

public theorem payTrue_horizon_eq : payTrue.horizon = payTrue'.horizon := by
  funext a b; simp only [payTrue, payTrue']; norm_num

/-- **`value_congr`, applied.** -/
public theorem payTrue_value_congr (start duration : ℕ) (trajectory : ℕ → Bool) :
    payTrue.value start duration trajectory = payTrue'.value start duration trajectory :=
  Objective.value_congr payTrue payTrue' payTrue_utility_eq payTrue_horizon_eq
    start duration trajectory

/-- The value the two agree on is `6`, not `0`, so the congruence is transporting
a real number across a real equality of records. -/
public theorem payTrue_value_eq_six : payTrue.value 0 3 (fun _ => true) = 6 := by
  simp only [Objective.value, payTrue]
  norm_num

end AISafetyAtlas.Examples.Wireheading.Objective
