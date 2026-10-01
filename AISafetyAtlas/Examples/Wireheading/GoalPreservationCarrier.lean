module

public import AISafetyAtlas.Wireheading.GoalPreservationCarrier

/-!
# Goal preservation at a model that has something to preserve

The only model of `GoalPreservation.Model` in the tree collapsed history,
action and policy name to `Unit`. Everything held there and nothing was said:
one candidate makes `OptimalAt` vacuous, one target makes `names_surjective`
free, and a constant-zero continuation makes the Bellman identity `0 = 0`.

`GoalPreservationCarrier.scheduleModel` is the model with none of those
collapses, and this file runs it at one bit. The agent may act or not act;
acting is worth one and not acting is worth nothing; the discount is a half, so
the schedule that always acts is worth two and the schedule that never acts is
worth nothing. `not_optimal_of_never_act` is that gap stated as a theorem --
without it, "optimality propagates" would again be a claim about a set with one
element in it.
-/

namespace AISafetyAtlas.Examples.Wireheading.GoalPreservationCarrier

open AISafetyAtlas.Wireheading.GoalPreservation

/-- One bit of action: act, or do not. -/
@[expose] public def bitUtility : Bool → ℝ := fun a => if a then 1 else 0

/-- The observation reports the action, so the history records what was done. -/
@[expose] public def bitObs : Bool → Bool := id

/-- The utility is bounded by one, which is what makes the discounted return
converge. -/
public theorem bitUtility_bounded (a : Bool) : |bitUtility a| ≤ 1 := by
  cases a <;> simp [bitUtility]

/-- **The model**: histories are the `Decision` carrier's, policy names are
schedules, and the continuation is a real discounted return at discount one
half. -/
@[expose] public noncomputable def bitModel :
    Model (AISafetyAtlas.Decision.History Bool Bool) Bool (Schedule Bool) :=
  scheduleModel bitObs bitUtility (d := 1 / 2) (by norm_num) (by norm_num)
    bitUtility_bounded

/-- The starting history: nothing has happened yet. -/
@[expose] public def start : AISafetyAtlas.Decision.History Bool Bool := (false, [])

/-! ## The model is not degenerate

Both halves matter. Without the first, `OptimalAt` would be a statement about a
one-element candidate set; without the second, the discounted return would not
be telling the two schedules apart.
-/

/-- The schedule that never acts is worth nothing. -/
public theorem scheduleValue_never :
    scheduleValue bitUtility (1 / 2) (fun _ => false) = 0 := by
  simp [scheduleValue, bitUtility]

/-- The schedule that always acts is worth two. -/
public theorem scheduleValue_always :
    scheduleValue bitUtility (1 / 2) (fun _ => true) = 2 := by
  rw [scheduleValue]
  simp only [bitUtility, if_pos, mul_one]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- **So the two schedules are told apart**, and by the continuation rather than
by their names. -/
public theorem scheduleValue_never_lt_always :
    scheduleValue bitUtility (1 / 2) (fun _ => false)
      < scheduleValue bitUtility (1 / 2) (fun _ => true) := by
  rw [scheduleValue_never, scheduleValue_always]; norm_num

/-- **And the candidate set has more than one thing in it.** Doing nothing
forever is strictly worse than acting forever, so optimality below is a choice
and not a tautology. -/
public theorem not_optimal_of_never_act :
    ¬ bitModel.OptimalAt (fun _ => false) start := by
  intro hopt
  have h := hopt (true, fun _ => true)
  rw [Model.qValue, Model.qValue] at h
  simp only [bitModel, scheduleModel, scheduleAct, bitUtility, if_pos,
    if_neg Bool.false_ne_true] at h
  rw [scheduleValue_always, scheduleValue_never] at h
  norm_num at h

/-! ## Goal preservation, at that model -/

/-- **Always acting is optimal at every history.** Discharged from the
domination lemma, not from there being one candidate. -/
public theorem bitModel_optimalAt (h : AISafetyAtlas.Decision.History Bool Bool) :
    bitModel.OptimalAt (fun _ => true) h :=
  scheduleModel_optimalAt bitObs bitUtility (d := 1 / 2) (by norm_num) (by norm_num)
    bitUtility_bounded (best := true) (fun a => by cases a <;> simp [bitUtility]) h

/-- **Optimality propagates along the self-modification path.** -/
public theorem bitModel_run_optimal (steps : ℕ) :
    bitModel.OptimalAt (bitModel.run steps (fun _ => true) start).1
      (bitModel.run steps (fun _ => true) start).2 :=
  Model.run_optimal bitModel (fun _ => true) start bitModel_optimalAt steps

/--
**Goal preservation, at a model with a goal to preserve.** At every reached
history the self-modified policy and the initial one obtain the same value under
the fixed initial objective -- and by `not_optimal_of_never_act` that is a claim
about a model in which some policies are worse than others.
-/
public theorem bitModel_goal_preservation (steps : ℕ) :
    bitModel.qValue (bitModel.run steps (fun _ => true) start).2
        (bitModel.act (bitModel.run steps (fun _ => true) start).1
          (bitModel.run steps (fun _ => true) start).2)
      = bitModel.qValue (bitModel.run steps (fun _ => true) start).2
        (bitModel.act (fun _ => true) (bitModel.run steps (fun _ => true) start).2) :=
  Model.goal_preservation bitModel (fun _ => true) start bitModel_optimalAt steps

/-- **A step lengthens the history**, so the run really moves along the
`Decision` carrier rather than standing still on a one-element type. -/
public theorem bitModel_step_length (h : AISafetyAtlas.Decision.History Bool Bool)
    (a : Bool) : (stepHistory bitObs h a).2.length = h.2.length + 1 :=
  length_stepHistory bitObs h a

/-- **And every successor is named**, which is `names_surjective` exhibited
rather than assumed. -/
public theorem bitModel_names_surjective (c : Bool × Schedule Bool) :
    ∃ p : Schedule Bool, scheduleAct p start = c :=
  scheduleAct_surjective start c

/-- The Bellman identity the continuation satisfies, at the always-acting
schedule: two is one plus half of two. -/
public theorem bitModel_coherent_always :
    scheduleValue bitUtility (1 / 2) (fun _ => true)
      = bitUtility true + (1 / 2) * scheduleValue bitUtility (1 / 2) (fun _ => true) :=
  scheduleValue_bellman bitUtility (by norm_num) (by norm_num) bitUtility_bounded
    (fun _ => true)

end AISafetyAtlas.Examples.Wireheading.GoalPreservationCarrier
