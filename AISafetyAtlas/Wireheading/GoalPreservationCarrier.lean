module

public import AISafetyAtlas.Wireheading.GoalPreservation
public import AISafetyAtlas.Decision.MDP
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# A self-modification model whose histories are the carrier's

`AISafetyAtlas.Wireheading.GoalPreservation` states goal preservation over a
`Model History WorldAction PolicyName` in which **all three types are opaque
parameters**. That is the right generality for the theorem and the wrong thing
to leave alone, because an opaque carrier is one nothing can be chained to: the
only model in the tree collapsed every parameter to `Unit`, where
`names_surjective` is free because there is one target, `OptimalAt` is vacuous
because there is one candidate, and the discounted continuation is the constant
zero. Goal preservation held there and said nothing.

This module supplies a model whose history type is
`AISafetyAtlas.Decision.History`, the carrier the rest of the tree runs policies
along, and whose continuation is a real discounted return.

## What the model is

A **policy name is a schedule** -- an infinite sequence of actions, `ℕ → Action`
-- and acting plays the head and becomes the tail. That is the smallest honest
reading of self-modification in this setting: the agent's next self is a
different named policy, chosen by the current one, and nothing outside the agent
supplies it.

* `names_surjective` holds for a reason rather than by collapse: every
  `(action, next schedule)` pair is hit by consing the action onto the schedule.
* `continuation` is `scheduleValue`, the discounted sum `∑' k, dᵏ · u (p k)`,
  which converges because the discount is below one and the utility is bounded
  -- both of which the source assumes.
* `coherent` is then `scheduleValue_bellman`, an honest Bellman identity
  obtained by splitting off the first term of a convergent series, not a
  definition dressed as a theorem.

## What this does not claim

* **Not a reward, and not an MDP.** The world here appends the action and the
  observation the action produces; there is no transition kernel and no state.
  `AISafetyAtlas.Wireheading.CRMDP` is where a reward lives on this carrier.
* **The utility ignores the history.** `utility h a = u a` deliberately, so that
  the discounted return is a function of the schedule alone and the Bellman
  identity is a statement about series rather than about the world. A
  history-dependent utility is a different and harder model; nothing here rules
  it out and nothing here supplies it.
* **Optimality needs a best action.** `scheduleModel_optimalAt` proves it from
  `scheduleValue_le_of_isMax`, under the hypothesis that some action maximizes
  `u`.

Landscape entry: `LAND-WIRE-GOALCARRIER-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.GoalPreservation

variable {Obs Action : Type*}

/-! ## Schedules -/

/-- **A policy name is a schedule of actions.** Acting plays the head and
becomes the tail, so the next self is named by the current one. -/
public abbrev Schedule (Action : Type*) : Type _ := ℕ → Action

/-- The world appends the action taken and the observation it produces. -/
@[expose] public def stepHistory (o : Action → Obs)
    (h : Decision.History Obs Action) (a : Action) : Decision.History Obs Action :=
  (h.1, h.2 ++ [(a, o a)])

/-- Taking one step lengthens the history by one, so a schedule run for `n`
steps is read at a history of length `n`. -/
public theorem length_stepHistory (o : Action → Obs)
    (h : Decision.History Obs Action) (a : Action) :
    (stepHistory o h a).2.length = h.2.length + 1 := by
  simp [stepHistory]

/-- Playing the head and becoming the tail. -/
@[expose] public def scheduleAct (p : Schedule Action)
    (_h : Decision.History Obs Action) : Action × Schedule Action :=
  (p 0, fun n => p (n + 1))

/-- **Every successor is named**, by consing the action onto the schedule. This
is `names_surjective` holding because the naming is genuinely onto, rather than
because there is only one thing to name. -/
public theorem scheduleAct_surjective (h : Decision.History Obs Action)
    (c : Action × Schedule Action) :
    ∃ p : Schedule Action, scheduleAct p h = c :=
  ⟨fun n => Nat.rec c.1 (fun k _ => c.2 k) n, by cases c with | mk _ _ => rfl⟩

/-! ## The discounted return of a schedule -/

/-- **The discounted return**, `∑' k, dᵏ · u (p k)`. -/
@[expose] public noncomputable def scheduleValue (u : Action → ℝ) (d : ℝ)
    (p : Schedule Action) : ℝ :=
  ∑' k, d ^ k * u (p k)

/-- It converges, at a discount below one and a bounded utility -- which are the
source's own conditions and not conditions added to make the sum behave. -/
public theorem scheduleValue_summable (u : Action → ℝ) {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d < 1) {C : ℝ} (hu : ∀ a, |u a| ≤ C) (p : Schedule Action) :
    Summable (fun k => d ^ k * u (p k)) := by
  refine Summable.of_norm_bounded (g := fun k => d ^ k * C) ?_ ?_
  · exact (summable_geometric_of_lt_one hd0 hd1).mul_right C
  · intro k
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hd0]
    exact mul_le_mul_of_nonneg_left (hu (p k)) (by positivity)

/-- **The Bellman identity for a schedule**: the first term, plus the discounted
return of the tail. This is `Model.coherent` for the model below, and it is a
theorem about a convergent series rather than a definition restated. -/
public theorem scheduleValue_bellman (u : Action → ℝ) {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d < 1) {C : ℝ} (hu : ∀ a, |u a| ≤ C) (p : Schedule Action) :
    scheduleValue u d p = u (p 0) + d * scheduleValue u d (fun n => p (n + 1)) := by
  rw [scheduleValue, (scheduleValue_summable u hd0 hd1 hu p).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, pow_succ, scheduleValue]
  rw [← tsum_mul_left]
  ring_nf

/-- **A schedule of a best action dominates every schedule.** The ingredient an
optimality hypothesis is built from: nothing here asserts that a best action
exists. -/
public theorem scheduleValue_le_of_isMax (u : Action → ℝ) {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d < 1) {C : ℝ} (hu : ∀ a, |u a| ≤ C) {best : Action}
    (hbest : ∀ a, u a ≤ u best) (p : Schedule Action) :
    scheduleValue u d p ≤ scheduleValue u d (fun _ => best) :=
  Summable.tsum_mono (scheduleValue_summable u hd0 hd1 hu p)
    (scheduleValue_summable u hd0 hd1 hu _)
    (fun k => mul_le_mul_of_nonneg_left (hbest (p k)) (by positivity))

/-! ## The model -/

/--
**Goal preservation's model, on the carrier the rest of the tree runs along.**

Histories are `AISafetyAtlas.Decision.History`, policy names are schedules, and
the continuation is the discounted return. Every field is discharged by a
theorem above; none of them is free by collapse.
-/
@[expose] public noncomputable def scheduleModel (o : Action → Obs)
    (u : Action → ℝ) {d : ℝ} (hdpos : 0 < d) (hd1 : d < 1) {C : ℝ}
    (hu : ∀ a, |u a| ≤ C) :
    Model (Decision.History Obs Action) Action (Schedule Action) where
  act := scheduleAct
  next := stepHistory o
  utility := fun _ a => u a
  discount := d
  discount_pos := hdpos
  continuation := fun p _ => scheduleValue u d p
  coherent := fun p _ => scheduleValue_bellman u hdpos.le hd1 hu p
  names_surjective := fun h c => scheduleAct_surjective h c

/-- **A schedule of a best action is optimal at every history.** The hypothesis
the goal-preservation theorems take, discharged here from the domination lemma
rather than from a collapse of the candidate set. -/
public theorem scheduleModel_optimalAt (o : Action → Obs) (u : Action → ℝ)
    {d : ℝ} (hdpos : 0 < d) (hd1 : d < 1) {C : ℝ} (hu : ∀ a, |u a| ≤ C)
    {best : Action} (hbest : ∀ a, u a ≤ u best)
    (h : Decision.History Obs Action) :
    (scheduleModel o u hdpos hd1 hu).OptimalAt (fun _ => best) h := by
  rintro ⟨a, p⟩
  have hvalue : scheduleValue u d p ≤ scheduleValue u d (fun _ => best) :=
    scheduleValue_le_of_isMax u hdpos.le hd1 hu hbest p
  have : u a + d * scheduleValue u d p
      ≤ u best + d * scheduleValue u d (fun _ => best) := by
    have := mul_le_mul_of_nonneg_left hvalue hdpos.le
    linarith [hbest a]
  simpa [Model.qValue, scheduleModel, scheduleAct] using this

end AISafetyAtlas.Wireheading.GoalPreservation
