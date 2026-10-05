module

public import AISafetyAtlas.Learning

/-!
# Two learners that differ, and a loss that cannot tell them apart

`ots_error_distribution_learner_indep` and `homogeneous_iff_learner_indep` are
Wolpert's supervised no-free-lunch in its distributional form: at a homogeneous
loss, the off-training-set error distribution does not depend on which learner
produced it. Neither had been run, so the hypotheses had never been met at a
pair of learners and the conclusion had never been read at one.

**Read at a single learner the statement would be an identity.** Both theorems
compare two learners, and applying either at `A = B` gives a sum equal to
itself. `learners_differ` is therefore the load-bearing half here: the two
learners below disagree on every input, and the theorems still say their error
distributions coincide.

The model is the smallest one with an off-training-set point at all — two
inputs, one of them trained on, Boolean labels, 0-1 loss, which
`homogeneous_zeroOne` already shows is homogeneous.

## A note on the spelling

The statements below are `def`s with their types inferred rather than theorems
with their conclusions restated, and `linter.defProp` is off for the same reason
it is off in `AISafetyAtlas.Examples.Learning.Sharp`. Restating the conclusion
spells `Fintype (Dom → Lab)` and the decidability of `x ∈ train` a second time,
and the instances a restatement picks are not the ones the theorem's own
statement carries — `Classical.propDecidable` on one side against a hand-written
`DecidablePred` on the other. Letting the applied term supply its type keeps the
two spellings the same term.
-/

set_option linter.defProp false

namespace AISafetyAtlas.Examples.Learning

open AISafetyAtlas.Learning

/-- Two inputs. -/
public abbrev Dom : Type := Fin 2

/-- Two labels. -/
public abbrev Lab : Type := Bool

/-- The training set is the first input, so the second is off-training-set and
the comparison below is about something. -/
@[expose] public def train : Set Dom := {0}

/-- A learner that always predicts `true`, whatever it was shown. -/
@[expose] public noncomputable def alwaysTrue : SupervisedLearner Dom Lab train :=
  fun _ _ => true

/-- A learner that always predicts `false`. -/
@[expose] public noncomputable def alwaysFalse : SupervisedLearner Dom Lab train :=
  fun _ _ => false

/-- **They are different learners**, and they disagree everywhere. Without this
the two theorems below would be comparing a sum with itself. -/
public theorem learners_differ : alwaysTrue ≠ alwaysFalse := by
  intro h
  have hval := congrFun (congrFun h (fun _ => true)) 0
  simp [alwaysTrue, alwaysFalse] at hval

/-- They disagree at the off-training-set point in particular, which is the only
point the loss below is summed over. -/
public theorem learners_differ_off_training (f : Dom → Lab) :
    predict alwaysTrue f 1 ≠ predict alwaysFalse f 1 := by
  simp [predict, alwaysTrue, alwaysFalse]

/--
**The off-training-set error distribution is the same for both**, at 0-1 loss.

Wolpert's scalar form: for every value `v`, as many targets give one learner
total loss `v` as give the other. The two learners agree nowhere, and the
distribution of their errors is identical.
-/
public def ots_distribution_agrees (v : ℝ) :=
  ots_error_distribution_learner_indep homogeneous_zeroOne train alwaysTrue alwaysFalse v

/--
**And the tight form: homogeneity is exactly learner-independence.**

`homogeneous_iff_learner_indep` is an equivalence, so it needs a loss and a
point off the training set. 0-1 loss and the second input supply both.
-/
public def homogeneous_iff_at_zeroOne :=
  homogeneous_iff_learner_indep (fun a y : Lab => if a = y then (0 : ℝ) else 1) train 1
    (by simp [train])

/-- The forward direction read off at 0-1 loss: every functional of the
off-training-set loss configuration sums the same over targets, whichever
learner produced it. -/
public def learner_indep_of_zeroOne :=
  homogeneous_iff_at_zeroOne.mp homogeneous_zeroOne

end AISafetyAtlas.Examples.Learning
