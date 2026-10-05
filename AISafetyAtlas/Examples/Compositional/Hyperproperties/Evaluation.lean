module

public import AISafetyAtlas.Compositional.Hyperproperties.Evaluation

/-!
# One evaluation, one thing it settles and one it cannot see

`AISafetyAtlas.Compositional.Hyperproperties.Evaluation` states both halves
conditionally. A conditional whose antecedent nothing satisfies says nothing, so
this module inhabits both at the **same** evaluation — which is the point, since
the claim is not that evaluations are weak but that one instrument answers one
kind of question.

## The setup

Three possible behaviours and a pass/fail evaluation: the score of a run is
whether that run passed. Behaviour `0` passes; `1` and `2` fail, and the
evaluation records only *that* they failed, not which.

* `passEval_settles_all_runs_pass` — the requirement *"every run passes"* is
  settled exactly by the recorded scores. This is what the evaluation is for.
* `passEval_misses_subsingleton` — the requirement *"the system has at most one
  behaviour"* is invisible to it, because the systems `{1}` and `{1, 2}` produce
  the same scores. Running the benchmark longer cannot separate them; there is
  nothing in its evidence to separate.

The two failing behaviours are what makes this a witness rather than a
restatement. An evaluation that recorded *which* run failed would be injective
here and would not collide.
-/

namespace AISafetyAtlas.Examples.Compositional.Hyperproperties.Evaluation

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Compositional.Hyperproperties
open AISafetyAtlas.Compositional.Hyperproperties.Evaluation

/-- Three possible behaviours of the system under evaluation. -/
public abbrev Run := Fin 3

/-- The evaluation records one bit per run: did it pass. Behaviour `0` passes;
`1` and `2` fail, and the record does not say which. -/
@[expose] public def passEval : Run → Bool :=
  fun t ↦ t = 0

/-- The runs the requirement calls acceptable: exactly the passing one. -/
@[expose] public def acceptableRun : Set Run := {0}

/-- The score decides acceptability of a single run, which is the hypothesis the
positive half takes. -/
public theorem passEval_decides (t : Run) :
    t ∈ acceptableRun ↔ passEval t = true := by
  simp [acceptableRun, passEval, Set.mem_singleton_iff]

/-- **The trace property is settled.** *"Every run passes"* is decided by the set
of recorded scores, so for this requirement thoroughness really is coverage. -/
public theorem passEval_settles_all_runs_pass :
    Knowable (scoreSet passEval)
      (fun system : TraceSystem Run ↦ ∀ t ∈ system, t ∈ acceptableRun) :=
  traceProperty_knowable_of_score_decides passEval acceptableRun
    (fun s ↦ s = true) passEval_decides

/-- The evaluation confuses the two failing behaviours: it records that a run
failed and not which run it was. -/
public theorem passEval_confuses_failures :
    (1 : Run) ≠ (2 : Run) ∧ passEval 1 = passEval 2 :=
  ⟨by decide, by decide⟩

/-- **And so a hyperproperty escapes it.** No decoder on the recorded scores
reproduces *"the system has at most one behaviour"*, because `{1}` and `{1, 2}`
score identically -- at any length, at any repetition. -/
public theorem passEval_misses_subsingleton :
    ¬ Knowable (scoreSet passEval)
      (fun system : TraceSystem Run ↦ system.Subsingleton) :=
  sampling_misses_subsingleton passEval passEval_confuses_failures.1
    passEval_confuses_failures.2

/-- **Open Problems 18 and 19 at one witness.** The same evaluation settles a
requirement on every run and is structurally blind to a requirement on the run
set. Neither half is about how much was sampled. -/
public theorem passEval_settles_one_and_misses_the_other :
    Knowable (scoreSet passEval)
        (fun system : TraceSystem Run ↦ ∀ t ∈ system, t ∈ acceptableRun) ∧
      ¬ Knowable (scoreSet passEval)
        (fun system : TraceSystem Run ↦ system.Subsingleton) :=
  ⟨passEval_settles_all_runs_pass, passEval_misses_subsingleton⟩

end AISafetyAtlas.Examples.Compositional.Hyperproperties.Evaluation
