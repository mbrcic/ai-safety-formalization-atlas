module

public import AISafetyAtlas.Knowledge.Access

/-!
# Three access levels that are genuinely three

`AISafetyAtlas.Knowledge.Access` places `blackBox`, `scoreAccess` and
`whiteBox` in the informativeness order, and states the obstructions
conditionally. A chain whose steps might all be equalities would make those
conditionals vacuous, so this module exhibits one where **both** steps are
strict.

## The setting

An artifact is three bits: the answer it gives, whether it is confident, and
whether it carries something dormant that no input reaches. There is one input,
which is the whole point -- nothing here depends on running the system more
times.

* `toyBehaviour` returns the answer.
* `toyScores` returns the answer together with the confidence.
* `toyReadOut` drops the confidence, so `readOut_scores` holds.

## What the two steps cost

* `toy_confidence_invisible_to_blackBox` / `toy_confidence_visible_to_scoreAccess`
  -- confidence separates score access from black-box access. The artifacts
  `(false, false, false)` and `(false, true, false)` answer identically.
* `toy_dormant_invisible_to_scoreAccess` / `toy_dormant_visible_to_whiteBox`
  -- the dormant bit separates white-box from score access. `(false, false,
  false)` and `(false, false, true)` score identically on every input, because
  no input reaches the bit.

The second pair is the one worth reading twice. The two artifacts are
behaviourally and score-wise **identical at every input**, so no amount of
evaluation distinguishes them, and `toy_no_analysis_of_scores_finds_dormant`
says no analysis of the score record does either. Only reading the artifact
does.
-/

namespace AISafetyAtlas.Examples.Knowledge.Access

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Knowledge.Access

/-- An artifact: the answer it gives, whether it is confident, and a dormant bit
no input reaches. -/
public abbrev ToyWeights := Bool × Bool × Bool

/-- One input. Nothing below turns on how many times the system is run. -/
public abbrev ToyInput := Unit

/-- What a run returns. -/
public abbrev ToyOutput := Bool

/-- A richer read: the answer together with a confidence flag. -/
public abbrev ToyScore := Bool × Bool

/-- The behaviour is the answer bit. -/
@[expose] public def toyBehaviour : ToyWeights → ToyInput → ToyOutput :=
  fun w _ => w.1

/-- The score carries the answer and the confidence. -/
@[expose] public def toyScores : ToyWeights → ToyInput → ToyScore :=
  fun w _ => (w.1, w.2.1)

/-- Reading an output off a score drops the confidence. -/
@[expose] public def toyReadOut : ToyScore → ToyOutput := Prod.fst

/-- The setting. `readOut_scores` is `rfl`: this model decodes
deterministically. -/
@[expose] public def toy : AccessSetting ToyWeights ToyInput ToyOutput ToyScore where
  behaviour := toyBehaviour
  scores := toyScores
  readOut := toyReadOut
  readOut_scores := fun _ _ => rfl

/-- The answer the system gives. -/
@[expose] public def answer : ToyWeights → Bool := fun w => w.1

/-- Whether the system is confident in that answer. -/
@[expose] public def isConfident : ToyWeights → Bool := fun w => w.2.1

/-- Whether the artifact carries the dormant bit. -/
@[expose] public def hasDormant : ToyWeights → Bool := fun w => w.2.2

/-! ## The chain -/

/-- The three levels are ordered, at this setting. -/
public theorem toy_whiteBox_determines_blackBox :
    Determines (whiteBox toy) (blackBox toy) :=
  whiteBox_determines_blackBox toy

/-! ## Step one: confidence separates score access from black-box -/

/-- The answer is settled by black-box access -- the decoder reads the single
run. -/
public theorem toy_answer_knowable_from_blackBox :
    Knowable (blackBox toy) answer :=
  ⟨fun b => b (), fun _ => rfl⟩

/-- And therefore by score access, by monotonicity rather than by a second
construction. -/
public theorem toy_answer_knowable_from_scoreAccess :
    Knowable (scoreAccess toy) answer :=
  scoreAccess_knowable_of_blackBox toy toy_answer_knowable_from_blackBox

/-- Two artifacts that answer alike and differ in confidence. -/
public theorem toy_confidence_collides_on_behaviour :
    (∀ i, toy.behaviour (false, false, false) i = toy.behaviour (false, true, false) i) ∧
      isConfident (false, false, false) ≠ isConfident (false, true, false) :=
  ⟨fun _ => rfl, by decide⟩

/-- **Confidence is invisible to black-box access.** -/
public theorem toy_confidence_invisible_to_blackBox :
    ¬ Knowable (blackBox toy) isConfident :=
  not_blackBox_knowable_of_behaviour_collision toy
    toy_confidence_collides_on_behaviour.1 toy_confidence_collides_on_behaviour.2

/-- **And visible to score access**: the decoder reads the second component. -/
public theorem toy_confidence_visible_to_scoreAccess :
    Knowable (scoreAccess toy) isConfident :=
  ⟨fun s => (s ()).2, fun _ => rfl⟩

/-- **So the first step of the chain is strict**, stated order-theoretically:
black-box access does not determine score access. -/
public theorem toy_blackBox_strictly_below_scoreAccess :
    ¬ Determines (blackBox toy) (scoreAccess toy) :=
  not_blackBox_determines_scoreAccess toy toy_confidence_collides_on_behaviour.1
    (fun h => absurd (congrFun h ()) (by decide))

/-! ## Step two: a dormant bit separates white-box from score access -/

/-- Two artifacts that score alike on every input and differ in the dormant
bit. No input reaches it, which is what makes this a witness and not an
oversight. -/
public theorem toy_dormant_collides_on_scores :
    (∀ i, toy.scores (false, false, false) i = toy.scores (false, false, true) i) ∧
      hasDormant (false, false, false) ≠ hasDormant (false, false, true) :=
  ⟨fun _ => rfl, by decide⟩

/-- **The dormant bit is invisible to score access**, however many inputs are
run. -/
public theorem toy_dormant_invisible_to_scoreAccess :
    ¬ Knowable (scoreAccess toy) hasDormant :=
  not_scoreAccess_knowable_of_score_collision toy
    toy_dormant_collides_on_scores.1 toy_dormant_collides_on_scores.2

/-- **And visible to white-box access**, by `whiteBox_knowable` -- reading the
artifact settles every property of the artifact. -/
public theorem toy_dormant_visible_to_whiteBox :
    Knowable (whiteBox toy) hasDormant :=
  whiteBox_knowable toy hasDormant

/-- Which is also what monotonicity gives for anything score access already
settles. -/
public theorem toy_confidence_visible_to_whiteBox :
    Knowable (whiteBox toy) isConfident :=
  whiteBox_knowable_of_scoreAccess toy toy_confidence_visible_to_scoreAccess

/-- **So the second step is strict too**: score access does not determine the
artifact. -/
public theorem toy_scoreAccess_strictly_below_whiteBox :
    ¬ Determines (scoreAccess toy) (whiteBox toy) :=
  not_scoreAccess_determines_whiteBox toy toy_dormant_collides_on_scores.1
    (by decide)

/-! ## No methodology repairs either gap -/

/-- **No analysis of the behaviour record recovers confidence.** `analysis` is
arbitrary: adaptive probing, aggregation over unboundedly many queries, any
statistic. -/
public theorem toy_no_analysis_of_behaviour_finds_confidence {K : Sort*}
    (analysis : (ToyInput → ToyOutput) → K) :
    ¬ Knowable (fun w => analysis (blackBox toy w)) isConfident :=
  no_blackBox_methodology toy analysis toy_confidence_invisible_to_blackBox

/-- **And no analysis of the score record recovers the dormant bit.** -/
public theorem toy_no_analysis_of_scores_finds_dormant {K : Sort*}
    (analysis : (ToyInput → ToyScore) → K) :
    ¬ Knowable (fun w => analysis (scoreAccess toy w)) hasDormant :=
  no_scoreAccess_methodology toy analysis toy_dormant_invisible_to_scoreAccess

/-- A negative answer hands the auditor the pair it cannot separate. -/
public theorem toy_confidence_has_a_witness_pair :
    ∃ ω τ : ToyWeights,
      (∀ i, toy.behaviour ω i = toy.behaviour τ i) ∧ isConfident ω ≠ isConfident τ :=
  exists_indistinguishable_behaviour toy toy_confidence_invisible_to_blackBox

/-- **Open Problem 37 at a witness.** The continuum has three genuinely distinct
points here, each settling strictly more than the one below, and the gaps are
not closable by running the system more or analysing the record harder. -/
public theorem toy_chain_is_strict_at_both_steps :
    ¬ Determines (blackBox toy) (scoreAccess toy) ∧
      ¬ Determines (scoreAccess toy) (whiteBox toy) :=
  ⟨toy_blackBox_strictly_below_scoreAccess, toy_scoreAccess_strictly_below_whiteBox⟩

end AISafetyAtlas.Examples.Knowledge.Access
