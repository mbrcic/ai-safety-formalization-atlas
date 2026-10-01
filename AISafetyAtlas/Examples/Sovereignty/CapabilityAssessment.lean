module

public import AISafetyAtlas.Sovereignty.CapabilityAssessment
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Two states an observer of finished work cannot tell apart

`AISafetyAtlas.Sovereignty.CapabilityAssessment` states everything at a ring
with two distinct elements. A ring can be trivial, in which case `x ≠ y` is
uninhabited and every conditional below says nothing, so this module fixes `ℤ`
and exhibits the states.

## The setting

A state is a pair: what the person can do unaided, and what is borrowed from the
assistance. Two states are compared throughout.

* `competent = (10, 0)` — full unaided capability, nothing borrowed.
* `dependent = (4, 6)` — capability at `4`, six points borrowed.

They produce **the same finished work**, `10`, and differ by more than half in
the quantity anyone cares about. That is `assessment_cannot_separate`, and it is
the whole obstruction at one pair.

* `withdrawal_separates_them` — taking the assistance away distinguishes them at
  once. This is the measurement the obstruction forces.
* `no_rubric_separates_them` — and no score computed from finished work does, at
  any level of sophistication, because it reads the same `10` in both cases.
* `sophistication_does_not_help` — including a rubric with unbounded range: the
  obstruction is in the evidence, not in the instrument's resolution.

`output_can_rise_while_capability_falls` makes the direction explicit: between
two states the observed work goes *up* while unaided capability goes *down*, so
an output-based programme is not merely uninformative but can read the trend
backwards.
-/

namespace AISafetyAtlas.Examples.Sovereignty.CapabilityAssessment

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Sovereignty.CapabilityAssessment

/-- A state: unaided capability, and what is borrowed. -/
public abbrev State := ℤ × ℤ

/-- Full unaided capability, nothing borrowed. -/
@[expose] public def competent : State := (10, 0)

/-- Much less unaided capability, the difference borrowed. -/
@[expose] public def dependent : State := (4, 6)

/-- **The finished work is identical.** -/
public theorem assessment_cannot_separate :
    outputProtocol ℤ competent = outputProtocol ℤ dependent := by
  decide

/-- **And the capability is not.** More than half of it is gone. -/
public theorem capability_differs :
    withdrawalProtocol ℤ competent ≠ withdrawalProtocol ℤ dependent := by
  decide

/-- **Withdrawal testing separates them**, which is the content of
`withdrawal_recovers_fallback` at this pair: the protocol reads the quantity, so
of course it distinguishes states that differ in it. -/
public theorem withdrawal_separates_them :
    Knowable (withdrawalProtocol ℤ) (fallbackCapability (R := ℤ)) ∧
      withdrawalProtocol ℤ competent ≠ withdrawalProtocol ℤ dependent :=
  ⟨withdrawal_recovers_fallback ℤ, capability_differs⟩

/-- Two distinct integers, which is what the conditionals in the layer-3 module
need and what a trivial ring would not supply. -/
public theorem four_ne_ten : (4 : ℤ) ≠ 10 := by decide

/-- **No score computed from finished work recovers unaided capability.**
`rubric` is arbitrary. -/
public theorem no_rubric_separates_them {K : Sort*} (rubric : ℤ → K) :
    ¬ Knowable (fun state : State => rubric (outputProtocol ℤ state))
      (fallbackCapability (R := ℤ)) :=
  no_procedure_on_output_recovers_fallback four_ne_ten rubric

/-- **Resolution is not the problem.** Even a rubric whose range is all of `ℤ`
-- the identity -- fails, because it is reading the same number in both states.
-/
public theorem sophistication_does_not_help :
    ¬ Knowable (fun state : State => id (outputProtocol ℤ state))
      (fallbackCapability (R := ℤ)) :=
  no_rubric_separates_them id

/-- **The two protocols are incomparable at `ℤ`.** Neither is a refinement of the
other, so no amount of one earns partial credit toward the other. -/
public theorem protocols_incomparable_at_int :
    ¬ Determines (outputProtocol ℤ) (withdrawalProtocol ℤ) ∧
      ¬ Determines (withdrawalProtocol ℤ) (outputProtocol ℤ) :=
  protocols_are_incomparable four_ne_ten

/-- **The observable can move the wrong way.** There are two states whose
finished work strictly rises while unaided capability strictly falls, so a
programme reading output does not merely fail to measure the decline -- it can
report an improvement. -/
public theorem output_can_rise_while_capability_falls :
    ∃ s t : ℤ × ℤ,
      assistedOutput s < assistedOutput t ∧
        fallbackCapability t < fallbackCapability s :=
  exists_output_rise_with_fallback_fall (by decide : (4 : ℤ) < 10)

/-- **Both halves at one pair.** The cheap protocol reads `10` in a state with
capability `10` and in a state with capability `4`; the expensive one tells them
apart. That is the argument that withdrawal testing is forced. -/
public theorem withdrawal_forced_at_this_pair {K : Sort*} (rubric : ℤ → K) :
    Knowable (withdrawalProtocol ℤ) (fallbackCapability (R := ℤ)) ∧
      ¬ Knowable (fun state : State => rubric (outputProtocol ℤ state))
        (fallbackCapability (R := ℤ)) :=
  withdrawal_settles_and_no_output_procedure_does four_ne_ten rubric

end AISafetyAtlas.Examples.Sovereignty.CapabilityAssessment
