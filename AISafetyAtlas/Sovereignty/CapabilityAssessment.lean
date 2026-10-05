module

public import AISafetyAtlas.Sovereignty.Capability

/-!
# Measuring what a person can do unaided: two protocols, and neither substitutes

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four
layers: *(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Capability`, which
holds a sum decomposition and the fact that a sum does not determine its
summands. What is added here is the arrow to a measurement question about
cognitive offloading, stated over the two protocols actually used to answer it.

## The question

The *International AI Safety Report 2026* (chair: Yoshua Bengio; expert panel
nominated by 30+ countries), §2.3.2 *Risks to human autonomy*:

> *"one study found that three months after the introduction of AI support,
> clinicians' ability to detect tumours **without AI assistance** had dropped by
> 6%"*

and the report's own caveat, which travels with every use of it:

> *"research into the relationship between use of AI and cognitive offloading
> and critical thinking is nascent, and further studies supporting these
> findings are warranted."*

*Ability without assistance* is `fallbackCapability`. The measurement question
is how anyone would ever know it.

## The answer this module states

Two protocols observe the same state — a fallback capability together with
whatever is borrowed.

* `outputProtocol` reads the **assisted output**, which is what an observer of
  ordinary work sees.
* `withdrawalProtocol` reads the fallback **directly**, by taking the assistance
  away and testing.

`withdrawal_recovers_fallback` is the positive half and is immediate:
withdrawal testing settles the question, because it observes the quantity.

`no_procedure_on_output_recovers_fallback` is the negative half and is the
reason the positive one matters. Not only does assisted output fail to determine
fallback — *no function of assisted output* determines it. Any statistic,
rubric, satisfaction score, productivity metric or summary computed from what
the assisted person produces is a function of evidence that does not contain the
answer, so it inherits the failure. That is `not_knowable_comp`. It concerns a
single assisted result with nothing known about the borrowed part: designs that
vary tasks, assistance or people, or that bound or measure the borrowed part, are
not modelled here and may well estimate unaided capability.

`protocols_are_incomparable` is the sharp form and the one to read twice.
Neither protocol is more informative than the other. Withdrawal testing is not
"more of" output observation, so assisted work does not determine it — and it is
not strictly better either, since fallback capability does not determine assisted
output. They measure different things, and neither has an exact decoder for the
other.

**So the 6% study is not an instance of the obstruction; it is the expensive way
around it.** The theorems say why withdrawal testing is the measurement the
obstruction forces, rather than a costly option a cheaper design could replace.

## What this module does not claim

**That any deployed system causes cognitive offloading.** Nothing here is
evidence of decline, and the report's caveat above is part of the claim, not a
footnote to it.

**That self-report is covered.** `no_procedure_on_output_recovers_fallback` is a
conditional: it applies to a report *if* that report is a function of assisted
output. Whether a person's self-assessment is such a function is a layer-4
premise — plausible, since someone judging their own competence largely sees
their own finished work, and **not established here**. The empirical literature
on self-report describes a *bias* mechanism; this module describes
*non-invertibility*. They are compatible and they are not the same claim, and
neither follows from the other.

**That decline is affine.** `AffineCapability` and
`maintenanceFloor_of_practice_floor` sit in the same layer-2 module and are
deliberately not used here. That recurrence is, in its own docstring, *"a
selected model, not a law"*; no measured human capability is claimed to satisfy
it, and nothing here predicts, explains or corroborates the 6% figure.

**That any practice policy follows.** No quantity, schedule or intervention is
recommended.

The decomposition `output = fallback + borrowed` is itself a model. A setting in
which assistance and capability do not compose additively is not this one.
-/

namespace AISafetyAtlas.Sovereignty.CapabilityAssessment

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Sovereignty

universe u

/--
**The output protocol**: assess from what the assisted person produces. This is
what an observer of ordinary work has, and what any metric computed from
delivered work is a function of.
-/
@[expose] public def outputProtocol (R : Type u) [Add R] : R × R → R :=
  assistedOutput

/--
**The withdrawal protocol**: take the assistance away and test. This observes
the fallback capability itself, which is the whole of its content and the whole
of its cost.
-/
@[expose] public def withdrawalProtocol (R : Type u) : R × R → R :=
  fallbackCapability

/-! ## Withdrawal testing works -/

/--
**The withdrawal protocol settles the question**, with the identity as its
decoder. There is nothing clever here: the protocol observes the quantity of
interest, which is exactly what makes it expensive.
-/
public theorem withdrawal_recovers_fallback (R : Type u) :
    Knowable (withdrawalProtocol R) (fallbackCapability (R := R)) :=
  ⟨id, fun _ => rfl⟩

/-! ## And nothing computed from assisted work does -/

/--
**No procedure on assisted output recovers fallback capability.**

`report` is arbitrary — a score, a rubric, an aggregate over many tasks, any
summary at all. It is a function of the assisted output, and the assisted output
does not contain the answer, so the summary does not either.

This is `not_knowable_comp` over
`fallback_not_knowable_from_assistedOutput`, and it is the statement that makes
the obstruction structural for this model: the failure is not that output-based
instruments are noisy, but that one assisted result, with the borrowed part
unconstrained, is not identifying. Richer experimental designs are not covered.
-/
public theorem no_procedure_on_output_recovers_fallback {R : Type u} [Ring R]
    {K : Sort*} {x y : R} (hxy : x ≠ y) (report : R → K) :
    ¬ Knowable (fun state : R × R => report (outputProtocol R state))
      (fallbackCapability (R := R)) :=
  not_knowable_comp report (fallback_not_knowable_from_assistedOutput hxy)

/-! ## The two protocols are incomparable -/

/--
**The withdrawal protocol does not determine assisted output.** Knowing what
someone can do unaided says nothing about what they produce with help, because
the borrowed part is free to be anything.
-/
public theorem not_withdrawal_determines_output {R : Type u} [Ring R]
    {x y : R} (hxy : x ≠ y) :
    ¬ Determines (withdrawalProtocol R) (outputProtocol R) := by
  refine not_knowable_of_collision (ω₁ := (0, 0)) (ω₂ := (0, x - y)) rfl ?_
  show (0 : R) + 0 ≠ 0 + (x - y)
  simpa using fun h : (0 : R) = x - y => hxy (sub_eq_zero.mp h.symm)

/--
**And assisted output does not determine the withdrawal protocol**, which is
`fallback_not_knowable_from_assistedOutput` read as a statement about the two
protocols.
-/
public theorem not_output_determines_withdrawal {R : Type u} [Ring R]
    {x y : R} (hxy : x ≠ y) :
    ¬ Determines (outputProtocol R) (withdrawalProtocol R) :=
  fallback_not_knowable_from_assistedOutput hxy

/--
**So the two protocols are incomparable in the informativeness order.**

This is the sharp form of the module. Withdrawal testing is not *more* of what
output observation gives, so no quantity of observed work approaches it, and no
partial credit accrues to a programme that collects only assisted output.
Neither is it strictly better: it says nothing about assisted performance. They
answer different questions, and the expense of the second is not redundancy.
-/
public theorem protocols_are_incomparable {R : Type u} [Ring R]
    {x y : R} (hxy : x ≠ y) :
    ¬ Determines (outputProtocol R) (withdrawalProtocol R) ∧
      ¬ Determines (withdrawalProtocol R) (outputProtocol R) :=
  ⟨not_output_determines_withdrawal hxy, not_withdrawal_determines_output hxy⟩

/--
**Both halves of the measurement question together.** Where the borrowed part is
unconstrained, the protocol that costs something settles it; nothing computed
from the assisted output alone does, at any level of sophistication. A consumer
holding this pair has the argument that some evidence beyond assisted output is
forced; withdrawal testing is one such.
-/
public theorem withdrawal_settles_and_no_output_procedure_does {R : Type u} [Ring R]
    {K : Sort*} {x y : R} (hxy : x ≠ y) (report : R → K) :
    Knowable (withdrawalProtocol R) (fallbackCapability (R := R)) ∧
      ¬ Knowable (fun state : R × R => report (outputProtocol R state))
        (fallbackCapability (R := R)) :=
  ⟨withdrawal_recovers_fallback R, no_procedure_on_output_recovers_fallback hxy report⟩

end AISafetyAtlas.Sovereignty.CapabilityAssessment
