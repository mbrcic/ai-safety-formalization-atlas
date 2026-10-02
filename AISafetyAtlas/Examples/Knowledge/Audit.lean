module

public import AISafetyAtlas.Knowledge.Audit
public import Mathlib.Order.Nat

/-!
# An audit that certifies what it audited and nothing about what ships

`AISafetyAtlas.Knowledge.Audit` states Open Problem 63's obstruction
conditionally: *given* a pair of deployments the audit cannot separate, the audit
does not determine what is deployed. A conditional whose antecedent nothing
satisfies says nothing, so this module inhabits it.

## The setup

Two times — the audit, then the deployment. Two worlds, differing only in whether
the operator swapped the model after the auditor left. The audit reads the system
as it stands at audit time, and the swap happens afterwards, so the audit's
report is the same in both worlds while the deployed version differs.

This is the smallest instance of the gap and deliberately so: nothing here is an
argument that real audits are uninformative. The audit's report being blind to the swap is the
reason the collision exists, and it is a *modelling choice* — an audit whose
evidence included a signed hash of the deployed weights would not have it.
-/

namespace AISafetyAtlas.Examples.Knowledge.Audit

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Knowledge.Audit

/-- The two times: `0` is the audit, `1` is the deployment after it. -/
public abbrev Stage := Nat

/-- The two worlds: `false` is "the audited model shipped", `true` is "the
operator swapped it afterwards". -/
public abbrev World := Bool

/-- The two model versions. -/
public abbrev Version := Bool

/--
**The audit that reads the system and leaves.** Its report is the version
standing at audit time, which is the audited version in both worlds; the
deployed version is the audited one unless the operator swapped it.
-/
@[expose] public def swapAfterAudit : AuditSetup World Stage (fun _ ↦ Version) Version where
  report := fun _ _ ↦ false
  version := fun t ω ↦ if t = 0 then false else ω

/-- The audit determines what it audited: at audit time the version is `false`
in both worlds, so the constant decoder works. -/
public theorem swapAfterAudit_knows_audited :
    Temporal.KnowableFrom swapAfterAudit.report swapAfterAudit.version 0 0 :=
  ⟨fun _ ↦ false, fun _ ↦ rfl⟩

/-- **And it cannot separate the two deployments.** The report is the same in
both worlds and the deployed version is not. -/
public theorem swapAfterAudit_collides :
    ∃ ω ω' : World, swapAfterAudit.report 0 ω = swapAfterAudit.report 0 ω' ∧
      swapAfterAudit.version 1 ω ≠ swapAfterAudit.version 1 ω' :=
  ⟨false, true, rfl, by decide⟩

/-- **Open Problem 63 at a witness.** The audit certifies the audited version and
is silent about the deployed one, with both halves proved of the same setup. -/
public theorem swapAfterAudit_certifies_audited_not_deployed :
    Temporal.KnowableFrom swapAfterAudit.report swapAfterAudit.version 0 0 ∧
      ¬ Temporal.KnowableFrom swapAfterAudit.report swapAfterAudit.version 0 1 :=
  audit_certifies_audited_not_deployed swapAfterAudit
    swapAfterAudit_knows_audited swapAfterAudit_collides

/-- This audit never forgets: its report does not depend on when it was taken. -/
public theorem swapAfterAudit_evidenceMonotone :
    Temporal.EvidenceMonotone swapAfterAudit.report :=
  fun _ _ _ ↦ ⟨id, fun _ ↦ rfl⟩

/-- The collision, in the `CollisionAt` vocabulary the second theorem takes. -/
public theorem swapAfterAudit_collisionAt :
    Temporal.CollisionAt swapAfterAudit.report swapAfterAudit.version 1 :=
  ⟨false, true, rfl, by decide⟩

/-- **Re-auditing later does not close the gap**, at the same witness: the later
audit still determines the audited version, and the deployment time stays
unknowable from its own evidence. -/
public theorem swapAfterAudit_later_audit_does_not_close_the_gap :
    Temporal.KnowableFrom swapAfterAudit.report swapAfterAudit.version 1 0 ∧
      ¬ Temporal.KnowableAt swapAfterAudit.report swapAfterAudit.version 1 :=
  later_audit_does_not_close_the_gap swapAfterAudit
    swapAfterAudit_evidenceMonotone (Nat.zero_le 1)
    swapAfterAudit_knows_audited swapAfterAudit_collisionAt

end AISafetyAtlas.Examples.Knowledge.Audit
