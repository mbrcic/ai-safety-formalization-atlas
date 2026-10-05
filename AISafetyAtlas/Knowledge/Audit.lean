module

public import AISafetyAtlas.Knowledge.Temporal

/-!
# What an audit certifies, and what it does not

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Knowledge.Temporal`, which is about
evidence, targets and time and mentions no AI system. What is added here is the
arrow to an AI-governance question, stated over a model of an audit.

## The question

Reuel, Bucknall et al., *Open Problems in Technical AI Governance*, TMLR
04/2025, Open Problem 63:

> *"How can it be verified that the model version on which an evaluation or
> audit was performed is the same as is deployed?"*

## The answer this module states

An audit is evidence gathered at one time about a target at one time, and those
two times need not agree. `audit_certifies_audited_not_deployed` says both halves
at once: the audit determines the version it audited (that half is the
hypothesis `haudited` returned), **and** the same evidence can fail to determine
the version at the deployment time — with the failure certified by an explicit
pair of worlds the audit cannot separate. `T` carries no order, so "later" is the
reading, not part of the statement.

`later_audit_does_not_close_the_gap` is narrower than its name. With cumulative
records, a later audit knows at least what an earlier audit knew about the moment
that audit examined; and where the records at a moment in question collide, an
audit performed *at that moment* cannot tell which version was running. Neither
half concerns a later audit asking about the moment in question: records added
since may well settle it, and nothing here says otherwise.

## What this does not claim

The atlas has **no model registry, no version identity and no attestation**. So
this is not a claim that version verification is impossible in practice: a
deployment that publishes a signed hash of its weights has evidence this model
does not have, and under that evidence the collision may simply not exist. The
statement is conditional, and the condition is `CollisionAt` — *the audit's own
evidence does not separate two deployments*. Read it as naming what an audit
scheme must rule out, not as saying no scheme can.

Identifying `report` with any real auditing methodology, or `version` with a real
model identity, is layer 4 and is not done here.
-/

namespace AISafetyAtlas.Knowledge.Audit

universe u v w y

variable {Ω : Type u} {T : Type v} {I : T → Type w} {V : Type y}

/--
An **audit setup**: what an audit reads, and what is actually deployed.

* `report t` is the evidence an audit performed at time `t` produces. Its type
  may depend on `t`, since an audit at one time and an audit at another need not
  produce commensurable artifacts.
* `version t ω` is the model version actually deployed at time `t` in world `ω`.

`Ω` ranges over the ways the world could be as far as anything here can tell.
Nothing constrains `report` to be honest, complete, or related to `version` at
all; the theorems below take whatever relationship they need as a hypothesis.
-/
public structure AuditSetup (Ω : Type u) (T : Type v) (I : T → Type w)
    (V : Type y) where
  /-- The evidence an audit performed at this time produces. -/
  report : ∀ t : T, Ω → I t
  /-- The model version actually deployed at this time. -/
  version : T → Ω → V

/--
**An audit certifies the version it audited, not the version deployed.**

Both halves are asserted together, because either alone is misleading. The first
is the hypothesis repeated: where it holds, it is what makes an audit worth
performing. The second is Open Problem 63. Only the audit's own records are
considered; records that bind the audited artifact to the running one, such as a
signed hash, are what remove the collision.

The second hypothesis is the whole content: two worlds that the audit's evidence
cannot tell apart, in which the deployed version differs. Given one, no decoder
on audit evidence returns the deployed version, whatever the decoder is allowed
to compute.
-/
public theorem audit_certifies_audited_not_deployed
    (A : AuditSetup Ω T I V) {tAudit tDeploy : T}
    (haudited : Temporal.KnowableFrom A.report A.version tAudit tAudit)
    (hcollide : ∃ ω ω' : Ω, A.report tAudit ω = A.report tAudit ω' ∧
      A.version tDeploy ω ≠ A.version tDeploy ω') :
    Temporal.KnowableFrom A.report A.version tAudit tAudit ∧
      ¬ Temporal.KnowableFrom A.report A.version tAudit tDeploy := by
  refine ⟨haudited, ?_⟩
  obtain ⟨ω, ω', hobs, hne⟩ := hcollide
  exact not_knowable_of_collision hobs hne

/--
**What a later audit keeps, and what an audit at the moment cannot see.**

Under cumulative evidence a later audit determines everything an earlier one did
— that is `knowableFrom_mono`, and it is why re-auditing is not pointless. And
where the records at the moment in question collide, an audit performed at that
moment cannot determine the version running then.

The name overstates it: nothing here concerns a later audit asking about the
moment in question. Records added since that moment may well settle it; only
re-reading that moment's own records gains nothing.
-/
public theorem later_audit_does_not_close_the_gap [Preorder T]
    (A : AuditSetup Ω T I V) {tAudit tLater tDeploy : T}
    (hmono : Temporal.EvidenceMonotone A.report)
    (hle : tAudit ≤ tLater)
    (haudited : Temporal.KnowableFrom A.report A.version tAudit tAudit)
    (hcollide : Temporal.CollisionAt A.report A.version tDeploy) :
    Temporal.KnowableFrom A.report A.version tLater tAudit ∧
      ¬ Temporal.KnowableAt A.report A.version tDeploy :=
  ⟨Temporal.knowableFrom_mono hmono hle haudited,
    Temporal.not_knowableAt_of_collisionAt hcollide⟩

end AISafetyAtlas.Knowledge.Audit
