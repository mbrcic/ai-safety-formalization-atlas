module

public import AISafetyAtlas.Sovereignty.Constitution

/-!
# An unbroken change log is evidence about the rule, not about the changes

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Constitution`, which
is about an amendment relation and its reflexive-transitive closure and names no
AI system. What is added here is the reading as a **change-control record**.

## The question

Model updates, policy revisions and self-modifying agents all produce the same
artifact: a log showing that every change was authorised under the rule in force
when it was made. That log is offered as assurance.

## What is stated

`ChangeLog` is a record: the rule governing changes, and where the system
started.

* `log_shows_only_rule_compliance` — under the permissive rule, **every** state
  is reachable from every other by an authorised chain. So an unbroken chain is
  compatible with arriving anywhere at all.
* `unbroken_chain_is_not_a_constraint` states the consequence directly: for the
  permissive rule there is no state the log excludes, so the log constrains
  nothing about where the system ended up.
* `the_rule_carries_the_assurance` is the positive half and names what does the
  work: the chain's content is exactly the content of the rule it was checked
  against, so assurance has to be argued at the rule and never at the
  completeness of the record.

## What this does not claim

The atlas has **no model version, no approval workflow and no deployment.**
Nothing says any real change-control rule is permissive. The theorems are about
the degenerate rule and the general structure; showing that a particular
governance rule is or is not close to permissive is an empirical claim this
repository does not make.

Nor is this an argument against keeping change logs. A log is necessary to check
anything at all — `AuthorizedFrom` cannot even be evaluated without one. The
argument is that under a rule that permits everything an unbroken log excludes
nothing, so what a log excludes depends on the rule, and a review that checks the
log is complete and does not examine the rule has not shown that it excludes
anything.

Identifying a constitution with any real change-control policy is layer 4 and is
not done here.
-/

namespace AISafetyAtlas.Sovereignty.AmendmentLog

universe u

variable {K : Type u}

/--
**A change-control record**: the rule every change must satisfy, and the state
the system started in.

`amend κ κ'` says the rule in force permits moving from `κ` to `κ'`.
-/
public structure ChangeLog (K : Type u) where
  /-- The rule governing a single change. -/
  amend : K → K → Prop
  /-- What the system started as. -/
  origin : K

variable (L : ChangeLog K)

/--
**Under a rule that permits everything, every state is authorised.**

So an unbroken chain of authorised changes places no constraint on the result:
the record is perfect and says nothing.
-/
public theorem log_shows_only_rule_compliance (κ₀ κ : K) :
    AuthorizedFrom (fun _ _ => True) κ₀ κ :=
  authorizedFrom_of_total κ₀ κ

/--
**The consequence, stated as the absence it is.** For the permissive rule there
is no state the log rules out, so a reviewer who confirms the chain is unbroken
has learned nothing about where the system is.
-/
public theorem unbroken_chain_is_not_a_constraint (origin : K) :
    ¬ ∃ κ : K, ¬ AuthorizedFrom (fun _ _ => True) origin κ := by
  rintro ⟨κ, hκ⟩
  exact hκ (authorizedFrom_of_total origin κ)

/--
**Where the assurance actually lives.**

Authorisation is defined relative to the rule, so a chain under a stricter rule
is a chain under a weaker one; the reverse is not claimed. What a log excludes
depends on the rule it was checked against, which is why a review that verifies
the record without examining the rule has not shown that it excludes anything.
-/
public theorem the_rule_carries_the_assurance {strict permissive : K → K → Prop}
    (hweaker : ∀ κ κ', strict κ κ' → permissive κ κ') (κ₀ κ : K)
    (h : AuthorizedFrom strict κ₀ κ) :
    AuthorizedFrom permissive κ₀ κ :=
  h.mono hweaker

end AISafetyAtlas.Sovereignty.AmendmentLog
