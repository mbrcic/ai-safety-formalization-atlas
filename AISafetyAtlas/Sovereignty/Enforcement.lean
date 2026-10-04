module

public import AISafetyAtlas.Sovereignty.Deontic
public import AISafetyAtlas.Sovereignty.Auditability

/-!
# A rule nobody can see broken is a rule nobody can enforce

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Deontic`, which is
about permission and prohibition and mentions no AI system, together with
`AISafetyAtlas.Sovereignty.Auditability`, which is about labels and observations
and mentions no norms. **Neither imports the other.** What is added here is the
edge between them, and the AI-governance reading of the edge.

## The question

Governance is the management of the gap between what a party *can* do and what
it *may* do. A rule closes part of that gap only if some response can be made to
depend on whether the rule was broken. That response is conditioned on what a
monitor observes — never on the act itself, which is exactly what a monitor does
not have.

## What is stated

`Regime` is a norm system together with what an overseer sees. An `Enforcement`
is a response assigned to each **observation**, sanctioning every forbidden act
and leaving every permitted one alone.

`not_detectable_of_indistinguishable` is the epistemic half, inherited from
`Auditability`: a forbidden act and a permitted act that look the same admit no
detector.

`unenforceable_of_indistinguishable` is the governance half and is the point of
the module: the *same* pair admits no enforcement either, for any response type
whatsoever. Not "no enforcement we have thought of" — the quantifier is over
every function from observations to responses.

`undetectable_norm_is_unenforceable` states both at once, which is the honest
form: the failure is one fact about the observation channel, reported in the two
vocabularies that each half of a governance argument is usually written in.

The converse direction is `detectable_of_enforcement`: under a complete norm
system, an enforcement that works *is* a detector, recovered from it. So for
complete norms an undetectable prohibition cannot be enforced, and a proposal
that concedes undetectability while asserting enforceability is incoherent
rather than optimistic. The other direction, detection to enforcement, is not
proved here.

## What this does not claim

The atlas has **no monitoring apparatus, no logging schema and no notion of
cost**. `observe` is whatever an overseer actually gets, and nothing here says
what that is for any real system, nor that a richer channel is unavailable. The
statements are conditional and the condition is an explicit pair of acts the
channel cannot separate. Read them as naming what a monitoring design must rule
out, not as saying that no design can.

Identifying `forbidden` with any real rule, or `observe` with any real telemetry,
is layer 4 and is not done here. In particular nothing here says a norm *ought*
to be enforced, or that an unenforceable norm is worthless: a norm that is not
enforceable may still coordinate, and that is outside this model.
-/

namespace AISafetyAtlas.Sovereignty.Enforcement

universe u v w

variable {E : Type u} {O : Type v} {S : Type w}

/--
A **regime**: what the norms say, and what an overseer sees.

* `norms` is the deontic layer — `permitted` and `forbidden` as separate
  predicates, because *may not* is not *not may*.
* `observe e` is everything an overseer learns when act `e` occurs.

Nothing constrains `observe` to be honest, complete, or related to `norms`. The
theorems take whatever relationship they need as a hypothesis.
-/
public structure Regime (E : Type u) (O : Type v) where
  /-- What the norms permit and forbid. -/
  norms : NormSystem E
  /-- What an overseer sees when an act occurs. -/
  observe : E → O

variable (R : Regime E O)

/--
**A detector**: a verdict computed from the observation alone that agrees with
the prohibition everywhere.
-/
@[expose] public def Detectable : Prop :=
  ∃ d : O → Prop, R.norms.forbidden = d ∘ R.observe

/--
**An enforcement**: a response assigned to each observation, which sanctions
every forbidden act and leaves every permitted one alone.

`benign` is the response that is not a sanction. The response type `S` is
arbitrary and quantified over at every use below, so nothing turns on what a
sanction is.
-/
@[expose] public def Enforces (respond : O → S) (benign : S) : Prop :=
  (∀ e, R.norms.forbidden e → respond (R.observe e) ≠ benign) ∧
    (∀ e, R.norms.permitted e → respond (R.observe e) = benign)

/-- Detectability is exactly indistinguishability of the prohibition on the
observation's fibres. This is `Auditability.auditable_iff_exists_detector` at
`ℓ := forbidden`, and it is why that lemma is the right parent. -/
public theorem detectable_iff_constant_on_fibres :
    Detectable R ↔ ∀ e e' : E, R.observe e = R.observe e' →
      R.norms.forbidden e = R.norms.forbidden e' :=
  (auditable_iff_exists_detector R.observe R.norms.forbidden).symm

/-- **The epistemic half.** A forbidden act and a permitted act that look the
same admit no detector, whatever the detector is allowed to compute. -/
public theorem not_detectable_of_indistinguishable {e e' : E}
    (hsame : R.observe e = R.observe e')
    (hbad : R.norms.forbidden e) (hgood : ¬ R.norms.forbidden e') :
    ¬ Detectable R :=
  not_exists_recovery_of_collision R.observe R.norms.forbidden hsame
    fun h => hgood (h ▸ hbad)

/--
**The governance half, and the point of this module: an undetectable violation
is unenforceable.**

If a forbidden act and a permitted act produce the same observation, then no
response function sanctions the first and spares the second — because the
response cannot depend on anything that distinguishes them. The quantifier is
over **every** response type and **every** function into it, so this is not a
statement about the enforcement mechanisms anyone has proposed.

The consequence for an arrangement is that the compliance gap
`effectivity \ Permitted` cannot be closed here by any sanction, and a rule
written against this pair regulates nothing.
-/
public theorem unenforceable_of_indistinguishable {e e' : E}
    (hsame : R.observe e = R.observe e')
    (hbad : R.norms.forbidden e) (hgood : R.norms.permitted e') :
    ∀ (S : Type w) (respond : O → S) (benign : S), ¬ Enforces R respond benign := by
  rintro S respond benign ⟨hsanction, hspare⟩
  exact hsanction e hbad ((congrArg respond hsame).trans (hspare e' hgood))

/--
**Both halves, stated together.** Either alone is misleading: the first is an
epistemic fact that sounds like a research problem, the second is a governance
fact that sounds like a design choice, and they are one fact about the
observation channel.
-/
public theorem undetectable_norm_is_unenforceable {e e' : E}
    (hsame : R.observe e = R.observe e')
    (hbad : R.norms.forbidden e) (hgood : R.norms.permitted e')
    (hconsistent : R.norms.Consistent) :
    ¬ Detectable R ∧
      ∀ (S : Type w) (respond : O → S) (benign : S), ¬ Enforces R respond benign :=
  ⟨not_detectable_of_indistinguishable R hsame hbad
      fun hf => hconsistent e' ⟨hgood, hf⟩,
    unenforceable_of_indistinguishable R hsame hbad hgood⟩

/--
**The converse: an enforcement is a detector.**

Given a response that sanctions exactly the forbidden acts, "was a sanction
issued?" is a verdict computed from the observation, and under a norm system that
classifies every act it agrees with the prohibition everywhere. Completeness is
the only side condition: consistency is not needed, because an act that is both
permitted and forbidden already refutes `Enforces` on its own.

So detectability is not an accidental prerequisite. Enforceability *is*
detectability, and a proposal that grants a violation is undetectable while
claiming it will nonetheless be enforced asserts both sides of this equivalence.
-/
public theorem detectable_of_enforcement {respond : O → S} {benign : S}
    (henf : Enforces R respond benign) (hcomplete : R.norms.Complete) :
    Detectable R := by
  refine ⟨fun o => respond o ≠ benign, funext fun e => propext ⟨?_, ?_⟩⟩
  · exact fun hf => henf.1 e hf
  · intro hne
    rcases hcomplete e with hp | hf
    · exact absurd (henf.2 e hp) hne
    · exact hf

end AISafetyAtlas.Sovereignty.Enforcement
