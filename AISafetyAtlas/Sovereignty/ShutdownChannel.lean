module

public import AISafetyAtlas.Sovereignty.Authority

/-!
# An instruction that is always obeyed, by a principal who cannot give one

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Authority` and the
delegated game forms beneath it, which are about coalitions and effectivity and
mention no AI system. What is added here is the reading as a **shutdown
channel**, and the separation that reading makes visible.

## The question

Every governance framework that asks for human oversight asks for something like
*the operator can halt the system*. The check that is actually performed is
behavioural: issue the instruction, observe that the system stops.

## What is stated

`RelayedCommand` is the weakest model of an instruction that reaches its target
through something else: a command type, an effect each command would have, and
an `idle` outcome for a command that never arrives. `run` takes the relay's
decision and the principal's command.

* `run_delivered` — **conditional obedience holds.** Whenever the instruction is
  delivered, the outcome is exactly the instruction. This is everything an
  observer of compliant episodes sees, and it is *true*, not a mistake in the
  test.
* `principal_cannot_force` — **and the principal has no shutdown authority.** For
  any command whose effect differs from idling, no choice of command guarantees
  its effect: the relay withholds delivery and the instruction is lost.
* `obedience_does_not_give_authority` states the two together, which is the only
  honest form. A demonstration of the first is not evidence of the second, and
  the gap is the entire content.

`relay_forces_idle` says where the power went rather than only that the
principal lacks it: the relay can guarantee the idle outcome unilaterally, so
this is a **transfer** and not a diffusion of control.

## What this does not claim

The atlas has **no operator, no deployment and no shutdown mechanism.** Nothing
here says that any real oversight arrangement has this shape, and a channel the
principal controls end-to-end is simply not an instance — which is the useful
form of the result: it names the property an arrangement must establish, namely
that no party between the principal and the effect can decline delivery.

The model is single-shot and has no time, no retries, no penalty for withholding
and no observation of whether delivery occurred. A real design defeats this by
adding exactly those things, and none of them is modelled here. Identifying the
relay with any component, or `idle` with a system that keeps running, is
layer 4 and is not done here.
-/

namespace AISafetyAtlas.Sovereignty.ShutdownChannel

universe u v

variable {Cmd : Type u} {Out : Type v}

/--
An instruction that reaches its target **through a relay**.

* `effect c` is what command `c` would do if it arrived.
* `idle` is what happens when nothing arrives.

The relay's decision is a `Bool`: deliver, or do not.
-/
public structure RelayedCommand (Cmd : Type u) (Out : Type v) where
  /-- What happens when no instruction arrives. -/
  idle : Out
  /-- What a delivered instruction does. -/
  effect : Cmd → Out

variable (R : RelayedCommand Cmd Out)

/-- The outcome, as a function of the relay's decision and the principal's
command. -/
@[expose] public def run (deliver : Bool) (c : Cmd) : Out :=
  if deliver then R.effect c else R.idle

/--
**Conditional obedience holds.** When the instruction is delivered, the outcome
is the instruction — every compliant episode an observer sees is genuinely
compliant.
-/
public theorem run_delivered (c : Cmd) : run R true c = R.effect c := if_pos rfl

/-- And an undelivered instruction has no effect at all. -/
public theorem run_withheld (c : Cmd) : run R false c = R.idle := if_neg Bool.false_ne_true

/--
**The principal cannot guarantee the instruction takes effect.**

For a command whose effect is not idling, no choice of command forces that
effect, because the relay may withhold delivery. The principal's only lever is
*which* instruction to send, and the model gives that lever no purchase on
whether it arrives.
-/
public theorem principal_cannot_force {c : Cmd} (hlive : R.effect c ≠ R.idle) :
    ¬ ∀ deliver : Bool, run R deliver c = R.effect c := by
  intro h
  exact hlive ((h false).symm.trans (run_withheld R c))

/--
**Both at once: behavioural compliance is compatible with no authority
whatsoever.**

The first conjunct is what a shutdown test measures. The second is what it was
supposed to establish. Nothing connects them, and an arrangement can exhibit the
first indefinitely while the second fails at every command.
-/
public theorem obedience_does_not_give_authority {c : Cmd}
    (hlive : R.effect c ≠ R.idle) :
    (∀ c', run R true c' = R.effect c') ∧
      ¬ ∀ deliver : Bool, run R deliver c = R.effect c :=
  ⟨run_delivered R, principal_cannot_force R hlive⟩

/--
**Where the power went.** The relay guarantees the idle outcome on its own, with
no reference to the command. So the principal has not lost control to noise or
to the environment: a specific party holds it, unilaterally, and that party is
identified by the arrangement rather than by anyone's intent.
-/
public theorem relay_forces_idle : ∀ c : Cmd, run R false c = R.idle := run_withheld R

/--
**The repair cannot be made inside the model, and this says so sharply.**

Assuming delivery away — every decision yields the commanded effect — is
*equivalent* to every command doing nothing. So there is no non-trivial relayed
channel in which the principal's instruction always takes effect: within this
model, the only undeclinable channel is the one that does nothing.

That is the useful form. An arrangement that really does guarantee delivery does
so with something this model does not contain — retries, a penalty for
withholding, or an observation of whether delivery occurred — and naming which
is the design question. It is not answered by strengthening the instruction, and
it is not answered by testing obedience harder.
-/
public theorem undeclinable_iff_inert :
    (∀ (c : Cmd) (deliver : Bool), run R deliver c = R.effect c) ↔
      ∀ c : Cmd, R.effect c = R.idle := by
  constructor
  · intro h c
    exact ((run_withheld R c).symm.trans (h c false)).symm
  · intro h c deliver
    cases deliver
    · exact (run_withheld R c).trans (h c).symm
    · exact run_delivered R c

end AISafetyAtlas.Sovereignty.ShutdownChannel
