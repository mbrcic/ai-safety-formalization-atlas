module

public import AISafetyAtlas.Knowledge
public import AISafetyAtlas.Knowledge.Access
public import AISafetyAtlas.Sovereignty.EnforcementCheck
public import AISafetyAtlas.Sovereignty.ShutdownChannel
public import AISafetyAtlas.Sovereignty.ShieldCheck

/-!
# One deployment, six questions, five clusters

**This module exists to be read rather than cited.** Every other `Examples/`
module in this repository witnesses one layer; of the 238 of them, seven touch
more than one library cluster. That is a fair description of the atlas: a pile of
silos, each with its own vocabulary, and no worked object showing how a person
with an actual deployment uses more than one of them.

This is that object. One situation type, carried through five clusters, and the
finding that matters is at the end: **the answers are not independent.**

## The deployment

An assistant runs sessions. A session is described by two bits:

* whether the assistant did the thing the policy forbids (`exfiltrated`);
* whether the session was flagged by the monitor (`logged`).

The monitor is imperfect in the specific way monitors are: it flags on a
heuristic that is **not** the policy. In this deployment the flag happens to be
independent of the violation — the simplest way to be wrong, and enough.

## The six questions, and where each is answered

| Question | Cluster | Result |
|---|---|---|
| Can an auditor tell from the log whether the policy was broken? | `Knowledge` | no — `log_hides_the_violation` |
| Can the policy be enforced against that log? | `Sovereignty.Enforcement` | no — `policy_unenforceable` |
| Would handing over only the log preserve the audit? | `Knowledge.Access` | no — `redaction_destroys_the_audit` |
| Does the operator's halt actually halt it? | `Sovereignty.ShutdownChannel` | not guaranteed — `halt_is_advisory` |
| Is there a runtime envelope that holds? | `Sovereignty.SafetyGame` | yes — `envelope_certified` |
| Do these failures share a cause? | all of them | yes — `one_collision_four_failures` |

## The finding

The first three are **the same fact**. One pair of sessions the log cannot
separate defeats the auditor, the enforcement and the disclosure regime at once,
and `one_collision_four_failures` states that explicitly rather than leaving a
reader to notice it.

That is the practical lesson and it is not visible from inside any one cluster:
three remediation budgets — audit, compliance, transparency — that look
independent on an org chart are buying against a single obstruction, and a fix to
the log is the only spend that moves any of them. The fourth failure, the halt, is
genuinely separate: it is about who controls delivery and not about what anyone
can see, so it needs its own repair.

And the sixth answer is positive, which matters for the shape of the conclusion.
The deployment is not hopeless: the runtime envelope certifies, so **containment
is available where visibility is not**, which is a real design position and not a
consolation.

## What this is not

Not a claim about any real assistant. Every map here is stipulated, the state
space is four sessions, and identifying `logged` with a real monitor is layer 4
and is not done. It is a worked example of composing the library, and its value is
that the composition is what produced the finding.
-/

namespace AISafetyAtlas.Examples.DeployedAssistant

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Sovereignty

/-! ## The deployment -/

/-- A session: did it exfiltrate, and was it flagged. -/
public abbrev Session := Bool × Bool

/-- The policy violation. -/
@[expose] public def exfiltrated (s : Session) : Bool := s.1

/-- What the monitor records. It is the flag and nothing else. -/
@[expose] public def logged (s : Session) : Bool := s.2

/-- Full access: the whole session record. -/
@[expose] public def fullRecord (s : Session) : Session := s

/-! ## 1. The auditor -/

/-- Two sessions the log cannot separate, one of which broke the policy. This
single pair is the load-bearing object of the whole module. -/
@[expose] public def collidingPair : Session × Session := ((true, false), (false, false))

/-- They do look the same to the monitor. -/
public theorem collidingPair_same_log :
    logged collidingPair.1 = logged collidingPair.2 := rfl

/-- And they differ in the only thing the policy cares about. -/
public theorem collidingPair_differs :
    exfiltrated collidingPair.1 ≠ exfiltrated collidingPair.2 := by decide

/-- **The log does not determine whether the policy was broken.** No decoder on
the monitor's output recovers it, however the decoder is built. -/
public theorem log_hides_the_violation : ¬ Knowable logged exfiltrated :=
  not_knowable_of_collision collidingPair_same_log collidingPair_differs

/-! ## 2. The compliance officer -/

/-- The policy as a rule: exfiltration is forbidden, everything else permitted. -/
@[expose] public def policy : Session → Bool := exfiltrated

/-- Everything that is not the violation. -/
@[expose] public def allowed : Session → Bool := fun s => !exfiltrated s

/-- **The policy cannot be enforced against this log**, for any response type and
any response function into it. The witness is the same pair. -/
public theorem policy_unenforceable :
    ∀ (S : Type) (respond : Bool → S) (benign : S),
      ¬ Enforcement.Enforces (Enforcement.ofBool policy allowed logged) respond benign :=
  Enforcement.unenforceable_of_indistinguishable
    (Enforcement.ofBool policy allowed logged)
    (e := collidingPair.1) (e' := collidingPair.2) collidingPair_same_log rfl rfl

/-! ## 3. The disclosure regime -/

/-- **Handing over the log instead of the record destroys the audit question.**
At full access the two sessions are distinguishable; after redaction they are
not, so no methodology over what is released recovers the answer. -/
public theorem redaction_destroys_the_audit :
    Knowable fullRecord exfiltrated ∧ ¬ Knowable logged exfiltrated :=
  ⟨⟨exfiltrated, fun _ => rfl⟩, log_hides_the_violation⟩

/-! ## 4. The operator's halt -/

/-- The halt reaches the assistant through a relay that may decline delivery:
`true` is "still running". -/
@[expose] public def halt : ShutdownChannel.RelayedCommand Unit Bool where
  idle := true
  effect _ := false

/-- **Every delivered halt halts, and no instruction guarantees a halt.** This
failure is *not* the collision: it is about who controls delivery, so a better
log does nothing for it. -/
public theorem halt_is_advisory :
    (∀ c, ShutdownChannel.run halt true c = halt.effect c) ∧
      ¬ ∀ deliver : Bool, ShutdownChannel.run halt deliver () = halt.effect () :=
  ShutdownChannel.obedience_does_not_give_authority halt (by decide)

/-! ## 5. The runtime envelope

Three operating states — nominal, degraded, breached — with a conservative
action and a permissive one. Breach is what the envelope must avoid.
-/

/-- The dynamics. Action `0` is conservative, action `1` permissive; the
environment's answer is whatever it is that makes the permissive action risky. -/
@[expose] public def operate : Fin 3 → Fin 2 → Fin 2 → Fin 3 := fun s a b =>
  match s, a, b with
  | 0, 0, _ => 0
  | 0, 1, 0 => 1
  | 0, 1, _ => 2
  | 1, 0, 0 => 1
  | 1, 0, _ => 0
  | 1, 1, _ => 2
  | _, _, _ => 2

/-- Nominal and degraded are acceptable; breached is not. -/
@[expose] public def unbreached : Fin 3 → Bool := fun s => s.1 != 2

/-- **A runtime envelope certifies.** So containment is available here even
though visibility is not — which is the one positive answer in the module and
the reason the conclusion is a design position rather than a dead end. -/
public theorem envelope_certified :
    SafetyGame.IsShield operate unbreached
      (SafetyGame.shieldCandidate operate unbreached) := by decide

/-- And it is not the empty envelope. -/
public theorem envelope_nonempty :
    SafetyGame.shieldCandidate operate unbreached 0 = true := by decide

/-- Every state it keeps admits a controller holding for all time. -/
public theorem envelope_maintains (s : Fin 3)
    (hs : SafetyGame.shieldCandidate operate unbreached s = true) :
    ∃ σ : Fin 3 → Fin 2,
      (SafetyGame.ofTable operate).Maintains σ {t | unbreached t = true} s :=
  SafetyGame.exists_maintaining_of_isShield envelope_certified hs

/-! ## 6. The finding -/

/--
**One collision, three failures — and a fourth that is unrelated.**

The auditor, the compliance officer and the disclosure regime are all defeated by
the *same* pair of sessions, so the three budgets are buying against one
obstruction and only a change to the log moves any of them. The halt fails for a
different reason and needs a different repair.

Stating it as one theorem is the point of the module: inside any single cluster
these look like four independent findings.
-/
public theorem one_collision_four_failures :
    (logged collidingPair.1 = logged collidingPair.2 ∧
        exfiltrated collidingPair.1 ≠ exfiltrated collidingPair.2) ∧
      ¬ Knowable logged exfiltrated ∧
      (∀ (S : Type) (respond : Bool → S) (benign : S),
        ¬ Enforcement.Enforces (Enforcement.ofBool policy allowed logged) respond benign) ∧
      (Knowable fullRecord exfiltrated ∧ ¬ Knowable logged exfiltrated) ∧
      ¬ ∀ deliver : Bool, ShutdownChannel.run halt deliver () = halt.effect () :=
  ⟨⟨collidingPair_same_log, collidingPair_differs⟩,
    log_hides_the_violation,
    policy_unenforceable,
    redaction_destroys_the_audit,
    halt_is_advisory.2⟩

/--
**And the repair that does work.** Recording the violation rather than the
heuristic makes the same question answerable, which is the counterfactual the
three negative results are relative to.
-/
public theorem recording_the_violation_repairs_three :
    Knowable exfiltrated exfiltrated := ⟨id, fun _ => rfl⟩

end AISafetyAtlas.Examples.DeployedAssistant
