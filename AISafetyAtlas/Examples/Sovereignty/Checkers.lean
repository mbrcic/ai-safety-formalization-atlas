module

public import AISafetyAtlas.Sovereignty.EnforcementCheck
public import AISafetyAtlas.Sovereignty.ShieldCheck

/-!
# The two new checkers, run

`EnforcementCheck` and `ShieldCheck` are the executable halves of two bridges,
and both have a positive branch that returns an artifact rather than a verdict.
A checker whose positive branch is never exercised is a checker nobody has seen
succeed, so both branches of both are run here at concrete models.

* `leakyLog` is a rule against an act the log does not record: the search returns
  the pair, and no response function of any type enforces it.
* `sharpLog` is the same rule under a log that records the act, and the search
  returns **the monitoring rule**, proved to sanction exactly the forbidden acts.
* `drift` is a two-state envelope with a leaky action and a holding one. The
  certificate keeps both safe states, and `exists_maintaining_of_isShield` turns
  that into a controller that holds for all time.
* `doomed` is a system with no envelope at all, which is the branch that shows
  the checker is not vacuously generous.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Checkers

open AISafetyAtlas.Sovereignty

/-! ## Enforcement -/

/-- Four acts. The log records only the second bit, and the forbidden act shares
its log entry with a permitted one. -/
@[expose] public def leakyLog : Fin 4 → Nat := fun e => if e.1 < 2 then 0 else 1

/-- Act `0` is the violation. -/
@[expose] public def forbiddenAct : Fin 4 → Bool := fun e => e.1 == 0

/-- Everything else is allowed. -/
@[expose] public def permittedAct : Fin 4 → Bool := fun e => e.1 != 0

/-- **The search finds the pair**, so the rule binds nothing. -/
public theorem leakyLog_unenforceable :
    ∀ (S : Type) (respond : Nat → S) (benign : S),
      ¬ Enforcement.Enforces
          (Enforcement.ofBool forbiddenAct permittedAct leakyLog) respond benign :=
  Enforcement.not_enforces_of_findUnenforceable_eq_some
    (enum := List.finRange 4) (p := (0, 1)) (by decide)

/-- A log that records the act itself. -/
@[expose] public def sharpLog : Fin 4 → Nat := fun e => e.1

/-- **And under that log the search returns a rule that works.** The positive
branch is constructive: this is the monitor, not a verdict about monitors. -/
public theorem sharpLog_enforced :
    Enforcement.Enforces
      (Enforcement.ofBool forbiddenAct permittedAct sharpLog)
      (Enforcement.sanctionOf (List.finRange 4) sharpLog forbiddenAct) false :=
  Enforcement.enforces_sanctionOf_of_findUnenforceable_eq_none
    (fun e => List.mem_finRange e) (by decide)

/-! ## Shield -/

/-- Three states, two actions, two answers. State `2` is unsafe; action `0`
holds, action `1` drifts towards it. -/
@[expose] public def drift : Fin 3 → Fin 2 → Fin 2 → Fin 3 := fun s a b =>
  match s, a, b with
  | 0, 0, _ => 0
  | 0, 1, 0 => 1
  | 0, 1, _ => 2
  | 1, 0, 0 => 1
  | 1, 0, _ => 0
  | 1, 1, _ => 2
  | _, _, _ => 2

/-- The safe set: everything but state `2`. -/
@[expose] public def driftSafe : Fin 3 → Bool := fun s => s.1 != 2

/-- **The candidate checks**, so it is a genuine certificate. -/
public theorem drift_isShield :
    SafetyGame.IsShield drift driftSafe (SafetyGame.shieldCandidate drift driftSafe) := by
  decide

/-- **And therefore every state it keeps admits a controller that holds
forever**, which is the operational content rather than the lattice one. -/
public theorem drift_maintains (s : Fin 3)
    (hs : SafetyGame.shieldCandidate drift driftSafe s = true) :
    ∃ σ : Fin 3 → Fin 2,
      (SafetyGame.ofTable drift).Maintains σ {t | driftSafe t = true} s :=
  SafetyGame.exists_maintaining_of_isShield drift_isShield hs

/-- The envelope is not empty: state `0` survives. -/
public theorem drift_keeps_zero :
    SafetyGame.shieldCandidate drift driftSafe 0 = true := by decide

/-- A system the environment can always push out of the safe set. -/
@[expose] public def doomed : Fin 2 → Fin 1 → Fin 2 → Fin 2 := fun _ _ b =>
  if b.1 = 0 then 0 else 1

/-- The safe set is the single state `0`. -/
@[expose] public def doomedSafe : Fin 2 → Bool := fun s => s.1 == 0

/-- **The envelope is empty**, so the checker does refuse when it should. Without
this the certified branch above would be evidence of nothing. -/
public theorem doomed_envelope_empty :
    ∀ s, SafetyGame.shieldCandidate doomed doomedSafe s = false := by decide

end AISafetyAtlas.Examples.Sovereignty.Checkers
