module

public import AISafetyAtlas.Sovereignty.SafetyGame
public import Mathlib.Data.Fintype.Pi

/-!
# Synthesising a runtime shield, and checking the certificate rather than the search

`AISafetyAtlas.Sovereignty.SafetyGame` proves that a state can be held inside a
protected set forever exactly when it lies in the controlled-invariant kernel,
and that any self-closed subset of the protected set lies inside that kernel.
The second half is `subset_safetyKernel`, the Knaster–Tarski direction, and it is
what makes this module cheap.

## The move

A shield synthesiser normally has to prove its fixpoint iteration converges to
the *greatest* invariant. **This does not, and does not need to.** It computes a
candidate by downward iteration, then *checks* two decidable conditions on the
result — the candidate sits inside the protected set, and every state of it has
an action keeping every answer inside the candidate — and
`subset_safetyKernel_of_isShield` turns that check into membership of the kernel.

Checking a certificate is sound whatever produced it. So the iteration is
untrusted: it is a heuristic that proposes, and the theorem disposes.

## What the practitioner gets

Not a verdict. `shieldAction` is **a controller**: one permitted action at every
state of the certificate, and
`exists_maintaining_of_isShield` says each of those states admits a positional
controller that keeps every play inside the protected set for all time, through
`mem_safetyKernel_iff_exists_maintaining`. This is the only artifact in the
checker family that hands back something to install rather than something to
worry about.

## What is not proved, and it matters

**Completeness is not claimed.** Nothing here says the returned set is the
largest invariant. A shield over a smaller set is still a correct shield — it
refuses more often than it must — so an empty or small result is not a finding
that the system cannot be shielded. It is a finding that *this* iteration, run
for this many rounds, did not certify more.

The environment is adversarial by construction: `cpre` quantifies over **every**
answer, so a state is kept only when one action works against all of them. A
model that gives the environment fewer answers than reality gives it will
certify a shield that does not hold.

Identifying `step` with any real dynamics is layer 4 and is not done here.
-/

namespace AISafetyAtlas.Sovereignty.SafetyGame

variable {n m k : ℕ}

/-! ## The game a transition table presents -/

/-- The safety game of a finite transition table. -/
@[expose] public def ofTable (table : Fin n → Fin m → Fin k → Fin n) :
    SafetyGame (Fin n) (Fin m) (Fin k) where
  step := table

/-! ## The untrusted search -/

/-- Does this action keep every answer inside the candidate? -/
@[expose] public def keepsInside (table : Fin n → Fin m → Fin k → Fin n)
    (W : Fin n → Bool) (s : Fin n) (a : Fin m) : Bool :=
  (List.finRange k).all fun b => W (table s a b)

/-- The first action at `s` that keeps every answer inside the candidate. -/
@[expose] public def actionAt (table : Fin n → Fin m → Fin k → Fin n)
    (W : Fin n → Bool) (s : Fin n) : Option (Fin m) :=
  (List.finRange m).find? (keepsInside table W s)

/-- One round of downward iteration: drop every state with no keeping action. -/
@[expose] public def shrink (table : Fin n → Fin m → Fin k → Fin n)
    (W : Fin n → Bool) : Fin n → Bool :=
  fun s => W s && (actionAt table W s).isSome

/--
The candidate, by `n` rounds of downward iteration from the protected set.

Untrusted. Its only job is to propose something `IsShield` can check, and the
round count is a budget rather than a convergence claim.
-/
@[expose] public def shieldCandidate (table : Fin n → Fin m → Fin k → Fin n)
    (V : Fin n → Bool) : Fin n → Bool :=
  (List.range n).foldl (fun W _ => shrink table W) V

/-! ## The certificate, and what checking it buys -/

/--
**A shield certificate**: a set inside the protected set, every state of which
has an action keeping every answer inside the set.
-/
@[expose] public def IsShield (table : Fin n → Fin m → Fin k → Fin n)
    (V W : Fin n → Bool) : Prop :=
  (∀ s, W s = true → V s = true) ∧ ∀ s, W s = true → (actionAt table W s).isSome = true

public instance decidableIsShield (table : Fin n → Fin m → Fin k → Fin n)
    (V W : Fin n → Bool) : Decidable (IsShield table V W) := by
  unfold IsShield
  infer_instance

/-- A state the certificate keeps has an action keeping every answer inside it. -/
public theorem exists_action_of_isShield {table : Fin n → Fin m → Fin k → Fin n}
    {V W : Fin n → Bool} (h : IsShield table V W) {s : Fin n} (hs : W s = true) :
    ∃ a : Fin m, ∀ b : Fin k, W (table s a b) = true := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h.2 s hs)
  refine ⟨a, ?_⟩
  have hkeep : keepsInside table W s a = true := List.find?_some ha
  intro b
  exact List.all_eq_true.mp hkeep b (List.mem_finRange b)

/--
**Checking the certificate places it inside the kernel.**

This is `subset_safetyKernel` — the Knaster–Tarski direction — and it is why the
search above needs no correctness proof: whatever produced `W`, if `W` passes
the two checks then every state of it can be held inside `V` forever.
-/
public theorem subset_safetyKernel_of_isShield
    {table : Fin n → Fin m → Fin k → Fin n} {V W : Fin n → Bool}
    (h : IsShield table V W) :
    {s | W s = true} ⊆ (ofTable table).safetyKernel {s | V s = true} := by
  refine subset_safetyKernel (ofTable table) (fun s hs => h.1 s hs) ?_
  intro s hs
  obtain ⟨a, ha⟩ := exists_action_of_isShield h hs
  exact ⟨a, fun b => ha b⟩

/--
**And therefore each of its states admits a controller that holds forever.**

`mem_safetyKernel_iff_exists_maintaining` is the bridge from membership to a
positional controller, so a checked certificate is a shield in the operational
sense and not only in the lattice-theoretic one.
-/
public theorem exists_maintaining_of_isShield [NeZero m] [NeZero k]
    {table : Fin n → Fin m → Fin k → Fin n} {V W : Fin n → Bool}
    (h : IsShield table V W) {s : Fin n} (hs : W s = true) :
    ∃ σ : Fin n → Fin m, (ofTable table).Maintains σ {s | V s = true} s := by
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩⟩
  exact (mem_safetyKernel_iff_exists_maintaining (ofTable table) _ s).mp
    (subset_safetyKernel_of_isShield h hs)

/-- The controller the certificate carries: the checked action at each of its
states, and an arbitrary action elsewhere. -/
@[expose] public def shieldAction [NeZero m] (table : Fin n → Fin m → Fin k → Fin n)
    (W : Fin n → Bool) (s : Fin n) : Fin m :=
  (actionAt table W s).getD ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

end AISafetyAtlas.Sovereignty.SafetyGame
