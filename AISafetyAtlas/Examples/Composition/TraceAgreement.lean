module

public import AISafetyAtlas.Composition.Rectangularity
public import Mathlib.Data.Fin.VecNotation

/-!
# Witness W2 — two-trace agreement (hyperproperty boundary)

A *single* component produces a Boolean output trace (`Unit → Bool`). The
agreement property — two executions produce the same output — relates **two
executions**, so the product here is indexed by the *execution* (`Fin 2`),
not by agents: the global object is `Fin 2 → (Unit → Bool)`, two runs of a
one-agent system.

The pairs `(false, false)` and `(true, true)` agree; splicing one run across
pairs yields `(false, true)`, which does not. By
`not_independent_of_failed_splice` (applied along the execution index), the
agreement property is not expressible by independent per-execution
predicates.

## Why the typing matters

Component scope (how many agents a property mentions) and trace arity (how
many executions it compares) are **independent axes**. Witness W1
(`SharedBudget`) is scope 2, arity 1; this witness is scope 1, arity 2. The
types carry the distinction: here the product index is the execution, and
the "local state" is an entire one-agent trace. We do *not* claim that
scope arity equals `k`-safety — the axes are distinct.

## Interpretation

- Mathematical: the same rectangularity machinery applies along the
  execution index; agreement (the core of observational determinism /
  noninterference-style 2-safety) is non-rectangular there.
- AI-safety: properties that compare runs (determinism, noninterference,
  privacy-by-composition) cannot be checked by any per-run predicate —
  a certified instance of the hyperproperty boundary of local contracts.
- Non-claim: this does not formalize noninterference for any real system;
  it pins the minimal two-point core of the boundary.
-/

namespace AISafetyAtlas.Examples.Composition.TraceAgreement

open AISafetyAtlas.Composition

/-- Two executions of a one-agent Boolean trace agree on their output. -/
@[expose] public def Agreement : Set (GlobalState (Fin 2) fun _ => Unit → Bool) :=
  {t | t 0 () = t 1 ()}

/-- Both runs output `false`: agreement holds. -/
public theorem both_false_mem : ![fun _ => false, fun _ => false] ∈ Agreement := rfl

/-- Both runs output `true`: agreement holds. -/
public theorem both_true_mem : ![fun _ => true, fun _ => true] ∈ Agreement := rfl

/-- Splicing run 1 of the second pair into the first breaks agreement. -/
public theorem splice_notMem :
    Function.update ![fun _ => false, fun _ => false] 1
      (![fun _ => true, fun _ => true] 1) ∉ Agreement := by
  intro h
  have h' : false = true := h
  exact Bool.noConfusion h'

/--
Two-trace agreement is not expressible by independent per-execution
predicates: the failed splice along the execution index certifies
non-rectangularity — the hyperproperty boundary in its minimal form.
-/
public theorem agreement_not_independentlyExpressible :
    ¬ IndependentlyExpressible Agreement :=
  not_independent_of_failed_splice both_false_mem both_true_mem splice_notMem

end AISafetyAtlas.Examples.Composition.TraceAgreement
