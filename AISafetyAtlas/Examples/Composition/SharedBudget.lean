module

public import AISafetyAtlas.Composition.Rectangularity
public import Mathlib.Data.Fin.VecNotation

/-!
# Witness W1 — shared-budget failure

Two agents each spend `0` or `1` unit against a shared cap of `1`. The
states `![1, 0]` and `![0, 1]` are individually safe, but splicing agent 1's
expenditure from the second into the first yields `![1, 1]`, which busts the
budget. By `not_independent_of_failed_splice`, no family of independent
per-agent spending predicates characterizes the safe set.

## Interpretation

- Engineering: per-agent spending approval is insufficient unless spending
  is charged against a shared ledger.
- AI-safety: a certified two-agent, single-execution relational safety
  failure — the minimal concrete case of "individually approved actions,
  jointly unsafe".
- Non-claim: nothing about learning, strategic behavior, or how a shared
  ledger should be implemented.
-/

namespace AISafetyAtlas.Examples.Composition.SharedBudget

open AISafetyAtlas.Composition

/-- Two agents each choose an expenditure; the global cap is `1`. -/
public def SafeBudget : Set (GlobalState (Fin 2) fun _ => ℕ) :=
  {x | x 0 + x 1 ≤ 1}

/-- Agent 0 spends the whole budget: safe. -/
public theorem left_mem : ![1, 0] ∈ SafeBudget := by
  show (1 : ℕ) + 0 ≤ 1
  decide

/-- Agent 1 spends the whole budget: safe. -/
public theorem right_mem : ![0, 1] ∈ SafeBudget := by
  show (0 : ℕ) + 1 ≤ 1
  decide

/-- Splicing agent 1's spend into the first safe state busts the cap. -/
public theorem splice_notMem :
    Function.update ![1, 0] 1 (![0, 1] 1) ∉ SafeBudget := by
  intro h
  have h' : (1 : ℕ) + 1 ≤ 1 := h
  omega

/--
The shared-budget safe set admits no independent per-agent
characterization: the failed splice certifies non-rectangularity.
-/
public theorem safeBudget_not_independentlyExpressible :
    ¬ IndependentlyExpressible SafeBudget :=
  not_independent_of_failed_splice left_mem right_mem splice_notMem

end AISafetyAtlas.Examples.Composition.SharedBudget
