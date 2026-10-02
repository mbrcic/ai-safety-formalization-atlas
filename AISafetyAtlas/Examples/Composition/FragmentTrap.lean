module

public import AISafetyAtlas.Composition.Rectangularity
public import Mathlib.Data.Fin.VecNotation

/-!
# Witness W3 — compositional fragment trap

Two agents each emit (`true`) or withhold (`false`) an output fragment.
Each fragment is locally permitted; the *aggregation* of both fragments is
prohibited. The states `![true, false]` and `![false, true]` are safe, their
splice `![true, true]` is not, so no independent per-agent output filter
characterizes the safe set.

**Formally this is the same non-rectangularity pattern as
`SharedBudget` (witness W1)** — one theorem, two certified instantiations.
Its distinct value is the interpretation: it is the minimal formal core of
the "compositional fragment trap" documented empirically in the multi-agent
safety literature (individually benign subtask outputs whose composition
violates policy — e.g. semantic intent fragmentation, compositional privacy
leakage). The bridge claim lives in the provenance/bridge documentation, not
in this file.

## Interpretation

- Engineering: a per-agent output monitor is not merely inaccurate here —
  it observes the wrong unit of analysis.
- AI-safety: individually benign fragments can compose into a prohibited
  payload; local filtering cannot exclude this by construction.
- Non-claim: no claim about any particular AI system, prompt-decomposition
  attack, or detector; the empirical bridge is documented separately.
-/

namespace AISafetyAtlas.Examples.Composition.FragmentTrap

open AISafetyAtlas.Composition

/-- Safe states: not both agents emit their fragment. -/
public def SafeFragments : Set (GlobalState (Fin 2) fun _ => Bool) :=
  {x | ¬(x 0 = true ∧ x 1 = true)}

/-- Only agent 0 emits: safe. -/
public theorem left_mem : ![true, false] ∈ SafeFragments :=
  fun h => Bool.noConfusion h.2

/-- Only agent 1 emits: safe. -/
public theorem right_mem : ![false, true] ∈ SafeFragments :=
  fun h => Bool.noConfusion h.1

/-- Splicing agent 1's emission into the first safe state assembles the
prohibited payload. -/
public theorem splice_notMem :
    Function.update ![true, false] 1 (![false, true] 1) ∉ SafeFragments :=
  fun h => h ⟨rfl, rfl⟩

/--
The fragment-trap safe set admits no independent per-agent output filter:
the failed splice certifies non-rectangularity.
-/
public theorem safeFragments_not_independentlyExpressible :
    ¬ IndependentlyExpressible SafeFragments :=
  not_independent_of_failed_splice left_mem right_mem splice_notMem

end AISafetyAtlas.Examples.Composition.FragmentTrap
