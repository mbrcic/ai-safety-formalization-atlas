module

public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Fintype.Basic
public import AISafetyAtlas.Compositional.Rectangularity

/-!
# Compositional expressibility: rectangularity of global safe sets

## Statement intent

- System object: a multi-agent global state assigning each agent a local state.
- Global safe set: an arbitrary set of global states.
- Local contract: one predicate per agent, checked independently.
- `IndependentlyExpressible`: the global safe set is exactly a product of
  per-agent local sets (`Set.pi Set.univ`).
- `CoordinateSpliceClosed`: replacing one agent's coordinate in a safe state
  by that agent's coordinate from another safe state stays safe.
- Conclusion (`independent_iff_rectangular`): for finitely many agents, the
  two notions coincide; the strongest independent local contracts are the
  coordinate projections of the global safe set
  (`independent_iff_eq_pi_projections`).
- Refutation form (`not_independent_of_failed_splice`): a single certified
  failed recombination proves that no family of independent per-agent
  predicates characterizes the global safe set. This direction needs neither
  finiteness nor nonemptiness of the agent type.

## Interpretation

- Mathematical: factorization of a subset of a (dependent) finite product;
  the "combinatorial rectangle" closure characterization (Kushilevitz–Nisan
  1997, Ch. 1, folklore) and the degenerate empty-antecedent case of Fagin's
  multivalued-dependency decomposition (Fagin 1977, ACM TODS 2(3)).
- Engineering: independent per-agent predicates are complete exactly for
  recombination-closed properties.
- AI-safety: individually approved agent states need not imply a safe joint
  configuration; one certified counterexample pins the failure on the
  contract architecture, not on the quality of any local check.
- Non-claim: nothing here concerns learning, strategic behavior, temporal
  evolution, hidden channels, or hyperproperties (multi-execution
  properties), and projections are not claimed to be computable or
  observable in practice.

The mathematics is established; the contribution is the mechanization and
the reusable safety-facing interface. **The canonical theorem is
`AISafetyAtlas.Compositional.coordinate_product_iff_spliceClosed`**, which this
module reads in agent-indexed vocabulary: the characterizations here are derived
from it (`CoordinateSpliceClosed` is `Compositional.SpliceClosed`), adding the
empty-set case and the refutation form. The `[Nonempty Agent]` hypothesis in
the characterizations excludes only the degenerate empty-agent corner, where
the empty product is a singleton and the empty set is splice-closed but not
a product.
-/

@[expose] public section

namespace AISafetyAtlas.Composition

open Set Function

variable {Agent : Type*} {LocalState : Agent → Type*}

/-- A global state assigns each agent a local state. -/
public abbrev GlobalState (Agent : Type*) (LocalState : Agent → Type*) :=
  ∀ i, LocalState i

variable {P : Set (GlobalState Agent LocalState)}

/--
The global safe set is decided by independent per-agent predicates: it is a
product (`Set.pi Set.univ`) of one local set per agent, with no relational
constraint across agents.
-/
public def IndependentlyExpressible
    (P : Set (GlobalState Agent LocalState)) : Prop :=
  ∃ L : ∀ i, Set (LocalState i), P = Set.pi Set.univ L

/--
Coordinate-splice closure ("mix and match"): taking an individually
acceptable coordinate from one safe state and inserting it into another safe
state never leaves the safe set.
-/
public def CoordinateSpliceClosed [DecidableEq Agent]
    (P : Set (GlobalState Agent LocalState)) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ∀ i, Function.update x i (y i) ∈ P

/--
An independently expressible safe set is splice-closed. This easy direction
needs no finiteness or nonemptiness of the agent type.
-/
public theorem IndependentlyExpressible.spliceClosed [DecidableEq Agent]
    (h : IndependentlyExpressible P) : CoordinateSpliceClosed P := by
  obtain ⟨L, rfl⟩ := h
  intro x hx y hy i j _
  rcases eq_or_ne j i with rfl | hne
  · simpa using hy j (mem_univ j)
  · simpa [Function.update_of_ne hne] using hx j (mem_univ j)

/--
Refutation form: one certified failed recombination — two safe states whose
one-coordinate splice is unsafe — proves that no family of independent
per-agent predicates characterizes the global safe set.
-/
public theorem not_independent_of_failed_splice [DecidableEq Agent]
    {x y : GlobalState Agent LocalState} {i : Agent}
    (hx : x ∈ P) (hy : y ∈ P) (hbad : Function.update x i (y i) ∉ P) :
    ¬ IndependentlyExpressible P :=
  fun h => hbad (h.spliceClosed x hx y hy i)

/--
A splice-closed set contains every state each of whose coordinates is
realized by some member: the core induction for the rectangularity
characterization, replacing one coordinate per step across the finite agent
set.
-/
public theorem CoordinateSpliceClosed.mem_of_forall_exists_eq
    [Fintype Agent] [DecidableEq Agent]
    (hP : CoordinateSpliceClosed P) (hne : P.Nonempty)
    {z : GlobalState Agent LocalState}
    (hz : ∀ i, ∃ w ∈ P, w i = z i) : z ∈ P := by
  obtain ⟨x₀, hx₀⟩ := hne
  have h := AISafetyAtlas.Compositional.spliceClosed_piecewise_mem hP hx₀ z Finset.univ
    fun i _ => hz i
  rwa [Finset.piecewise_univ] at h

/--
The strongest independent local contracts are the projections: a global safe
set is independently expressible iff it equals the product of its coordinate
projections. If rebuilding from projections adds states, independent
contracts have lost global information.
-/
public theorem independent_iff_eq_pi_projections
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent] :
    IndependentlyExpressible P ↔
      P = Set.pi Set.univ fun i => Function.eval i '' P := by
  constructor
  · intro h
    rcases P.eq_empty_or_nonempty with rfl | hne
    · have i := Classical.arbitrary Agent
      rw [Set.pi_eq_empty (Set.mem_univ i) (by simp)]
    · exact (AISafetyAtlas.Compositional.coordinate_product_iff_spliceClosed P hne).mpr
        h.spliceClosed
  · exact fun h => ⟨_, h⟩

/--
Rectangularity characterization: a global safe set is decidable by
independent per-agent predicates iff it is closed under coordinate splicing.
Independent verification works exactly when safe local pieces can be freely
recombined.
-/
public theorem independent_iff_rectangular
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent] :
    IndependentlyExpressible P ↔ CoordinateSpliceClosed P := by
  refine ⟨IndependentlyExpressible.spliceClosed, fun hP => ?_⟩
  rcases P.eq_empty_or_nonempty with rfl | hne
  · have i := Classical.arbitrary Agent
    exact ⟨fun _ => ∅, by rw [Set.pi_eq_empty (Set.mem_univ i) rfl]⟩
  · exact ⟨_, (AISafetyAtlas.Compositional.coordinate_product_iff_spliceClosed P hne).mpr hP⟩

end AISafetyAtlas.Composition
