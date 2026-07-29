module

public import Mathlib.Data.Nat.Basic

/-!
# Deterministic symmetry obstruction

This is the inductive core of Angluin's anonymous-network leader-election
impossibility (*Local and global properties in networks of processors*, STOC
1980): nodes with indistinguishable observations and identical deterministic
transition code remain indistinguishable, so a configuration with exactly one
leader cannot be reached.

The module isolates the symmetry argument rather than claiming Angluin's full
network/view theory.  Randomness, identifiers, asymmetric initial states, and
asymmetric observations are intentionally outside the hypotheses.
-/

namespace AISafetyAtlas.Compositional.Symmetry

/-- All nodes have the same local state. -/
@[expose] public def IsSymmetric {Node State : Type*}
    (configuration : Node → State) : Prop :=
  ∀ i j, configuration i = configuration j

/-- The node type contains two distinct nodes. -/
@[expose] public def HasAtLeastTwo (Node : Type*) : Prop :=
  ∃ i j : Node, i ≠ j

/-- Exactly one node's state satisfies the leader predicate. -/
@[expose] public def HasUniqueLeader {Node State : Type*}
    (leader : State → Prop) (configuration : Node → State) : Prop :=
  ∃ i, leader (configuration i) ∧
    ∀ j, leader (configuration j) → j = i

/--
An anonymous deterministic synchronous protocol.

The observation interface may contain arbitrary network structure.  The sole
anonymity premise used by the theorem is explicit: a symmetric configuration
gives every node the same observation.  `decide` is shared deterministic code.
-/
public structure Protocol (Node State Observation : Type*) where
  observe : (Node → State) → Node → Observation
  decide : Observation → State
  symmetric_observation :
    ∀ c, IsSymmetric c → ∀ i j, observe c i = observe c j

namespace Protocol

variable {Node State Observation : Type*}

/-- One synchronous protocol round. -/
@[expose] public def step (P : Protocol Node State Observation)
    (c : Node → State) : Node → State :=
  fun i => P.decide (P.observe c i)

/-- Execute `rounds` synchronous rounds. -/
@[expose] public def run (P : Protocol Node State Observation) :
    ℕ → (Node → State) → Node → State
  | 0, c => c
  | n + 1, c => P.step (P.run n c)

/-- A deterministic anonymous round preserves a symmetric configuration. -/
public theorem step_preserves_symmetry (P : Protocol Node State Observation)
    {c : Node → State} (hc : IsSymmetric c) :
    IsSymmetric (P.step c) := by
  intro i j
  exact congrArg P.decide (P.symmetric_observation c hc i j)

/-- Symmetry is invariant for every finite number of synchronous rounds. -/
public theorem run_preserves_symmetry (P : Protocol Node State Observation)
    {c : Node → State} (hc : IsSymmetric c) (rounds : ℕ) :
    IsSymmetric (P.run rounds c) := by
  induction rounds with
  | zero => exact hc
  | succ n ih => exact P.step_preserves_symmetry ih

/-- A symmetric configuration on at least two nodes has no unique leader. -/
public theorem symmetric_no_unique_leader
    {leader : State → Prop} {c : Node → State}
    (nodes : HasAtLeastTwo Node) (hc : IsSymmetric c) :
    ¬ HasUniqueLeader leader c := by
  rintro ⟨chosen, hleader, hunique⟩
  obtain ⟨i, j, hij⟩ := nodes
  have hi : leader (c i) := hc chosen i ▸ hleader
  have hj : leader (c j) := hc chosen j ▸ hleader
  exact hij ((hunique i hi).trans (hunique j hj).symm)

/--
**Angluin symmetry obstruction (inductive core).**

From a symmetric initial configuration, no finite execution of an anonymous
deterministic protocol can end with exactly one leader.
-/
public theorem no_unique_leader_from_symmetric_start
    (P : Protocol Node State Observation)
    (nodes : HasAtLeastTwo Node)
    (leader : State → Prop)
    (initial : Node → State)
    (symmetric : IsSymmetric initial)
    (rounds : ℕ) :
    ¬ HasUniqueLeader leader (P.run rounds initial) :=
  symmetric_no_unique_leader nodes (P.run_preserves_symmetry symmetric rounds)

end Protocol
end AISafetyAtlas.Compositional.Symmetry
