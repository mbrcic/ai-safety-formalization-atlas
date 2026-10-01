module

public import AISafetyAtlas.Compositional.NetworkTraces
public import AISafetyAtlas.Examples.Compositional.Networks

/-!
# Angluin's impossibility, at the smallest symmetric network

`Compositional.NetworkTraces` carries Angluin's conclusion three ways — as a
hyperproperty, as a knowability failure, and as the non-existence of a unique
leader among node-eye traces — together with the two interface theorems that say
which finite observations each trace system realizes. None of them reached an
`Examples/` application, and the reason is visible in
`Examples.Compositional.Networks`: the only network in the tree is one node with
the **identity** automorphism, which has a fixed point. Every impossibility here
needs a *fixed-point-free* one.

`pairNetwork` is that: two nodes, no ports, and the swap. Ports are where a
network's structure lives, and having none makes `port_equivariant` vacuous — but
the swap is a genuine fixed-point-free automorphism, which is the only hypothesis
the impossibilities read. The degeneracy is in the graph, not in the symmetry.

`oneNode` is the opposite corner and is here for one statement: leader election
has to be *possible* somewhere or `electsLeader_witnessed_by_one_snapshot` would
have nothing to fire at. One node with a Boolean state elects itself.
-/

namespace AISafetyAtlas.Examples.Compositional.NetworkTraces

open AISafetyAtlas.Compositional.Networks
open AISafetyAtlas.Compositional.Hyperproperties
open AISafetyAtlas.Compositional

/-! ## Two nodes and a swap -/

/-- Two nodes, no ports. -/
public def pairNetwork : Network (Fin 2) 0 where
  port := fun _ i => i.elim0

/-- The swap, which fixes neither node. -/
public def swapAutomorphism : Automorphism pairNetwork where
  toEquiv := Equiv.swap 0 1
  port_equivariant := fun _ i => i.elim0

/-- **It is fixed-point-free**, which is the hypothesis every impossibility
below reads and the one the trivial network cannot supply. -/
public theorem swap_fixedPointFree : ∀ v : Fin 2, swapAutomorphism.toEquiv v ≠ v := by
  decide

/-- The algorithm that does nothing, there being no ports to send on. -/
public def pairAlgorithm : Algorithm Unit Unit 0 where
  send := fun _ i => i.elim0
  update := fun s _ => s

/-- The only configuration there is, the state type being a point. -/
public def pairConfig : Config (Fin 2) Unit := fun _ => ()

/-- It is invariant under the swap, trivially — and the triviality is the
content: a symmetric network started symmetrically stays symmetric. -/
public theorem pairConfig_invariant : Invariant swapAutomorphism pairConfig :=
  fun _ => rfl

/-! ## Angluin's conclusion, three ways -/

/-- **No algorithm on this network elects a leader.** Angluin at the level of
trace systems: the whole system, from every symmetric start, is outside the
hyperproperty. -/
public theorem pair_not_electsLeader (leader : Unit → Prop) :
    systemOf pairNetwork pairAlgorithm {pairConfig} ∉ ElectsLeader leader :=
  not_electsLeader_of_fixedPointFree swapAutomorphism pairAlgorithm swap_fixedPointFree
    leader (fun c hc => by cases hc; exact pairConfig_invariant)

/-- **And a node cannot learn which node it is.** The same obstruction as a
knowability failure: the node's own identity is not a function of what it
observes. -/
public theorem pair_node_not_knowable :
    ¬ Knowledge.Knowable (ObsTrace pairNetwork pairAlgorithm pairConfig) (id : Fin 2 → Fin 2) :=
  not_knowable_node_of_fixedPointFree swapAutomorphism pairAlgorithm swap_fixedPointFree
    pairConfig_invariant

/-- **And no predicate on node-eye traces picks out a unique node.** The third
reading, which is the one a protocol designer would state: whatever test you
apply to what a node saw, it cannot single one out. -/
public theorem pair_no_unique_leader (leader : (ℕ → Unit) → Prop) :
    ¬ ∃! u : Fin 2, leader (ObsTrace pairNetwork pairAlgorithm pairConfig u) :=
  no_unique_leader_from_obsTrace swapAutomorphism pairAlgorithm swap_fixedPointFree
    pairConfig_invariant leader

/-! ## The two interface theorems -/

/-- **Which finite observations the run system realizes**: exactly those whose
every snapshot is reached from an admitted start. Run at the pair, where there
is one start and the configuration never moves. -/
public theorem pair_realizes_systemOf (M : Observation (Snapshot (Fin 2) Unit)) :
    Realizes observedAt M (systemOf pairNetwork pairAlgorithm {pairConfig}) ↔
      ∀ s ∈ M, ∃ c ∈ ({pairConfig} : Set (Config (Fin 2) Unit)),
        runFor pairNetwork pairAlgorithm c s.1 = s.2 :=
  realizes_systemOf pairNetwork pairAlgorithm {pairConfig} M

/-- **And which the node's-eye system realizes**, the companion statement for
`ObsTrace`. -/
public theorem pair_realizes_obsSystem (M : Observation (ℕ × Unit)) :
    Realizes stateAtRound M (obsSystem pairNetwork pairAlgorithm pairConfig) ↔
      ∀ p ∈ M, ∃ u : Fin 2, runFor pairNetwork pairAlgorithm pairConfig p.1 u = p.2 :=
  realizes_obsSystem pairNetwork pairAlgorithm pairConfig M

/-! ## The other corner: election is possible somewhere -/

/-- One node, no ports, a Boolean state. -/
public def oneNode : Network Unit 0 where
  port := fun _ i => i.elim0

/-- It does nothing; the leader is decided at the start. -/
public def oneAlgorithm : Algorithm Bool Unit 0 where
  send := fun _ i => i.elim0
  update := fun s _ => s

/-- The single node, elected. -/
public def electedConfig : Config Unit Bool := fun _ => true

/-- **The system does elect a leader**, so the hyperproperty is not empty and the
witness theorem below has something to fire at. -/
public theorem oneNode_electsLeader :
    systemOf oneNode oneAlgorithm {electedConfig} ∈ ElectsLeader (· = true) :=
  ⟨runOf oneNode oneAlgorithm electedConfig, ⟨electedConfig, rfl, rfl⟩, 0,
    ⟨(), rfl, fun _ _ => rfl⟩⟩

/-- **Leader election is witnessed by a single snapshot.** It is a `1`-safety
property of the complement: one round, one configuration, and the question is
settled. That places election in the finite-observation vocabulary, which is what
the module was built to do and what nothing had run. -/
public theorem oneNode_election_one_snapshot :
    ∃ M : Observation (Snapshot Unit Bool),
      M.card = 1 ∧ Realizes observedAt M (systemOf oneNode oneAlgorithm {electedConfig}) ∧
      IsBadObservation observedAt {S' | S' ∉ ElectsLeader (· = true)} M :=
  electsLeader_witnessed_by_one_snapshot (· = true) oneNode_electsLeader

end AISafetyAtlas.Examples.Compositional.NetworkTraces
