module

public import AISafetyAtlas.Compositional.Networks
public import AISafetyAtlas.Compositional.Hyperproperties
public import AISafetyAtlas.Knowledge

/-!
# A network's runs, as a trace system

## Statement intent

- **Objects.** A `Run` is a whole synchronous execution, `ℕ → Config Node State`.
  A `Snapshot` is the finite observation atom "at round `n` the configuration is
  `c`". A network with an algorithm and a set of initial configurations produces
  a `Hyperproperties.TraceSystem`.
- **Interface.** `realizes_systemOf` says exactly which finite observations that
  system realizes: those whose every snapshot is reached from some admitted
  initial configuration.
- **Payoff.** `not_electsLeader_of_fixedPointFree` is Angluin's conclusion at the
  level of trace systems, and `electsLeader_witnessed_by_one_snapshot` places
  leader election in the finite-observation vocabulary, as an
  `IsBadObservation` at `k = 1` for the complement.

## Why this direction

`Compositional.Hyperproperties` defines `TraceSystem`, `Realizes`,
`IsBadObservation`, `IsKSafety`, `IsSafetyPredicate`, the self-composition
reduction and the prefix topology — and **nothing in the tree produced a trace**.
The four modules that generate executions (`Networks`, `Symmetry`,
`Wireheading.CRMDP`, `Wireheading.GoalPreservation`) had no consumer that reads
them as traces. Both halves were live and unconnected. This module is a producer
for the first of them.

The dependency runs one way: `Hyperproperties` is untouched, and nothing here is
imported by it.

## What this does and does not commit to

- **No general answer to "what is a system".** `Trace` and `Prefix` are free type
  parameters throughout `Hyperproperties`, and `prefixOf` is supplied by the
  caller, so instantiating them for `Networks` commits nothing about how any
  other model should be read. A shared transition-system interface would be a
  different and much larger decision; this is an instantiation, not an ontology.
- **Two readings of "a trace", and both are built.** A run can be the
  round-indexed sequence of whole *configurations* (`Run`, §1), or the sequence
  one *node* observes (`ObsTrace`, §4). The first is the outside view and is what
  a global safety argument wants. The second is the more faithful notion for an
  *anonymous* network, because it is what a node actually has, and it is what
  makes anonymity statable: `not_knowable_node_of_fixedPointFree` says a node
  cannot recover its own identity from what it observes.

  The finer readings are still not built. A node's own state sequence is not
  everything it could see — `Algorithm.update` reads incoming messages, and the
  state sequence does not determine them, so a node permitted to record received
  messages would know strictly more. `ObsTrace` is the coarsest honest choice,
  not the finest possible one.
- **The machinery becomes applicable; the example exercises little of it.**
  Connecting the types puts `IsKSafety`, `IsHyperSafety`, `IsHyperLiveness`, the
  self-composition reduction and the prefix topology within reach of a real
  dynamic model. What is *worked* below is a single `k = 1` certificate. No
  `k ≥ 2` hyperproperty of networks is stated here, and the genuinely
  hyperproperty-shaped claims — non-interference, collusion, privacy under
  composition — remain unformalized over this model.
- **Not new network mathematics, and no BY-043 status follows.**
  `not_electsLeader_of_fixedPointFree` is
  `Networks.no_unique_leader_of_fixedPointFree` transported across the producer;
  it proves nothing about networks that the Angluin route did not already prove.
  `Networks` remains an upstream dependency of the survey-original BY-043 and
  this does not change that.
- **`ElectsLeader` is not offered as the interesting hyperproperty.** It is the
  one the tree can already refute, chosen so that the producer is exercised by a
  theorem rather than by a definition.

## Scope boundary

Everything inherits `Networks`' non-claims: deterministic and synchronous only,
no randomness, no asynchrony, and the simplified message routing in which the
message received on port `i` is what the port-`i` neighbour sends on index `i`.
`inits` is an arbitrary `Set`, not required finite or nonempty; the empty set
gives the empty trace system, which realizes only the empty observation.
-/

namespace AISafetyAtlas.Compositional.Networks

open AISafetyAtlas.Compositional.Hyperproperties

variable {Node State Msg : Type*} {deg : ℕ}

/-! ## The producer -/

/-- A trace of an anonymous network: the whole synchronous run, round by round. -/
public abbrev Run (Node State : Type*) : Type _ := ℕ → Config Node State

/-- A finite observation atom: "at round `n` the configuration is `c`". -/
public abbrev Snapshot (Node State : Type*) : Type _ := ℕ × Config Node State

/-- A run exhibits a snapshot when it matches there. This is the `prefixOf`
relation the trace theory is parameterized by. -/
@[expose] public def observedAt (s : Snapshot Node State) (t : Run Node State) : Prop :=
  t s.1 = s.2

/-- The run produced from one initial configuration. -/
@[expose] public def runOf (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) : Run Node State :=
  fun n => runFor N A c n

/-- The trace system produced over a set of admitted initial configurations. -/
@[expose] public def systemOf (N : Network Node deg) (A : Algorithm State Msg deg)
    (inits : Set (Config Node State)) : TraceSystem (Run Node State) :=
  runOf N A '' inits

/-! ## Producer meets consumer -/

/--
**Which finite observations a network's runs realize.**

The trace theory's `Realizes` asks that every observed prefix extend to some
complete trace in the system. Over a network's runs that is exactly: every
snapshot is reached, at its own round, from some admitted initial configuration.

This is the interface theorem. Everything the trace theory says about
`systemOf N A inits` is said about the right-hand side.
-/
public theorem realizes_systemOf (N : Network Node deg)
    (A : Algorithm State Msg deg) (inits : Set (Config Node State))
    (M : Observation (Snapshot Node State)) :
    Realizes observedAt M (systemOf N A inits) ↔
      ∀ s ∈ M, ∃ c ∈ inits, runFor N A c s.1 = s.2 := by
  constructor
  · intro h s hs
    obtain ⟨t, ⟨c, hc, rfl⟩, ht⟩ := h s hs
    exact ⟨c, hc, ht⟩
  · intro h s hs
    obtain ⟨c, hc, hrun⟩ := h s hs
    exact ⟨runOf N A c, ⟨c, hc, rfl⟩, hrun⟩

/-! ## Leader election over trace systems -/

/-- The hyperproperty "this system elects a unique leader at some round". -/
@[expose] public def ElectsLeader (leader : State → Prop) :
    Hyperproperty (Run Node State) :=
  {S | ∃ t ∈ S, ∃ n, Symmetry.HasUniqueLeader leader (t n)}

/--
**Angluin, at the level of trace systems.**

A fixed-point-free automorphism under which every admitted start is invariant
puts the *whole generated system* outside the leader-election hyperproperty — not
one execution at a time.

Transported from `no_unique_leader_of_fixedPointFree` across the producer. It
proves nothing new about networks; what is new is that the conclusion is now a
statement in the trace theory's own vocabulary.
-/
public theorem not_electsLeader_of_fixedPointFree {N : Network Node deg}
    (σ : Automorphism N) (A : Algorithm State Msg deg)
    (hfree : ∀ v, σ.toEquiv v ≠ v) (leader : State → Prop)
    {inits : Set (Config Node State)}
    (hinv : ∀ c ∈ inits, Invariant σ c) :
    systemOf N A inits ∉ ElectsLeader leader := by
  rintro ⟨t, ⟨c, hc, rfl⟩, n, hlead⟩
  exact no_unique_leader_of_fixedPointFree σ A hfree leader (hinv c hc) n hlead

/--
**Electing a leader is certified by one snapshot.**

If a system elects, a single finite observation witnesses it, and every system
realizing that observation elects too. That is `IsBadObservation` at `k = 1` for
the *complement* of `ElectsLeader`: one snapshot already rules out never
electing.

Stated over an arbitrary `TraceSystem` rather than over `systemOf`, because it
uses nothing about networks — which is the point. The producer is what lets a
network's runs be an instance of it.
-/
public theorem electsLeader_witnessed_by_one_snapshot (leader : State → Prop)
    {S : TraceSystem (Run Node State)} (hS : S ∈ ElectsLeader leader) :
    ∃ M : Observation (Snapshot Node State),
      M.card = 1 ∧ Realizes observedAt M S ∧
      IsBadObservation observedAt {S' | S' ∉ ElectsLeader leader} M := by
  obtain ⟨t, htS, n, hlead⟩ := hS
  refine ⟨{(n, t n)}, Finset.card_singleton _, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_singleton] at hs
    exact ⟨t, htS, by rw [hs]; rfl⟩
  · intro S' hreal hmem
    obtain ⟨t', ht'S, ht'⟩ := hreal (n, t n) (Finset.mem_singleton_self _)
    exact hmem ⟨t', ht'S, n, by rw [show t' n = t n from ht']; exact hlead⟩

/-! ## 4. The other reading: what one node sees

`Run` above is the outside view. A node has no such thing: it has no identifier,
no global picture, and one shared pair of `send`/`update` functions. What it has
is its own state, round by round. That is `ObsTrace`, and stating anonymity needs
it — the configuration-level results below §2 quantify over a global object no
participant holds.
-/

/-- What one node observes: its own state, round by round. -/
@[expose] public def ObsTrace (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) (u : Node) : ℕ → State :=
  fun n => runFor N A c n u

/--
**An automorphism of an invariant configuration identifies what two nodes see.**

`invariant_of_automorphism` says the configuration stays `σ`-invariant at every
round. Read node-wise and across all rounds, that is: `σ u` and `u` observe the
same thing, forever.
-/
public theorem obsTrace_automorphism {N : Network Node deg} (σ : Automorphism N)
    (A : Algorithm State Msg deg) {c : Config Node State}
    (hc : Invariant σ c) (u : Node) :
    ObsTrace N A c (σ.toEquiv u) = ObsTrace N A c u := by
  funext n
  exact invariant_of_automorphism σ A hc n u

/--
**Anonymity, as a knowability statement: a node cannot tell which node it is.**

Take the node as the unknown, its observation trace as the observation, and its
own identity as the target. A fixed-point-free automorphism of an invariant start
leaves the observation fixed and moves the identity, which is exactly
`Knowledge.not_knowable_of_invariant_transform`.

This is what "anonymous" means in Angluin's model, said in the kernel's
vocabulary rather than left implicit in the absence of identifiers from the
`Algorithm` type.

`[Nonempty Node]` is load-bearing, not defensive: over an empty node type the
decoder is vacuous and the identity *is* knowable, so a reader who drops the
instance gets a false statement rather than a failed proof.
-/
public theorem not_knowable_node_of_fixedPointFree {N : Network Node deg}
    [Nonempty Node] (σ : Automorphism N) (A : Algorithm State Msg deg)
    (hfree : ∀ v, σ.toEquiv v ≠ v) {c : Config Node State} (hc : Invariant σ c) :
    ¬ Knowledge.Knowable (ObsTrace N A c) (id : Node → Node) := by
  obtain ⟨u⟩ := ‹Nonempty Node›
  exact Knowledge.not_knowable_of_invariant_transform σ.toEquiv
    (fun v => obsTrace_automorphism σ A hc v) u (hfree u)

/--
**Leader election fails against a node's whole history, not just its state.**

Strictly stronger than `no_unique_leader_of_fixedPointFree`, which evaluates a
`State → Prop` at one round. Here the predicate may read the entire observation
trace — every state the node has ever been in, in order — and still cannot single
one out. Handing a node unbounded memory of its own past does not break the
symmetry, because the symmetry acts on the past too.
-/
public theorem no_unique_leader_from_obsTrace {N : Network Node deg}
    (σ : Automorphism N) (A : Algorithm State Msg deg)
    (hfree : ∀ v, σ.toEquiv v ≠ v) {c : Config Node State} (hc : Invariant σ c)
    (leader : (ℕ → State) → Prop) :
    ¬ ∃! u : Node, leader (ObsTrace N A c u) := by
  rintro ⟨u, hu, huniq⟩
  exact hfree u (huniq _ (show leader _ by rw [obsTrace_automorphism σ A hc u]; exact hu))

/-- The observation system: one trace per **node**, where `systemOf` gives one per
initial configuration. -/
@[expose] public def obsSystem (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) : TraceSystem (ℕ → State) :=
  Set.range (ObsTrace N A c)

/-- A prefix atom for an observation trace: "at round `n` I was in state `s`". -/
@[expose] public def stateAtRound (p : ℕ × State) (t : ℕ → State) : Prop := t p.1 = p.2

/-- Which finite observations a node's-eye trace system realizes. The interface
theorem for `ObsTrace`, matching `realizes_systemOf` for `Run`. -/
public theorem realizes_obsSystem (N : Network Node deg)
    (A : Algorithm State Msg deg) (c : Config Node State)
    (M : Observation (ℕ × State)) :
    Realizes stateAtRound M (obsSystem N A c) ↔
      ∀ p ∈ M, ∃ u : Node, runFor N A c p.1 u = p.2 := by
  constructor
  · intro h p hp
    obtain ⟨t, ⟨u, rfl⟩, ht⟩ := h p hp
    exact ⟨u, ht⟩
  · intro h p hp
    obtain ⟨u, hu⟩ := h p hp
    exact ⟨ObsTrace N A c u, ⟨u, rfl⟩, hu⟩

end AISafetyAtlas.Compositional.Networks
