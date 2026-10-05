module

public import AISafetyAtlas.Compositional.Networks

/-!
# Evaluating a fleet of identical agents

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Compositional.Networks`, which
carries Angluin's anonymous-network results about processors, ports and views and
names no AI system. What is added here is the reading as a **deployed fleet of
identical agents**, which is the shape multi-agent deployments actually have:
many instances of one model, no built-in identifiers, talking over a topology.

## The question

Reuel, Bucknall et al. Open Problem 25: *"How can the capabilities and risks of
networks of multiple interacting AI agents be evaluated?"*

## Both halves, and the positive one is the surprise

`evaluating_one_covers_its_peers` is the **useful** half. Two agents whose local
view of the deployment agrees to depth `n` are in the same state after `n` rounds
of interaction. So an evaluation of one agent is an evaluation of every agent
with the same view, and a fleet does not have to be tested instance by instance
— which is what makes evaluating a large deployment tractable at all.

`no_designated_agent_emerges` is the cost of the same fact. If the deployment has
a symmetry that moves every agent, then **no** run of **any** deterministic
anonymous protocol ends with exactly one agent in a distinguished role. Not "it is
hard to elect a coordinator": no execution of any length does it. A safety
architecture that assigns one instance to be the monitor, the tie-breaker or the
kill-switch holder is relying on something outside this model — an identifier, an
asymmetry in the topology, or an external assignment — and naming which is the
design obligation.

`symmetry_is_the_shared_cause` states the two together, because they are one
property of the deployment read twice: **the same indistinguishability that lets
you test one agent instead of all of them is what stops any of them becoming
special.** An architecture cannot have the cheap evaluation and the designated
coordinator for free.

## What this does not claim

The atlas has **no agent, no message format and no deployment.** `Algorithm` is
one send function and one update function shared by every node, which is
anonymity in the technical sense: no identifiers anywhere in the state. A real
fleet whose instances carry distinct keys, addresses or system prompts is **not**
an instance of this, and that is the useful reading — the theorem names the
property an architecture must break, and breaking it is cheap and ordinary.

Determinism is load-bearing too: the results are about deterministic protocols,
and randomised symmetry-breaking is outside the model. Nothing here says a
randomised protocol fails.

Identifying a node with any real agent is layer 4 and is not done here.
-/

namespace AISafetyAtlas.Compositional.AgentNetwork

open AISafetyAtlas.Compositional

variable {Node State Msg : Type*} {deg : ℕ}

/--
**A fleet**: a topology, one shared program, and the state every instance starts
in.

`program` is shared by every node, which is what makes the fleet *identical
agents* rather than a system of distinct components. `initial` is the starting
configuration, per node. `Networks.Network` gives every node the same number
`deg` of ports, so fleets of unequal degree are not covered.
-/
public structure Fleet (Node : Type*) (State Msg : Type*) (deg : ℕ) where
  /-- Who talks to whom, through which port. -/
  topology : Networks.Network Node deg
  /-- The one program every instance runs. -/
  program : Networks.Algorithm State Msg deg
  /-- What each instance starts holding: a configuration, so the starting state may
  differ from node to node. -/
  initial : Networks.Config Node State

variable (F : Fleet Node State Msg deg)

/--
**Evaluating one agent covers every agent that sees the same thing.**

Two instances whose view of the deployment agrees to depth `n` hold the same
state after `n` rounds. So a fleet does not need testing instance by instance:
the evaluation transfers along the symmetry, and this is what makes evaluating a
large deployment tractable rather than linear in its size.
-/
public theorem evaluating_one_covers_its_peers (n : ℕ) (u v : Node)
    (hview : Networks.SameView F.topology F.initial n u v) :
    Networks.runFor F.topology F.program F.initial n u
      = Networks.runFor F.topology F.program F.initial n v :=
  Networks.runFor_eq_of_view_eq F.topology F.program F.initial n u v hview

/--
**And no agent ever becomes the designated one.**

If the deployment has a symmetry moving every instance, then no run of the shared
program, at any length, ends with exactly one instance in a distinguished role.
The quantifier is over every round count, so this is not a statement about how
long anyone waited.

An architecture that names one instance the monitor, the arbiter or the holder of
the shutdown authority is therefore relying on something this model does not
contain, and the repair is ordinary: give the instances identifiers, break the
topology, or assign the role from outside.
-/
public theorem no_designated_agent_emerges (σ : Networks.Automorphism F.topology)
    (hmoves : ∀ v, σ.toEquiv v ≠ v) (role : State → Prop)
    (hsym : Networks.Invariant σ F.initial) (n : ℕ) :
    ¬ Symmetry.HasUniqueLeader role
        (Networks.runFor F.topology F.program F.initial n) :=
  Networks.no_unique_leader_of_fixedPointFree σ F.program hmoves role hsym n

/--
**One property, read twice.**

Both halves rest on indistinguishability: two agents with the same view run
identically, and a symmetry moving every agent, with an initial configuration
invariant under it, leaves no unique leader. The halves share no hypothesis, so
this does not show that one cannot be had without the other; it shows that a
design assuming a designated coordinator under such a symmetry has assumed
something the protocol cannot deliver.
-/
public theorem symmetry_is_the_shared_cause (σ : Networks.Automorphism F.topology)
    (hmoves : ∀ v, σ.toEquiv v ≠ v) (role : State → Prop)
    (hsym : Networks.Invariant σ F.initial) (n : ℕ) (u v : Node)
    (hview : Networks.SameView F.topology F.initial n u v) :
    Networks.runFor F.topology F.program F.initial n u
        = Networks.runFor F.topology F.program F.initial n v ∧
      ¬ Symmetry.HasUniqueLeader role
        (Networks.runFor F.topology F.program F.initial n) :=
  ⟨evaluating_one_covers_its_peers F n u v hview,
    no_designated_agent_emerges F σ hmoves role hsym n⟩

end AISafetyAtlas.Compositional.AgentNetwork
