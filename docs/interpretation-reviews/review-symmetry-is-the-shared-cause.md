# Bridge review — `Compositional.AgentNetwork.symmetry_is_the_shared_cause`

**Row `BY-043` · module `AISafetyAtlas/Compositional/AgentNetwork.lean` · `HUMAN_REVIEW`**

Only bridge on this row. Base: `Compositional.Networks` (Angluin's
anonymous-network results). Arrow to Reuel, Bucknall et al., TMLR 04/2025,
**Open Problem 25**.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☑ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-04 |
| Note | Statement accepted 2026-10-04. AI reading withheld: the join of two separately stated halves is mostly packaging, and its conditions (identical deterministic agents without identifiers) rarely hold. |

## The statement

```lean
public theorem symmetry_is_the_shared_cause (σ : Networks.Automorphism F.topology)
    (hmoves : ∀ v, σ.toEquiv v ≠ v) (role : State → Prop)
    (hsym : Networks.Invariant σ F.initial) (n : ℕ) (u v : Node)
    (hview : Networks.SameView F.topology F.initial n u v) :
    Networks.runFor F.topology F.program F.initial n u
        = Networks.runFor F.topology F.program F.initial n v ∧
      ¬ Symmetry.HasUniqueLeader role
        (Networks.runFor F.topology F.program F.initial n)
```

## What to check

1. **The positive half is the useful one.** Two agents whose local view agrees to
   depth `n` are in the same state after `n` rounds, so evaluating one evaluates
   every agent with that view. That is what makes evaluating a large deployment
   tractable at all.
2. **The negative half is strong and so is its hypothesis.** With an automorphism
   moving **every** agent and an initial configuration invariant under it
   (`hsym`), **no** run of **any** deterministic anonymous protocol
   ends with exactly one agent in a distinguished role. Not "hard to elect a
   coordinator": no execution of any length does it.
3. **The bridge grade rests on the join.** Both halves are separately true and
   separately stated (`evaluating_one_covers_its_peers`,
   `no_designated_agent_emerges`). This declaration is the conjunction. **Decide
   whether the join is a claim or repackaging** — it is the whole question here.

## Allowed claim

> In a deployment of instances identical in state and protocol, deterministic and
> without identifiers, agents whose local view agrees to depth `n` are in the same
> state after `n` rounds — so evaluating one evaluates all of them with that view.
> Where the deployment also has a symmetry moving every agent, no run of any
> deterministic protocol leaves exactly one agent in a distinguished role. Both
> halves rest on indistinguishability; the conjunction does not show that one
> cannot be had without the other.

## Forbidden

- **Not** "multi-agent systems cannot be governed." The theorem names the
  property an architecture must **break**, and breaking it is cheap and ordinary
  — distinct keys, addresses or prompts.
- **Not** applicable to a fleet whose instances differ. That is not an instance.
- **Not** about randomised protocols. Determinism is load-bearing; randomised
  symmetry-breaking is outside the model and is not claimed to fail.
- **Not** about capability, collusion or emergent behaviour.
- **Not** that evaluating one instance is *sufficient* in practice — conditional
  on view agreement to the relevant depth.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Agent swarms provably cannot elect a safety monitor." | needs full anonymity, determinism, a symmetry moving every node, and an initial state invariant under it; identifiers break the first |
| "So test one agent and ship the fleet." | conditional on view agreement to depth `n` |
| "Randomised leader election is ruled out." | explicitly outside the model |
| "This is about misaligned embodiment." | the row title; the module models identical instances on a topology, nothing about embodiment |

## Witness

`AISafetyAtlas/Examples/Practitioner.lean`.
