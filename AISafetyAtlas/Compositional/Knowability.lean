module

public import AISafetyAtlas.Compositional.Networks
public import AISafetyAtlas.Knowledge

/-!
# What a node's view settles about its state

`Compositional.Networks` proves the Angluin lemma: nodes whose views agree to
depth `n` are in the same state after `n` rounds (`runFor_eq_of_view_eq`). That
is a statement about two nodes at a time. This module says what it amounts to
about the network as a whole.

Fix a network, an anonymous algorithm, an initial configuration and a round
count; treat the **node** as the unknown. Then the depth-`n` view is an
observation map, the state after `n` rounds is a target property, and the
Angluin lemma is exactly the no-collision condition. So the state is
`Knowledge.Knowable` from the view: one decoder, uniform in the node, turns any
depth-`n` view into the state it leads to.

## What this adds

`Compositional` had no cross-domain library import in either direction. It has
one now, and the edge carries a theorem: the Angluin lemma, expressed in the
vocabulary `AISafetyAtlas.Knowledge` shares with `Wireheading`, `Preference` and
`Oversight`, so a consumer holding a question about what an observation settles
can reach the network model without restating a factorization argument.

That is the whole justification. No claim is made about this being the kernel's
first positive instance, or its only unconditional one — the kernel already
concludes `Knowable` in `Knowledge.Devices`, `Knowledge.Check`, and twice in
`Oversight.JointObservation`, and an earlier draft of this docstring made a
uniqueness claim that had to be narrowed twice before it was true. A restatement
does not need to be unique to be worth having.

## Why the view is a function, not a set

`SameView` is stated as a universally quantified equality over port sequences.
An observation map has to be a single value, so `view` packages that
quantification as a function on the sequences of length at most `n`. The
repackaging is exactly faithful: `sameView_iff_view_eq` is proved in both
directions, so nothing is lost or added on the way into the kernel.

## What is *not* assumed

`knowable_iff_no_collision` carries a `[Nonempty Y]` hypothesis — it assembles
the decoder through `Function.extend`, which needs a junk value on observations
no state realizes. That hypothesis is **not** imposed here. With no states there
are no nodes either, since a configuration maps nodes to states, and then the
observation type is itself empty and a decoder exists for nothing to do. The
theorem below is therefore unconditional in `State`, and the case split in its
proof is where that is discharged.

## Explicit non-claims

- **Not new BY-043 coverage.** `Networks` is an upstream dependency for the
  survey-original result and says so; expressing its lemma through `Knowable`
  changes nothing about that. Any ledger row must record this as a shared-API
  formulation.
- **Not a new theorem about networks.** `runFor_eq_of_view_eq` does all the
  mathematical work. What is added is that `Compositional`, previously the
  atlas's most isolated domain, now consumes a shared law.
- **Deterministic and synchronous only**, inheriting every non-claim in
  `Compositional.Networks` — no randomness, no asynchrony, and the simplified
  message routing.
- **Not** a claim that a node can *compute* the decoder. `Knowable` asserts a
  function exists; it is silent about how a node would obtain one, and the
  decoder here is assembled classically.
-/

namespace AISafetyAtlas.Compositional.Networks

open AISafetyAtlas.Knowledge

variable {Node State Msg : Type*} {deg : ℕ}

/-- A node's view to depth `n`, packaged as a single observation: the label
reached by each port sequence of length at most `n`. -/
@[expose] public def view (N : Network Node deg) (c : Config Node State) (n : ℕ)
    (u : Node) : {p : List (Fin deg) // p.length ≤ n} → State :=
  fun p => c (pathTo N u p.1)

/-- The packaging is faithful: having the same view is having equal views. -/
public theorem sameView_iff_view_eq (N : Network Node deg) (c : Config Node State)
    (n : ℕ) (u v : Node) :
    SameView N c n u v ↔ view N c n u = view N c n v := by
  constructor
  · intro h
    funext p
    exact h p.1 p.2
  · intro h p hp
    exact congrFun h ⟨p, hp⟩

/--
**The state after `n` rounds is knowable from the depth-`n` view.**

One decoder, uniform in the node, recovers the state of every node after `n`
synchronous rounds from its view to depth `n`. This is the Angluin lemma
`runFor_eq_of_view_eq` read as a factorization: an anonymous algorithm cannot
see past the depth its messages have travelled, and equally, it needs nothing
deeper than that.

Unconditional in `State`: the empty case is degenerate rather than excluded.
-/
public theorem knowable_runFor (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) (n : ℕ) :
    Knowable (view N c n) (runFor N A c n) := by
  classical
  cases isEmpty_or_nonempty State with
  | inl _ =>
      exact ⟨fun f => isEmptyElim (f ⟨[], by simp⟩), fun u => isEmptyElim (c u)⟩
  | inr _ =>
      refine (knowable_iff_no_collision _ _).mpr ?_
      intro u v hobs
      exact runFor_eq_of_view_eq N A c n u v ((sameView_iff_view_eq N c n u v).mpr hobs)

end AISafetyAtlas.Compositional.Networks
