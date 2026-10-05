# Keiding 1985 — what was transcribed and what was not

**Date.** 2026-09-13. Row `LAND-SOV-STABILITY-001`.

## The document

the private literature store,
sha256 `f39fab6dd1c7a5d38035d122b84f7ac58819062542fb56b1b97aa6d47ace1082`,
manifested in the private manifest of 2026-09-12.

Face: *"International Journal of Game Theory, Vol. 14, Issue 2, page 93-101"*,
H. Keiding, Copenhagen. 9 pages. **Read 2026-09-12 and re-read 2026-09-13 at
folios 96–97, from rendered page images.**

## What the paper says, at the folios

* **Definition 3.3, p. 96.** *"Let `E : P(N) → P²(A)` be an effectivity
  function. A cycle in `E` is a family `(S₁,…,S_k; B₁,…,B_k)`, where `Sᵢ ∈ 2^N`,
  `Bᵢ ∈ 2^A`, `Bᵢ ∈ E(Sᵢ)`, `i = 1,…,k`, such that there are sets
  `C₁,…,C_k ∈ 2^A` satisfying:"*
  * **(i)** `Cᵢ ∩ Cⱼ = ∅` for `i ≠ j`, and `⋃ᵢ Cᵢ = A`;
  * **(ii)** `Cᵢ ∩ Bᵢ = ∅`, and for `i₁,…,i_r ∈ {1,…,k}`, if
    `C_{i_j} ∩ B_{i_{j+1}} ≠ ∅` for `j = 1,…,r−1`, then
    `⋂_{j=1}^r S_{i_j} = ∅` or `C_{i_r} ∩ B_{i₁} = ∅`.

  *"The effectivity function `E : P(N) → P²(A)` is said to be acyclic if there
  are no cycles in `E`."*
* **Remark 3.4, p. 96.** The "or" in 3.3(ii) is **not exclusive**.
* **Lemma 3.5, p. 96.** A strong cycle gives a cycle.
* **Theorem 3.6, p. 97.** A cycle implies `E` is unstable.
* **Lemma 3.7, p. 97.** An acyclic binary relation on a **finite** set extends
  to an ordering.
* **Theorem 3.8, p. 97.** Acyclic implies stable.

Together, 3.6 and 3.8 are **stable iff acyclic**.

## Why this is statable here with no new substrate

Keiding's `E : P(N) → P²(A)` **is** the type of
`AISafetyAtlas.Sovereignty.effectivity`: `Set N → Set (Set X)`.
`GameFormAcyclic G` is *defined* as `Acyclic (effectivity G)` and
`gameFormAcyclic_iff` is `Iff.rfl`, so there is no translation step between
print's object and the repository's that could be got wrong.

And Definition 3.3 mentions **only `E`**. No preference, no utility, no
ordering. That is the whole reason this row exists: a purely combinatorial
property of a distribution of power decides whether that distribution can be
blocked from every direction at once.

## What was not transcribed, and the cost of doing it

**This section is superseded in part.** It was written when neither theorem was
carried; Theorem 3.6 now is. The table below is kept because the costing was
wrong in two places and the corrections are the point.

| Needed | Held? |
|---|---|
| A preference-profile type — `K(A)^N`, orderings on the outcome space, one per agent | **Yes.** `AISafetyAtlas.SocialChoice.Profile` is `Fin N → Preorder' A`, a complete and transitive weak preference per player, carried for Arrow. Its index is `Fin voterCount` where this tree takes an arbitrary player type, so the profile these coalitions need is `N → Preorder' X` and costs a line. The word `profile` in the `Sovereignty` tree means a *strategy* profile, which is a naming collision and not an absence |
| The core `C(A, E, R^N)` as a set of unblocked outcomes | **No.** This is the gap. `Sovereignty.Domination` is not it — its `Veto` and `Dominates` block a *demand*, a set of outcomes, and mention no preference — and neither is `nonmonotonicCore` (in `TrulyPlayable`), which is the core of a family of sets at one coalition, from Goranko, Jamroga and Turrini |
| Finiteness, for Lemma 3.7 | **Free.** Recorded as absent, but print applies 3.7 to `Dᵢ ⊆ {1, …, k}`, which is `Fin c.len` and finite by construction. Nothing needs `X` finite |

So the condition needed **one definition and two proofs**, not a layer.
Corrected 2026-09-16: the first row previously read "no preference-profile type
anywhere in the repository", which was false, and the second inherited the error
by deferring to it.

**Taken the same day.** The core is defined (`WeakOrder`, `Profile`,
`DominatesVia`, `Dominated`, `core`, `Stable`, from Definitions 2.1 to 2.3), and
**Theorem 3.6 is proved** as `not_stable_of_cycle`, with `acyclic_of_stable` its
contrapositive under Definition 2.1(i). No separate game-form form is carried —
`gameFormAcyclic_iff` is `Iff.rfl`, so the two propositions are one. Lemma 3.7 is `exists_wellOrder_ge_of_acyclic`, assembled
from Mathlib rather than reconstructed: the transitive closure of an acyclic
relation on a finite type is irreflexive and transitive, hence well-founded, and
a well-founded relation extends to a well order.

**The finiteness cost was over-recorded too.** Lemma 3.7 wants a finite set and
Theorem 3.6 applies it to `Dᵢ ⊆ {1, …, k}`, which is `Fin c.len` and finite for
free. `not_stable_of_cycle` does **not** assume `X` finite, where print's `A` is.

**Theorem 3.8 is still not carried.** Its proof runs the other way — from an
empty core it builds a cycle, choosing the `Cᵢ` inside the dominating sets and
closing them up — and that construction is not transcribed.

**One fidelity defect was found and fixed while doing it.** Definition 3.3 writes
`Sᵢ ∈ 2^N`, and p. 94 defines `2^D = P(D) \ {∅}`, so a cycle's coalitions are
non-empty. The first transcription dropped that, which made `Cycle` wider than
print and Theorem 3.6 false — the empty coalition dominates nothing.
`Cycle.Snonempty` carries it now. Non-emptiness of each `Bᵢ` is **not** a field:
print gets it from Definition 2.1(i), which this module does not impose on `E`,
so it is a hypothesis of Theorem 3.6 and a derivation inside `acyclic_of_stable`.

**Lemma 3.5's strong cycle** is also not carried, because nothing consumes it.
Keiding's own reason for needing the weaker notion is on p. 96: Peleg 1983a
example 6.3.16 gives an unstable `E` with no strong cycle.

## Non-vacuity, both sides

Neither side of the predicate is assumed inhabited; both are proved.

* `acyclic_bot` — the effectivity function effective for nothing is acyclic. A
  cycle needs some `Bᵢ ∈ E(Sᵢ)` and `len > 0`.
* `Examples.Sovereignty.Stability.duelCycle` — two agents, two outcomes, agent
  `i` effective for exactly outcome `i`, blocks crossed. The chain condition is
  discharged by the argument that makes cycles finite objects at all:
  consecutive indices must differ, because a block never meets its own `B`
  (`Cycle.ne_of_block_inter_B_nonempty`), so with two agents any chain of length
  two visits both, and two singleton coalitions intersect emptily.

`duel_not_acyclic` follows, and `duel_not_stable` now draws Theorem 3.6's
conclusion on the same object: some profile of weak orders leaves every outcome
dominated. `duel_stable_would_be_acyclic` runs the contrapositive on it, and
`noEmptySet_duel` discharges Definition 2.1(i), so both routes are exercised.
