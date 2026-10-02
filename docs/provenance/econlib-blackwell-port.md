# Porting Econlib's bounded fixed-point core (2026-09-16)

Registry row `LAND-BELLMAN-BDD-001`. Notice:
[`AISafetyAtlas/Upstream/LICENSE-NOTICE`](../../AISafetyAtlas/Upstream/LICENSE-NOTICE).
Costing this executes:
[`lean-reuse-sources.md`](../agent/policy/lean-reuse-sources.md), section
"`danlyng/Econlib` against `AISafetyAtlas.Decision.DiscountedValue`".

## What was taken

One file. `Econlib/Math/Analysis/Blackwell.lean` at
`003655ccf010cdf44c4f67d6675167b54ce0e9df`, 301 lines, Apache-2.0 with **no
upstream `NOTICE`**, so redistribution incurs §4(a)–(c) and not §4(d).

    sha256  1879097686a79081481812eab72871a33ac01d635ef49369759a602b333f6c9d

It lands as `AISafetyAtlas/Analysis/Blackwell.lean`. Atlas changes: the
namespace; per-declaration `public` and `@[expose]` in place of upstream's
`@[expose] public section`, because a section-scoped declaration is invisible to
`scripts/check_public_api.py` and `scripts/check_print_axioms.py`; the two
closed-invariant-set lemmas moved out of Mathlib's `ContractingWith` namespace
into ours, so they are named rather than reached by dot notation and the
certificate is an explicit argument; and the toolchain repairs below. The
mathematics is Daniel Lyng's.

## What was declined, and why it is not a nearby call

The seventeen-file `Optimization/DynamicProgramming/` subtree. Its three
carriers are `DetMDP` (arbitrary state, **deterministic** transition), `FinMDP`
(state `Fin n`, stochastic) and `StochMDP` (state `ℝ`, measure-valued).
`AISafetyAtlas.Decision.MDP` is `T : State → Action → PMF State` over an
arbitrary state type — stochastic **and** unconstrained. Econlib has stochastic,
or unconstrained, never both, so `Core/Bellman.lean`'s contraction and
fixed-point theorems are statements about a deterministic transition and do not
transfer. What transfers is the method, and the method is the file that was
taken.

## The cost was measured by grepping names, and that was low by a factor of three

The costing checked every Mathlib name the upstream file mentions against
`.lake/packages/mathlib` at our pin and reported **one** absent name, used twice.
Compiling found four breakages:

| site | what happened |
|---|---|
| `bddAbove_range_abs_sub`, `toBddFun` | `abs_sub` in the form \|a − b\| ≤ \|a\| + \|b\| does not resolve. Restated once as a `private` lemma, used at both sites — this is the one the costing found |
| that restatement itself | its own ingredient had moved: `abs_add` is `abs_add_le` here |
| `contractingWith_liftBddFun` | `rw [NNReal.coe_mk]` finds no pattern, because the coercion of `⟨β, hβ₀⟩` is already `β`. A `show` discharges the cast instead |
| `BddFun` | `@[expose]` on an `abbrev` is a **hard error** at v4.33.0: "this declaration would be exposed by default" |

None is mathematics, each is one line, and the port took under an hour, so the
verdict stands. The method does not. Three of the four were invisible to a
name-by-name check, one of them *inside the repair that check proposed*. Read a
costing of this shape as a lower bound.

## What it buys

Gap 3 of `AISafetyAtlas.Decision.DiscountedValue`: the fixed point no longer
needs `[Fintype State]`. `AISafetyAtlas.Decision.BoundedValue` discharges
Blackwell's two conditions for the stochastic Bellman operator and defines
`vPiBdd` on an arbitrary `Nonempty` state type, in exchange for a uniform bound
on the reward, with the pointwise Bellman equation and uniqueness **among bounded
solutions**.

Three definitions — `qVal`, `bellmanPolicyOp`, `bellmanOptOp` — lost their
`[Fintype State]` binders in the same change, because none of them ever used
finiteness; only the fixed point did. So the atlas has one policy Bellman
operator under two completeness arguments, not two operators that resemble each
other.

`vPiBdd_eq_vPi` is the join: on a finite nonempty state type the two value
functions are the same function. Without it this would be a parallel development
with similar names, and the claim that anything was widened would rest on the
reader.

## What it does not buy

Gaps 1 and 2 of that module, on which no external tree bears. `vPi` is a
**stationary deterministic** policy's value, not the carrier's
history-dependent stochastic `Policy`; and it is **defined** as a fixed point
rather than proved equal to the discounted return along
`AISafetyAtlas.Decision.MDP.run`.

There is no bounded counterpart of `vStar`. The optimality operator maximises
over actions with `Finset.sup'`, so widening it is a statement about suprema over
a possibly infinite action set — a different change.

## The witness

`AISafetyAtlas/Examples/Decision/BoundedValue.lean` runs the layer where the
narrower development **cannot be stated**: a one-action walk on `ℕ` at discount
`1/2`.

* constant reward `1` → the constant value `2`, by handing the constant function
  to `vPiBdd_unique`;
* reward paid at state `0` only → a value that is **not constant**, so the fixed
  point is a function rather than a number in disguise;
* an alternating reward with no closed form computed → `vPiBdd_bounded` and the
  Bellman equation still bound it, which is the case boundedness-as-hypothesis
  exists for;
* the nonnegative bounded functions as a nonempty closed invariant set, so
  `isFixedPt_mem_of_isClosed` reads nonnegativity off the operator;
* `loop_vPiBdd_eq_vPi` runs the join on the finite model of
  `AISafetyAtlas.Examples.Decision.DiscountedValue`, and `loop_vPiBdd_eq_two`
  carries it through that module's own `vPi_act`.

The port added **no witness debt**: `scripts/check_witness_debt.py` reports 8
ungrounded, 3 leaves and 314 unapplied before and after, against 25 more pinned
public declarations. `scripts/check_print_axioms.py` is clean, so the new
material rests on nothing beyond `propext`, `Classical.choice` and `Quot.sound`.
