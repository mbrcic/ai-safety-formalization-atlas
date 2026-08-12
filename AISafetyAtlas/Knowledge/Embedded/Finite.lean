module

public import AISafetyAtlas.Knowledge.Embedded.Composition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

/-!
# Finite operational cardinality bridges

When apparatus and global state spaces are finite, a strict cardinality gap

\[
  |A| < |\Omega|
\]

forces the restriction `Ω → A` to be non-injective (pigeonhole), hence
`ProperInclusion`, hence Breuer Proposition 1 under meshing.

This is **not** the universal physical theorem. It is the operational corollary
for finite hardware abstractions, bounded controllers, and discretized
environments. Infinite or continuous models should use
`Embedded.Composition` (nontrivial remainder) instead of inventing a cardinality
comparison they do not have.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `properInclusion_of_card_lt` | Pigeonhole: `card A < card Ω` forces the restriction to collide |
| **Boundary** | `no_meshing_measures_all_of_card_lt` | Breuer Proposition 1 under a finite cardinality gap |
| **Law** | `properInclusion_product_of_card_rest_ge_two` | Product form, when only `2 ≤ card R` is known rather than two named remainders |

All three are classical: they route through `properInclusion_iff_not_injective`,
whose backward direction pushes a negation through a binder and so pulls
`Classical.choice`. Constructivity does not follow from the finiteness.

## Bekenstein

Entropy/energy bounds (Bekenstein and related literature) can **motivate**
finite operational models in provenance notes. They do **not** automatically
yield `|A| < |Ω|` for every physical subsystem, and this module does not encode
any such implication. See `docs/provenance/self-measurement-kernel.md`.

## Explicit non-claims

* Not “every physical containment has a cardinality gap.”
* Not a quantum / continuum result.
* Not Breuer’s paper theorem (that remains `Knowledge.Embedded`).
-/

namespace AISafetyAtlas.Knowledge.Embedded.Finite

open AISafetyAtlas.Knowledge.Embedded
open AISafetyAtlas.Knowledge.Embedded.Composition

universe u v

/--
**Pigeonhole.** A map from a larger finite set into a smaller one cannot be
injective, so the restriction properly includes (collides).
-/
public theorem properInclusion_of_card_lt
    {Ω : Type u} {A : Type v} [Fintype Ω] [Fintype A]
    (restrict : Restriction Ω A)
    (h : Fintype.card A < Fintype.card Ω) :
    ProperInclusion restrict := by
  apply (properInclusion_iff_not_injective restrict).mpr
  intro hinj
  have hle : Fintype.card Ω ≤ Fintype.card A :=
    Fintype.card_le_of_injective restrict hinj
  exact Nat.lt_le_asymm h hle

/--
**Breuer Proposition 1 under a finite cardinality gap.**

If the apparatus has strictly fewer finite states than the global system, no
meshing inference map exactly measures every global state.
-/
public theorem no_meshing_measures_all_of_card_lt
    {Ω : Type u} {A : Type v} [Fintype Ω] [Fintype A]
    (restrict : Restriction Ω A) (M : InferenceMap Ω A)
    (h : Fintype.card A < Fintype.card Ω)
    (hm : Meshing restrict M) :
    ¬ MeasuresAllStates M :=
  no_meshing_inference_measures_all_states restrict M
    (properInclusion_of_card_lt restrict h) hm

/--
Specialisation to product models: if the remainder is finite and nontrivial
(`|R| ≥ 2`) and the apparatus is nonempty finite, then
`|A| < |A × R|` and the projection collides. Redundant with
`properInclusion_of_nontrivial_remainder` when two remainder points are known,
but useful when only a cardinality lower bound on `R` is available.
-/
public theorem properInclusion_product_of_card_rest_ge_two
    {A : Type v} {R : Type u} [Fintype A] [Fintype R] [Nonempty A]
    (hR : 2 ≤ Fintype.card R) :
    ProperInclusion (productRestriction A R) := by
  have hposA : 0 < Fintype.card A := Fintype.card_pos
  have hcard : Fintype.card A < Fintype.card (A × R) := by
    rw [Fintype.card_prod]
    -- `|A| < |A| * |R|` when `|A| > 0` and `|R| ≥ 2`
    have : Fintype.card A * 1 < Fintype.card A * Fintype.card R := by
      exact Nat.mul_lt_mul_of_pos_left (Nat.lt_of_lt_of_le (by decide : 1 < 2) hR) hposA
    simpa using this
  exact properInclusion_of_card_lt (productRestriction A R) hcard

end AISafetyAtlas.Knowledge.Embedded.Finite
