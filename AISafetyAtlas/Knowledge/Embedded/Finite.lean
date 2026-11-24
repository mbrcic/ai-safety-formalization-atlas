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
| **Boundary** | `not_measuresAllStates_of_card_lt` | Breuer §3.4's finite remark: a cardinality gap defeats every inference map, meshing or not |
| **Law** | `card_lt_of_properInclusion` | Breuer §3.4: surjective restriction plus proper inclusion gives `card A < card Ω` |

All five are classical. The first three and `card_lt_of_properInclusion` route
through `properInclusion_iff_not_injective`, whose backward direction pushes a
negation through a binder and so pulls `Classical.choice`;
`not_measuresAllStates_of_card_lt` chooses a reading per state. Constructivity does not follow from the finiteness.

## Bekenstein

Entropy/energy bounds (Bekenstein and related literature) can **motivate**
finite operational models in provenance notes. They do **not** automatically
yield `|A| < |Ω|` for every physical subsystem, and this module does not encode
any such implication. See `docs/provenance/self-measurement-kernel.md`.

## Explicit non-claims

* Not “every physical containment has a cardinality gap.”
* Not a quantum / continuum result.
* Not Breuer’s §3.5 theorems (those remain `Knowledge.Embedded`). The two §3.4
  declarations above are the paper's finite remark, stated as printed.
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
**Breuer §3.4, the finite remark, without meshing.** *"If `O` has only finitely
many possible states, this already exludes the possibility of exact measurement
of all states from inside the observed system"* (Breuer 1995, §3.4, printed
before meshing is introduced in §3.5). With strictly fewer apparatus states than
global states, no inference map at all — meshing or not — exactly measures every
state: measuring every state injects the global states into the readings
(`exists_injective_of_measuresAllStates`).

`no_meshing_measures_all_of_card_lt` is this theorem with a meshing hypothesis
it does not need.
-/
public theorem not_measuresAllStates_of_card_lt
    {Ω : Type u} {A : Type v} [Fintype Ω] [Fintype A] (M : InferenceMap Ω A)
    (h : Fintype.card A < Fintype.card Ω) :
    ¬ MeasuresAllStates M := fun hall => by
  obtain ⟨g, hg⟩ := exists_injective_of_measuresAllStates M hall
  exact Nat.lt_le_asymm h (Fintype.card_le_of_injective g hg)

/--
**Breuer §3.4: proper inclusion leaves strictly more global states.** *"But if
additionally `A` is a properly included in `O`, there are strictly more states of
`O` than states of `A`"* — the printed sentence asserts it from proper inclusion
and the §3.3 surjective restriction. The converse of `properInclusion_of_card_lt`
under surjectivity.

Finite only, and necessarily so: on `ℕ` the map `n ↦ n / 2` is surjective and
not injective with equal cardinalities, so the sentence read at an infinite `O`
is false. The finite form is the one the printed next sentence uses.
-/
public theorem card_lt_of_properInclusion
    {Ω : Type u} {A : Type v} [Fintype Ω] [Fintype A]
    (restrict : Restriction Ω A) (hsurj : Function.Surjective restrict)
    (hp : ProperInclusion restrict) :
    Fintype.card A < Fintype.card Ω :=
  Fintype.card_lt_of_surjective_not_injective restrict hsurj
    ((properInclusion_iff_not_injective restrict).mp hp)

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
