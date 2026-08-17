module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Capacity of a discrete noiseless channel

`channelCapacity O = log |O|`: the logarithm of the number of distinct signals a
channel can carry, which is Shannon's capacity per use when the channel is
noiseless.

The definition takes the **output type**, not a signal count together with a use
count. That choice is what makes repeated use and parallel composition into
*lemmas* — `channelCapacity_fun` and `channelCapacity_prod` — rather than
separate definitions that would then have to be related.

Nothing here is about control, or about any particular application. This is a
finite-cardinality quantity with three closure properties:

* it is read off any presentation of the signal count as a power
  (`channelCapacity_eq_of_card_eq_pow`, with
  `channelCapacity_eq_of_card_eq_two_pow` for the bit case);
* `n` uses of one channel carry `n` times its capacity (`channelCapacity_fun`);
* channels used side by side add (`channelCapacity_prod`);
* and it is monotone in the signal count (`channelCapacity_le_of_card_le`).

`AISafetyAtlas.Control.RequisiteVariety` is one consumer, where this is Ashby's
measure of a regulator's variety and the four capacity exercises of his §11/14
are instances of the lemmas above. It is not the only possible one, which is why
this lives here rather than there.

The noisy case — capacity as `sup I(in ; out)` over input distributions — is
**not** defined here and is not needed by the noiseless statements.
-/

namespace AISafetyAtlas.InformationTheory

open Real

/--
**Capacity of a discrete noiseless channel**: `log` of the number of distinct
signals it can carry, which is Shannon's capacity per use for a noiseless
channel.

Defined on the output type rather than on a signal count and a use count, so
that repeated use and parallel channels are lemmas rather than separate
definitions — see `channelCapacity_fun` and `channelCapacity_prod`.
-/
@[expose] public noncomputable def channelCapacity (O : Type*) [Fintype O] : ℝ :=
  Real.log (Fintype.card O)

/-- Capacity is read off any presentation of the signal count as a power, which
is the form a channel's specification usually takes. -/
public theorem channelCapacity_eq_of_card_eq_pow {O : Type*} [Fintype O] {b n : ℕ}
    (h : Fintype.card O = b ^ n) : channelCapacity O = n * Real.log b := by
  rw [channelCapacity, h]
  push_cast
  rw [Real.log_pow]

/-- Capacity in bits. Stated separately from `channelCapacity_eq_of_card_eq_pow`
so that a caller never has to normalize casts on a term containing the signal
count — that count can be astronomically large, and `push_cast` would try to
evaluate it. -/
public theorem channelCapacity_eq_of_card_eq_two_pow {O : Type*} [Fintype O] {n : ℕ}
    (h : Fintype.card O = 2 ^ n) : channelCapacity O = n * Real.log 2 := by
  rw [channelCapacity_eq_of_card_eq_pow h]
  norm_num

/-- **`n` uses of one channel carry `n` times its capacity.** -/
public theorem channelCapacity_fun (A : Type*) [Fintype A] (n : ℕ) :
    channelCapacity (Fin n → A) = n * Real.log (Fintype.card A) :=
  channelCapacity_eq_of_card_eq_pow (by simp)

/-- **Channels used side by side add their capacities.** This is what lets two
channels running at different rates be counted together. -/
public theorem channelCapacity_prod (O₁ O₂ : Type*) [Fintype O₁] [Fintype O₂]
    [Nonempty O₁] [Nonempty O₂] :
    channelCapacity (O₁ × O₂) = channelCapacity O₁ + channelCapacity O₂ := by
  have h₁ : (Fintype.card O₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h₂ : (Fintype.card O₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [channelCapacity, channelCapacity, channelCapacity, Fintype.card_prod]
  push_cast
  exact Real.log_mul h₁ h₂

/-- Capacity is monotone in the signal count. -/
public theorem channelCapacity_le_of_card_le {O₁ O₂ : Type*} [Fintype O₁] [Fintype O₂]
    [Nonempty O₁] (h : Fintype.card O₁ ≤ Fintype.card O₂) :
    channelCapacity O₁ ≤ channelCapacity O₂ :=
  Real.log_le_log (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast h)

end AISafetyAtlas.InformationTheory
