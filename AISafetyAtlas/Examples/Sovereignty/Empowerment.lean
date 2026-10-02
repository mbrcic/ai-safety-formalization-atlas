module

public import AISafetyAtlas.Sovereignty.Empowerment

/-!
# Four inputs, two outputs, one bit of empowerment

`parity_empowerment` is the reading `B2` is for: an actuator with four settings
that moves only a single bit has one bit of empowerment, and the three extra
settings buy nothing. `constant_empowerment` is the degenerate end -- an
actuator that always does the same thing has none, whatever its input alphabet.

Both are computations of `Set.ncard (Set.range f)` and nothing else, which is
the content of `B2`: the input alphabet enters only through what it reaches.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Empowerment

open AISafetyAtlas.Sovereignty
open Real

/-- An actuator with four settings that only flips one bit. -/
@[expose] public def parity (i : Fin 4) : Bool := i.val % 2 == 0

/-- Both outputs are reachable. -/
public theorem parity_range : Set.range parity = (Set.univ : Set Bool) := by
  ext b
  cases b <;> simp
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- **One bit of empowerment**, from four settings. -/
public theorem parity_empowerment : empowerment parity = log 2 := by
  rw [empowerment_eq_log_card_range, parity_range, Set.ncard_univ, Nat.card_eq_fintype_card]
  norm_num

/-- An actuator that always does the same thing. -/
@[expose] public def constant (_ : Fin 4) : Bool := true

/-- Only one output is reachable. -/
public theorem constant_range : Set.range constant = ({true} : Set Bool) := by
  ext b
  cases b <;> simp [constant]

/-- **No empowerment at all.** -/
public theorem constant_empowerment : empowerment constant = 0 := by
  rw [empowerment_eq_log_card_range, constant_range, Set.ncard_singleton]
  simp

/-! ## Empowerment is a channel capacity -/

/-- **The actuator's empowerment is the capacity of the channel it opens.**

`parity_empowerment` computes the number; this says what the number *is*. The
identification is the reason empowerment inherits the information-theoretic
reading rather than merely resembling one -- and at this actuator both sides are
`log 2`, one bit from four settings. -/
public theorem parity_empowerment_eq_capacity :
    empowerment parity =
      InformationTheory.channelCapacity (Set.range parity) :=
  empowerment_eq_channelCapacity_range parity

end AISafetyAtlas.Examples.Sovereignty.Empowerment
