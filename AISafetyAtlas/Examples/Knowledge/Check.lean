module

public import AISafetyAtlas.Knowledge.Check

/-!
# What changes a knowability question, and what does not

`Knowledge.Check` carries the congruences: two ways of rewriting a knowability
question that leave the answer alone. Both had no application, so the rules an
argument would use to move between formulations were proved and never used.

The two are different in kind and the models here keep them apart.

* **Relabelling the observation changes nothing** when the relabelling is
  injective. An instrument that reports in different units is the same
  instrument. `blind` sees nothing and stays blind however its output is encoded.
* **Replacing the property changes nothing** when the new one has the same
  fibres. Knowability is a question about what the property *separates*, not
  about what it is called, so a property and any faithful recoding of it are
  knowable together.
-/

namespace AISafetyAtlas.Examples.Knowledge.Check

open AISafetyAtlas.Knowledge AISafetyAtlas.Knowledge.Check

/-- Two bits; the observation reports the first. -/
@[expose] public def readFirst : Bool × Bool → Bool := Prod.fst

/-- The property the observation cannot recover: the second bit. -/
@[expose] public def second : Bool × Bool → Bool := Prod.snd

/-- **It is not knowable.** Two worlds agreeing on the first bit and differing
on the second. -/
public theorem second_not_knowable : ¬ Knowable readFirst second := by
  rintro ⟨d, hd⟩
  have h0 := hd (true, false)
  have h1 := hd (true, true)
  rw [show readFirst (true, false) = readFirst (true, true) from rfl] at h0
  exact absurd (h0.trans h1.symm) (by decide)

/-! ## Relabelling the instrument -/

/-- An injective recoding of the observation's output. -/
@[expose] public def tag : Bool → Bool × Bool := fun b => (b, false)

public theorem tag_injective : Function.Injective tag := by
  intro a b h
  exact congrArg Prod.fst h

/-- **Recoding the instrument leaves the question alone.** The reading is now a
pair rather than a bit and the answer is the same, which is what lets an
argument normalise an observation type without arguing about it. -/
public theorem knowable_through_tag_iff :
    Knowable (tag ∘ readFirst) second ↔ Knowable readFirst second :=
  knowable_comp_left_iff tag_injective

/-- So the recoded instrument is blind to the second bit too. -/
public theorem second_not_knowable_through_tag : ¬ Knowable (tag ∘ readFirst) second :=
  fun h => second_not_knowable (knowable_through_tag_iff.mp h)

/-! ## Recoding the question -/

/-- The same property, reported as a number rather than a bit. -/
@[expose] public def secondAsNat : Bool × Bool → ℕ := fun u => if u.2 then 1 else 0

/-- It separates exactly what `second` separates. -/
public theorem secondAsNat_same_fibres (u v : Bool × Bool) :
    second u = second v ↔ secondAsNat u = secondAsNat v := by
  unfold second secondAsNat
  cases u.2 <;> cases v.2 <;> simp

/-- **A property and any faithful recoding of it are knowable together.**
Knowability asks what the property separates and not what its values are called,
so the answer cannot depend on the units. -/
public theorem knowable_secondAsNat_iff :
    Knowable readFirst second ↔ Knowable readFirst secondAsNat :=
  knowable_congr_property secondAsNat_same_fibres

/-- And so the numbered form is unknowable too — without re-running the
collision argument. -/
public theorem secondAsNat_not_knowable : ¬ Knowable readFirst secondAsNat :=
  fun h => second_not_knowable (knowable_secondAsNat_iff.mpr h)

end AISafetyAtlas.Examples.Knowledge.Check
