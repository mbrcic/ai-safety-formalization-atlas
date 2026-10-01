module

public import AISafetyAtlas.Logic

/-!
# Lawvere's fixed point, used the way it is actually used

`AISafetyAtlas.Logic.lawvere_fixed_point` says that a family `f : α → (α → β)`
representing *every* function `α → β` forces every endofunction of `β` to have a
fixed point. It had no application anywhere, and the reason is worth stating,
because it is not that nobody got round to it.

**The theorem's hypothesis is almost never satisfiable, and that is the point.**
Any `β` with two elements carries an endofunction with no fixed point — `not` on
`Bool` — so the conclusion fails, so the hypothesis must: no `f : α → (α → Bool)`
is surjective, for any `α` whatsoever. That is Cantor's theorem, and running
Lawvere in the contrapositive is how it is used in practice.

So the witness for a fixed-point theorem whose fixed points are unobtainable is
the diagonal argument it encodes. `no_surjection_onto_predicates` is that, at an
arbitrary type and with no cardinality reasoning anywhere in it.
-/

namespace AISafetyAtlas.Examples.Logic

open AISafetyAtlas.Logic

/-- **`not` has no fixed point**, which is the whole input to the argument. -/
public theorem not_has_no_fixed_point : ¬ ∃ b : Bool, (!b) = b := by
  rintro ⟨b, hb⟩
  cases b <;> simp at hb

/--
**Cantor's theorem, out of Lawvere's.** No family indexed by `α` represents every
predicate on `α` — for *any* `α`, with no counting and no finiteness. Feed the
fixed-point theorem an endofunction that has none and the hypothesis is what
gives way.
-/
public theorem no_surjection_onto_predicates {α : Type*} (f : α → α → Bool) :
    ¬ Function.Surjective f :=
  fun hf => not_has_no_fixed_point (lawvere_fixed_point f hf (fun b => !b))

/-- The same at a named type, so the general statement has an instance and not
only a proof. -/
public theorem no_surjection_onto_bool_predicates (f : ℕ → ℕ → Bool) :
    ¬ Function.Surjective f :=
  no_surjection_onto_predicates f

/-- **And the positive direction is not vacuous**: where `β` is a point, every
endofunction does have a fixed point, and a surjection exists. The theorem is
therefore true-and-usable rather than true-and-empty — its content is entirely
in the contrapositive above. -/
public theorem fixed_point_at_unit (g : Unit → Unit) : ∃ y, g y = y :=
  lawvere_fixed_point (fun (_ : Unit) (_ : Unit) => ()) (fun _ => ⟨(), funext fun _ => rfl⟩) g

end AISafetyAtlas.Examples.Logic
