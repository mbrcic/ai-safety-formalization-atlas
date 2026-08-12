module

import AISafetyAtlas.Knowledge.SelfReference

/-!
# Both sides of the self-model characterization

`selfComplete_iff_subsingleton_rest` is an iff, and an iff whose right side were
uninhabitable would be an impossibility result wearing a disguise. Both
directions are inhabited here.

The degenerate case is the interesting one to state: an observer *can* completely
know the state it is in, provided there is nothing in that state except itself.
That is what makes the obstruction a characterization rather than a blanket
denial — and it is the precise sense in which "a system cannot model itself" is
false as usually said.
-/

namespace AISafetyAtlas.Examples.Knowledge.SelfReference

open AISafetyAtlas.Knowledge.SelfReference

/-! ## Completeness is achievable — and only degenerately

With a one-element remainder there is nothing besides the model, and the
projection is injective. -/

example : SelfComplete Bool Unit :=
  selfComplete_iff_subsingleton_rest.mpr inferInstance

/-! ## Anything else defeats it

One bit outside the model is enough. Note the model here is a single value: the
obstruction is not about the model being *small*, it is about the remainder being
nontrivial. -/

example : ¬ SelfComplete Unit Bool :=
  not_selfComplete_of_two_rest () (by decide : (false : Bool) ≠ true)

/-- A larger model does not help — `Bool × Bool` states, a two-valued model. -/
example : ¬ SelfComplete Bool Bool :=
  not_selfComplete_of_two_rest true (by decide : (false : Bool) ≠ true)

/-! ## The counting form agrees

`card_rest_le_one_of_selfComplete` is the same obstruction as an inequality. Its
contrapositive on a two-element remainder is the previous example, reached by
cardinality rather than by exhibiting a pair. -/

example (h : SelfComplete Bool Bool) : Fintype.card Bool ≤ 1 :=
  card_rest_le_one_of_selfComplete h

/-! ## What is not shown

Nothing here is dynamic: the state does not change while being modelled, and no
observer updates anything. The obstruction is structural, and one level deep —
there is no regress over models of models. -/

end AISafetyAtlas.Examples.Knowledge.SelfReference
