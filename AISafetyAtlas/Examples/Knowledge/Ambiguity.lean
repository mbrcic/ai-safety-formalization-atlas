module

import AISafetyAtlas.Knowledge.Ambiguity
import Mathlib.Data.Fintype.Prod

/-!
# What the counting bound catches, and what it misses

`AISafetyAtlas.Knowledge.Ambiguity` offers two ways to refute exactness: name a
colliding pair, or compare two cardinalities. They are not the same strength, and
a module that only showed the first working would leave the second looking like
a restatement.

Three models:

1. the counting obstruction firing where no pair is named;
2. a model where **the cardinalities are fine and the property is still
   unknowable** — so `not_knowable_of_card_lt` is sufficient, never necessary;
3. ambiguity **strictly** increasing under coarsening, so `ambiguity_le_of_comp`
   is not silently an equality.

Model 2 is the one that keeps the bound honest.
-/

namespace AISafetyAtlas.Examples.Knowledge.Ambiguity

open AISafetyAtlas.Knowledge

/-! ## 1. Counting alone refutes exactness

Four states, a two-valued observation, a three-valued target. No colliding pair
is exhibited anywhere below — the refutation is `2 < 3`. -/

private def obs2 : Fin 4 → Bool
  | 0 => false | 1 => false | 2 => true | 3 => true

private def tgt3 : Fin 4 → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 2

example : ¬ Knowable obs2 tgt3 :=
  not_knowable_of_card_lt (by decide)

/-! ## 2. The bound is sufficient, not necessary

Here the observation has exactly as many outcomes as the target has values, so
the counting test is silent — and the target is still not knowable, because the
two outcomes are matched to the wrong states. Exactness is about *which* states
collide, not only *how many* values there are. -/

private def obsFst : Bool × Bool → Bool := Prod.fst
private def tgtSnd : Bool × Bool → Bool := Prod.snd

/-- The counting test cannot fire: both cardinalities are 2. -/
example : (Finset.univ.image obsFst).card = (Finset.univ.image tgtSnd).card := by
  decide

/-- Yet the target is not knowable — a colliding pair is required to see it. -/
example : ¬ Knowable obsFst tgtSnd :=
  not_knowable_of_collision (ω₁ := (false, false)) (ω₂ := (false, true))
    rfl (by decide)

/-- And the ambiguity count registers what the cardinality comparison missed. -/
example : ambiguity obsFst tgtSnd false = 2 := by decide

/-! ## 3. Coarsening strictly loses information

An injective observation reads every state exactly; collapsing it to a single
value loses both. `ambiguity_le_of_comp` bounds this, and the bound is strict
here, so it is not an equality in disguise. -/

private def obsId : Bool → Bool := id
private def tgtId : Bool → Bool := id

example : ambiguity obsId tgtId true = 1 := by decide

example : ambiguity (fun ω => (fun _ => ()) (obsId ω)) tgtId () = 2 := by decide

/-- The instance of the general bound, with the inequality strict. -/
example :
    ambiguity obsId tgtId true
      < ambiguity (fun ω => (fun _ => ()) (obsId ω)) tgtId () := by
  decide

/-! ## What none of this shows

Counting possibilities is not weighing them. Nothing here says an ambiguity of 2
is twice as bad as an ambiguity of 1, or attaches a probability to either
outcome; `ambiguity` is a cardinality and carries no measure. -/

end AISafetyAtlas.Examples.Knowledge.Ambiguity
