module

public import AISafetyAtlas.Preference

/-!
# The core degeneracy, at two behaviours and two rewards

`AISafetyAtlas.Preference` opens with Armstrong and Mindermann's core
observation: a planner and a reward together explain a behaviour, and with the
planner free to vary, *every* reward explains *every* behaviour. Two statements
of that had no application anywhere, so the degeneracy was proved and never
exhibited.

Nothing here needs a model worth the name — that is the point. The smallest
types make the degeneracy plainest: the identity planner explains its own
output, and the set of rewards consistent with a fixed behaviour is everything.
-/

namespace AISafetyAtlas.Examples.Preference

open AISafetyAtlas.Preference

/-- The planner that carries the reward through unchanged. -/
@[expose] public def literal : Planner Bool Bool := id

/-- **A behaviour in a planner's range has a reward explaining it.** The forward
half of the degeneracy, at the literal planner where the reward is the behaviour
itself. -/
public theorem literal_explains_true : ∃ r : Bool, Explains literal r true :=
  exists_reward literal true ⟨true, rfl⟩

/-- **And every reward is consistent with every behaviour.** The half that makes
it a degeneracy rather than an observation: the consistent set is not merely
large, it is everything, so consistency alone rules nothing out. -/
public theorem consistent_with_true_is_everything :
    {r : Bool | ∃ p : Planner Bool Bool, Explains p r true} = Set.univ :=
  consistent_rewards_eq_univ true

end AISafetyAtlas.Examples.Preference
