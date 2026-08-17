module

public import AISafetyAtlas.InformationTheory.Determinism
public import Mathlib.Data.Fin.Basic

/-!
# A coarsening carries no new uncertainty

`InformationTheory.condEntropy_comp_self_left` at concrete types, to fix which
direction it runs in.

The state is one of four values and the coarsening reports only which half it
fell in. Knowing the state tells you the half, so the half adds nothing:
`H[half ∘ state | state] = 0`, whatever the measure.

The converse reading — that knowing the half tells you the state — is false, and
that is the whole content of the asymmetry. The lemma is about a function of the
conditioning variable, not about a function whose value the conditioning variable
happens to determine in some other sense.

`AISafetyAtlas.Examples.Knowledge.Entropy` carries the sharper failure: even
`H[Y | X] = 0` does not make `Y` a function of `X` at every state, because a
measure cannot see a null set.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory
open AISafetyAtlas.InformationTheory (condEntropy_comp_self_left)

/-- Four states. -/
@[expose] public def state : Fin 4 → Fin 4 := id

/-- The coarsening: which half of the range the state fell in. -/
@[expose] public def half : Fin 4 → Bool := fun n => 2 ≤ n.val

/--
**The coarsening adds nothing.** `H[half ∘ state | state ; μ] = 0` for every
measure, because `half ∘ state` is a function of `state`.

Stated for an arbitrary measure rather than a chosen one: the lemma does not
depend on how the four states are weighted, which is the point of it.
-/
public theorem condEntropy_half_state_eq_zero (μ : Measure (Fin 4))
    [IsZeroOrProbabilityMeasure μ] :
    H[half ∘ state | state ; μ] = 0 :=
  condEntropy_comp_self_left μ (measurable_of_countable state) (measurable_of_countable half)

/-- The coarsening really does lose something: two states share a half. This is
what makes the direction of `condEntropy_half_state_eq_zero` a claim rather than
a symmetry. -/
public theorem half_not_injective : ¬ Function.Injective half := by
  intro h
  have : (0 : Fin 4) = 1 := h (by decide)
  exact absurd this (by decide)

end AISafetyAtlas.Examples.InformationTheory
