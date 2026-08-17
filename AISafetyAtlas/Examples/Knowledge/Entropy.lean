module

public import AISafetyAtlas.Knowledge.Entropy

/-!
# The null set entropy cannot see

`AISafetyAtlas.Knowledge.Entropy` proves that knowability forces the conditional
entropy to vanish, and says the converse fails. This is the counterexample that
makes that non-claim load-bearing rather than cautious.

The state space is `Fin 2`, the observation tells the two states apart not at all,
and the property is the state itself. So the property is **not** knowable: no
decoder reading a constant can return two different values.

Now weigh the space with `Measure.dirac 0`. The second state has measure zero,
the property is almost surely constant, and the conditional entropy is `0`.

Both facts hold of the same three objects at once, which is what a
counterexample has to do. Entropy answers a question about the measure;
`Knowable` answers a question about every state, and a null set is exactly the
difference between them.

The example is as small as it can be — two states and a point mass — because the
gap is not a subtle one. Any measure that misses a colliding pair produces it.
-/

namespace AISafetyAtlas.Examples.Knowledge

open MeasureTheory ProbabilityTheory
open AISafetyAtlas.Knowledge

/-- The observation that separates nothing. -/
@[expose] public def blindObservation : Fin 2 → Unit := fun _ => ()

/-- The property to be recovered: the state itself. -/
@[expose] public def wholeState : Fin 2 → Fin 2 := id

/-- The point mass that cannot see the second state. -/
@[expose] public noncomputable def pointMass : Measure (Fin 2) := Measure.dirac 0

public instance : IsProbabilityMeasure pointMass := by
  unfold pointMass; infer_instance

/-- **Not knowable.** A decoder reading a constant returns a constant, and the
property is not constant. -/
public theorem not_knowable_wholeState : ¬ Knowable blindObservation wholeState := by
  rintro ⟨decoder, hdec⟩
  have h0 : (0 : Fin 2) = decoder () := hdec 0
  have h1 : (1 : Fin 2) = decoder () := hdec 1
  exact absurd (h0.trans h1.symm) (by decide)

/-- **Yet the conditional entropy vanishes**, because the colliding state is
null. -/
public theorem condEntropy_wholeState_eq_zero :
    H[wholeState | blindObservation ; pointMass] = 0 := by
  have hmap : pointMass.map wholeState = pointMass.map (fun _ : Fin 2 => (0 : Fin 2)) := by
    simp [pointMass, wholeState, measurable_id, measurable_const]
  have hent : H[wholeState ; pointMass] = 0 := by
    rw [entropy_def, hmap, ← entropy_def]
    exact entropy_const 0
  have hle : H[wholeState | blindObservation ; pointMass] ≤ H[wholeState ; pointMass] :=
    condEntropy_le_entropy pointMass measurable_id measurable_const
  have hnn : 0 ≤ H[wholeState | blindObservation ; pointMass] :=
    condEntropy_nonneg wholeState blindObservation pointMass
  linarith

/-- **The two together.** Vanishing conditional entropy is not a certificate of
knowability, so `Knowledge.Entropy`'s implication cannot be strengthened to an
`iff`. -/
public theorem condEntropy_eq_zero_and_not_knowable :
    H[wholeState | blindObservation ; pointMass] = 0
      ∧ ¬ Knowable blindObservation wholeState :=
  ⟨condEntropy_wholeState_eq_zero, not_knowable_wholeState⟩

end AISafetyAtlas.Examples.Knowledge
