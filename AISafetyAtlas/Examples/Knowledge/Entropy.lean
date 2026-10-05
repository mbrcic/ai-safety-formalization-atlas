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

/-! ## The criterion in the direction that does certify

The pair above shows a vanishing conditional entropy is not a certificate of
knowability. The converse direction is: a *non*-vanishing one certifies
unknowability, and it is a criterion rather than an observation because it never
looks at a decoder. Under a measure that sees both states it applies to the same
blind observation.
-/

/-- The fair coin, which unlike `pointMass` gives the colliding state weight. -/
@[expose] public noncomputable def fairCoin : Measure (Fin 2) :=
  uniformOn (Set.univ : Set (Fin 2))

public instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin; infer_instance

/-- Under the fair coin the blind observation leaves a whole bit undetermined. -/
public theorem condEntropy_wholeState_fairCoin :
    H[wholeState | blindObservation ; fairCoin] = Real.log 2 := by
  have hind : ProbabilityTheory.IndepFun wholeState blindObservation fairCoin :=
    ProbabilityTheory.indepFun_const_right _ ()
  rw [hind.condEntropy_eq_entropy measurable_id measurable_const, fairCoin, wholeState,
    IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- **So the state is not knowable, by the entropy criterion.**
`not_knowable_wholeState` reaches the same conclusion by chasing a decoder; this
reaches it without ever naming one, which is what makes the criterion worth
having. -/
public theorem not_knowable_by_entropy : ¬ Knowable blindObservation wholeState :=
  not_knowable_of_condEntropy_ne_zero fairCoin measurable_const
    (by rw [condEntropy_wholeState_fairCoin]; positivity)

/-! ## Fano through a decoder, where the bound is not zero

`le_errorProb_of_decoder` is the Fano bound with a decoder in the middle: the
observation is post-processed, the Markov chain argument absorbs it, and what
comes back is a lower bound on the error probability. Nothing had run it.

**Running it at two states would be a waste of the statement.** With an alphabet
of size two the bound reads `(H - log 2) / log 2`, and the blind observation
leaves exactly `log 2`, so the bound is `0` and `0 ≤ error` is free. The point of
Fano is that it forces error to be *positive*, and that needs an alphabet with
room in it.

So the model here is four states, uniform, and an observation that sees none of
them. The bound comes out at exactly `1 / 2`: **no decoder whatsoever recovers
the state more than half the time**, which is a statement about every decoder
and not about the one below.
-/

/-- Four states, uniform. -/
@[expose] public noncomputable def fairFour : Measure (Fin 4) :=
  uniformOn (Set.univ : Set (Fin 4))

public instance : IsProbabilityMeasure fairFour := by
  unfold fairFour; infer_instance

/-- The property is the whole state. -/
@[expose] public def wideState : Fin 4 → Fin 4 := id

/-- The observation sees nothing. -/
@[expose] public def blindWide : Fin 4 → Unit := fun _ => ()

/-- A decoder that always guesses the same state. Any other decoder would do:
the bound below does not mention it. -/
@[expose] public def zeroDecoder : Unit → Fin 4 := fun _ => 0

public instance : FiniteRange (fun _ : Fin 4 => PUnit.unit) := ⟨Set.toFinite _⟩
public instance : FiniteRange blindWide := ⟨Set.toFinite _⟩
public instance : FiniteRange wideState := ⟨Set.toFinite _⟩
public instance : FiniteRange (zeroDecoder ∘ blindWide) := ⟨Set.toFinite _⟩
public instance :
    FiniteRange (AISafetyAtlas.InformationTheory.errorPair wideState
      (zeroDecoder ∘ blindWide)) := ⟨Set.toFinite _⟩

/-- The blind observation leaves two whole bits undetermined. -/
public theorem condEntropy_wideState_fairFour :
    H[wideState | blindWide ; fairFour] = Real.log 4 := by
  have hind : ProbabilityTheory.IndepFun wideState blindWide fairFour :=
    ProbabilityTheory.indepFun_const_right _ ()
  rw [hind.condEntropy_eq_entropy measurable_id measurable_const, fairFour, wideState,
    IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- **Fano, through the decoder.** -/
public theorem fano_through_decoder :
    (H[wideState | blindWide ; fairFour] - Real.log 2)
        / Real.log ((Finset.univ : Finset (Fin 4)).card : ℝ)
      ≤ AISafetyAtlas.InformationTheory.errorProb fairFour wideState
        (zeroDecoder ∘ blindWide) :=
  le_errorProb_of_decoder (A := (Finset.univ : Finset (Fin 4))) fairFour
    measurable_const measurable_id (fun _ => Finset.mem_univ _) (by simp) zeroDecoder

/-- **And the bound is a half**, not zero -- which is what makes running it at
four states rather than two worth the trouble. -/
public theorem fano_bound_eq_half :
    (H[wideState | blindWide ; fairFour] - Real.log 2)
        / Real.log ((Finset.univ : Finset (Fin 4)).card : ℝ) = 1 / 2 := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [condEntropy_wideState_fairFour]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  rw [h4]
  field_simp
  ring

/-- **So the decoder is wrong at least half the time.** -/
public theorem half_le_errorProb :
    (1:ℝ) / 2 ≤ AISafetyAtlas.InformationTheory.errorProb fairFour wideState
      (zeroDecoder ∘ blindWide) :=
  fano_bound_eq_half ▸ fano_through_decoder

end AISafetyAtlas.Examples.Knowledge
