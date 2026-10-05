module

public import AISafetyAtlas.Preference.Complexity

/-!
# The pairing, and two compatible pairs

`encodeExplanation_injective` is exercised at the empty reward: the encoding of
two distinct behaviours under that fixed reward is itself distinct.

The rest of the file exercises the **evaluation map** the source's §5.1 lower
bound runs through. `EvaluatesTo` is a relation nobody can use until some pair
inhabits it, so both of `evalPair`'s witnesses are computed here at a concrete
behaviour, and the lower bound is instantiated at each. Without this the bound
would be a statement about a class that might be empty.
-/

namespace AISafetyAtlas.Examples.Preference

open AISafetyAtlas.Preference

/-- Injectivity of the encoding, fixed at the empty reward. -/
theorem encodeExplanation_injective_nil :
    Function.Injective (encodeExplanation ([] : Kolmogorov.BitString)) :=
  encodeExplanation_injective []

/-- Two distinct behaviours receive distinct encodings, exhibited by name. -/
theorem encodeExplanation_ne :
    encodeExplanation ([] : Kolmogorov.BitString) [true] ≠
      encodeExplanation ([] : Kolmogorov.BitString) [false] :=
  fun h => by simpa using encodeExplanation_injective_nil h

/-- A concrete behaviour to evaluate to. -/
@[expose] public def sampleBehaviour : Kolmogorov.BitString := [true, false, true]

/-- **The pairing reads back**, at the reading pair's own index. -/
theorem pairProgram_readerPair :
    pairProgram (readerPair sampleBehaviour) = Nat.Partrec.Code.id := by
  rw [readerPair, pairProgram_pairString, Denumerable.ofNat_encode]

/-- …and its reward slot is the behaviour. -/
theorem pairReward_readerPair :
    pairReward (readerPair sampleBehaviour) = sampleBehaviour :=
  pairReward_pairString _ _

/-- **A compatible pair, computed.** The reading pair evaluates to the behaviour. -/
theorem evaluatesTo_readerPair_sample :
    EvaluatesTo (readerPair sampleBehaviour) sampleBehaviour :=
  evaluatesTo_readerPair sampleBehaviour

/-- **The source's own degenerate pair is compatible too**, at the empty reward,
which is the source's `(p_π̇, 0)`. -/
theorem evaluatesTo_degeneratePair_sample :
    EvaluatesTo (degeneratePair [] sampleBehaviour) sampleBehaviour :=
  evaluatesTo_degeneratePair [] sampleBehaviour

/-- **The lower bound, instantiated at both.** One constant bounds the
behaviour's complexity by that of every compatible pair, so in particular by
each of these two — which are different strings naming different planners. -/
theorem behaviour_le_both_pairs (U : Kolmogorov.Map)
    (hU : Kolmogorov.isOptimalConditional U) :
    ∃ c : ℕ,
      Kolmogorov.plainK U sampleBehaviour
          ≤ Kolmogorov.plainK U (readerPair sampleBehaviour) + (c : ENat) ∧
        Kolmogorov.plainK U sampleBehaviour
          ≤ Kolmogorov.plainK U (degeneratePair [] sampleBehaviour) + (c : ENat) := by
  obtain ⟨c, hc⟩ := behaviour_le_of_evaluatesTo U hU
  exact ⟨c, hc _ _ evaluatesTo_readerPair_sample,
    hc _ _ evaluatesTo_degeneratePair_sample⟩

/-- **Evaluation is partial computable**, which is the source's reason, named. -/
theorem partrec_evalPair_named : Partrec evalPair := partrec_evalPair

/-- The reading pair is within additive constants of the behaviour in both
directions, which is the source's second §5.1 claim on an object the first one
covers. -/
theorem readerPair_two_sided (U : Kolmogorov.Map)
    (hU : Kolmogorov.isOptimalConditional U) :
    ∃ c₁ c₂ : ℕ, ∀ b : Kolmogorov.BitString,
      Kolmogorov.plainK U b ≤ Kolmogorov.plainK U (readerPair b) + (c₁ : ENat) ∧
      Kolmogorov.plainK U (readerPair b) ≤ Kolmogorov.plainK U b + (c₂ : ENat) :=
  readerPair_complexity_eq_behaviour U hU

/-- Invariance under a partial computable map, named at the evaluation map. -/
theorem plainK_le_of_partrec_evalPair (U : Kolmogorov.Map)
    (hU : Kolmogorov.isOptimalConditional U) :
    ∃ c : ℕ, ∀ x b : Kolmogorov.BitString, b ∈ evalPair x →
      Kolmogorov.plainK U b ≤ Kolmogorov.plainK U x + (c : ENat) :=
  plainK_le_of_partrec U hU evalPair partrec_evalPair

/-- The reading pair is computable in the behaviour, which the degenerate pair is
not shown to be. -/
theorem computable_readerPair_named : Computable readerPair := computable_readerPair

end AISafetyAtlas.Examples.Preference
