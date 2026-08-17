module

public import AISafetyAtlas.Knowledge
public import AISafetyAtlas.InformationTheory.Determinism
public import AISafetyAtlas.InformationTheory.DataProcessing
public import AISafetyAtlas.InformationTheory.Fano

/-!
# Knowability, measured

`AISafetyAtlas.Knowledge` decides knowability by **counting**: a property is
knowable from an observation exactly when no two states the observation confuses
disagree about it. `AISafetyAtlas.Knowledge.Ambiguity` is explicit that it works
with no probability and no entropy at all.

This module supplies the missing half. Put a measure on the state space and the
same question has a quantitative answer, and the two answers are related in one
direction exactly and in the other only up to a null set.

## What is proved

`condEntropy_eq_zero_of_knowable` — **a decoder costs no entropy.** If the
property is knowable from the observation then `H[property | observation] = 0`.

`not_knowable_of_condEntropy_ne_zero` — the contrapositive, and the one a
consumer reaches for: **a positive conditional entropy is a certificate of
unknowability.** It never names the colliding pair, which is what makes it
usable where `IndistinguishabilityWitness` is out of reach — the entropy is a
number one can estimate, and the witness is an object one has to find.

`le_errorProb_of_decoder` — **how badly unknowability bites.** Every decoder
built from the observation, not merely some decoder, errs with probability at
least `(H[property | observation] − log 2) / log |A|`. This is Fano's inequality
(`InformationTheory.le_errorProb`) reached through data processing
(`InformationTheory.condEntropy_le_condEntropy_of_isMarkovChain` at
`isMarkovChain_comp`): a decoder can only coarsen the observation, and coarsening
never lowers the conditional entropy, so the bound proved against the decoder's
own output transfers to the observation it was computed from.

That chain is the point of the module. The counting kernel says *whether* a
property can be recovered; the entropy layer says *how often any procedure must
get it wrong*, and the second is proved from the printed Cover–Thomas material
rather than by a fresh argument.

## Why the converse is a null set away

`H[property | observation ; μ] = 0` does **not** give `Knowable`. It gives a
decoder correct `μ`-almost everywhere, and `Knowable` asks for one correct at
every state, including states of measure zero. The gap is real and not a
technicality of the encoding: `Examples.Knowledge.Entropy` exhibits a property
that is not knowable, whose conditional entropy is nonetheless zero, by hiding
the collision on a null set.

So the implication proved here runs one way on purpose. Entropy is a sound
certificate of unknowability and an unsound certificate of knowability.

## Explicit non-claims

- **Not** a claim that vanishing conditional entropy implies `Knowable`. It
  implies an almost-everywhere decoder against the measure in hand, and the
  counterexample in `Examples.Knowledge.Entropy` shows the two are different.
- **Not** a claim about any particular observer, sensor or agent. `observation`
  is an arbitrary measurable map; nothing here asserts that a real system's
  measurements are one.
- **Not** an improvement on Fano. `le_errorProb_of_decoder` is Cover & Thomas
  (2.132) instantiated and then weakened along a Markov chain; the constant is
  theirs.
- The error bound is **vacuous when the conditional entropy is below `log 2`**,
  which is the printed inequality's own behaviour and not an artefact here.
-/

namespace AISafetyAtlas.Knowledge

open MeasureTheory ProbabilityTheory Function
open AISafetyAtlas.InformationTheory
  (condEntropy_comp_self_left condEntropy_le_condEntropy_of_isMarkovChain isMarkovChain_comp
    errorProb le_errorProb)

variable {Ω : Type*} {I : Type*} {Y : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace I] [MeasurableSpace Y]
variable [MeasurableSingletonClass I] [MeasurableSingletonClass Y]
variable [Countable I] [Countable Y]

/--
**A decoder costs no entropy.** If `property` is knowable from `observation` —
that is, some decoder reads it off the observation at every state — then the
observation leaves no uncertainty about it.

The measurability of the decoder is not a hypothesis: `I` is countable with
measurable singletons, so every map out of it is measurable.
-/
public theorem condEntropy_eq_zero_of_knowable (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] {observation : Ω → I} {property : Ω → Y}
    (hobs : Measurable observation) [FiniteRange observation]
    (h : Knowable observation property) :
    H[property | observation ; μ] = 0 := by
  obtain ⟨decoder, hdec⟩ := h
  have hfun : property = decoder ∘ observation := funext hdec
  rw [hfun]
  exact condEntropy_comp_self_left μ hobs (measurable_of_countable decoder)

/--
**Positive conditional entropy certifies unknowability.**

The contrapositive of `condEntropy_eq_zero_of_knowable`, and the direction a
consumer uses: an entropy is a number that can be estimated, where an
`IndistinguishabilityWitness` is an object that has to be exhibited.
-/
public theorem not_knowable_of_condEntropy_ne_zero (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] {observation : Ω → I} {property : Ω → Y}
    (hobs : Measurable observation) [FiniteRange observation]
    (h : H[property | observation ; μ] ≠ 0) :
    ¬ Knowable observation property :=
  fun hk => h (condEntropy_eq_zero_of_knowable μ hobs hk)

/--
**Every decoder errs at least this often.**

Fano's inequality bounds an estimator's error probability below by the entropy
left by *that estimator*. A decoder is a function of the observation, so it is a
coarsening, and coarsening never lowers conditional entropy — that is data
processing. Composing the two gives a floor stated against the observation
itself, uniform over decoders.

`hA` is what makes `log |A|` positive; the printed statement needs it for the
same reason.
-/
public theorem le_errorProb_of_decoder [DecidableEq Y] {A : Finset Y} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {observation : Ω → I} {property : Ω → Y}
    (hobs : Measurable observation) (hprop : Measurable property)
    (hpropA : ∀ ω, property ω ∈ A) (hA : 2 ≤ A.card)
    (decoder : I → Y)
    [FiniteRange observation] [FiniteRange property]
    [FiniteRange (decoder ∘ observation)]
    [FiniteRange (AISafetyAtlas.InformationTheory.errorPair property (decoder ∘ observation))] :
    (H[property | observation ; μ] - Real.log 2) / Real.log (A.card : ℝ)
      ≤ errorProb μ property (decoder ∘ observation) := by
  have hdec : Measurable (decoder ∘ observation) :=
    (measurable_of_countable decoder).comp hobs
  have hlog : 0 < Real.log (A.card : ℝ) := Real.log_pos (by exact_mod_cast hA)
  have hmarkov :
      H[property | observation ; μ] ≤ H[property | decoder ∘ observation ; μ] :=
    condEntropy_le_condEntropy_of_isMarkovChain μ hprop hobs hdec
      (isMarkovChain_comp μ hprop hobs (measurable_of_countable decoder))
  have hfano := le_errorProb (A := A) μ hprop hdec hpropA hA
  calc (H[property | observation ; μ] - Real.log 2) / Real.log (A.card : ℝ)
      ≤ (H[property | decoder ∘ observation ; μ] - Real.log 2) / Real.log (A.card : ℝ) := by
        gcongr
    _ ≤ errorProb μ property (decoder ∘ observation) := hfano

end AISafetyAtlas.Knowledge
