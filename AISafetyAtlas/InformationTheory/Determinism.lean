module

public import PFR.ForMathlib.Entropy.Basic

/-!
# Deterministic dependence has no conditional entropy

One fact, stated once: **a function of a variable adds no uncertainty to it.**

`condEntropy_comp_self_left : H[g ∘ X | X ; μ] = 0`

It is elementary — pair `g ∘ X` with `X`, note the pairing is injective, and read
the chain rule backwards — and it is the entropy side of every "this quantity is
determined by that one" statement in the library. It lives here rather than in a
domain because it mentions no domain: `Control.RequisiteVariety` uses it for a
regulator playing a determinate strategy, `Control.CompleteControl` for an
outcome that is a function of the controller, and `Knowledge.Entropy` for a
decoder reading a property off an observation. Three unrelated readings, one
lemma.

The converse fails and the failure is not a technicality. `H[Y | X ; μ] = 0` says
`Y` is determined by `X` **`μ`-almost everywhere**, which is weaker than being
determined by `X` everywhere: entropy cannot see a null set. `Knowledge.Entropy`
records what that costs, with a worked counterexample.

## Explicit non-claims

- **Not** a claim that vanishing conditional entropy makes `Y` a function of `X`.
  It gives an almost-everywhere decoder, and only against the measure in hand.
- **Not** a statement about mutual information or channels. Nothing here needs a
  channel, an alphabet size, or a capacity.
-/

namespace AISafetyAtlas.InformationTheory

open MeasureTheory ProbabilityTheory Function

variable {Ω : Type*} {S : Type*} {T : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
variable [Countable S] [Countable T]

/-- A function of a variable adds no uncertainty to it: `H[g ∘ X | X] = 0`. -/
public theorem condEntropy_comp_self_left (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} (hX : Measurable X) {g : S → T} (hg : Measurable g)
    [FiniteRange X] :
    H[g ∘ X | X ; μ] = 0 := by
  have hpair : H[⟨g ∘ X, X⟩ ; μ] = H[X ; μ] :=
    entropy_comp_of_injective μ hX (fun s => (g s, s)) fun _ _ h => congrArg Prod.snd h
  have hchain : H[⟨g ∘ X, X⟩ ; μ] = H[X ; μ] + H[g ∘ X | X ; μ] :=
    chain_rule μ (hg.comp hX) hX
  linarith

end AISafetyAtlas.InformationTheory
