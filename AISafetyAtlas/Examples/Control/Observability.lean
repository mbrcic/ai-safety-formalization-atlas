module

public import AISafetyAtlas.Control.Observability

/-!
# Sensor loss — worked consequences

Two readings of `AISafetyAtlas.Control.Observability`.

1. **An injective sensor loses nothing.** `sensorLoss_eq_zero_of_injective` is the
   simplest perfectly observable system: a sensor that reports a distinguishing
   function of the state. It witnesses that `PerfectlyObservable` is satisfiable,
   which a characterization theorem on its own does not.
2. **What perfect observability buys.**
   `of_perfectlyObservable` chains Theorems 5, 6 and Corollary 7: from the
   *structural* condition on the sensor, both information-theoretic conclusions
   follow with no further hypothesis.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control AISafetyAtlas.InformationTheory

universe uΩ uS uK uN

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
variable [Countable S] [Countable K] [Countable N]

omit [MeasurableSingletonClass N] [Countable N] in
/--
**An injective sensor loses nothing.** If the reading distinguishes every pair of
states, the state retains no entropy once the reading is known.

The source's condition is exactly injectivity on the support — "maps no two
values of `X` to a single observational output value `c`" — so this is the
canonical instance rather than a special case.
-/
public theorem sensorLoss_eq_zero_of_injective (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} (hX : Measurable X) [FiniteRange X] {f : S → K}
    (hf : Injective f) (hfm : Measurable f) :
    sensorLoss μ X (f ∘ X) = 0 := by
  rw [sensorLoss, condEntropy_comp_self hX hfm, entropy_comp_of_injective μ hX f hf, sub_self]

/--
**What perfect observability buys.** A perfectly observable system's sensor makes
the purification noise redundant twice over: the noise says nothing about the
state once the reading is known, and adjoining it to the reading adds no
information at all.

Theorems 5, 6 and Corollary 7 in one chain — the structural condition in, both
information-theoretic conclusions out.
-/
public theorem of_perfectlyObservable (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange Z]
    (hobs : PerfectlyObservable μ X C) :
    I[X : Z | C ; μ] = 0 ∧ I[X : ⟨C, Z⟩ ; μ] = I[X : C ; μ] := by
  have h := (perfectlyObservable_iff_sensorLoss_eq_zero μ hX hC).1 hobs
  exact ⟨condMutualInfo_eq_zero_of_sensorLoss_eq_zero μ hX hC hZ h,
    mutualInfo_prod_eq_of_sensorLoss_eq_zero μ hX hC hZ h⟩

end AISafetyAtlas.Examples.Control
