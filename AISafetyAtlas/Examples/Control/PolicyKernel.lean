module

public import AISafetyAtlas.Control.PolicyKernel

/-!
# Eq. (28)'s minimum — worked consequences

Three readings of `AISafetyAtlas.Control.PolicyKernel`.

1. **Pure beats mixed, at the control loss.** `kernelControlLoss_bestAction_le`
   says no conditional distribution `p(c|x)` loses less than the deterministic
   one that plays a minimizing action at each state. This is the `L_C` analogue
   of the source's own Theorem 9, which proves the same for `ΔH_open` and says it
   in those words: *"no random choice of the controller's state can improve upon
   that decrease"*.
2. **Theorem 2's inequality, at the printed `L_C`.**
   `kernelMinControlLoss_le_entropy_noise` bounds the source's own minimum over
   `{p(c|x)}` by `H(Z)` — not a represented family standing in for it. Only one
   admitted controller has to be purified, since a minimum is capped by any
   single member.
3. **The representation gap is zero.** `no_representation_gap` states the bridge
   in the form the provenance record needs: the infimum over the controllers
   realizable on one sample space is not merely `≥` the minimum over all
   conditional distributions, it is equal to it.

The discriminating witnesses for the surrounding definitions — that the
minimization is not a formality, and that `Set.univ` is not eq. (28)'s feasible
set — live in `AISafetyAtlas.Examples.Control.InformationLimits`, and they are
what make `IsInputPolicy` load-bearing here.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control AISafetyAtlas.InformationTheory

universe uΩ uS uK uN uT

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K]
variable [MeasurableSpace N] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K]
variable [MeasurableSingletonClass N] [MeasurableSingletonClass T]
variable [Countable S] [Countable K] [Countable N] [Countable T]

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/--
**Pure beats mixed.** The deterministic state feedback that plays a minimizing
action at every state loses no more than any conditional distribution `p(c|x)`.

Randomizing the controller cannot pay, because the objective is an average of
plant numbers over weights the controller chooses, and no average beats its own
least term.
-/
public theorem kernelControlLoss_bestAction_le [Fintype S] [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z) (hbest : Measurable (bestAction μ F X Z))
    (κ : Kernel S K) [IsMarkovKernel κ] :
    kernelControlLoss μ F hX Z (Kernel.deterministic _ hbest)
      ≤ kernelControlLoss μ F hX Z κ := by
  have hdet : kernelControlLoss μ F hX Z (Kernel.deterministic _ hbest)
      = closedFormLoss μ F X Z := by
    rw [kernelControlLoss_deterministic μ F hX hZ _ hbest, closedFormLoss]
    exact Finset.sum_congr rfl fun x _ => by rw [atomLoss_bestAction]
  rw [hdet]
  exact closedFormLoss_le_kernelControlLoss μ F hX hZ κ

/--
**Theorem 2's inequality at the source's own `L_C`.** The minimum over all
conditional distributions `{p(c|x)}` is bounded by the entropy of the actuation
noise.

Before the bridge this was available only for a represented family on a fixed
sample space; the direction happened to be safe, but the printed object was not
the one bounded. Now it is.
-/
public theorem kernelMinControlLoss_le_entropy_noise [Fintype S] [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    {C : Ω → K} (hCP : C ∈ inputPolicies μ X Z) (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange Z] [FiniteRange (plantOutcome F X C Z)]
    [FiniteRange (plantOutcome F X (bestAction μ F X Z ∘ X) Z)]
    (hpure : Purified μ X C Z (plantOutcome F X C Z))
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ]) :
    kernelMinControlLoss μ F hX Z ≤ H[Z ; μ] := by
  rw [← minControlLoss_inputPolicies_eq_kernelMin μ F hX hZ]
  exact minControlLoss_inputPolicies_le_entropy_noise μ F hCP hX hZ hpure hindep

/--
**No representation gap.** The controllers realizable on one sample space achieve
exactly the source's minimum over all conditional distributions.

Stated in this direction because it is the claim the provenance record needs: a
fixed `Ω` realizes only some kernels, so the realized infimum could in principle
have exceeded the printed minimum. It does not, and the witness is deterministic
state feedback — the one policy shape that needs no auxiliary randomness and so
exists on every space.
-/
public theorem no_representation_gap [Fintype S] [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange (plantOutcome F X (bestAction μ F X Z ∘ X) Z)] :
    minControlLoss μ F X Z (inputPolicies μ X Z) = kernelMinControlLoss μ F hX Z :=
  minControlLoss_inputPolicies_eq_kernelMin μ F hX hZ

end AISafetyAtlas.Examples.Control
