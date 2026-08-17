module

public import AISafetyAtlas.Control.OpenLoop

/-!
# Open-loop optimality — worked consequences

Two readings of `AISafetyAtlas.Control.OpenLoop`.

1. **A bound on every fixed action bounds every controller.**
   `entropyReduction_le_of_forall_pure` is Theorem 9 in the form the rest of the
   development consumes: to bound what *any* open-loop controller can remove from
   the state, it is enough to bound what each single action removes. The
   randomized case comes for free. `exists_optimal_pure` records the printed
   attainment clause separately: some constant action reaches the supremum.
2. **A controller blind to its own outcome loses nothing by averaging.**
   `entropyReduction_eq_of_blind` is Lemma 8's equality case read at
   `I(X' ; C) = 0`.
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

/--
**A bound on every pure action bounds every controller.** If no single action
removes more than `Δ` from the state's entropy, then no controller does — however
it randomizes.

This is Theorem 9 in the shape the open-loop bound of Theorem 10 wants: the
quantifier over *all* controllers collapses to a quantifier over *actions*.
-/
public theorem entropyReduction_le_of_forall_pure [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T)
    {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange (plantOutcome F X C Z)]
    (hindep : IndepFun C (⟨X, Z⟩ : Ω → S × N) μ) {Δ : ℝ}
    (hpure : ∀ c : K, openLoopReduction μ F X Z c ≤ Δ) :
    entropyReduction μ X (plantOutcome F X C Z) ≤ Δ :=
  le_trans (entropyReduction_le_iSup_openLoopReduction μ F hX hC hZ hindep) (ciSup_le hpure)

omit [MeasurableSpace K] [MeasurableSpace N] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/-- **The best pure action exists.** This is Theorem 9's printed equality clause,
not merely the definitional fact that a chosen constant controller realizes its
own constant-action reduction. -/
public theorem exists_optimal_pure [Fintype K] [Nonempty K] (μ : Measure Ω)
    (F : S → K → N → T) (X : Ω → S) (Z : Ω → N) :
    ∃ c : K, entropyReduction μ X (plantOutcome F X (fun _ => c) Z)
      = ⨆ k : K, openLoopReduction μ F X Z k :=
  exists_entropyReduction_const_eq_iSup_openLoopReduction μ F X Z

omit [MeasurableSingletonClass S] [MeasurableSingletonClass N] [Countable S] [Countable N] in
/--
**A controller blind to its own outcome loses nothing by averaging.** Lemma 8's
equality case: when the action carries no information about the final state, the
reduction achieved equals the average of the per-action reductions exactly.
-/
public theorem entropyReduction_eq_of_blind (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {X' : Ω → T} (hX' : Measurable X') (hC : Measurable C)
    [FiniteRange X'] [FiniteRange C] (hblind : I[X' : C ; μ] = 0) :
    entropyReduction μ X X' = H[X ; μ] - H[X' | C ; μ] :=
  (entropyReduction_eq_condEntropy_form_iff μ hX' hC).2 hblind

/--
**Blind feedback cannot beat the printed open-loop maximum.** Theorem 10 against
eq. (48), read at `I(X ; C) = 0`: a controller whose action carries no information
about the state does no better than the best pure open-loop controller on the
best input distribution.

The bound is the source's own `ΔH_open^max`, not the atlas's `OpenLoopBound`
rendering of it — which is the difference `entropyReduction_le_openLoopMax` buys.
-/
public theorem entropyReduction_le_openLoopMax_of_blind [Fintype S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T)
    {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange (plantOutcome F X C Z)]
    (hindep : IndepFun (⟨X, C⟩ : Ω → S × K) Z μ) (hblind : I[X : C ; μ] = 0) :
    entropyReduction μ X (plantOutcome F X C Z) ≤ openLoopMax F (μ.map Z) := by
  have h := entropyReduction_le_openLoopMax μ F hX hC hZ hindep
  rw [hblind, add_zero] at h
  exact h

end AISafetyAtlas.Examples.Control
