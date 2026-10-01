module

public import AISafetyAtlas.Sovereignty.Value
public import AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-!
# The qualitative layer, read as values

Two games already in the tree, seen through the Dirac law.

`decider_lowerValue_eq_one`: the principal who names the outcome has lower
value `1` for the target it names -- it wins for sure, and the bridge says so.

`bitMatch_lowerValue_ne_one`: in the simultaneous-bit game the principal's
lower value for agreement is not `1`. The bridge turns the qualitative failure
already proved into a statement about the value, without computing the value.

Both are instances of `lowerValue_diracLaw_eq_one_iff` and neither needs a
distribution to be evaluated, which is the point: the sure layer sits inside
the quantitative one rather than beside it.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Value

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Quantifiers
open scoped ENNReal

/-- **Sure winning is lower value one.** -/
public theorem decider_lowerValue_eq_one :
    (diracLaw decider).lowerValue {false} ({true} : Set Bool) = 1 :=
  (lowerValue_diracLaw_eq_one_iff {false} (MeasurableSet.singleton true)).mpr
    (principalDecides_forces_singleton true)

/-- **And no sure win is lower value below one.** -/
public theorem bitMatch_lowerValue_ne_one :
    (diracLaw bitMatch).lowerValue {false} ({true} : Set Bool) ≠ 1 := by
  intro h
  exact bitMatch_not_forces
    ((lowerValue_diracLaw_eq_one_iff {false} (MeasurableSet.singleton true)).mp h)

/-- **`B1` at the same witness.** The payoff value at the indicator of the
target is the target's own value, so the sure layer reaches the payoff layer
without a separate calculation. -/
public theorem decider_lowerPayoff_eq_one :
    (diracLaw decider).lowerPayoff {false}
      (Set.indicator ({true} : Set Bool) 1) = 1 := by
  rw [OutcomeLaw.lowerPayoff_indicator _ _ (MeasurableSet.singleton true)]
  exact decider_lowerValue_eq_one

/-! ## Every value lemma, applied

`AISafetyAtlas.Sovereignty.Value` proves nine results that nothing instantiated.
Each is applied below on `diracLaw decider`, whose lower value at `{true}` is
already known to be one. Several are applied at the slack that makes them
trivial -- `ε = 0`, or `ε = 1` where the conclusion is `0 ≤ ·` -- and say so;
what they establish is that the hypotheses are inhabited.
-/

/-- A law is a subprobability, and the lower value is monotone in the target. -/
public theorem value_law_le_one (s : ∀ i, decider.strategy i) (Φ : Set Bool) :
    (diracLaw decider).law s Φ ≤ 1 :=
  OutcomeLaw.law_le_one _ s Φ

public theorem value_lowerValue_mono :
    (diracLaw decider).lowerValue {false} ({true} : Set Bool)
      ≤ (diracLaw decider).lowerValue {false} (Set.univ : Set Bool) :=
  OutcomeLaw.lowerValue_mono _ {false} (Set.subset_univ _)

/-- The two halves of `Q4`, at a threshold strictly below the value: strict
dominance gives threshold ability, and threshold ability gives the bound back. -/
public theorem value_thresholdAbility_roundTrip :
    (diracLaw decider).ThresholdAbility {false} ({true} : Set Bool) 0 ∧
      (0 : ℝ≥0∞) ≤ (diracLaw decider).lowerValue {false} ({true} : Set Bool) :=
  have hlt : (0 : ℝ≥0∞) < (diracLaw decider).lowerValue {false} ({true} : Set Bool) := by
    rw [decider_lowerValue_eq_one]; exact zero_lt_one
  have ht := OutcomeLaw.thresholdAbility_of_lt_lowerValue _ {false} _ hlt
  ⟨ht, OutcomeLaw.le_lowerValue_of_thresholdAbility _ {false} _ ht⟩

/-- The guarantee and its opponent's cannot add past one. -/
public theorem value_lowerValue_add_opponent_le_one :
    (diracLaw decider).lowerValue {false} ({true} : Set Bool)
      + (diracLaw decider).opponentLowerValue {false} ({true} : Set Bool) ≤ 1 :=
  OutcomeLaw.lowerValue_add_opponentLowerValue_le_one (K := diracLaw decider) {false}
    (MeasurableSet.singleton true)

/-- **At zero slack**, `Q5` says a law dominated pointwise has a dominated lower
value; applied to a law against itself, which is the degenerate instance. -/
public theorem value_lowerValue_le_of_law_le :
    (diracLaw decider).lowerValue {false} ({true} : Set Bool)
      ≤ (diracLaw decider).lowerValue {false} ({true} : Set Bool) + 0 :=
  OutcomeLaw.lowerValue_le_of_law_le _ _ {false} _ 0 (fun _ => by simp)

/-- **At full slack**, the two-target bound is `0 ≤ ·`: the premises hold for
any law and the conclusion is vacuous, which is the honest instance available
without a second measurable target this file builds. -/
public theorem value_le_law_inter (s : ∀ i, decider.strategy i) :
    1 - (1 + 1) ≤ (diracLaw decider).law s (({true} : Set Bool) ∩ {true}) :=
  OutcomeLaw.le_law_inter _ s (MeasurableSet.singleton true)
    (MeasurableSet.singleton true) 1 1 (by simp) (by simp)

/-- The infimum is below the integral, on the point mass at `true`. -/
public theorem value_iInf_le_lintegral :
    (⨅ _ : Bool, (1 : ℝ≥0∞))
      ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(MeasureTheory.Measure.dirac true) :=
  Sovereignty.iInf_le_lintegral _ _

/-- The step-to-product bound, on the sequence that never degrades. -/
public theorem value_prod_le_of_step_le (T : ℕ) :
    (∏ _t ∈ Finset.range T, (1 - (0 : ℝ≥0∞))) ≤ (fun _ : ℕ => (1 : ℝ≥0∞)) T :=
  Sovereignty.prod_le_of_step_le (fun _ => 1) (fun _ => 0) (by simp) (fun _ => by simp) T


end AISafetyAtlas.Examples.Sovereignty.Value
