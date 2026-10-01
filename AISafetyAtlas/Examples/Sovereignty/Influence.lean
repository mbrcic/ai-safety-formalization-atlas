module

public import AISafetyAtlas.Sovereignty.Influence
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Influence without loss of options, and a value the support cannot see

Two witnesses for the quantitative layer.

`accept` is `Q9`. The principal has three actions -- force `false`, force
`true`, and defer to the assistant -- and the assistant names a bit the same
way. The principal forces either outcome, so it has full binary option
sovereignty; and at the deferring action the assistant moves the outcome from
one certainty to the other, so the influence capacity there is maximal. Whether
deferring is legitimate is a separate question about the constitution, which is
exactly print's remark.

`bern` is `P12`. Two laws on one game form, with different mass on `true`. They
have the same null sets, hence the same support-based sure effectivity, and
different lower values. So no function of the qualitative data recovers the
quantity, and `qualitative_does_not_determine_value` says so at an arbitrary
non-degenerate pair rather than at print's `1/4` and `3/4`.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Influence

open AISafetyAtlas.Sovereignty
open MeasureTheory
open scoped ENNReal

/-! ## `Q9`: the assistant moves everything, and takes nothing away -/

/-- Each party either forces an outcome or defers. The principal (`false`)
decides unless it defers, in which case the assistant's choice is read, and a
deferring assistant leaves `false`. -/
@[expose] public def accept : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Option Bool
  outcome s := (s false).getD ((s true).getD false)

/-- Everyone has a strategy. -/
public instance accept_nonempty (i : Bool) : Nonempty (accept.strategy i) := ⟨none⟩

/-- **The principal forces `false`.** -/
public theorem accept_forces_false : Forces accept {false} ({false} : Set Bool) :=
  ⟨fun _ => some false, fun s hs => by
    have h : s false = some false := hs ⟨false, rfl⟩
    show accept.outcome s ∈ ({false} : Set Bool)
    simp [accept, h]⟩

/-- **And the principal forces `true`.** Full binary option sovereignty. -/
public theorem accept_forces_true : Forces accept {false} ({true} : Set Bool) :=
  ⟨fun _ => some true, fun s hs => by
    have h : s false = some true := hs ⟨false, rfl⟩
    show accept.outcome s ∈ ({true} : Set Bool)
    simp [accept, h]⟩

/-- The deferring commitment. -/
@[expose] public def defer : ∀ i : ({false} : Set Bool), accept.strategy i :=
  fun _ => none

/-- The assistant is outside the principal's coalition. -/
public theorem assistant_mem : (true : Bool) ∈ (({false} : Set Bool)ᶜ) := by simp

/-- Reading the outcome at the deferring commitment: the assistant decides. -/
public theorem accept_outcome_defer
    (b : ∀ i : (({false} : Set Bool)ᶜ : Set Bool), accept.strategy i) :
    accept.outcome (spliceProfile {false} defer b) =
      (b ⟨true, assistant_mem⟩).getD false := by
  show ((spliceProfile {false} defer b) false).getD
      (((spliceProfile {false} defer b) true).getD false) = _
  simp [spliceProfile, defer]

/-- **At the deferring action the assistant moves the outcome completely**, so
the influence capacity there is not zero. -/
public theorem accept_influence_ne_zero :
    influenceCapacity (diracLaw accept) {false} defer ≠ 0 := by
  rw [Ne, influenceCapacity_eq_zero_iff]
  intro h
  have e₀ := accept_outcome_defer (fun _ => (some true : Option Bool))
  have e₁ := accept_outcome_defer (fun _ => (some false : Option Bool))
  have heq := h (fun _ => some true) (fun _ => some false)
  have hval := congrArg (fun μ => μ ({true} : Set Bool)) heq
  simp only [diracLaw] at hval
  rw [e₀, e₁] at hval
  simp [Measure.dirac_apply_of_mem (Set.mem_singleton true),
    Measure.dirac_apply' _ (MeasurableSet.singleton true)] at hval

/-! ## `P12`: same support, different value -/

/-- A biased coin on `Bool`. -/
@[expose] public noncomputable def bern (p : ℝ≥0∞) : Measure Bool :=
  p • Measure.dirac true + (1 - p) • Measure.dirac false

/-- The chance of `true`. -/
public theorem bern_apply_true (p : ℝ≥0∞) : bern p ({true} : Set Bool) = p := by
  simp [bern, Measure.dirac_apply' _ (MeasurableSet.singleton true)]

/-- It is a probability measure when the bias is a probability. -/
public theorem bern_isProbability {p : ℝ≥0∞} (hp : p ≤ 1) :
    IsProbabilityMeasure (bern p) := by
  constructor
  simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  exact add_tsub_cancel_of_le hp

/-- **Its null sets do not depend on the bias**, as long as the coin is not
degenerate. -/
public theorem bern_eq_zero_iff {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp₁ : 1 - p ≠ 0)
    (Φ : Set Bool) (hΦ : MeasurableSet Φ) :
    bern p Φ = 0 ↔ (true ∉ Φ ∧ false ∉ Φ) := by
  simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_eq_zero, mul_eq_zero, hp₀, hp₁, false_or,
    Measure.dirac_apply' _ hΦ]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · simp [Set.indicator_of_mem hmem] at h₁
    · simp [Set.indicator_of_mem hmem] at h₂
  · rintro ⟨h₁, h₂⟩
    exact ⟨Set.indicator_of_notMem h₁ _, Set.indicator_of_notMem h₂ _⟩

/-- A game in which nobody chooses anything, so all the structure is in the
law. -/
@[expose] public def solo : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Unit
  outcome _ := true

/-- Everyone has a strategy. -/
public instance solo_nonempty (i : Bool) : Nonempty (solo.strategy i) :=
  ⟨show Unit from ()⟩

/-- The coin, as an outcome law on that game. -/
@[expose] public noncomputable def coin {p : ℝ≥0∞} (hp : p ≤ 1) : OutcomeLaw solo where
  law _ := bern p
  isProbability _ := bern_isProbability hp

/-- The lower value of `{true}` is the bias. -/
public theorem coin_lowerValue {p : ℝ≥0∞} (hp : p ≤ 1) :
    (coin hp).lowerValue {false} ({true} : Set Bool) = p := by
  simp [OutcomeLaw.lowerValue, coin, bern_apply_true]

/--
**`P12`: the qualitative data does not determine the value.**

Two non-degenerate coins have the same null sets, hence the same support-based
sure effectivity, and different lower values. Print exhibits `1/4` against
`3/4`; this holds at every non-degenerate pair.
-/
public theorem qualitative_does_not_determine_value {p q : ℝ≥0∞}
    (hp : p ≤ 1) (hq : q ≤ 1) (hp₀ : p ≠ 0) (hp₁ : 1 - p ≠ 0)
    (hq₀ : q ≠ 0) (hq₁ : 1 - q ≠ 0) (hpq : p ≠ q) :
    supportEffectivity (coin hp) {false} = supportEffectivity (coin hq) {false} ∧
      (coin hp).lowerValue {false} ({true} : Set Bool) ≠
        (coin hq).lowerValue {false} ({true} : Set Bool) := by
  refine ⟨supportEffectivity_congr _ fun _ Φ => ?_, ?_⟩
  · by_cases hΦ : MeasurableSet Φ
    · rw [show (coin hp).law _ Φ = bern p Φ from rfl,
        show (coin hq).law _ Φ = bern q Φ from rfl,
        bern_eq_zero_iff hp₀ hp₁ Φ hΦ, bern_eq_zero_iff hq₀ hq₁ Φ hΦ]
    · exact absurd (MeasurableSpace.measurableSet_top (s := Φ)) hΦ
  · rw [coin_lowerValue, coin_lowerValue]
    exact hpq

/-! ## `Q4`: a supremum of one that nothing attains -/

/-- The controller names a natural number; nothing else is chosen. -/
@[expose] public def escalate : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := ℕ
  outcome _ := true

/-- Everyone has a strategy. -/
public instance escalate_nonempty (i : Bool) : Nonempty (escalate.strategy i) :=
  ⟨show ℕ from 0⟩

/-- The number a full profile names. -/
@[expose] public def effort (s : ∀ i, escalate.strategy i) : ℕ :=
  show ℕ from s false

/-- The number a commitment of the controller names. -/
@[expose] public def effortOf
    (sC : ∀ i : ({false} : Set Bool), escalate.strategy i) : ℕ :=
  show ℕ from sC ⟨false, rfl⟩

/-- Splicing does not change it. -/
public theorem effort_spliceProfile
    (sC : ∀ i : ({false} : Set Bool), escalate.strategy i)
    (sD : ∀ i : ((({false} : Set Bool))ᶜ : Set Bool), escalate.strategy i) :
    effort (spliceProfile {false} sC sD) = effortOf sC := by
  show (spliceProfile {false} sC sD) false = _
  simp [spliceProfile, effortOf]

/-- **Escalating effort.** Naming `n` succeeds with chance `1 - n⁻¹`, which is
below one at every `n` and approaches one along the sequence. -/
@[expose] public noncomputable def escalating : OutcomeLaw escalate where
  law s := bern (1 - ((effort s : ℕ) : ℝ≥0∞)⁻¹)
  isProbability _ := bern_isProbability tsub_le_self

/-- The chance of success at a profile. -/
public theorem escalating_apply (s : ∀ i, escalate.strategy i) :
    escalating.law s ({true} : Set Bool) = 1 - ((effort s : ℕ) : ℝ≥0∞)⁻¹ :=
  bern_apply_true _

/-- The reciprocals of the naturals have infimum zero. -/
public theorem iInf_inv_natCast : (⨅ n : ℕ, ((n : ℝ≥0∞))⁻¹) = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
  exact absurd (iInf_le (fun n : ℕ => ((n : ℝ≥0∞))⁻¹) n) (not_le.mpr hn)

/-- **The lower value of success is one.** -/
public theorem escalating_lowerValue :
    escalating.lowerValue {false} ({true} : Set Bool) = 1 := by
  have hval : ∀ sC : ∀ i : ({false} : Set Bool), escalate.strategy i,
      (⨅ sD : ∀ i : ((({false} : Set Bool))ᶜ : Set Bool), escalate.strategy i,
        escalating.law (spliceProfile {false} sC sD) ({true} : Set Bool))
        = 1 - ((effortOf sC : ℕ) : ℝ≥0∞)⁻¹ := by
    intro sC
    have hone : ∀ sD : ∀ i : ((({false} : Set Bool))ᶜ : Set Bool),
        escalate.strategy i,
        escalating.law (spliceProfile {false} sC sD) ({true} : Set Bool)
          = 1 - ((effortOf sC : ℕ) : ℝ≥0∞)⁻¹ := by
      intro sD
      rw [escalating_apply, effort_spliceProfile]
    simp [hone]
  rw [OutcomeLaw.lowerValue]
  simp only [hval]
  have hsup : (⨆ sC : ∀ i : ({false} : Set Bool), escalate.strategy i,
      (1 - ((effortOf sC : ℕ) : ℝ≥0∞)⁻¹))
      = ⨆ n : ℕ, (1 - ((n : ℝ≥0∞))⁻¹) := by
    refine le_antisymm (iSup_le fun sC =>
      le_iSup (fun n : ℕ => 1 - ((n : ℝ≥0∞))⁻¹) (effortOf sC)) ?_
    exact iSup_le fun n =>
      le_iSup_of_le (fun _ => show escalate.strategy _ from n) le_rfl
  rw [hsup, ← ENNReal.sub_iInf, iInf_inv_natCast, tsub_zero]

/--
**`Q4`: and nothing attains it.**

Every commitment names some `n`, and its chance of success is strictly below
one. So threshold ability at `1` fails although the lower value is `1`: the
second half of the threshold correspondence really does need a strict
inequality.
-/
public theorem escalating_not_thresholdAbility_one :
    ¬ escalating.ThresholdAbility {false} ({true} : Set Bool) 1 := by
  rintro ⟨sC, hsC⟩
  have hlt : (1 : ℝ≥0∞) - ((effortOf sC : ℕ) : ℝ≥0∞)⁻¹ < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  have hge := hsC fun _ => show escalate.strategy _ from (0 : ℕ)
  rw [escalating_apply, effort_spliceProfile] at hge
  exact absurd hge (not_le.mpr hlt)

/-! ## `Q8` at a witness: what a coarse report destroys -/

/-- **Coarsening to a single cell**: the audit that reports one summary figure
and separates nothing. -/
@[expose] public def collapse : Bool → Unit := fun _ => ()

/-- It is measurable, as every map into `Unit` is. -/
public theorem collapse_measurable : Measurable collapse := measurable_const

/-- A set of `Unit` is empty or everything, which is the whole of what the
coarse report can say. -/
public theorem unit_set_cases (Φ : Set Unit) : Φ = ∅ ∨ Φ = Set.univ := by
  by_cases h : () ∈ Φ
  · right; ext x; cases x; simpa using h
  · left; ext x; cases x; simpa using h

/-- **Downstairs the two coins agree exactly**, whatever their biases: the only
events are the impossible one and the certain one. -/
public theorem eventGap_collapse {p q : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1) :
    eventGap ((bern p).map collapse) ((bern q).map collapse) = 0 := by
  have := bern_isProbability hp
  have := bern_isProbability hq
  refine (eventGap_eq_zero_iff _ _).mpr fun Φ hΦ => ?_
  rcases unit_set_cases Φ with rfl | rfl
  · rw [Measure.map_apply collapse_measurable MeasurableSet.empty,
      Measure.map_apply collapse_measurable MeasurableSet.empty,
      Set.preimage_empty, measure_empty, measure_empty]
  · rw [Measure.map_apply collapse_measurable MeasurableSet.univ,
      Measure.map_apply collapse_measurable MeasurableSet.univ,
      Set.preimage_univ, measure_univ, measure_univ]

/--
**`Q8` at a witness.** Two coins that genuinely differ are indistinguishable
once the report coarsens to one cell, and `eventGap_map_le` is the reason the
implication only ever runs one way. Perfect agreement downstairs bounds nothing
upstairs, so an audit reading summary statistics cannot certify non-influence.
-/
public theorem coarse_agreement_proves_nothing {p q : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1) :
    eventGap ((bern p).map collapse) ((bern q).map collapse) = 0 ∧
      eventGap ((bern p).map collapse) ((bern q).map collapse)
        ≤ eventGap (bern p) (bern q) :=
  ⟨eventGap_collapse hp hq, eventGap_map_le collapse collapse_measurable _ _⟩

/-! ## The gap's two standing facts, at the coins -/

/-- **The gap is symmetric**, so neither coin is the reference one. -/
public theorem bern_eventGap_comm (p q : ℝ≥0∞) :
    eventGap (bern p) (bern q) = eventGap (bern q) (bern p) :=
  eventGap_comm _ _

/-- **And it never exceeds one**, so the measure is on the scale print reads it
on. -/
public theorem bern_eventGap_le_one {p q : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1) :
    eventGap (bern p) (bern q) ≤ 1 := by
  have := bern_isProbability hp
  have := bern_isProbability hq
  exact eventGap_le_one _ _

end AISafetyAtlas.Examples.Sovereignty.Influence
