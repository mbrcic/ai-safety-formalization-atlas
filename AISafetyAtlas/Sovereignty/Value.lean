module

public import AISafetyAtlas.Sovereignty.Domination
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Data.ENNReal.Operations
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Values, and the sure layer sitting inside them

Everything in the sovereignty modules so far is qualitative: a coalition either
forces a target or it does not. The proposal's §4 asks for the quantity behind
that, and this module supplies it.

## The shape, and three choices that are not forced

`OutcomeLaw` attaches a probability measure to every complete profile. It is a
plain function and **not** a `ProbabilityTheory.Kernel`, because a kernel would
need a σ-algebra on strategy profiles, none of the results below measure
anything in the strategy argument, and inventing that structure would be a
hypothesis nobody asked for.

Values live in `ℝ≥0∞`. Suprema and infima there are complete-lattice
operations, so no boundedness or nonemptiness side conditions appear in any
statement; the price is truncated subtraction, which is paid once in
`lowerValue_add_opponentLowerValue_le_one` and which is the right behaviour
anyway, since print writes the bound as `max(0, ·)`.

`spliceProfile` merges a coalition's commitment with the complement's, so the lower
and upper values are two orderings of quantifiers over **one** index pair. That
is what makes `lowerValue_le_upperValue` a one-line instance of the general
lattice fact rather than an argument.

## The bridge

`lowerValue_diracLaw_eq_one_iff` is the reason to trust the definitions: under
the law that puts all mass on the outcome, a coalition's lower value for a
target is `1` exactly when it forces the target. Print's *"sure winning
quantifies over every possible outcome"* is that statement, and if it failed
the quantifier order above would be wrong and everything after it would inherit
the error.

Measurability of the target is a hypothesis here for the same reason print
states one: `Measure.dirac` is only computed on measurable sets.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

open MeasureTheory
open scoped ENNReal

universe u v w

variable {N : Type u} {X : Type v} [MeasurableSpace X] {G : GameForm.{u, v, w} N X}

/-! ## Splicing a coalition's commitment into a full profile -/

open Classical in
/-- **Merge a coalition's commitment with the complement's.** -/
@[expose] public noncomputable def spliceProfile (C : Set N) (sC : ∀ i : C, G.strategy i)
    (sD : ∀ i : (Cᶜ : Set N), G.strategy i) : ∀ i, G.strategy i :=
  fun i => if hi : i ∈ C then sC ⟨i, hi⟩ else sD ⟨i, hi⟩

omit [MeasurableSpace X] in
/-- **Forcing, read through the spliceProfile.** The coalition commits and the
complement answers, with no agreement condition left over. -/
public theorem forces_iff_forall_splice {C : Set N} {A : Set X} :
    Forces G C A ↔ ∃ sC : ∀ i : C, G.strategy i,
      ∀ sD : ∀ i : (Cᶜ : Set N), G.strategy i, G.outcome (spliceProfile C sC sD) ∈ A := by
  classical
  constructor
  · rintro ⟨sC, hsC⟩
    refine ⟨sC, fun sD => hsC _ ?_⟩
    rintro ⟨i, hi⟩
    simp [spliceProfile, hi]
  · rintro ⟨sC, hsC⟩
    refine ⟨sC, fun s hs => ?_⟩
    have : spliceProfile C sC (fun i => s i) = s := by
      funext i
      by_cases hi : i ∈ C
      · simpa [spliceProfile, hi] using (hs ⟨i, hi⟩).symm
      · simp [spliceProfile, hi]
    exact this ▸ hsC (fun i => s i)

/-! ## A stochastic outcome semantics -/

/--
**A probability law on outcomes, one per complete profile.**

Deliberately a function and not a kernel: nothing below measures anything in
the strategy argument, so a σ-algebra on profiles would be an unused
hypothesis.
-/
public structure OutcomeLaw (G : GameForm.{u, v, w} N X) where
  /-- The outcome distribution produced by a complete profile. -/
  law : (∀ i, G.strategy i) → Measure X
  /-- Every profile produces a probability distribution. -/
  isProbability : ∀ s, IsProbabilityMeasure (law s)

namespace OutcomeLaw

variable (K : OutcomeLaw G)

/-- Every value is at most one. -/
public theorem law_le_one (s : ∀ i, G.strategy i) (Φ : Set X) : K.law s Φ ≤ 1 :=
  have := K.isProbability s
  prob_le_one

/--
**The lower value.** The coalition commits first; the complement answers
knowing the commitment.
-/
@[expose] public noncomputable def lowerValue (C : Set N) (Φ : Set X) : ℝ≥0∞ :=
  ⨆ sC : ∀ i : C, G.strategy i, ⨅ sD : ∀ i : (Cᶜ : Set N), G.strategy i,
    K.law (spliceProfile C sC sD) Φ

/--
**The upper value.** The complement commits first.
-/
@[expose] public noncomputable def upperValue (C : Set N) (Φ : Set X) : ℝ≥0∞ :=
  ⨅ sD : ∀ i : (Cᶜ : Set N), G.strategy i, ⨆ sC : ∀ i : C, G.strategy i,
    K.law (spliceProfile C sC sD) Φ

/-- **`Q1`: the minimax inequality.** Committing first cannot help. Both sides
range over the same index pair, so this is the lattice fact and nothing more --
which is the honest measure of its depth. -/
public theorem lowerValue_le_upperValue (C : Set N) (Φ : Set X) :
    K.lowerValue C Φ ≤ K.upperValue C Φ :=
  iSup_iInf_le_iInf_iSup _

/-- Both values are at most one. -/
public theorem upperValue_le_one [∀ i, Nonempty (G.strategy i)] (C : Set N)
    (Φ : Set X) : K.upperValue C Φ ≤ 1 :=
  iInf_le_of_le (Classical.arbitrary _) (iSup_le fun _ => K.law_le_one _ _)

/-- The lower value is monotone in the target. -/
public theorem lowerValue_mono (C : Set N) {Φ Ψ : Set X} (h : Φ ⊆ Ψ) :
    K.lowerValue C Φ ≤ K.lowerValue C Ψ :=
  iSup_mono fun _ => iInf_mono fun _ => measure_mono h

/-! ## `Q2`: the complement relation -/

/--
**The complement's lower value.** Everyone outside `C` commits first and tries
to keep the outcome out of `Φ`.
-/
@[expose] public noncomputable def opponentLowerValue (C : Set N) (Φ : Set X) : ℝ≥0∞ :=
  ⨆ sD : ∀ i : (Cᶜ : Set N), G.strategy i, ⨅ sC : ∀ i : C, G.strategy i,
    K.law (spliceProfile C sC sD) Φᶜ

/--
**`Q2`: the exact complement relation.** What the complement can guarantee
against `Φ` is exactly one minus what the coalition's upper value is for `Φ`.

Equality here is between the *upper* value and the complement's *lower* value,
which is print's point: it is not a sovereignty-versus-domination identity, and
it becomes one only when the two values of `Φ` coincide.
-/
public theorem opponentLowerValue_eq_one_sub_upperValue
    [∀ i, Nonempty (G.strategy i)] (C : Set N) {Φ : Set X} (hΦ : MeasurableSet Φ) :
    K.opponentLowerValue C Φ = 1 - K.upperValue C Φ := by
  have hcompl : ∀ s, K.law s Φᶜ = 1 - K.law s Φ := by
    intro s
    have := K.isProbability s
    rw [prob_compl_eq_one_sub hΦ]
  simp only [opponentLowerValue, upperValue, hcompl]
  rw [ENNReal.sub_iInf]
  exact iSup_congr fun _ => (ENNReal.sub_iSup ENNReal.one_ne_top).symm

/-- **And the two guarantees cannot add to more than one**, which is print's
inequality. Truncated subtraction in `ℝ≥0∞` supplies the `max(0, ·)` print
writes by hand. -/
public theorem lowerValue_add_opponentLowerValue_le_one
    [∀ i, Nonempty (G.strategy i)] (C : Set N) {Φ : Set X} (hΦ : MeasurableSet Φ) :
    K.lowerValue C Φ + K.opponentLowerValue C Φ ≤ 1 := by
  rw [K.opponentLowerValue_eq_one_sub_upperValue C hΦ]
  calc K.lowerValue C Φ + (1 - K.upperValue C Φ)
      ≤ K.upperValue C Φ + (1 - K.upperValue C Φ) :=
        add_le_add (K.lowerValue_le_upperValue C Φ) le_rfl
    _ = 1 := add_tsub_cancel_of_le (K.upperValue_le_one C Φ)

/-! ## `Q5` and `Q6`: perturbation, and one policy for two demands -/

/--
**`Q5`: values are nonexpansive in the law.**

Print hypothesizes that every event probability differs by at most `ε` and
concludes that the lower values differ by at most `ε`. Stated one-sidedly, as
it is used: a uniform bound on the law transfers through both quantifiers,
because adding a constant commutes with suprema and infima.
-/
public theorem lowerValue_le_of_law_le [∀ i, Nonempty (G.strategy i)]
    (K K' : OutcomeLaw G) (C : Set N) (Φ : Set X) (ε : ℝ≥0∞)
    (h : ∀ s, K.law s Φ ≤ K'.law s Φ + ε) :
    K.lowerValue C Φ ≤ K'.lowerValue C Φ + ε := by
  simp only [lowerValue, ENNReal.iSup_add]
  refine iSup_mono fun sC => ?_
  rw [ENNReal.iInf_add]
  exact iInf_mono fun sD => h _

/--
**`Q6`: one policy, two demands, the failures add.**

If a single profile keeps the failure probability of `Φ` below `ε₁` and that of
`Ψ` below `ε₂`, it keeps the failure probability of their conjunction below the
sum. Print's proof is the union bound on failures and so is this.

The truncated subtraction in `ℝ≥0∞` is print's `max(0, ·)`: when the budgets
already exceed one the statement is vacuous rather than false.
-/
public theorem le_law_inter (K : OutcomeLaw G) (s : ∀ i, G.strategy i)
    {Φ Ψ : Set X} (hΦ : MeasurableSet Φ) (hΨ : MeasurableSet Ψ) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : 1 - ε₁ ≤ K.law s Φ) (h₂ : 1 - ε₂ ≤ K.law s Ψ) :
    1 - (ε₁ + ε₂) ≤ K.law s (Φ ∩ Ψ) := by
  have hp := K.isProbability s
  have hcΦ : K.law s Φᶜ ≤ ε₁ := by
    rw [prob_compl_eq_one_sub hΦ]
    exact tsub_le_iff_right.mpr (by rw [add_comm]; exact tsub_le_iff_right.mp h₁)
  have hcΨ : K.law s Ψᶜ ≤ ε₂ := by
    rw [prob_compl_eq_one_sub hΨ]
    exact tsub_le_iff_right.mpr (by rw [add_comm]; exact tsub_le_iff_right.mp h₂)
  have hunion : K.law s (Φ ∩ Ψ)ᶜ ≤ ε₁ + ε₂ := by
    rw [Set.compl_inter]
    exact le_trans (measure_union_le _ _) (add_le_add hcΦ hcΨ)
  rw [prob_compl_eq_one_sub (hΦ.inter hΨ)] at hunion
  rw [tsub_le_iff_right] at hunion ⊢
  rw [add_comm]
  exact hunion

/-! ## `Q4`: thresholds, and what attainment adds -/

/--
**Threshold ability at `p`.** Some commitment of the coalition keeps the chance
of `Φ` at `p` or above against every answer.
-/
@[expose] public def ThresholdAbility (K : OutcomeLaw G) (C : Set N) (Φ : Set X)
    (p : ℝ≥0∞) : Prop :=
  ∃ sC : ∀ i : C, G.strategy i, ∀ sD : ∀ i : (Cᶜ : Set N), G.strategy i,
    p ≤ K.law (spliceProfile C sC sD) Φ

/-- **`Q4`, first half: threshold ability at `p` puts the lower value at `p`.** -/
public theorem le_lowerValue_of_thresholdAbility (K : OutcomeLaw G) (C : Set N)
    (Φ : Set X) {p : ℝ≥0∞} (h : K.ThresholdAbility C Φ p) :
    p ≤ K.lowerValue C Φ := by
  obtain ⟨sC, hsC⟩ := h
  exact le_iSup_of_le sC (le_iInf hsC)

/--
**`Q4`, second half: a lower value strictly above `p` is threshold ability at
`p`.**

The two halves do not meet at the boundary: a lower value *equal* to `p` gives
nothing, because the supremum need not be attained. The witness is
`AISafetyAtlas.Examples.Sovereignty.Influence.escalating_not_thresholdAbility_one`,
where the lower value is `1` and no commitment reaches it.
-/
public theorem thresholdAbility_of_lt_lowerValue (K : OutcomeLaw G) (C : Set N)
    (Φ : Set X) {p : ℝ≥0∞} (h : p < K.lowerValue C Φ) :
    K.ThresholdAbility C Φ p := by
  rw [lowerValue, lt_iSup_iff] at h
  obtain ⟨sC, hsC⟩ := h
  exact ⟨sC, fun sD => le_iInf_iff.mp hsC.le sD⟩

/-! ## `B1`: target power is payoff power at an indicator -/

/--
**The lower payoff value.** The same quantifiers as `lowerValue`, against a
bounded utility instead of a target.
-/
@[expose] public noncomputable def lowerPayoff (K : OutcomeLaw G) (C : Set N)
    (u : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ sC : ∀ i : C, G.strategy i, ⨅ sD : ∀ i : (Cᶜ : Set N), G.strategy i,
    ∫⁻ x, u x ∂(K.law (spliceProfile C sC sD))

/--
**`B1`: at an indicator, payoff power is target power.**

The expectation of an indicator is the probability of the event, so the whole
qualitative-target theory is the special case of the payoff theory at
zero-one utilities. A general utility adds a preference scale that qualitative
effectivity does not carry, which is print's point and the reason this is an
adapter rather than a generalization to be preferred.
-/
public theorem lowerPayoff_indicator (K : OutcomeLaw G) (C : Set N) {Φ : Set X}
    (hΦ : MeasurableSet Φ) :
    K.lowerPayoff C (Φ.indicator 1) = K.lowerValue C Φ := by
  simp only [lowerPayoff, lowerValue]
  exact iSup_congr fun _ => iInf_congr fun _ => lintegral_indicator_one hΦ

end OutcomeLaw

/-! ## `S5`: a minimum is below an average -/

/--
**`S5`: the worst protected demand is below the weighted mean.**

Print's warning is what the inequality does *not* give: the converse needs a
lower bound on the weight of the critical demand, and there is none here. A
high average certifies nothing about an indispensable low-scoring capability.
-/
public theorem iInf_le_lintegral {Q : Type*} [MeasurableSpace Q]
    (μ : MeasureTheory.Measure Q) [MeasureTheory.IsProbabilityMeasure μ]
    (v : Q → ℝ≥0∞) : (⨅ q : Q, v q) ≤ ∫⁻ q, v q ∂μ := by
  calc (⨅ q : Q, v q) = ∫⁻ _ : Q, (⨅ q : Q, v q) ∂μ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ q, v q ∂μ := lintegral_mono fun q => iInf_le _ q

/-! ## `D6`: clean operation through a horizon -/

/--
**`D6`: chaining one-step integrity bounds.**

If the chance of staying clean through step `t` is at least `1 - ε t` times the
chance of having been clean before it, then the chance of being clean through
the horizon is at least the product.

The hypothesis is the chain rule already applied; deriving it from conditional
probabilities is print's proof and is not carried out here, which is why this
is stated over an abstract sequence rather than over a filtration. Print also
notes that independence is unnecessary, and nothing here assumes it.
-/
public theorem prod_le_of_step_le (q ε : ℕ → ℝ≥0∞) (h0 : 1 ≤ q 0)
    (hstep : ∀ t, (1 - ε t) * q t ≤ q (t + 1)) (T : ℕ) :
    (∏ t ∈ Finset.range T, (1 - ε t)) ≤ q T := by
  induction T with
  | zero => simpa using h0
  | succ k ih =>
      rw [Finset.prod_range_succ]
      calc (∏ t ∈ Finset.range k, (1 - ε t)) * (1 - ε k)
          ≤ q k * (1 - ε k) := by gcongr
        _ = (1 - ε k) * q k := mul_comm _ _
        _ ≤ q (k + 1) := hstep k


/-! ## The sure layer sits inside -/

/-- **The law that puts all the mass on the outcome.** -/
@[expose] public noncomputable def diracLaw (G : GameForm.{u, v, w} N X) :
    OutcomeLaw G where
  law s := Measure.dirac (G.outcome s)
  isProbability _ := inferInstance

/--
**The bridge: sure winning is lower value one.** Under the Dirac law a
coalition's lower value for a measurable target is `1` exactly when it forces
the target.

This is the non-vacuity of the whole quantitative layer, and it is also its
test: the quantifier order in `lowerValue` is correct precisely because this
holds.
-/
public theorem lowerValue_diracLaw_eq_one_iff [∀ i, Nonempty (G.strategy i)]
    (C : Set N) {Φ : Set X} (hΦ : MeasurableSet Φ) :
    (diracLaw G).lowerValue C Φ = 1 ↔ Forces G C Φ := by
  classical
  have hval : ∀ s : ∀ i, G.strategy i,
      (diracLaw G).law s Φ = if G.outcome s ∈ Φ then 1 else 0 := by
    intro s
    simp [diracLaw, Measure.dirac_apply' _ hΦ, Set.indicator_apply]
  constructor
  · intro h
    rw [forces_iff_forall_splice]
    by_contra hcon
    have hzero : ∀ sC : ∀ i : C, G.strategy i,
        ⨅ sD : ∀ i : (Cᶜ : Set N), G.strategy i, (diracLaw G).law (spliceProfile C sC sD) Φ = 0 := by
      intro sC
      obtain ⟨sD, hsD⟩ : ∃ sD, G.outcome (spliceProfile C sC sD) ∉ Φ := by
        by_contra hall
        exact hcon ⟨sC, fun sD => by
          by_contra hmem
          exact hall ⟨sD, hmem⟩⟩
      refine le_antisymm (iInf_le_of_le sD ?_) bot_le
      rw [hval, if_neg hsD]
    simp only [OutcomeLaw.lowerValue] at h
    simp only [hzero, iSup_const] at h
    exact zero_ne_one h
  · intro h
    obtain ⟨sC, hsC⟩ := forces_iff_forall_splice.mp h
    refine le_antisymm (iSup_le fun _ => iInf_le_of_le (Classical.arbitrary _)
      ((diracLaw G).law_le_one _ _)) ?_
    refine le_iSup_of_le sC (le_iInf fun sD => ?_)
    rw [hval, if_pos (hsC sD)]

end AISafetyAtlas.Sovereignty
