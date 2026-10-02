module

public import AISafetyAtlas.Inference.Stochastic.Bridge
public import AISafetyAtlas.Inference.Stochastic.Interop
public import AISafetyAtlas.Examples.Inference.Device

/-!
# The general section-8 layer, inhabited

`Inference/Stochastic/Measure.lean` states Definitions 9–11 and Proposition 6 over
an arbitrary measurable space. Until this file, **nothing instantiated any of it**:
no example mentioned `massOn`, `IndependentOn`, `inferenceAccuracyOn` or
`prop6_half_of_miDistinguishabilityOn_eq_one`, and no module outside
`Inference/Stochastic/` imported the layer at all. It compiled, and it was a
theorem about nothing as far as the tree could show.

That is the same defect this development caught twice in the finite layer — an
uninhabited `Prop6Law`, and section 9's uninhabited `Infallible` — and it was
reintroduced by the generalisation itself.

The witness is the one already used for the finite layer: the four-point square
under the uniform measure. It costs nothing new, which is the point of
`Bridge.lean` — a `FinPMF` model **is** a measure-space model.
-/

namespace AISafetyAtlas.Examples.Inference.StochasticGeneral

open AISafetyAtlas.Inference MeasureTheory
open AISafetyAtlas.Examples.Inference.Device

/-- The uniform square as a genuine probability measure on `𝔹 × 𝔹`. -/
public noncomputable abbrev p6measure : Measure (Bool × Bool) := p6pmf.toMeasure

-- `fun_prop` discharges these from the `@[fun_prop]` lemmas in
-- `Stochastic/Measure.lean`; naming `Measurable.of_discrete` by hand is what the
-- general layer used to cost.
public theorem meas₁ : Measurable p6dev1.setup := by fun_prop
public theorem meas₂ : Measurable p6dev2.setup := by fun_prop
public theorem measc₁ : Measurable p6dev1.concl := by fun_prop
public theorem measc₂ : Measurable p6dev2.concl := by fun_prop

/-- Definition 9's masses transfer: the general fibre mass is the finite one. -/
public theorem p6_massOn_dev1_false : massOn p6measure p6dev1.setup false = 1 / 2 := by
  rw [massOn_toMeasure]; exact p6dev1_mass_false

public theorem p6_massOn_dev2_false : massOn p6measure p6dev2.setup false = 1 / 2 := by
  rw [massOn_toMeasure]; exact p6dev2_mass_false

/-- **The general layer's independence hypothesis, witnessed.** -/
public theorem p6_independentOn :
    IndependentOn p6measure p6dev1.setup p6dev2.setup :=
  (independentOn_toMeasure p6pmf p6dev1.setup p6dev2.setup).mpr p6_setups_independent

/-- **Definition 10 at its extreme value, over a genuine measure.** -/
public theorem p6_miDistinguishabilityOn_eq_one :
    miDistinguishabilityOn p6measure p6dev1 p6dev2 = 1 := by
  rw [miDistinguishabilityOn_toMeasure]
  exact p6_miDistinguishability_eq_one

public theorem p6_entropyOn_pos :
    0 < setupEntropyOn p6measure p6dev1 + setupEntropyOn p6measure p6dev2 := by
  rw [setupEntropyOn_toMeasure, setupEntropyOn_toMeasure]
  exact p6_entropy_pos

/-- **Proposition 6 over a general measure, on a witness.**

Every hypothesis of `prop6_half_of_miDistinguishabilityOn_eq_one` holds here,
including the one the paper actually prints — mutual-information
distinguishability `1`. So the general statement is not vacuous, and neither is
the measurability it asks for beyond the source. -/
public theorem p6_general_half :
    inferenceAccuracyOn p6measure p6dev1 p6dev2.concl *
      inferenceAccuracyOn p6measure p6dev2 p6dev1.concl ≤ 1 / 4 :=
  prop6_half_of_miDistinguishabilityOn_eq_one p6measure p6dev1 p6dev2
    meas₁ meas₂ measc₁ measc₂
    ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩ (by decide)
    (fun w => by cases h : w.1 <;> simp [p6dev1, h])
    ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩ (by decide)
    (fun w => by cases h : w.2 <;> simp [p6dev2, h])
    p6_massOn_dev1_false p6_massOn_dev2_false
    p6_entropyOn_pos p6_miDistinguishabilityOn_eq_one

/-! ## The same model, in Mathlib's vocabulary

`Interop.lean` claims the atlas independence predicate is Mathlib's `IndepFun`
and that a Mathlib `PMF` is a `FinPMF`. Both claims are exercised here, on the
model Proposition 6 already runs on — so the translation is not merely stated. -/

/-- **Proposition 6's independence hypothesis, as Mathlib states it.** -/
public theorem p6_indepFun :
    ProbabilityTheory.IndepFun p6dev1.setup p6dev2.setup p6measure :=
  (independentOn_iff_indepFun p6measure p6dev1.setup p6dev2.setup meas₁ meas₂).mp
    p6_independentOn

/-- …and back again, which is the direction a reader who already has `IndepFun`
needs. -/
public theorem p6_independentOn_of_indepFun :
    IndependentOn p6measure p6dev1.setup p6dev2.setup :=
  (independentOn_iff_indepFun p6measure p6dev1.setup p6dev2.setup meas₁ meas₂).mpr
    p6_indepFun

/-- A Mathlib `PMF` on the square gives the same measure as the `FinPMF` it
becomes, so every model above transfers to `PMF` input unchanged. -/
public theorem p6_ofPMF (p : PMF (Bool × Bool)) :
    (FinPMF.ofPMF p).toMeasure = p.toMeasure :=
  FinPMF.ofPMF_toMeasure p

/-- …and the translation is lossless in both directions: the model's own mass
function survives the round trip through `PMF`. -/
public theorem p6_pmf_round_trip (u : Bool × Bool) :
    (FinPMF.ofPMF p6pmf.toPMF).mass u = p6pmf.mass u :=
  FinPMF.ofPMF_toPMF p6pmf u

/-! ## Propositions 8 and 11 over a general measure, inhabited

`inferenceAccuracyOn_ge` and `prop11_of_independentOn` are the measure-space
forms, and they are modelled here rather than left to the finite layer. The
module-level example gate cannot see the difference: this module already covers
`Stochastic/Measure.lean` through Proposition 6, so a generalisation added there
counts as exercised whether or not any model reaches it.

Nothing new is needed: the square, its measurability facts and its masses are all
above.
-/

/-- Both fibre masses of the first device are positive. -/
public theorem p6_massOn_dev1_true : massOn p6measure p6dev1.setup true = 1 / 2 := by
  rw [massOn_toMeasure]; exact p6dev1_mass_true

public theorem p6_massOn_dev2_true : massOn p6measure p6dev2.setup true = 1 / 2 := by
  rw [massOn_toMeasure]; exact p6dev2_mass_true

/-- **Proposition 8 over a general measure, on a witness.** The target is the
second device's conclusion, whose realized range has two values, so the printed
factor `2 − |Γ(U)|` is `0` here and the bound says accuracy is nonnegative. -/
public theorem p6_prop8_general :
    ((2 - ((rangeFinset p6dev2.concl).card : ℝ)) *
        (positiveMassSetupsOn p6measure p6dev1).sup'
          (positiveMassSetupsOn_nonempty p6measure p6dev1)
          (fun x => condExpectPmOn p6measure p6dev1.setup x p6dev1.concl)) /
        ((rangeFinset p6dev2.concl).card : ℝ)
      ≤ inferenceAccuracyOn p6measure p6dev1 p6dev2.concl :=
  inferenceAccuracyOn_ge p6measure p6dev1 meas₁ measc₁ p6dev2.concl measc₂
    (by simp [rangeFinset, Finset.univ_eq_empty_iff])

/-- **Proposition 11 over a general measure, on a witness.** Every hypothesis is
discharged from facts already proved for Proposition 6 — the two devices' setups
are two-valued, realized, of positive mass, and independent. -/
public theorem p6_prop11_general :
    inferenceAccuracyOn p6measure p6dev1 p6dev2.concl *
        inferenceAccuracyOn p6measure p6dev2 p6dev1.concl ≤
      ⨆ z : Prop6Quadruple,
        prop6Expr (massOn p6measure p6dev1.setup false)
          (massOn p6measure p6dev2.setup false) z :=
  prop11_of_independentOn p6measure p6dev1 p6dev2 meas₁ meas₂ measc₁ measc₂
    ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩ (by decide)
    (fun w => by cases h : w.1 <;> simp [p6dev1, h])
    (by rw [p6_massOn_dev1_false]; norm_num)
    (by rw [p6_massOn_dev1_true]; norm_num)
    ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩ (by decide)
    (fun w => by cases h : w.2 <;> simp [p6dev2, h])
    (by rw [p6_massOn_dev2_false]; norm_num)
    (by rw [p6_massOn_dev2_true]; norm_num)
    p6_independentOn

/-! ## The `tsum` entropy layer, exercised

`entropySum` and `miDistinguishabilitySum` state Definition 10 with no
finiteness on the setup range. A definition with only an agreement theorem
behind it is the weak point this file exists to remove, so both are evaluated
here — through the agreement theorem, on the model Proposition 6 already runs
on.
-/

/-- The `tsum` entropy is positive on the square, so the layer is not
vacuously zero. -/
public theorem p6_entropySum_pos :
    0 < entropySum p6measure p6dev1.setup + entropySum p6measure p6dev2.setup := by
  rw [entropySum_eq_entropyOn, entropySum_eq_entropyOn]
  exact p6_entropyOn_pos

/-- **Definition 10 at its extreme value, in the `tsum` form.** The two devices
are maximally distinguishable, and the value survives the widening. -/
public theorem p6_miDistinguishabilitySum_eq_one :
    miDistinguishabilitySum p6measure p6dev1 p6dev2 = 1 := by
  rw [miDistinguishabilitySum_eq]
  exact p6_miDistinguishabilityOn_eq_one

/-! ## Ten more leaves of `Stochastic/Measure.lean`, on the same witness

Each of these was shipped and unapplied: nothing in the tree instantiated it.
The model is the one already built above -- no new construction, only the
application. -/

/-- **Independence is symmetric, witnessed.** -/
public theorem p6_independentOn_symm :
    IndependentOn p6measure p6dev2.setup p6dev1.setup :=
  IndependentOn.symm p6measure p6_independentOn

/-- **Definition 9's measurability, cited by name** rather than discharged
silently by `fun_prop` as `meas₁` above does. -/
public theorem p6_measurable_setup_cited : Measurable p6dev1.setup :=
  measurable_setup p6dev1

public theorem p6_measurable_concl_cited : Measurable p6dev1.concl :=
  measurable_concl p6dev1

/-- **The agreement indicator against a probe is measurable**, at the two
devices' conclusions. -/
public theorem p6_measurable_agree_probe :
    Measurable (fun u : Bool × Bool => p6dev1.concl u == probe true (p6dev2.concl u)) :=
  measurable_agree_probe p6dev1.concl measc₁ p6dev2.concl measc₂ true

/-- **Gibbs' inequality over a general measure, at the witness.** The general
form of `p6_entropyOn_pos`'s companion fact. -/
public theorem p6_mutualInfoOn_nonneg :
    0 ≤ mutualInfoOn p6measure p6dev1.setup p6dev2.setup :=
  mutualInfoOn_nonneg p6measure p6dev1.setup p6dev2.setup meas₁ meas₂

/-- **The joint range sits inside the product of the marginals' ranges.** -/
public theorem p6_rangeFinset_prod_subset :
    rangeFinset (fun u : Bool × Bool => (p6dev1.setup u, p6dev2.setup u)) ⊆
      rangeFinset p6dev1.setup ×ˢ rangeFinset p6dev2.setup :=
  rangeFinset_prod_subset p6dev1.setup p6dev2.setup

/-- **Joint masses marginalise**, at the witness. -/
public theorem p6_sum_massOn_marginal :
    (rangeFinset p6dev2.setup).sum
        (fun b => massOn p6measure (fun u => (p6dev1.setup u, p6dev2.setup u)) (false, b))
      = massOn p6measure p6dev1.setup false :=
  sum_massOn_marginal p6measure p6dev1.setup p6dev2.setup meas₁ meas₂ false

/-- **The printed `max` and the `sup'` form agree**, unconditionally on a
finite setup range. -/
public theorem p6_accuracySupOn_eq_sup' :
    accuracySupOn p6measure p6dev1 p6dev2.concl
      = (positiveMassSetupsOn p6measure p6dev1).sup' (positiveMassSetupsOn_nonempty p6measure p6dev1)
          (fun x => condExpectPmOn p6measure p6dev1.setup x p6dev2.concl) :=
  accuracySupOn_eq_sup' p6measure p6dev1 p6dev2.concl

/-- **Definition 9's accuracy is at most one**, over a general measure. -/
public theorem p6_inferenceAccuracyOn_le_one :
    inferenceAccuracyOn p6measure p6dev1 p6dev2.concl ≤ 1 :=
  inferenceAccuracyOn_le_one p6measure p6dev1 p6dev2.concl

/-! ## Reporting `true` unconditionally: the general `IsGreatest` and `ge` forms

Fixing the report at the constant `true` makes every positively-massed setup
value agree with it certainly, so the accuracy supremum collapses to the single
value `1` -- cheap to compute and enough to inhabit both remaining conditional
theorems. -/

/-- **A constant report is certain wherever the setup has any mass at all.** -/
public theorem p6_condExpectPmOn_dev1_true (x : Bool)
    (hx : 0 < massOn p6measure p6dev1.setup x) :
    condExpectPmOn p6measure p6dev1.setup x (fun _ => true) = 1 := by
  have hset : (fun u : Bool × Bool => (p6dev1.setup u, true)) ⁻¹' {(x, true)}
      = p6dev1.setup ⁻¹' {x} := by
    ext u
    simp
  have hmass : massOn p6measure (fun u : Bool × Bool => (p6dev1.setup u, true)) (x, true)
      = massOn p6measure p6dev1.setup x := by
    show (p6measure ((fun u : Bool × Bool => (p6dev1.setup u, true)) ⁻¹' {(x, true)})).toReal
      = massOn p6measure p6dev1.setup x
    rw [hset]
    rfl
  have hagree : condAgreeOn p6measure p6dev1.setup x (fun _ => true) = 1 := by
    show (if massOn p6measure p6dev1.setup x = 0 then 0
        else massOn p6measure (fun u => (p6dev1.setup u, (fun _ => true) u)) (x, true)
          / massOn p6measure p6dev1.setup x) = 1
    rw [if_neg (ne_of_gt hx)]
    show massOn p6measure (fun u : Bool × Bool => (p6dev1.setup u, true)) (x, true)
        / massOn p6measure p6dev1.setup x = 1
    rw [hmass]
    exact div_self (ne_of_gt hx)
  show 2 * condAgreeOn p6measure p6dev1.setup x (fun _ => true) - 1 = 1
  rw [hagree]
  ring

/-- **The image, at `report := true`, is the single point `1`.** -/
public theorem p6_isGreatest_dev1_true :
    IsGreatest ((fun x => condExpectPmOn p6measure p6dev1.setup x (fun _ => true)) ''
      positiveMassSetOn p6measure p6dev1) 1 := by
  constructor
  · refine ⟨false, ?_, p6_condExpectPmOn_dev1_true false ?_⟩
    · show 0 < massOn p6measure p6dev1.setup false
      rw [p6_massOn_dev1_false]; norm_num
    · rw [p6_massOn_dev1_false]; norm_num
  · rintro y ⟨x, hx, rfl⟩
    exact (p6_condExpectPmOn_dev1_true x hx).le

/-- **The printed `max` and the `sSup` form agree here**, over an arbitrary
setup range -- the theorem `accuracySupOn_eq_sup'` cannot state, since it needs
finiteness. -/
public theorem p6_accuracySupOn_eq_of_isGreatest :
    accuracySupOn p6measure p6dev1 (fun _ => true) = 1 :=
  accuracySupOn_eq_of_isGreatest p6measure p6dev1 (fun _ => true) p6_isGreatest_dev1_true

/-- **Proposition 8's general lower bound, at the witness.** The target is the
constant report, whose realized range is the singleton `{true}`, so the printed
factor is `1` and the bound reads off `accuracySupOn` directly. -/
public theorem p6_inferenceAccuracySupOn_ge :
    ((2 - ((rangeFinset (fun _ : Bool × Bool => true)).card : ℝ)) *
        accuracySupOn p6measure p6dev1 p6dev1.concl) /
        ((rangeFinset (fun _ : Bool × Bool => true)).card : ℝ)
      ≤ inferenceAccuracySupOn p6measure p6dev1 (fun _ : Bool × Bool => true) :=
  inferenceAccuracySupOn_ge p6measure p6dev1 meas₁ measc₁ (fun _ => true) measurable_const
    ⟨false, by rw [p6_massOn_dev1_false]; norm_num⟩
    (by
      have hmem : true ∈ rangeFinset (fun _ : Bool × Bool => true) :=
        self_mem_rangeFinset _ (false, false)
      exact (Finset.card_pos.mpr ⟨true, hmem⟩).ne')

/-! ## Interop, at the witness -/

/-- **`toPMF` reads off the mass, at the witness.** -/
public theorem p6_toPMF_apply : p6pmf.toPMF (false, false) = ENNReal.ofReal (p6pmf.mass (false, false)) :=
  FinPMF.toPMF_apply p6pmf (false, false)

/-- **And a Mathlib `PMF` survives the round trip through `FinPMF`**, at the
witness. -/
public theorem p6_toPMF_ofPMF :
    (FinPMF.ofPMF p6pmf.toPMF).toPMF (false, false) = p6pmf.toPMF (false, false) :=
  PMF.toPMF_ofPMF p6pmf.toPMF (false, false)

/-! ## The pointwise Gibbs step, at one triple

`gibbs_cell_eq_iff` needs no model at all -- three real numbers. The equality
case at `q = p₁p₂` is the one the module exists for. -/

/-- **Equality in the pointwise Gibbs step, at a triple where it holds.** -/
public theorem gibbs_eq_iff_at_quarter :
    ((if (1 / 4 : ℝ) = 0 then 0 else (1 / 4 : ℝ) * Real.log (1 / 2)) +
        (if (1 / 4 : ℝ) = 0 then 0 else (1 / 4 : ℝ) * Real.log (1 / 2)) -
        (if (1 / 4 : ℝ) = 0 then 0 else (1 / 4 : ℝ) * Real.log (1 / 4))
      = (1 / 2 : ℝ) * (1 / 2) - 1 / 4) ↔ (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2) :=
  gibbs_cell_eq_iff (by norm_num) (by norm_num) (by norm_num)

/-! ## Seven leaves of the finite layer, `Stochastic.lean`, on the same witness

`p6pmf`/`p6dev1`/`p6dev2` are `FinPMF` objects already, so the finite-layer
statements apply to them directly -- no widening through `Bridge.lean` needed. -/

/-- **A mass function's values are at most one.** -/
public theorem p6_mass_le_one : p6pmf.mass (false, false) ≤ 1 :=
  FinPMF.mass_le_one p6pmf (false, false)

/-- **Statistical independence is symmetric, at the witness.** -/
public theorem p6_setups_independent_symm :
    StatisticallyIndependent p6pmf p6dev2.setup p6dev1.setup :=
  StatisticallyIndependent.symm p6_setups_independent

/-- **Negation flips the `±1` reading.** -/
public theorem p6_boolPm_not : boolPm (!true) = -boolPm true :=
  boolPm_not true

/-- **`cov = 1` iff exact inference, at the witness's own devices.** Both
directions are exercised, since the iff is the leaf. -/
public theorem p6_inferenceAccuracy_eq_one_iff :
    inferenceAccuracy p6dev1 p6pmf p6dev2.concl = 1 ↔ WeaklyInfers p6dev1 p6dev2.concl :=
  inferenceAccuracy_eq_one_iff p6dev1 p6pmf p6dev2.concl (fun _ => by norm_num [p6pmf])

/-- **The finite-layer accuracy bound, at the witness.** -/
public theorem p6_inferenceAccuracy_le_one :
    inferenceAccuracy p6dev1 p6pmf p6dev2.concl ≤ 1 :=
  inferenceAccuracy_le_one p6dev1 p6pmf p6dev2.concl

/-- **Some setup value is realized.** -/
public theorem p6_realizedSetups_nonempty : (Finset.univ.image p6dev1.setup).Nonempty :=
  realizedSetups_nonempty p6dev1

/-- **A positive pushforward mass names a realizing point.** -/
public theorem p6_realized_of_pushOnImage_pos : ∃ u : Bool × Bool, p6dev1.setup u = false :=
  realized_of_pushOnImage_pos p6pmf p6dev1.setup
    (show (0 : ℝ) < pushOnImage p6pmf p6dev1.setup false by
      rw [show pushOnImage p6pmf p6dev1.setup false = setupMass p6pmf p6dev1 false from rfl,
        p6dev1_mass_false]
      norm_num)

/-! ## Six of the seven leaves of `Complexity/Measure.lean`, on the same witness -/

/-- Both setup values of the first device carry positive mass -- both cases of
the same fact `p6_massOn_dev1_false`/`p6_massOn_dev1_true` already established. -/
public theorem p6_massOn_dev1_pos (x : Bool) : 0 < massOn p6measure p6dev1.setup x := by
  cases x
  · rw [p6_massOn_dev1_false]; norm_num
  · rw [p6_massOn_dev1_true]; norm_num

/-- **Definition 6's length is anti-symmetric under subtraction**, at the
witness's two devices. -/
public theorem p6_measureLength_sub_measureLength :
    measureLength p6measure p6dev1 false - measureLength p6measure p6dev2 false
      = Real.log (massOn p6measure p6dev2.setup false / massOn p6measure p6dev1.setup false) :=
  measureLength_sub_measureLength p6measure p6dev1 p6dev2 false false
    (p6_massOn_dev1_pos false)
    (by rw [p6_massOn_dev2_false]; norm_num)

/-- **The length is nonnegative**, at the witness. -/
public theorem p6_relativeLength_nonneg : 0 ≤ relativeLength p6measure p6dev1 false :=
  relativeLength_nonneg p6measure p6dev1 false

/-- **The two forms of the union complexity agree**, at the witness. -/
public theorem p6_unionInferenceComplexityOn_eq :
    unionInferenceComplexityOn p6measure p6dev1 p6dev2.concl
      = unionInferenceComplexity p6measure p6dev1 p6dev2.concl :=
  unionInferenceComplexityOn_eq p6measure p6dev1 p6dev2.concl

/-- **The answering mass is the sum of `exp(-length)` over the answering set**,
at the witness. Every setup value of `p6dev1` carries positive mass, so
`hpos` is free of any membership case-analysis. -/
public theorem p6_answeringMass_eq_sum_exp :
    answeringMass p6measure p6dev1 p6dev2.concl id
      = (answeringSet p6dev1 p6dev2.concl id).sum
          (fun x => Real.exp (-(measureLength p6measure p6dev1 x))) :=
  answeringMass_eq_sum_exp p6measure p6dev1 meas₁ p6dev2.concl id
    (fun x _ => p6_massOn_dev1_pos x)

/-! ### A device whose setup carries no information

`relativeLength_eq_zero_of_cond_eq` and its converse both need a setup value
whose conditional law is the prior itself. Conditioning on the whole space does
that for free: a device with a single setup value conditions on `Set.univ`,
and `ProbabilityTheory.cond_univ` is exactly *"conditioning on everything
changes nothing."* -/

/-- **The device that never actually sets up anything**: one setup value, the
first device's conclusion. -/
@[expose] public noncomputable def constDevice : InferenceDevice (Bool × Bool) where
  Setup := Unit
  setup _ := ()
  concl := p6dev1.concl
  concl_surjective := p6dev1.concl_surjective

/-- **Its one setup value's fibre is the whole space.** -/
public theorem p6_constDevice_fibre_univ :
    (constDevice.setup ⁻¹' {()} : Set (Bool × Bool)) = Set.univ :=
  Set.eq_univ_of_forall (fun _ => rfl)

/-- **So its conditional law is the prior, unconditionally.** -/
public theorem p6_condLawOn_constDevice : condLawOn p6measure constDevice () = p6measure := by
  show ProbabilityTheory.cond p6measure (constDevice.setup ⁻¹' {()}) = p6measure
  rw [p6_constDevice_fibre_univ, ProbabilityTheory.cond_univ]

/-- **A setup value that says nothing costs nothing, at the witness.** -/
public theorem p6_relativeLength_eq_zero_of_cond_eq :
    relativeLength p6measure constDevice () = 0 :=
  relativeLength_eq_zero_of_cond_eq p6measure constDevice () p6_condLawOn_constDevice

/-- **And conversely: zero length recovers the equality, at the witness.**

The forward direction above proves `condLawOn = p6measure` directly; this cites
the converse theorem to re-derive it from the length being zero, which is what
grounds it. -/
public theorem p6_relativeLength_zero_recovers_condLawOn :
    condLawOn p6measure constDevice () = p6measure := by
  have : IsFiniteMeasure (condLawOn p6measure constDevice ()) := by
    rw [p6_condLawOn_constDevice]; infer_instance
  exact condLawOn_eq_of_relativeLength_eq_zero p6measure constDevice ()
    (by rw [p6_condLawOn_constDevice, InformationTheory.klDiv_self]; exact ENNReal.zero_ne_top)
    p6_relativeLength_eq_zero_of_cond_eq

/-! ## The last leaf: `sourceStochasticComplexity_eq`

`p6pmf` is already exactly uniform, so it is its own witness for "uniform on
every fibre" -- the constant `c := fun _ => 1/4` needs no case split. -/

/-- **`massOn` against the identity reads off the mass function directly.** -/
public theorem p6_massOn_id_eq (u : Bool × Bool) : massOn p6measure id u = p6pmf.mass u := by
  rw [massOn_toMeasure]
  show pushOnImage p6pmf id u = p6pmf.mass u
  simp [pushOnImage, Finset.filter_eq']

/-- **Every singleton carries positive measure.** -/
public theorem p6_measure_singleton_ne_zero (u : Bool × Bool) : p6measure {u} ≠ 0 := by
  intro h
  have hzero : massOn p6measure id u = 0 := by
    show (p6measure (id ⁻¹' {u})).toReal = 0
    rw [show (id ⁻¹' {u} : Set (Bool × Bool)) = {u} from rfl, h]
    rfl
  rw [p6_massOn_id_eq] at hzero
  norm_num [p6pmf] at hzero

/-- **The source's `ε = 1` identity, at the witness.** `hagree` is free because
every function out of a discrete space is measurable; `hpos` is free because
both setup values carry positive mass; `huniform` is free because `p6pmf` is
already constant. Nothing here is case analysis -- the witness was chosen so
that the hardest three hypotheses collapse to `rfl`. -/
public theorem p6_sourceStochasticComplexity_eq :
    sourceStochasticComplexity p6measure p6pmf p6dev1 p6dev2.concl 1
      = inferenceComplexityTotal p6dev1 (setupLength p6dev1) p6dev2.concl :=
  sourceStochasticComplexity_eq p6measure p6pmf p6dev1 meas₁ p6dev2.concl
    (fun _ => Measurable.of_discrete)
    (fun u => p6_measure_singleton_ne_zero u)
    (fun x _ => (p6_massOn_dev1_pos x).ne')
    (fun _ => (1 / 4 : ℝ)) (fun _ => by norm_num)
    (fun _ _ _ => rfl)

/-- **`cov = 1` iff exact inference, over a general measure, at the witness.**
The general-measure counterpart of `p6_inferenceAccuracy_eq_one_iff` above --
missed in the first pass over `Stochastic/Measure.lean`, closed here. -/
public theorem p6_inferenceAccuracyOn_eq_one_iff :
    inferenceAccuracyOn p6measure p6dev1 p6dev2.concl = 1 ↔ WeaklyInfers p6dev1 p6dev2.concl :=
  inferenceAccuracyOn_eq_one_iff p6measure p6dev1 meas₁ measc₁ p6dev2.concl measc₂
    p6_measure_singleton_ne_zero ⟨(false, false)⟩

end AISafetyAtlas.Examples.Inference.StochasticGeneral
