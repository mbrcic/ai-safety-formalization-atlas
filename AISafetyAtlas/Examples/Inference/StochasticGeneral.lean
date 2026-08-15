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

end AISafetyAtlas.Examples.Inference.StochasticGeneral
