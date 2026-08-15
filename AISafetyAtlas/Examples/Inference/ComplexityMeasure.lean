module

public import AISafetyAtlas.Inference.Complexity.Measure
public import AISafetyAtlas.Inference.Stochastic.Bridge
public import AISafetyAtlas.Examples.Inference.Complexity

/-!
# Section 5 under a general measure, inhabited

`Inference/Complexity/Measure.lean` restates Definition 6 with `ℒ(x) =
−ln μ(X⁻¹(x))` for an arbitrary measure, and adds section 8's prose definition
`C̄_ε(Γ ∣ C)`. Until this file **nothing instantiated any of it**: no example
mentioned `measureLength`, `inferenceComplexityMeasure`, `accurateSet` or
`stochasticInferenceComplexity`, and the module was reachable only from the build
target list.

Sixth instance of a defect this development keeps producing — after `Prop6Law`,
section 9's `Infallible`, the general section-8 layer, section 5's inference
complexity and Proposition 3(ii). This one and the section-8 layer were
reintroduced by the generalisation itself; the rest were never witnessed at all.
`scripts/check_example_coverage.py` now fails the gate on the module-sized cases
rather than waiting for a review.

The witness is the `Fin 4` pair from `Examples.Inference.Complexity` under the
uniform measure. Two things worth having follow from it:

* Theorem 4's bound is attained here too, and by the *same* number `2·log 2` as
  in the counting case. That constant is a difference of lengths, and the uniform
  measure is counting measure divided by `4`, so every length shifts by `log 4`
  and the difference does not move. That is the substantive content of the
  general-measure restatement being an instantiation rather than a second theorem;
* Definition 6 under counting measure is `inferenceComplexity` on the nose
  (`count_complexity_eq`), which is what the general module's header asserts.
-/

namespace AISafetyAtlas.Examples.Inference.ComplexityMeasure

open AISafetyAtlas.Inference MeasureTheory
open AISafetyAtlas.Examples.Inference.Device
open AISafetyAtlas.Examples.Inference.Complexity

/-- The uniform mass on the four-point universe. -/
@[expose] public noncomputable def uniform4 : FinPMF (Fin 4) where
  mass := fun _ => 1 / 4
  nonneg := fun _ => by norm_num
  sum_one := by norm_num

/-- …as a genuine measure, via `Bridge.lean`. -/
public noncomputable abbrev mu4 : Measure (Fin 4) := uniform4.toMeasure

/-! ## Fibre masses -/

public theorem mass_fine (x : Fin 4) : massOn mu4 fineDevice.setup x = 1 / 4 := by
  classical
  rw [massOn_toMeasure]
  unfold pushOnImage
  have h : (Finset.univ.filter (fun u : Fin 4 => fineDevice.setup u = x)) = {x} := by
    ext u
    simp [fineDevice]
  rw [h, Finset.sum_singleton]
  norm_num [uniform4]

public theorem mass_coarse (x : Bool) : massOn mu4 coarseForcedDevice.setup x = 1 / 2 := by
  classical
  rw [massOn_toMeasure]
  unfold pushOnImage
  cases x
  · have h : (Finset.univ.filter (fun u : Fin 4 => coarseForcedDevice.setup u = false))
        = ({0, 1} : Finset (Fin 4)) := by
      ext u
      fin_cases u <;> simp [coarseForcedDevice]
    rw [h, Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1)]
    norm_num [uniform4]
  · have h : (Finset.univ.filter (fun u : Fin 4 => coarseForcedDevice.setup u = true))
        = ({2, 3} : Finset (Fin 4)) := by
      ext u
      fin_cases u <;> simp [coarseForcedDevice]
    rw [h, Finset.sum_pair (by decide : (2 : Fin 4) ≠ 3)]
    norm_num [uniform4]

/-! ## The general-measure length

Under the uniform measure the lengths are `log 4` and `log 2`, against `0` and
`−log 2` under counting measure. The offset is the constant `log 4` in both
cases, so `measureLength` here is `setupLength` renormalised. -/

public theorem measureLength_fine (x : Fin 4) :
    measureLength mu4 fineDevice x = Real.log 4 := by
  unfold measureLength
  rw [mass_fine, show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]

public theorem measureLength_coarse (x : Bool) :
    measureLength mu4 coarseForcedDevice x = Real.log 2 := by
  unfold measureLength
  rw [mass_coarse, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]

/-- **Definition 6 under counting measure is Definition 6 under counting measure.**
The general module's header says its Example 6 case *is* `setupLength`; this is
that claim on a worked model, through `measureLength_count`. -/
public theorem count_complexity_eq :
    inferenceComplexityMeasure (MeasureTheory.Measure.count : Measure (Fin 4)) fineDevice
        gamma4 fine_weaklyInfers_gamma4 =
      inferenceComplexity fineDevice (setupLength fineDevice) gamma4
        fine_weaklyInfers_gamma4 := by
  unfold inferenceComplexityMeasure
  congr 1
  funext x
  exact measureLength_count fineDevice x

/-- Hence it is `0` here, exactly as the counting computation gave. -/
public theorem count_complexity_zero :
    inferenceComplexityMeasure (MeasureTheory.Measure.count : Measure (Fin 4)) fineDevice
      gamma4 fine_weaklyInfers_gamma4 = 0 := by
  rw [count_complexity_eq, fine_complexity]

/-- The uniform-measure length is the counting length shifted by a constant. The
shift is the same for both devices, which is why Theorem 4's bound — a difference
of lengths — is unchanged below. -/
public theorem measureLength_eq_setupLength_add (x : Fin 4) (y : Bool) :
    measureLength mu4 fineDevice x = setupLength fineDevice x + Real.log 4 ∧
      measureLength mu4 coarseForcedDevice y
        = setupLength coarseForcedDevice y + Real.log 4 := by
  refine ⟨by rw [measureLength_fine, fine_setupLength]; ring, ?_⟩
  rw [measureLength_coarse, coarse_setupLength]
  have : Real.log 4 = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [this]
  ring

/-! ## Definition 6 and Theorem 4 under the general measure -/

public theorem fine_complexityMeasure :
    inferenceComplexityMeasure mu4 fineDevice gamma4 fine_weaklyInfers_gamma4
      = 2 * Real.log 4 := by
  unfold inferenceComplexityMeasure inferenceComplexity inferenceComplexityTotal
  have hterm : ∀ γ ∈ rangeFinset gamma4,
      minAnsweringLength fineDevice (measureLength mu4 fineDevice) gamma4 (probe γ)
        = Real.log 4 := by
    intro γ hγ
    unfold minAnsweringLength
    rw [dif_pos (answeringSet_nonempty_of_weaklyInfers fineDevice fine_weaklyInfers_gamma4 γ
      ((mem_rangeFinset gamma4 γ).mp hγ))]
    exact inf'_of_const _ _ _ (fun y _ => measureLength_fine y)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, rangeFinset_gamma4]
  simp

public theorem coarse_complexityMeasure :
    inferenceComplexityMeasure mu4 coarseForcedDevice gamma4 coarse_weaklyInfers_gamma4
      = 2 * Real.log 2 := by
  unfold inferenceComplexityMeasure inferenceComplexity inferenceComplexityTotal
  have hterm : ∀ γ ∈ rangeFinset gamma4,
      minAnsweringLength coarseForcedDevice (measureLength mu4 coarseForcedDevice) gamma4
          (probe γ) = Real.log 2 := by
    intro γ hγ
    unfold minAnsweringLength
    rw [dif_pos (answeringSet_nonempty_of_weaklyInfers coarseForcedDevice
      coarse_weaklyInfers_gamma4 γ ((mem_rangeFinset gamma4 γ).mp hγ))]
    exact inf'_of_const _ _ _ (fun y _ => measureLength_coarse y)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, rangeFinset_gamma4]
  simp

public theorem emulationCostMeasure_eq :
    emulationCost fineDevice coarseForcedDevice (measureLength mu4 fineDevice)
      (measureLength mu4 coarseForcedDevice) = Real.log 2 := by
  unfold emulationCost
  have hne : (realizedSetups coarseForcedDevice).Nonempty := by
    refine ⟨false, ?_⟩
    unfold realizedSetups
    exact (mem_rangeFinset _ _).mpr (coarse_realized false)
  rw [dif_pos hne]
  refine sup'_of_const _ _ _ (fun y _ => ?_)
  unfold emulationCostAt
  rw [dif_pos (emulationSet_nonempty_of_stronglyInfers fine_stronglyInfers_coarse
    (coarse_realized y))]
  refine inf'_of_const _ _ _ (fun z _ => ?_)
  rw [measureLength_fine, measureLength_coarse,
    show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- **Theorem 4 under a general measure, attained.** Both sides are `2·log 2` —
the same number as in the counting case, because the bound compares lengths and
the change of measure shifts them all by `log 4`. -/
public theorem witness_thm4_measure_tight :
    inferenceComplexityMeasure mu4 fineDevice gamma4 fine_weaklyInfers_gamma4 -
        inferenceComplexityMeasure mu4 coarseForcedDevice gamma4 coarse_weaklyInfers_gamma4 =
      ((rangeFinset gamma4).card : ℝ) *
        emulationCost fineDevice coarseForcedDevice (measureLength mu4 fineDevice)
          (measureLength mu4 coarseForcedDevice) := by
  rw [fine_complexityMeasure, coarse_complexityMeasure, emulationCostMeasure_eq,
    rangeFinset_gamma4,
    show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  simp
  ring

/-- The general-measure Theorem 4 applies here, as an inequality. -/
public theorem witness_thm4_measure :
    inferenceComplexityMeasure mu4 fineDevice gamma4 fine_weaklyInfers_gamma4 -
        inferenceComplexityMeasure mu4 coarseForcedDevice gamma4 coarse_weaklyInfers_gamma4 ≤
      ((rangeFinset gamma4).card : ℝ) *
        emulationCost fineDevice coarseForcedDevice (measureLength mu4 fineDevice)
          (measureLength mu4 coarseForcedDevice) :=
  inferenceComplexityMeasure_le_of_stronglyInfers mu4 gamma4 fine_stronglyInfers_coarse
    coarse_weaklyInfers_gamma4

/-! ## Section 8's stochastic complexity

`stochasticInferenceComplexity_le` is the source's `ε = 1` remark in the
direction that needs no extra hypothesis. Its positive-mass side condition is
satisfiable, and here trivially so: every coarse fibre has mass `1/2`. -/

public theorem coarse_mass_ne_zero (x : Bool) :
    x ∈ realizedSetups coarseForcedDevice → massOn mu4 coarseForcedDevice.setup x ≠ 0 := by
  intro _
  rw [mass_coarse]
  norm_num

/-- **`C̄₁(Γ ∣ C) ≤ 𝒞(Γ ∣ C)` on a witness.** Relaxing exact answering to
accuracy `1` only enlarges the set the minimum ranges over. -/
public theorem witness_stochasticComplexity_le :
    stochasticInferenceComplexity mu4 coarseForcedDevice
        (measureLength mu4 coarseForcedDevice) gamma4 1 ≤
      inferenceComplexityTotal coarseForcedDevice
        (measureLength mu4 coarseForcedDevice) gamma4 :=
  stochasticInferenceComplexity_le mu4 coarseForcedDevice _ gamma4
    coarse_weaklyInfers_gamma4 coarse_mass_ne_zero

/-- Definition 9's accuracy set is inhabited at `ε = 1`, so the minimum in
`C̄₁` is not the totalization either. -/
public theorem witness_accurateSet_nonempty (γ : Bool) (hγ : ∃ w, gamma4 w = γ) :
    (accurateSet mu4 coarseForcedDevice gamma4 (probe γ) 1).Nonempty := by
  obtain ⟨x, hx⟩ :=
    answeringSet_nonempty_of_weaklyInfers coarseForcedDevice coarse_weaklyInfers_gamma4 γ hγ
  refine ⟨x, mem_accurateSet_of_answersProbe mu4 coarseForcedDevice gamma4 (probe γ) ?_ hx⟩
  rw [mass_coarse]
  norm_num

/-- The uniform measure gives every point positive mass, which is the atlas form
of the source's *"`P` proportional to `dμ` across the support of `P`"*. -/
public theorem mu4_atomic (u : Fin 4) : mu4 {u} ≠ 0 := by
  classical
  have h : massOn mu4 (fun v : Fin 4 => v) u = 1 / 4 := by
    rw [massOn_toMeasure]
    unfold pushOnImage
    have hf : (Finset.univ.filter (fun v : Fin 4 => v = u)) = {u} := by
      ext v
      simp
    rw [hf, Finset.sum_singleton]
    norm_num [uniform4]
  intro h0
  rw [massOn, show ((fun v : Fin 4 => v) ⁻¹' {u}) = ({u} : Set (Fin 4)) from rfl, h0] at h
  norm_num at h

/-- **The source's `ε = 1` remark in full, on a witness.** With no null points the
two complexities are equal, not merely ordered. -/
public theorem witness_stochasticComplexity_eq :
    stochasticInferenceComplexity mu4 coarseForcedDevice
        (measureLength mu4 coarseForcedDevice) gamma4 1 =
      inferenceComplexityTotal coarseForcedDevice
        (measureLength mu4 coarseForcedDevice) gamma4 :=
  stochasticInferenceComplexity_eq mu4 coarseForcedDevice Measurable.of_discrete _ gamma4
    (fun _ => Measurable.of_discrete) mu4_atomic coarse_mass_ne_zero

/-- …and the common value is `2·log 2`, so neither side is degenerate. -/
public theorem witness_stochasticComplexity_value :
    stochasticInferenceComplexity mu4 coarseForcedDevice
      (measureLength mu4 coarseForcedDevice) gamma4 1 = 2 * Real.log 2 := by
  rw [witness_stochasticComplexity_eq]
  exact coarse_complexityMeasure

/-! ## The S4 layer: conditional entropy and the source's own `C̄_ε`

`condEntropy` and `sourceStochasticComplexity` were added so the printed object
of §8 — *"`C̄_ε` with the length fixed at `−ℍ(U ∣ x)`"* — would finally have a
name. They had bridge theorems and **no evaluation**: nothing in the tree
computed `ℍ(U ∣ x)` at a model, so `neg_condEntropy_eq_setupLength_of_uniform`
related two objects of which one had never been seen to take a value.

Both are computed here on the model above.
-/

/-- **`ℍ(U ∣ x) = 0` on the fine device.** Its setup is the identity, so every
fibre is a single point, the conditional distribution is a point mass, and the
conditional entropy vanishes. -/
theorem condEntropy_fine (x : Fin 4) : condEntropy uniform4 fineDevice.setup x = 0 := by
  classical
  have h : (Finset.univ.filter (fun u : Fin 4 => fineDevice.setup u = x)) = {x} := by
    ext u; simp [fineDevice]
  rw [condEntropy, h]
  simp [uniform4]

/-- **`ℍ(U ∣ x) = −ln 2` in the negated form on the coarse device**, whose fibres
carry two of the four states each. `neg_condEntropy_eq_setupLength_of_uniform`
is the source's *"`P` proportional to `dμ` across the support"*, which at a
uniform mass function is exactly uniformity on the fibre. -/
theorem neg_condEntropy_coarse (x : Bool) :
    -condEntropy uniform4 coarseForcedDevice.setup x
      = setupLength coarseForcedDevice x :=
  neg_condEntropy_eq_setupLength_of_uniform uniform4 coarseForcedDevice x
    (c := 1 / 4) (by norm_num) (fun _ _ => rfl)

/-- **The printed `C̄_ε` at `ε = 1`, evaluated.** With the length fixed at
`−ℍ(U ∣ x)` and `P` uniform, the source's object is the section-5 complexity of
the same device, and here that is `2 ln 2` — the value the Theorem 4 witness
above is tight at, up to the normalisation. The printed remark *"for `ε = 1`,
`C̄_ε = 𝒞`"* is therefore not only proved but exhibited at a number.

The sign is worth noting: `setupLength` is `−log` of a **fibre cardinality**, so
a two-element fibre costs `−ln 2` and the total is negative. Under `mu4` the same
device's `measureLength` is `−log` of a *mass*, which shifts every length by
`ln 4` and lands the section-5 value at `+2 ln 2` — `coarse_complexityMeasure`.
Two normalisations of one object, and this is the counting one. -/
theorem sourceStochasticComplexity_value :
    sourceStochasticComplexity mu4 uniform4 coarseForcedDevice gamma4 1
      = -(2 * Real.log 2) := by
  rw [sourceStochasticComplexity]
  rw [show (fun x => -condEntropy uniform4 coarseForcedDevice.setup x)
      = setupLength coarseForcedDevice from funext neg_condEntropy_coarse]
  rw [stochasticInferenceComplexity_eq mu4 coarseForcedDevice Measurable.of_discrete _ gamma4
    (fun _ => Measurable.of_discrete) mu4_atomic coarse_mass_ne_zero]
  rw [← inferenceComplexity_eq_total coarseForcedDevice _ gamma4 coarse_weaklyInfers_gamma4]
  exact coarse_complexity

end AISafetyAtlas.Examples.Inference.ComplexityMeasure
