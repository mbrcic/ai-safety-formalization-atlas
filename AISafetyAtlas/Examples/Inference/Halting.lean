module

public import AISafetyAtlas.Inference

/-!
# Worked models: halting, recursive devices, and the two readings of Definition 9

Definition 8's identification is exercised on a device that halts everywhere and
one that does not, so `recursive_iff_refines` is shown separating real cases
rather than holding vacuously.

The Definition 9 material is a source finding rather than a theorem to
instantiate, and it lives with the definition: `two_rpow_neg_measureLength` says
what the printed formula computes, `two_rpow_neg_measureLengthBase2` says what the
base-consistent reading computes, and `sum_pushOnImage_le_one` shows the second
reading restricts nothing.
-/

namespace AISafetyAtlas.Examples.Inference.Halting

open AISafetyAtlas.Inference

/-- A device whose setup determines its conclusion: it halts at every setup. -/
public abbrev haltingDevice : InferenceDevice.{0, 0} Bool :=
  { Setup := Bool, setup := id, concl := id, concl_surjective := fun b => ⟨b, rfl⟩ }

/-- A device whose single setup value leaves both conclusions open: it halts
nowhere it is realized. -/
public abbrev stuckDevice : InferenceDevice.{0, 0} Bool :=
  { Setup := Unit, setup := fun _ => (), concl := id, concl_surjective := fun b => ⟨b, rfl⟩ }

theorem haltingDevice_recursive : Recursive haltingDevice := by
  rw [recursive_iff_refines]
  intro u u' h
  exact h

theorem stuckDevice_not_recursive : ¬ Recursive stuckDevice := by
  rw [recursive_iff_refines]
  intro h
  exact Bool.noConfusion (h true false rfl)

/-- A device whose setup takes the value `false` at no state: `false` is an
unrealized setup value, so Definition 8's vacuous clause has a genuine
instance to fire on. -/
public abbrev sparseDevice : InferenceDevice.{0, 0} Bool :=
  { Setup := Bool, setup := fun _ => true, concl := id,
    concl_surjective := fun b => ⟨b, rfl⟩ }

theorem sparseDevice_not_realized_false : ¬ sparseDevice.Realized false := by
  rintro ⟨u, hu⟩
  exact Bool.noConfusion hu

/-- Halting holds vacuously at the unrealized setup value. -/
theorem sparseDevice_haltsAt_false : HaltsAt sparseDevice false :=
  haltsAt_of_not_realized sparseDevice sparseDevice_not_realized_false

/-- The setup value of the stuck device is realized, so Definition 8's second
half is not satisfied vacuously. -/
theorem stuckDevice_realized : stuckDevice.Realized () := ⟨true, rfl⟩

/-- Halting is not an empty condition on the stuck device's own setup type: the
one realized value fails it. -/
theorem stuckDevice_not_haltsAt : ¬ HaltsAt stuckDevice () := by
  rintro ⟨y, hy⟩
  have h1 : (true : Bool) = y := hy true rfl
  have h2 : (false : Bool) = y := hy false rfl
  exact Bool.noConfusion (h1.trans h2.symm)

/-! ## The two readings of Definition 9, separated by a model

`sum_pushOnImage_le_one` proves the base-consistent reading is **automatic**:
it holds for every device, every halting set, and every measure of total mass at
most one. Clash 21 argues that the printed reading — `ℳ` in natural logarithm,
the exponent in base 2 — is a different condition. Until now nothing exhibited
the difference: no device in the tree was shown to satisfy `PrefixFree`, and
none was shown to fail it, so clash 21 rested entirely on the algebra of
`μ^{ln 2}` against `μ`.

`haltingDevice` under the uniform measure on `Bool` separates them. Each fibre
carries mass `1/2` and both setups halt, so:

* base-consistent: `1/2 + 1/2 = 1 ≤ 1`, satisfied;
* **as printed**: each summand is `(1/2)^{ln 2} > 1/2`, since `ln 2 < 1` and
  `(1/2)^·` is decreasing, so the sum exceeds `1` and the condition **fails**.

One device, one measure, opposite verdicts. Clash 21 is now a demonstration.
-/

/-- The uniform probability measure on `Bool`: each point carries mass `1/2`. -/
noncomputable def uniformBool : MeasureTheory.Measure Bool :=
  (2 : ENNReal)⁻¹ • MeasureTheory.Measure.count

instance : MeasureTheory.IsProbabilityMeasure uniformBool := by
  constructor
  simp [uniformBool, MeasureTheory.Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem uniformBool_singleton (b : Bool) : uniformBool {b} = 2⁻¹ := by
  simp [uniformBool]

/-- Every fibre of the identity setup carries mass `1/2`. -/
theorem massOn_haltingDevice (b : Bool) :
    massOn uniformBool haltingDevice.setup b = 1 / 2 := by
  have : (haltingDevice.setup ⁻¹' {b}) = {b} := rfl
  rw [massOn, this, uniformBool_singleton]
  norm_num

noncomputable instance : DecidablePred (HaltsAt haltingDevice) := fun _ => Classical.dec _

/-- The identity setup pins the conclusion, so every setup value halts. -/
theorem haltingDevice_haltsAt (b : Bool) : HaltsAt haltingDevice b :=
  ⟨b, fun _ hu => hu⟩

/-- Both setup values are realized and both halt, so the index of Definition 9's
sum is all of `Bool`. -/
theorem haltingSetups_haltingDevice : haltingSetups haltingDevice = Finset.univ := by
  ext b
  simp only [Finset.mem_univ, iff_true]
  exact (mem_haltingSetups_iff haltingDevice b).mpr ⟨⟨b, rfl⟩, haltingDevice_haltsAt b⟩

/-- **The base-consistent reading is satisfied**, with the sum exactly `1`. -/
theorem base2_sum_eq_one :
    (haltingSetups haltingDevice).sum
      (fun x => (2 : ℝ) ^ (-measureLengthBase2 uniformBool haltingDevice x)) = 1 := by
  rw [haltingSetups_haltingDevice]
  have h : ∀ b : Bool, (2 : ℝ) ^ (-measureLengthBase2 uniformBool haltingDevice b) = 1 / 2 := by
    intro b
    rw [two_rpow_neg_measureLengthBase2 uniformBool haltingDevice b
      (by rw [massOn_haltingDevice]; norm_num), massOn_haltingDevice]
  simp [h]

/-- **The printed reading fails on the same device and the same measure.** Each
summand is `(1/2)^{ln 2}`, and `ln 2 < 1` makes that strictly greater than
`1/2`, so the two of them exceed `1`. Clash 21's two readings are separated. -/
theorem not_prefixFree_haltingDevice : ¬ PrefixFree uniformBool haltingDevice := by
  rw [PrefixFree, haltingSetups_haltingDevice]
  have hpos : ∀ b : Bool, (0 : ℝ) < massOn uniformBool haltingDevice.setup b := by
    intro b; rw [massOn_haltingDevice]; norm_num
  have h : ∀ b : Bool, (2 : ℝ) ^ (-measureLength uniformBool haltingDevice b)
      = (1 / 2 : ℝ) ^ Real.log 2 := by
    intro b
    rw [two_rpow_neg_measureLength uniformBool haltingDevice b (hpos b), massOn_haltingDevice]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  have hgt : (1 / 2 : ℝ) < (1 / 2 : ℝ) ^ Real.log 2 := by
    have h1 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
      linarith
    calc (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := by norm_num
    _ < (1 / 2 : ℝ) ^ Real.log 2 :=
        Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) h1
  intro hle
  nlinarith [hgt]

/-- The uniform mass on `Bool`, as a `FinPMF`. -/
noncomputable def boolPmf : FinPMF Bool where
  mass := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by norm_num

/-- **Definition 9's `Finset` mass bound**, at the uniform mass and the halting
device: the two fibres' pushed-forward mass sums to exactly `1`, which is
`≤ 1`. -/
theorem boolPmf_sum_pushOnImage_le_one :
    (Finset.univ : Finset Bool).sum (fun x => pushOnImage boolPmf haltingDevice.setup x)
      ≤ 1 :=
  sum_pushOnImage_le_one boolPmf haltingDevice Finset.univ

/-- **The two readings of `PrefixFree` agree on a finite setup range.** The
base-consistent and printed readings disagree at `haltingDevice`
(`base2_sum_eq_one`/`not_prefixFree_haltingDevice`), but the *identification*
between the `Finset`- and measure-scoped versions of each reading holds
regardless. -/
theorem prefixFreeOn_iff_prefixFree_haltingDevice :
    PrefixFreeOn uniformBool haltingDevice ↔ PrefixFree uniformBool haltingDevice :=
  prefixFreeOn_iff_prefixFree uniformBool haltingDevice

end AISafetyAtlas.Examples.Inference.Halting
