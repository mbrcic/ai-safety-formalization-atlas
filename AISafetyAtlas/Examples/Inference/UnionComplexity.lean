module

public import AISafetyAtlas.Inference

/-!
# Worked model: the probe that two setups answer

Both papers introduce `Ĉ` as *"a natural modification"* of Definition 6 — remove
the `min`, and charge the union of **all** the setups that answer a probe rather
than the cheapest one. Neither paper gives an instance where that changes
anything, and if every answering set were a singleton it would not.

Here is one where it is not. Four states, two setups splitting them evenly, and a
target equal to the device's own conclusion. Then **both** setups answer the
probe of `true`: the first fibre concludes `true` where the probe wants `true`,
and the second concludes `false` where the probe wants `false`.

Under any measure giving the two fibres equal positive mass, `Ĉ` would charge
`−ln 1 = 0` for that probe against the `min` form's `−ln(1/2) = ln 2`. **No
measure appears in this module and neither number is proved here** — what is
proved is the combinatorial fact those numbers rest on, that the answering set
has two elements rather than one. `Ĉ` and Definition 6 coincide exactly when
every answering set is a singleton, and here one is not.

Consistency check, because the model looks like it should be impossible:
Proposition 1(ii) says no device weakly infers its own conclusion, and this
device does not. The **other** probe, of `false`, is answered by neither setup —
`uc_no_setup_answers_false`. Weak inference needs every probe answered, so the
two facts sit together.
-/

namespace AISafetyAtlas.Examples.Inference.UnionComplexity

open AISafetyAtlas.Inference

/-- Two setups, each carrying two of the four states. -/
public abbrev ucSetup : Fin 4 → Bool := ![false, false, true, true]

/-- The conclusion: `true` on the first fibre, `false` on the second. Surjective,
as Definition 1 requires. -/
public abbrev ucConcl : Fin 4 → Bool := ![true, true, false, false]

/-- The device of the model. -/
public abbrev ucDevice : InferenceDevice.{0, 0} (Fin 4) where
  Setup := Bool
  setup := ucSetup
  concl := ucConcl
  concl_surjective := by decide

/-- The target is the device's own conclusion. -/
public abbrev ucGamma : Fin 4 → Bool := ucConcl

/-- **Both** setups answer the probe of `true`. This is what makes `Ĉ` differ
from Definition 6 here: the answering set is not a singleton. -/
public theorem uc_both_setups_answer_true :
    ∀ x : Bool, x ∈ answeringSet ucDevice ucGamma (probe true) := by
  intro x
  rw [mem_answeringSet_iff]
  revert x
  unfold InferenceDevice.Realized
  decide

/-- So the answering set is everything, and has two elements where Definition 6
would have taken a `min` over one. -/
public theorem uc_answeringSet_true_card :
    (answeringSet ucDevice ucGamma (probe true)).card = 2 := by
  have h : answeringSet ucDevice ucGamma (probe true) = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr uc_both_setups_answer_true
  rw [h]
  decide

/-- The probe of `false` is answered by **no** setup, which is why the device does
not weakly infer its own conclusion — Proposition 1(ii) is not contradicted. -/
public theorem uc_no_setup_answers_false :
    ∀ x : Bool, x ∉ answeringSet ucDevice ucGamma (probe false) := by
  intro x
  rw [mem_answeringSet_iff]
  revert x
  unfold InferenceDevice.Realized
  decide

/-- Proposition 1(ii) on this device, from the library rather than by hand. -/
public theorem uc_not_weaklyInfers_own_concl :
    ¬ WeaklyInfers ucDevice ucDevice.concl :=
  not_weaklyInfers_own_concl ucDevice

/-! ## The two numbers, now proved

The header above named `0` and `ln 2` and declined to prove either, because no
measure appeared in this module. That made `Ĉ` a definition the tree never
evaluated — it could not have been vacuous, but it could have been quietly
wrong, and the 2008 map's own standard for the section-5 layer is a computed
value, not a compiled definition.

Under the uniform measure on `Fin 4` each fibre carries mass `1/2`, so:

* the **min** form charges `−ln(1/2) = ln 2` for the probe of `true`, since every
  answering setup has fibre mass `1/2`;
* `Ĉ` charges `−ln 1 = 0`, because the union of *all* the answering fibres is the
  whole space.

`ln 2 > 0`, so the *"natural modification"* genuinely modifies. Definition 6 and
`Ĉ` agree exactly when every answering set is a singleton, and this is a model
where one is not.
-/

/-- The uniform probability measure on the four states. -/
public noncomputable def uc4 : MeasureTheory.Measure (Fin 4) :=
  (4 : ENNReal)⁻¹ • MeasureTheory.Measure.count

public instance : MeasureTheory.IsProbabilityMeasure uc4 := by
  constructor
  simp [uc4, MeasureTheory.Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Every fibre of the setup map carries half the mass. -/
public theorem uc_massOn (x : Bool) : massOn uc4 ucDevice.setup x = 1 / 2 := by
  have h : (ucDevice.setup ⁻¹' {x}) = if x then {2, 3} else {0, 1} := by
    ext u; fin_cases u <;> cases x <;> simp [ucDevice, ucSetup]
  rw [massOn, h]
  cases x <;>
    simp [uc4, MeasureTheory.Measure.count_apply_finite] <;>
    norm_num

/-- **The min form's charge: `ln 2`.** Each answering setup costs `−ln(1/2)`. -/
public theorem uc_measureLength (x : Bool) :
    measureLength uc4 ucDevice x = Real.log 2 := by
  rw [measureLength, uc_massOn]
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]

/-- The answering fibres of the probe of `true` cover the whole space. -/
public theorem uc_union_true :
    (⋃ x ∈ answeringSet ucDevice ucGamma (probe true), ucDevice.setup ⁻¹' {x})
      = Set.univ := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_preimage,
    Set.mem_singleton_iff]
  exact ⟨ucDevice.setup u, uc_both_setups_answer_true _, rfl⟩

/-- **`Ĉ`'s charge: `0`.** The union of all answering fibres has full mass. -/
public theorem uc_answeringMass_true :
    answeringMass uc4 ucDevice ucGamma (probe true) = 1 := by
  rw [answeringMass, uc_union_true]
  simp

/-- **The separation, as one inequality.** `Ĉ` charges strictly less than the
`min` form for this probe, so the modification is not cosmetic. -/
public theorem uc_union_lt_min :
    -Real.log (answeringMass uc4 ucDevice ucGamma (probe true))
      < measureLength uc4 ucDevice false := by
  rw [uc_answeringMass_true, uc_measureLength, Real.log_one, neg_zero]
  exact Real.log_pos (by norm_num)

end AISafetyAtlas.Examples.Inference.UnionComplexity
