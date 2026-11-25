module

public import AISafetyAtlas.Inference

/-!
# Worked model: the entropy bound fails

Proposition 12 is refuted as printed, so what an example can add is the check that
the countermodel is genuinely inside the proposition's scope and that its two
sides are the real numbers claimed. The repaired form, `prop12_repaired`, is
instantiated at the end of this file by a uniform model that attains it.

`prop12_inside_scope` collects the printed hypotheses. `prop12_sides` records
both values. The rest is `prop12_refuted`.

The repaired statement, `prop12_repaired`, is inhabited by the same device and
target under uniform mass (`uniform_prop12_repaired`). There the complexity is
positive and the bound is attained.
-/

namespace AISafetyAtlas.Examples.Inference.EntropyBound

open AISafetyAtlas.Inference

/-- Every hypothesis Proposition 12 states, satisfied: a probability measure, a
target with finite image, and `D > Γ`. -/
theorem prop12_inside_scope :
    WeaklyInfers prop12Device prop12Gamma ∧ (rangeFinset prop12Gamma).card = 2 :=
  ⟨prop12_weaklyInfers, by rw [prop12_rangeFinset]; decide⟩

/-- Both sides, exactly. -/
theorem prop12_sides :
    inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
        prop12_weaklyInfers = 4 * Real.log 2 - Real.log 3 ∧
      entropyOn prop12Measure prop12X = 2 * Real.log 2 - 3 / 4 * Real.log 3 :=
  ⟨prop12_complexity, prop12_entropy⟩

/-- The two setup fibres carry `3/4` and `1/4`; the small one is what breaks the
printed proof's term-by-term comparison, which needs every fibre to carry at
least `1/|Γ|`. Here `1/|Γ| = 1/2` and one fibre carries `1/4`. -/
theorem prop12_small_fibre :
    massOn prop12Measure prop12X false = 1 / 4 ∧
      massOn prop12Measure prop12X false < 1 / (rangeFinset prop12Gamma).card := by
  refine ⟨prop12_mass_false, ?_⟩
  rw [prop12_mass_false, prop12_rangeFinset]
  norm_num

/-- **Proposition 12 is false as printed.** The inference complexity of the
witness device exceeds the entropy bound the proposition asserts, so the bound
cannot hold in general. Named here because a refutation with no application is
a refutation nothing consumes. -/
public theorem prop12_is_refuted :
    ¬ (inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
        prop12_weaklyInfers
      ≤ (rangeFinset prop12Gamma).card * entropyOn prop12Measure prop12X) :=
  prop12_refuted

/-! ## The repair, inhabited

The countermodel's device and target, with the mass spread evenly. Each fibre now
carries `1/2 = 1/|Γ|`, the identity is an injective answering selection, and
`AISafetyAtlas.Inference.prop12_repaired` applies. Both sides equal `2 ln 2`, so
the repaired bound is attained here, not only satisfied. -/

/-- Uniform masses on the four states. -/
public noncomputable def uniformPMF : FinPMF (Fin 4) where
  mass := fun _ => 1 / 4
  nonneg := by intro _; norm_num
  sum_one := by simp

public noncomputable def uniformMeasure : MeasureTheory.Measure (Fin 4) := uniformPMF.toMeasure

public instance : MeasureTheory.IsProbabilityMeasure uniformMeasure := by
  unfold uniformMeasure
  infer_instance

public theorem uniform_mass (x : Bool) : massOn uniformMeasure prop12X x = 1 / 2 := by
  rw [uniformMeasure, massOn_toMeasure]
  cases x <;> simp only [pushOnImage, uniformPMF] <;> rw [Finset.sum_filter, Fin.sum_univ_four] <;>
    simp <;> norm_num

/-- **The repair's hypothesis holds.** -/
public theorem uniform_heavyAnsweringSelection :
    HeavyAnsweringSelection uniformMeasure prop12Device prop12Gamma := by
  refine ⟨id, Set.injOn_id _, fun γ _ => ⟨?_, ?_⟩⟩
  · cases γ
    · rw [prop12_answering_false]; exact Finset.mem_singleton_self _
    · rw [prop12_answering_true]; exact Finset.mem_singleton_self _
  · rw [prop12_rangeFinset, show prop12Device.setup = prop12X from rfl, uniform_mass]
    norm_num

/-- **`C_μ(Γ; D) = 2 ln 2`**, positive. -/
public theorem uniform_complexity :
    inferenceComplexityMeasure uniformMeasure prop12Device prop12Gamma
      prop12_weaklyInfers = 2 * Real.log 2 := by
  rw [inferenceComplexityMeasure, inferenceComplexity_eq_total, inferenceComplexityTotal,
    prop12_rangeFinset]
  rw [show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide : (false : Bool) ≠ true)]
  unfold minAnsweringLength
  rw [prop12_answering_false, prop12_answering_true]
  simp only [Finset.singleton_nonempty, dif_pos, Finset.inf'_singleton]
  unfold measureLength
  rw [show prop12Device.setup = prop12X from rfl, uniform_mass, uniform_mass,
    Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

/-- **`|Γ| × H_μ(X) = 2 ln 2`.** -/
public theorem uniform_bound :
    (rangeFinset prop12Gamma).card * entropyOn uniformMeasure prop12X = 2 * Real.log 2 := by
  have hrange : rangeFinset prop12X = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
    cases x
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
  rw [prop12_rangeFinset]
  unfold entropyOn
  rw [hrange, show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide : (false : Bool) ≠ true), uniform_mass, uniform_mass,
    if_neg (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_one,
    Finset.card_pair (by decide : (false : Bool) ≠ true)]
  push_cast
  ring

/-- **The repaired Proposition 12, applied.** The hypothesis is met, the
complexity is positive, and the bound holds with equality. -/
public theorem uniform_prop12_repaired :
    0 < inferenceComplexityMeasure uniformMeasure prop12Device prop12Gamma
        prop12_weaklyInfers ∧
      inferenceComplexityMeasure uniformMeasure prop12Device prop12Gamma
          prop12_weaklyInfers
        ≤ (rangeFinset prop12Gamma).card * entropyOn uniformMeasure prop12Device.setup ∧
      inferenceComplexityMeasure uniformMeasure prop12Device prop12Gamma
          prop12_weaklyInfers
        = (rangeFinset prop12Gamma).card * entropyOn uniformMeasure prop12X := by
  refine ⟨?_, AISafetyAtlas.Inference.prop12_repaired uniformMeasure prop12Device prop12Gamma
    prop12_weaklyInfers uniform_heavyAnsweringSelection, ?_⟩
  · rw [uniform_complexity]
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  · rw [uniform_complexity, uniform_bound]

/-- **The printed proof's own shape, applied.** The uniform model has distinct
answering setups and every realized setup carries mass `1/2 = 1/|Γ(U)|`, so the
form of the repair that mirrors the printed chain applies too. -/
public theorem uniform_prop12_repaired_of_massBound :
    inferenceComplexityMeasure uniformMeasure prop12Device prop12Gamma
        prop12_weaklyInfers
      ≤ (rangeFinset prop12Gamma).card * entropyOn uniformMeasure prop12Device.setup := by
  obtain ⟨σ, hinj, hσ⟩ := uniform_heavyAnsweringSelection
  refine AISafetyAtlas.Inference.prop12_repaired_of_massBound uniformMeasure prop12Device
    prop12Gamma prop12_weaklyInfers ⟨σ, hinj, fun γ hγ => (hσ γ hγ).1⟩ ?_
  intro x _
  rw [prop12_rangeFinset, show prop12Device.setup = prop12X from rfl, uniform_mass]
  norm_num

/-- **The countermodel lacks only the mass half.** Its two probes are answered by
distinct setups, and it still fails the repair's hypothesis, because the small
fibre carries `1/4 < 1/2`. -/
public theorem countermodel_lacks_only_mass :
    (∃ σ : Bool → Bool, Set.InjOn σ (rangeFinset prop12Gamma : Set Bool) ∧
        ∀ γ ∈ rangeFinset prop12Gamma,
          σ γ ∈ answeringSet prop12Device prop12Gamma (probe γ)) ∧
      ¬ HeavyAnsweringSelection prop12Measure prop12Device prop12Gamma :=
  ⟨prop12_distinct_insufficient.1, prop12_not_heavyAnsweringSelection⟩

/-- **The collision model lacks only distinctness.** Every realized setup meets the
mass bound, no injective answering selection exists, and the printed bound fails. -/
public theorem collision_lacks_only_distinctness :
    (∀ x ∈ realizedSetups prop12CollideDevice,
        1 / ((rangeFinset prop12CollideGamma).card : ℝ) ≤
          massOn prop12CollideMeasure prop12CollideDevice.setup x) ∧
      (¬ ∃ σ : Fin 4 → Bool, Set.InjOn σ (rangeFinset prop12CollideGamma : Set (Fin 4)) ∧
        ∀ γ ∈ rangeFinset prop12CollideGamma,
          σ γ ∈ answeringSet prop12CollideDevice prop12CollideGamma (probe γ)) ∧
      ¬ (inferenceComplexityMeasure prop12CollideMeasure prop12CollideDevice
          prop12CollideGamma prop12Collide_weaklyInfers
        ≤ (rangeFinset prop12CollideGamma).card *
            entropyOn prop12CollideMeasure prop12CollideDevice.setup) :=
  ⟨prop12_massBound_insufficient.1, prop12Collide_not_injective_selection,
    prop12_massBound_insufficient.2⟩

/-- **Step 3's term comparison at the two fibres of the countermodel.** At mass
`1/2` with `|Γ| = 2` it holds; at the small fibre's `1/4` it fails, which is where
the printed chain breaks. -/
public theorem step3_term_at_half_and_quarter :
    -Real.log (1 / 2) / 2 ≤ -((1 / 2) * Real.log (1 / 2)) ∧
      ¬ (-Real.log (1 / 4) / 2 ≤ -((1 / 4) * Real.log (1 / 4))) := by
  refine ⟨(prop12_step3_term_iff (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num),
    fun h => ?_⟩
  have := (prop12_step3_term_iff (m := 1 / 4) (n := 2) (by norm_num) (by norm_num)
    (by norm_num)).1 h
  norm_num at this

end AISafetyAtlas.Examples.Inference.EntropyBound
