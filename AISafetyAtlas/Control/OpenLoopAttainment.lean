module

public import AISafetyAtlas.Control.Purification
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Equation (48) is a maximum, not merely a supremum

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, eq. (48) and the sentence
below it.

The source writes

> `ΔH_open^max = max over p_X ∈ P, c ∈ C  ΔH_open`

with `P` *"the set of all probability distributions"* for the initial state, and
uses it as the right-hand side of Theorem 10. `AISafetyAtlas.Control.OpenLoop`
renders that object as `sSup` of the corresponding set and proves the set is
bounded, which is enough to *use*, but it is not the printed object: writing
`max` asserts that some input law and some action attain it, and `sSup ≥ max`
whenever both exist, so a bound stated against `sSup` is formally weaker than
the printed one.

This module supplies the missing assertion. The argument is the expected one and
the work is in the plumbing:

* a probability measure on a finite state space is a point of `stdSimplex ℝ S`,
  and every point of the simplex is one — `ofWeights` and `weights` are mutually
  inverse there;
* against that coordinate the reduction becomes `openLoopObjective`, an explicit
  finite sum of `Real.negMulLog`s, whose second argument is *linear* in the
  weights because running the kernel is;
* Mathlib's continuity of *negMulLog* makes it continuous, `isCompact_stdSimplex` makes
  the domain compact, and the action alphabet is finite, so the joint maximum is
  attained.

The conclusion is `isGreatest_kernelOpenLoopMax`: eq. (48)'s value belongs to the
set it is the supremum of. `kernelOpenLoopMax` may therefore be read as the
printed `max`.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uS uK uT

variable {S : Type uS} {K : Type uK} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
variable [Fintype S] [Fintype K] [Fintype T]

/-! ## Probability measures on a finite space are simplex points -/

/-- The weight vector of a measure on a finite space: its mass on each atom. -/
@[expose] public noncomputable def weights (ν : Measure S) : S → ℝ := fun x => ν.real {x}

/-- The measure with prescribed atom masses. -/
@[expose] public noncomputable def ofWeights (w : S → ℝ) : Measure S :=
  ∑ x : S, ENNReal.ofReal (w x) • Measure.dirac x

omit [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype K] [Fintype T] in
public theorem ofWeights_apply_singleton (w : S → ℝ) (_hw : ∀ x, 0 ≤ w x) (y : S) :
    ofWeights w {y} = ENNReal.ofReal (w y) := by
  classical
  rw [ofWeights, Measure.finsetSum_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro x _ hxy
    simp [Measure.dirac_apply' _ (MeasurableSet.singleton y), Set.indicator_of_notMem, hxy]
  · simp

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype K] [Fintype T] in
public theorem ofWeights_univ (w : S → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ofWeights w Set.univ = ENNReal.ofReal (∑ x, w x) := by
  classical
  rw [ofWeights, Measure.finsetSum_apply, ENNReal.ofReal_sum_of_nonneg (fun x _ => hw x)]
  simp

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype K] [Fintype T] in
public theorem isProbabilityMeasure_ofWeights {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) :
    IsProbabilityMeasure (ofWeights w) :=
  ⟨by rw [ofWeights_univ w hw.1, hw.2, ENNReal.ofReal_one]⟩

omit [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype K] [Fintype T] in
public theorem weights_ofWeights {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) :
    weights (ofWeights w) = w := by
  funext x
  rw [weights, measureReal_def, ofWeights_apply_singleton w hw.1 x, ENNReal.toReal_ofReal (hw.1 x)]

omit [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype K] [Fintype T] in
public theorem weights_mem_stdSimplex (ν : Measure S) [IsProbabilityMeasure ν] :
    weights ν ∈ stdSimplex ℝ S := by
  refine ⟨fun x => measureReal_nonneg, ?_⟩
  have hid : ∀ x : S, weights ν x = ν.real ((fun y : S => y) ⁻¹' {x}) := fun _ => rfl
  simp_rw [hid]
  rw [sum_measureReal_preimage_singleton _ fun x _ => MeasurableSet.singleton x]
  simp

omit [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype K] [Fintype T] in
public theorem ofWeights_weights (ν : Measure S) [IsProbabilityMeasure ν] :
    ofWeights (weights ν) = ν := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [ofWeights_apply_singleton _ (weights_mem_stdSimplex ν).1 x, weights, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top ν _)]

omit [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype K] [Fintype T] in
/-- **The entropy of a measure given by its atom masses.** -/
public theorem measureEntropy_ofWeights {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) :
    Hm[ofWeights w] = ∑ x, Real.negMulLog (w x) := by
  have := isProbabilityMeasure_ofWeights hw
  rw [measureEntropy_of_isProbabilityMeasure_finite (A := Finset.univ) (by simp)]
  exact Finset.sum_congr rfl fun x _ => by
    rw [show (ofWeights w).real {x} = w x from congrFun (weights_ofWeights hw) x]

/-! ## The objective in simplex coordinates -/

/--
**Eq. (48)'s objective, in coordinates.** `Hm[ν]` becomes a sum of `negMulLog`s
over the atoms, and the outcome law is *linear* in the weights because running the
kernel is: the mass the outcome puts on `t` is `∑ₓ w x · κ(x,c){t}`.
-/
@[expose] public noncomputable def openLoopObjective (κ : Kernel (S × K) T) (c : K)
    (w : S → ℝ) : ℝ :=
  (∑ x, Real.negMulLog (w x)) - ∑ t, Real.negMulLog (∑ x, w x * (κ (x, c)).real {t})

omit [MeasurableSingletonClass K] [Fintype K] [Fintype T] in
/-- Running the kernel on a weighted input law is a weighted average of its
columns. This is the linearity the continuity argument rests on. -/
public theorem comp_ofWeights_real (κ : Kernel (S × K) T) [IsMarkovKernel κ]
    {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) (c : K) (t : T) :
    (κ ∘ₘ ((ofWeights w).map fun x => (x, c))).real {t}
      = ∑ x, w x * (κ (x, c)).real {t} := by
  classical
  have hmk : Measurable (fun x : S => (x, c)) := measurable_id.prodMk measurable_const
  have hlint : (κ ∘ₘ ((ofWeights w).map fun x => (x, c))) {t}
      = ∑ x : S, ENNReal.ofReal (w x) * κ (x, c) {t} := by
    rw [Measure.bind_apply (MeasurableSet.singleton t) κ.aemeasurable,
      lintegral_map (κ.measurable_coe (MeasurableSet.singleton t)) hmk, ofWeights,
      lintegral_finsetSum_measure]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [measureReal_def, hlint, ENNReal.toReal_sum
    (fun x _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw.1 x), measureReal_def]

omit [MeasurableSingletonClass K] [Fintype K] in
/-- The coordinate objective is the printed reduction. -/
public theorem openLoopObjective_eq (κ : Kernel (S × K) T) [IsMarkovKernel κ] (c : K)
    {w : S → ℝ} (hw : w ∈ stdSimplex ℝ S) :
    openLoopObjective κ c w = kernelOpenLoopReductionAt κ (ofWeights w) c := by
  classical
  have := isProbabilityMeasure_ofWeights hw
  have : IsProbabilityMeasure (κ ∘ₘ ((ofWeights w).map fun x => (x, c))) := by
    have : IsProbabilityMeasure ((ofWeights w).map fun x => (x, c)) :=
      Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_const).aemeasurable
    infer_instance
  have hin : Hm[ofWeights w] = ∑ x, Real.negMulLog (w x) := measureEntropy_ofWeights hw
  have hout : Hm[κ ∘ₘ ((ofWeights w).map fun x => (x, c))]
      = ∑ t, Real.negMulLog (∑ x, w x * (κ (x, c)).real {t}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite (A := Finset.univ) (by simp)]
    exact Finset.sum_congr rfl fun t _ => by rw [comp_ofWeights_real κ hw c t]
  rw [openLoopObjective, kernelOpenLoopReductionAt, hin, hout]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype K] in
/-- Continuity: `negMulLog` is continuous and the inner sums are linear. -/
public theorem continuous_openLoopObjective (κ : Kernel (S × K) T) (c : K) :
    Continuous (openLoopObjective κ c) := by
  unfold openLoopObjective
  refine Continuous.sub (continuous_finsetSum _ fun x _ => ?_)
    (continuous_finsetSum _ fun t _ => ?_)
  · exact Real.continuous_negMulLog.comp (continuous_apply x)
  · refine Real.continuous_negMulLog.comp (continuous_finsetSum _ fun x _ => ?_)
    exact (continuous_apply x).mul continuous_const

/-! ## Eq. (48)'s maximum is attained -/

omit [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype K] in
/-- For a fixed action the reduction attains its maximum over input laws: the
simplex is compact and the objective is continuous on it. -/
public theorem exists_isMaxOn_openLoopObjective [Nonempty S] (κ : Kernel (S × K) T) (c : K) :
    ∃ w ∈ stdSimplex ℝ S, IsMaxOn (openLoopObjective κ c) (stdSimplex ℝ S) w := by
  have hne : (stdSimplex ℝ S).Nonempty :=
    ⟨weights (Measure.dirac (Classical.arbitrary S)), weights_mem_stdSimplex _⟩
  obtain ⟨w, hw, hmax⟩ := (isCompact_stdSimplex ℝ S).exists_isMaxOn hne
    (continuous_openLoopObjective κ c).continuousOn
  exact ⟨w, hw, hmax⟩

omit [MeasurableSingletonClass K] in
/--
**Eq. (48) is a maximum.** The value `kernelOpenLoopMax κ` belongs to the set of
reductions it is the supremum of, so the source's `max` is justified: some input
distribution and some action attain it.

With this, `kernelEntropyReduction_le_kernelOpenLoopMax` is Theorem 10 against the
printed right-hand side rather than against a supremum that merely bounds it.
-/
public theorem isGreatest_kernelOpenLoopMax [Nonempty S] [Nonempty K]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    IsGreatest (kernelOpenLoopReductions κ) (kernelOpenLoopMax κ) := by
  classical
  -- a best input law for each action, then a best action
  choose w hw hmax using fun c : K => exists_isMaxOn_openLoopObjective (S := S) κ c
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_max_image Finset.univ
    (fun c => openLoopObjective κ c (w c)) ⟨Classical.arbitrary K, Finset.mem_univ _⟩
  have hmem : openLoopObjective κ c₀ (w c₀) ∈ kernelOpenLoopReductions κ :=
    ⟨ofWeights (w c₀), isProbabilityMeasure_ofWeights (hw c₀), c₀,
      (openLoopObjective_eq κ c₀ (hw c₀)).symm⟩
  have hub : ∀ r ∈ kernelOpenLoopReductions κ, r ≤ openLoopObjective κ c₀ (w c₀) := by
    rintro _ ⟨ν, hν, c, rfl⟩
    have hνw : kernelOpenLoopReductionAt κ ν c = openLoopObjective κ c (weights ν) := by
      rw [openLoopObjective_eq κ c (weights_mem_stdSimplex ν), ofWeights_weights ν]
    rw [hνw]
    exact le_trans (hmax c (weights_mem_stdSimplex ν)) (hc₀ c (Finset.mem_univ _))
  have : IsGreatest (kernelOpenLoopReductions κ) (openLoopObjective κ c₀ (w c₀)) := ⟨hmem, hub⟩
  rw [kernelOpenLoopMax, this.csSup_eq]
  exact this

omit [MeasurableSingletonClass K] in
/-- The printed maximum, exhibited: an input law and an action realizing eq. (48). -/
public theorem exists_kernelOpenLoopReductionAt_eq_max [Nonempty S] [Nonempty K]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    ∃ (ν : Measure S), IsProbabilityMeasure ν ∧ ∃ c : K,
      kernelOpenLoopReductionAt κ ν c = kernelOpenLoopMax κ :=
  (isGreatest_kernelOpenLoopMax κ).1

/--
**Theorem 10 against the printed right-hand side.** The source's `ΔH_open^max` is
now an *attained* maximum, so Theorem 10 can be stated with the bound realized by
an explicit input distribution and an explicit action rather than by a supremum
that merely dominates the family.

This is the form eq. (48)'s `max` promises, and the reason the coverage audit
records no residual against Theorem 10.
-/
public theorem exists_kernelEntropyReduction_le_at_max [Nonempty S] [Nonempty K]
    (ρ : Measure (S × K)) [IsProbabilityMeasure ρ]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    ∃ (ν : Measure S), IsProbabilityMeasure ν ∧ ∃ c : K,
      kernelEntropyReduction ρ κ
        ≤ kernelOpenLoopReductionAt κ ν c + I[Prod.fst : Prod.snd ; ρ] := by
  obtain ⟨ν, hν, c, hattain⟩ := exists_kernelOpenLoopReductionAt_eq_max (S := S) κ
  exact ⟨ν, hν, c, hattain ▸ kernelEntropyReduction_le_kernelOpenLoopMax ρ κ⟩

end AISafetyAtlas.Control
