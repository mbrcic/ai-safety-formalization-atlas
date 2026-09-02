module

public import AISafetyAtlas.Control.InformationLimits

/-!
# The sensor side: observability and sensor loss

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, Theorems 5 and 6 and
Corollary 7.

Where `AISafetyAtlas.Control.InformationLimits` measures what an *actuator*
leaves undetermined, this module measures what a *sensor* loses. The paper calls
a system **perfectly observable** when the sensor "maps no two values of `X` to a
single observational output value `c`" — reading `c` pins the state down — and
defines the **sensor loss** `L_S = H(X|C)`, "the information loss … of the sensor
channel", by analogy with a lossless communication channel.

Three results follow.

* **Theorem 5** — perfectly observable iff `L_S = 0`. The source omits the proof
  ("readily follows from well-known properties of entropy"); it is supplied here,
  and the load-bearing step is `entropy_eq_zero_iff`: a finite-range variable has
  zero entropy exactly when some value carries all the mass.
* **Theorem 6** — `L_S = 0` implies `I(X ; Z | C) = 0`.
* **Corollary 7** — `L_S = 0` implies `I(X ; C, Z) = I(X ; C)`.

## What is *not* claimed

The paper is explicit that the observability side is not the controllability side
with symbols renamed: *"the fact that a communication channel is lossless has
nothing to do with the fact that it can be non-deterministic"*, so Theorem 2's
bound `L_C ≤ H(Z)` has **no** direct analogue `L_S ≤ H(Z)`. The paper repairs it
with a *backward* purification `L_S ≤ H(Z_B)`, stated in prose and left to the
reader. That repair is not formalized here.

The converse of Theorem 6 also fails, and the source says so: `I(X ; Z | C) = 0`
gives `H(X|C) = H(X|C,Z)` and no further, so it does not force `H(X|C) = 0`.
Only the stated direction is proved.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uΩ uS uK uN

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
variable [Countable S] [Countable K] [Countable N]
variable {μ : Measure Ω}

/-! ## Zero entropy means one value carries everything -/

omit [MeasurableSingletonClass K] [MeasurableSingletonClass N] [Countable S] [Countable K]
  [Countable N] in
/--
**A finite-range variable has zero entropy exactly when it is almost surely
constant.** The "well-known property of entropy" Theorem 5 is said to follow
from.

Both directions run through the finite sum `∑ₓ negMulLog p(x)`: every term is
nonnegative, so the sum vanishes iff every term does, and `negMulLog t = 0` on
`[0,1]` exactly at the endpoints. Masses summing to one then force exactly one
value to carry all of it.
-/
public theorem entropy_eq_zero_iff (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} (hX : Measurable X) [FiniteRange X] :
    H[X ; μ] = 0 ↔ ∃ x : S, μ (X ⁻¹' {x}) = 1 := by
  have hreal : ∀ x : S, (μ.map X).real {x} = μ.real (X ⁻¹' {x}) :=
    fun x => map_measureReal_apply hX (.singleton x)
  have hnn : ∀ x ∈ FiniteRange.toFinset X, 0 ≤ negMulLog ((μ.map X).real {x}) := fun x _ => by
    rw [hreal]
    exact negMulLog_nonneg measureReal_nonneg measureReal_le_one
  have htotal : ∑ x ∈ FiniteRange.toFinset X, μ.real (X ⁻¹' {x}) = 1 := by
    have := Measure.isProbabilityMeasure_map hX.aemeasurable (μ := μ)
    rw [sum_measureReal_preimage_singleton _ fun x _ => hX (.singleton x), measureReal_def,
      ← Measure.map_apply hX (Finset.measurableSet _),
      (prob_compl_eq_zero_iff (Finset.measurableSet _)).1 (full_measure_of_finiteRange hX),
      ENNReal.toReal_one]
  rw [entropy_eq_sum_finiteRange hX]
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
    -- every mass is 0 or 1, and they add to 1, so one of them carries everything
    have hbin : ∀ x ∈ FiniteRange.toFinset X,
        μ.real (X ⁻¹' {x}) = 0 ∨ μ.real (X ⁻¹' {x}) = 1 := fun x hx => by
      have hmul : μ.real (X ⁻¹' {x}) * Real.log (μ.real (X ⁻¹' {x})) = 0 := by
        simpa [negMulLog, hreal] using hz x hx
      rcases (measureReal_nonneg (μ := μ) (s := X ⁻¹' {x})).lt_or_eq with h0 | h0
      · exact Or.inr (Real.eq_one_of_pos_of_log_eq_zero h0
          ((mul_eq_zero.1 hmul).resolve_left h0.ne'))
      · exact Or.inl h0.symm
    obtain ⟨x, hx, hxne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [htotal]; exact one_ne_zero)
    refine ⟨x, (ENNReal.toReal_eq_one_iff _).1 ?_⟩
    rw [← measureReal_def]
    exact (hbin x hx).resolve_left hxne
  · rintro ⟨x₀, hx₀⟩
    have hx₀real : μ.real (X ⁻¹' {x₀}) = 1 := by
      rw [measureReal_def, hx₀, ENNReal.toReal_one]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hreal]
    by_cases hxx : x = x₀
    · rw [hxx, hx₀real, negMulLog_one]
    · have hzero : μ (X ⁻¹' {x}) = 0 := by
        refine measure_mono_null ?_ ((prob_compl_eq_zero_iff (hX (.singleton x₀))).2 hx₀)
        rw [← Set.preimage_compl]
        exact Set.preimage_mono (Set.singleton_subset_iff.2 hxx)
      rw [measureReal_def, hzero, ENNReal.toReal_zero, negMulLog_zero]

/-! ## Sensor loss and perfect observability -/

/-- **`L_S = H(X|C)`, the sensor loss.** What the state retains once the sensor
reading is known — "the information loss, or sensor loss, of the sensor channel"
in the source's words, by analogy with a lossless communication channel. -/
@[expose] public noncomputable def sensorLoss (μ : Measure Ω) (X : Ω → S) (C : Ω → K) : ℝ :=
  H[X | C ; μ]

/-- **Perfect observability.** Every reading the sensor can actually produce pins
the state down: on the event `C = c` some single state carries all the mass.

The source's phrasing is that the sensor "maps no two values of `X` to a single
observational output value `c`", equivalently that "for all `c ∈ C` there exists
only one value `x` such that `p(x|c) = 1`". Readings of probability zero are
excluded, matching the source's "with respect to all observed value
`c ∈ supp(C)`". -/
@[expose] public def PerfectlyObservable (μ : Measure Ω) (X : Ω → S) (C : Ω → K) : Prop :=
  ∀ c : K, μ (C ⁻¹' {c}) ≠ 0 → ∃ x : S, (μ[|C ⁻¹' {c}]) (X ⁻¹' {x}) = 1

omit [MeasurableSingletonClass N] [Countable S] [Countable K] [Countable N] in
/--
**Theorem 5.** A system is perfectly observable exactly when its sensor loss
vanishes.

The source states this and omits the proof. It decomposes `H(X|C)` over the
sensor's readings: the sum of nonnegative terms is zero exactly when each
positively-weighted reading has zero conditional entropy, which by
`entropy_eq_zero_iff` is exactly one state carrying that reading's mass.
-/
public theorem perfectlyObservable_iff_sensorLoss_eq_zero (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → S} {C : Ω → K} (hX : Measurable X) (hC : Measurable C)
    [FiniteRange X] [FiniteRange C] :
    PerfectlyObservable μ X C ↔ sensorLoss μ X C = 0 := by
  have hmem : ∀ c : K, μ (C ⁻¹' {c}) ≠ 0 → c ∈ FiniteRange.toFinset C := fun c hc => by
    by_contra hcon
    refine hc ?_
    rw [Set.preimage_singleton_eq_empty.2 fun ⟨ω, hω⟩ => hcon (hω ▸ FiniteRange.mem C ω),
      measure_empty]
  have hnn : ∀ c ∈ FiniteRange.toFinset C,
      0 ≤ ((μ.map C).real {c}) * H[X | C ← c ; μ] :=
    fun c _ => mul_nonneg measureReal_nonneg (entropy_nonneg _ _)
  rw [sensorLoss, condEntropy_eq_sum _ _ _ hC]
  constructor
  · intro hobs
    refine Finset.sum_eq_zero fun c hc => ?_
    by_cases hcm : μ (C ⁻¹' {c}) = 0
    · simp [map_measureReal_apply hC (.singleton c), measureReal_def, hcm]
    · have : IsProbabilityMeasure (μ[|C ⁻¹' {c}]) := cond_isProbabilityMeasure hcm
      rw [(entropy_eq_zero_iff _ hX).2 (hobs c hcm), mul_zero]
  · intro hsum c hc
    have : IsProbabilityMeasure (μ[|C ⁻¹' {c}]) := cond_isProbabilityMeasure hc
    refine (entropy_eq_zero_iff _ hX).1 ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum c (hmem c hc)
    rcases mul_eq_zero.1 hz with h0 | h0
    · exact absurd ((measureReal_eq_zero_iff (measure_ne_top _ _)).1
        (by rwa [map_measureReal_apply hC (.singleton c)] at h0)) hc
    · exact h0

/-! ## Theorem 6 and Corollary 7 -/

/--
**Theorem 6.** If the state is perfectly observable then the sensor's
purification noise tells you nothing more about it: `I(X ; Z | C) = 0`.

The source's three-line proof, mechanized: `H(X|C) ≥ H(X|C,Z) ≥ 0`, so a
vanishing sensor loss squeezes both, and the conditional mutual information is
their difference.
-/
public theorem condMutualInfo_eq_zero_of_sensorLoss_eq_zero (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange Z]
    (hobs : sensorLoss μ X C = 0) :
    I[X : Z | C ; μ] = 0 := by
  rw [sensorLoss] at hobs
  have hzero : H[X | ⟨Z, C⟩ ; μ] = 0 :=
    le_antisymm (hobs ▸ entropy_submodular (μ := μ) hX hZ hC) (condEntropy_nonneg _ _ _)
  rw [condMutualInfo_eq' hX hZ hC μ, hobs, hzero, sub_zero]

/--
**Corollary 7.** If the sensor loses nothing, the noise adds nothing:
`I(X ; C, Z) = I(X ; C)`.

Both mutual informations are `H(X)` minus a conditional entropy, and a vanishing
sensor loss makes both conditional entropies zero.
-/
public theorem mutualInfo_prod_eq_of_sensorLoss_eq_zero (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange Z]
    (hobs : sensorLoss μ X C = 0) :
    I[X : ⟨C, Z⟩ ; μ] = I[X : C ; μ] := by
  rw [sensorLoss] at hobs
  have hzero : H[X | ⟨Z, C⟩ ; μ] = 0 :=
    le_antisymm (hobs ▸ entropy_submodular (μ := μ) hX hZ hC) (condEntropy_nonneg _ _ _)
  have hswap : H[X | ⟨C, Z⟩ ; μ] = H[X | ⟨Z, C⟩ ; μ] :=
    condEntropy_of_injective' μ hX (hZ.prodMk hC) Prod.swap Prod.swap_injective
      (measurable_swap.comp (hZ.prodMk hC))
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hC.prodMk hZ) μ,
    mutualInfo_eq_entropy_sub_condEntropy hX hC μ, hswap, hzero, hobs]

end AISafetyAtlas.Control
