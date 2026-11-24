module

public import AISafetyAtlas.InformationTheory.DataProcessing

/-!
# Data processing at countable alphabets of finite entropy

Cover & Thomas, Theorem 2.10.1 (PDF p. 64), second inequality of (2.130): for
any estimator with X → Y → X̂, the conditional entropy of X given the
estimate is at least its conditional entropy given the observation. The proof
in print (PDF p. 65) is one appeal to data processing and never uses the size
of the alphabet of X; Chapter 2's random variables are discrete with countable
alphabets (Problem 2.1 is a geometric flip count).

`condEntropy_le_condEntropy_of_isMarkovChain_countable` in
AISafetyAtlas.InformationTheory.DataProcessing already lets the observation
and the estimate take countably many values, but keeps `FiniteRange` on X.
This module replaces that by finite entropy of X: summability of the
`negMulLog` of its probability mass function, which is exactly the statement
that the series defining the entropy of X converges. PFR's entropy is a
`tsum` and returns the junk value 0 on a divergent series, so the hypothesis
is what makes the entropy of X a genuine sum; the lemmas below show that the
two conditional entropies are then genuine weighted sums of genuine fibre sums
(`summable_negMulLog_cond`, `hasSum_condEntropy_of_summable`). PFR has a
`ProbabilityTheory.FiniteEntropy` predicate with the same content, with no API around it.

The only new mathematics is a countable Gibbs-type bound,
`tsum_mul_negMulLog_cond_le_entropy`: the joint series of the weighted fibre
terms over pairs of values is summable with sum at most the entropy of X. A
single fibre entropy is not bounded by the entropy of X (a rare fibre can
carry more), so the bound is on the weighted series. It is proved by
truncating X to finitely many values, which brings back the finite-range
lemmas of AISafetyAtlas.InformationTheory.DataProcessing, and by
`entropy_comp_le_of_summable`, the countable form of "a function of X has at
most the entropy of X" (PFR's `entropy_comp_le` needs `FiniteRange`). The
rest repeats the countable-conditioner chain of that module with this
hypothesis in place of `FiniteRange`.
-/

namespace AISafetyAtlas.InformationTheory

open MeasureTheory ProbabilityTheory Real Function

universe uΩ uS uT uU

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
variable [Countable S] [Countable T] [Countable U]
variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- Countable subadditivity of `negMulLog` on a summable nonnegative family:
lumping the masses of a countable family together does not raise its
`negMulLog` sum. -/
public theorem negMulLog_tsum_le {ι : Type*} {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (hp : Summable p)
    (hq : Summable fun i => negMulLog (p i)) :
    negMulLog (∑' i, p i) ≤ ∑' i, negMulLog (p i) := by
  have hP : negMulLog (∑' i, p i) = ∑' i, p i * (-log (∑' i, p i)) := by
    rw [hp.tsum_mul_right, negMulLog]
    ring
  rw [hP]
  refine (hp.mul_right _).tsum_le_tsum (fun i => ?_) hq
  rcases (h0 i).eq_or_lt with h | h
  · simp [← h]
  · rw [negMulLog, neg_mul, ← mul_neg]
    exact mul_le_mul_of_nonneg_left
      (neg_le_neg (log_le_log h (hp.le_tsum i fun j _ => h0 j))) h.le

omit [MeasurableSingletonClass S] [Countable S] in
/-- The entropy of a variable as the series of its probability mass function,
for a probability (or zero) measure. -/
public theorem entropy_eq_tsum [IsZeroOrProbabilityMeasure μ] (X : Ω → S) :
    H[X ; μ] = ∑' x, negMulLog ((μ.map X).real {x}) := by
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]

omit [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [MeasurableSingletonClass U]
  [Countable U] in
/-- The probability mass function of a countable-valued variable is summable. -/
public theorem summable_measureReal_map_singleton [IsFiniteMeasure μ] (X : Ω → S) :
    Summable fun x => (μ.map X).real {x} := by
  have h : ∑' x, (μ.map X) {x} = (μ.map X) Set.univ := by
    simpa using Measure.tsum_indicator_apply_singleton (μ.map X) Set.univ MeasurableSet.univ
  exact ENNReal.summable_toReal (h ▸ measure_ne_top _ _)

omit [Countable S] [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  [MeasurableSingletonClass U] [Countable U] in
/-- A finite-range variable has finite entropy, so the hypothesis used below
is implied by the `FiniteRange` of AISafetyAtlas.InformationTheory.DataProcessing. -/
public theorem summable_negMulLog_of_finiteRange (hX : Measurable X) [FiniteRange X] :
    Summable fun x => negMulLog ((μ.map X).real {x}) := by
  refine summable_of_ne_finset_zero (s := FiniteRange.toFinset X) fun x hx => ?_
  have : X ⁻¹' {x} = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hx (FiniteRange.mem X ω)
  rw [map_measureReal_apply hX (.singleton _), this]
  simp

omit [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Countable U] in
/--
**A function of a variable has at most its entropy, at a countable alphabet of
finite entropy**: the inequality of Cover & Thomas, Problem 2.4, for a discrete X
whose entropy series converges, and any f.

PFR's `entropy_comp_le` needs FiniteRange X. Here each value of f ∘ X
lumps a countable fibre of values of X, and `negMulLog_tsum_le` bounds each
lump by the fibre's share of the entropy series of X.
-/
public theorem entropy_comp_le_of_summable [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) (f : S → U) :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  set p : S → ℝ := fun x => (μ.map X).real {x} with hp_def
  have hp0 : ∀ x, 0 ≤ p x := fun _ => measureReal_nonneg
  have hpsum : Summable p := summable_measureReal_map_singleton X
  have hfX : Measurable (f ∘ X) := (Measurable.of_discrete (f := f)).comp hX
  have hq : ∀ u, (μ.map (f ∘ X)).real {u} = ∑' x : f ⁻¹' {u}, p x := by
    intro u
    rw [map_measureReal_apply hfX (.singleton u), Set.preimage_comp, measureReal_def,
      ← tsum_measure_preimage_singleton (Set.to_countable _) (fun y _ => hX (.singleton y)),
      ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
    simp only [hp_def, map_measureReal_apply hX (.singleton _), measureReal_def]
  have hfib := hH.hasSum.tsum_fiberwise f
  have hle : ∀ u, negMulLog ((μ.map (f ∘ X)).real {u}) ≤ ∑' x : f ⁻¹' {u}, negMulLog (p x) :=
    fun u => by
      rw [hq u]
      exact negMulLog_tsum_le (fun _ => hp0 _) (hpsum.subtype _) (hH.subtype _)
  rw [entropy_eq_tsum, entropy_eq_tsum, ← hfib.tsum_eq]
  refine Summable.tsum_le_tsum hle ?_ hfib.summable
  exact Summable.of_nonneg_of_le (fun u => negMulLog_nonneg measureReal_nonneg measureReal_le_one)
    hle hfib.summable

omit [MeasurableSingletonClass U] [Countable U] in
/-- The box form of the countable Gibbs bound: over finitely many values y of
the conditioner and x of X, the weighted fibre terms sum to at most the
entropy of X. Proved by truncating X to the finite set of values. -/
public theorem sum_sum_mul_negMulLog_cond_le_entropy [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) (F : Finset T) (G : Finset S) :
    ∑ y ∈ F, ∑ x ∈ G, (μ.map Y).real {y} * negMulLog ((μ[|Y ⁻¹' {y}].map X).real {x})
      ≤ H[X ; μ] := by
  classical
  let : MeasurableSpace (Option S) := ⊤
  have : DiscreteMeasurableSpace (Option S) := ⟨fun _ => trivial⟩
  set g : S → Option S := fun x => if x ∈ G then some x else none with hg
  have hgX : Measurable (g ∘ X) := (Measurable.of_discrete (f := g)).comp hX
  have : FiniteRange (g ∘ X) :=
    ⟨((insert none (G.image some) : Finset (Option S)).finite_toSet).subset (by
      rintro _ ⟨ω, rfl⟩
      by_cases h : X ω ∈ G <;> simp [hg, h])⟩
  have hpre : ∀ x ∈ G, (g ∘ X) ⁻¹' {some x} = X ⁻¹' {x} := by
    intro x hx
    ext ω
    by_cases h : X ω ∈ G
    · simp [hg, h]
    · simp only [Set.mem_preimage, Function.comp_apply, hg, h, if_false, Set.mem_singleton_iff,
        reduceCtorEq, false_iff]
      rintro rfl
      exact h hx
  have hfib : ∀ y, ∑ x ∈ G, negMulLog ((μ[|Y ⁻¹' {y}].map X).real {x})
      ≤ H[g ∘ X ; μ[|Y ⁻¹' {y}]] := by
    intro y
    set ν := μ[|Y ⁻¹' {y}]
    rw [entropy_eq_tsum]
    have hs : Summable fun v => negMulLog ((ν.map (g ∘ X)).real {v}) := by
      refine summable_of_ne_finset_zero (s := insert none (G.image some)) fun v hv => ?_
      rcases v with _ | x
      · simp at hv
      · have hx : x ∉ G := by simpa using hv
        have hempty : (g ∘ X) ⁻¹' {some x} = ∅ := by
          ext ω
          by_cases h : X ω ∈ G
          · simp only [Set.mem_preimage, Function.comp_apply, hg, h, if_true,
              Set.mem_singleton_iff, Option.some.injEq, Set.mem_empty_iff_false, iff_false]
            rintro rfl
            exact hx h
          · simp [hg, h]
        rw [map_measureReal_apply hgX (.singleton _), hempty]
        simp
    calc ∑ x ∈ G, negMulLog ((ν.map X).real {x})
        = ∑ v ∈ G.map ⟨some, Option.some_injective _⟩, negMulLog ((ν.map (g ∘ X)).real {v}) := by
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun x hx => ?_
          simp only [Function.Embedding.coeFn_mk]
          rw [map_measureReal_apply hgX (.singleton _), map_measureReal_apply hX (.singleton _),
            hpre x hx]
      _ ≤ _ := hs.sum_le_tsum _ fun _ _ => negMulLog_nonneg measureReal_nonneg measureReal_le_one
  have hs := hasSum_condEntropy (μ := μ) hgX Y
  calc ∑ y ∈ F, ∑ x ∈ G, (μ.map Y).real {y} * negMulLog ((μ[|Y ⁻¹' {y}].map X).real {x})
      = ∑ y ∈ F, (μ.map Y).real {y} * ∑ x ∈ G, negMulLog ((μ[|Y ⁻¹' {y}].map X).real {x}) := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ y ∈ F, (μ.map Y).real {y} * H[g ∘ X | Y ← y ; μ] :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfib y) measureReal_nonneg
    _ ≤ ∑' y, (μ.map Y).real {y} * H[g ∘ X | Y ← y ; μ] :=
        hs.summable.sum_le_tsum _ fun _ _ => mul_nonneg measureReal_nonneg (entropy_nonneg _ _)
    _ = H[g ∘ X | Y ; μ] := hs.tsum_eq
    _ ≤ H[g ∘ X ; μ] := condEntropy_le_entropy_countable hgX hY
    _ ≤ H[X ; μ] := entropy_comp_le_of_summable hX hH g

omit [MeasurableSingletonClass U] [Countable U] in
/-- **The countable Gibbs bound, joint form**: at a variable X of finite
entropy and any countable-valued conditioner Y, the weighted fibre terms are
summable over pairs of values. This is the integrability that makes every
conditional entropy of X below a genuine sum. -/
public theorem summable_mul_negMulLog_cond [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hH : Summable fun x => negMulLog ((μ.map X).real {x})) :
    Summable fun q : T × S =>
      (μ.map Y).real {q.1} * negMulLog ((μ[|Y ⁻¹' {q.1}].map X).real {q.2}) := by
  classical
  refine summable_of_sum_le (c := H[X ; μ])
    (fun q => mul_nonneg measureReal_nonneg (negMulLog_nonneg measureReal_nonneg
      measureReal_le_one)) fun u => ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := u.image Prod.fst ×ˢ u.image Prod.snd)
    (fun q hq => Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq,
      Finset.mem_image_of_mem _ hq⟩)
    fun q _ _ => mul_nonneg measureReal_nonneg (negMulLog_nonneg measureReal_nonneg
      measureReal_le_one)) ?_
  rw [Finset.sum_product]
  exact sum_sum_mul_negMulLog_cond_le_entropy hX hY hH _ _

omit [MeasurableSingletonClass U] [Countable U] in
/-- **The countable Gibbs bound**: the joint series of weighted fibre terms sums
to at most the entropy of X. -/
public theorem tsum_mul_negMulLog_cond_le_entropy [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) :
    ∑' q : T × S, (μ.map Y).real {q.1} * negMulLog ((μ[|Y ⁻¹' {q.1}].map X).real {q.2})
      ≤ H[X ; μ] := by
  classical
  refine (summable_mul_negMulLog_cond hX hY hH).tsum_le_of_sum_le fun u => ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := u.image Prod.fst ×ˢ u.image Prod.snd)
    (fun q hq => Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq,
      Finset.mem_image_of_mem _ hq⟩)
    fun q _ _ => mul_nonneg measureReal_nonneg (negMulLog_nonneg measureReal_nonneg
      measureReal_le_one)) ?_
  rw [Finset.sum_product]
  exact sum_sum_mul_negMulLog_cond_le_entropy hX hY hH _ _

omit [MeasurableSingletonClass U] [Countable U] in
/-- **Finite entropy survives conditioning on a fibre**: if X has finite
entropy under μ, it has finite entropy under μ conditioned on Y = y, for
every value y of a countable-valued Y. So every fibre entropy is a genuine
sum. -/
public theorem summable_negMulLog_cond [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hH : Summable fun x => negMulLog ((μ.map X).real {x})) (y : T) :
    Summable fun x => negMulLog ((μ[|Y ⁻¹' {y}].map X).real {x}) := by
  rcases eq_or_ne ((μ.map Y).real {y}) 0 with h | h
  · rw [map_measureReal_apply hY (.singleton _),
      measureReal_eq_zero_iff (measure_ne_top _ _)] at h
    rw [cond_eq_zero_of_meas_eq_zero h]
    simp
  · exact (summable_mul_left_iff h).mp ((summable_mul_negMulLog_cond hX hY hH).prod_factor y)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T]
  [MeasurableSingletonClass U] [Countable U] in
/-- A fibre term of a conditional entropy, as the series of its weighted fibre
terms. -/
private theorem mul_entropy_cond_eq_tsum [IsZeroOrProbabilityMeasure μ] (y : T) :
    (μ.map Y).real {y} * H[X | Y ← y ; μ]
      = ∑' x, (μ.map Y).real {y} * negMulLog ((μ[|Y ⁻¹' {y}].map X).real {x}) := by
  rw [entropy_eq_tsum, tsum_mul_left]

omit [MeasurableSingletonClass U] [Countable U] in
/--
**Conditional entropy as a countable sum, at a variable of finite entropy**: the
printed definition H(X|Y) = ∑_y p(y) H(X|Y = y) (Cover & Thomas (2.10), PDF
p. 43) for countable-valued X and Y, with only the entropy series of X
assumed convergent.

`hasSum_condEntropy` in AISafetyAtlas.InformationTheory.DataProcessing needs
FiniteRange X. PFR's conditional entropy is a Bochner integral that returns
0 on a non-integrable integrand; `summable_mul_negMulLog_cond` is what makes
this one integrable, so the value here is the genuine sum.
-/
public theorem hasSum_condEntropy_of_summable [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hH : Summable fun x => negMulLog ((μ.map X).real {x})) :
    HasSum (fun y => (μ.map Y).real {y} * H[X | Y ← y ; μ]) H[X | Y ; μ] := by
  have hsum : Summable fun y => (μ.map Y).real {y} * H[X | Y ← y ; μ] := by
    simp only [mul_entropy_cond_eq_tsum]
    exact (summable_mul_negMulLog_cond hX hY hH).prod
  have hint : Integrable (fun y => H[X | Y ← y ; μ]) (μ.map Y) := by
    have h := integrable_sum_dirac (f := fun y => H[X | Y ← y ; μ]) (x := fun y : T => y)
      (c := fun y => (μ.map Y) {y}) (fun _ => measure_ne_top _ _) (by
        simpa [Real.norm_eq_abs, abs_of_nonneg (entropy_nonneg _ _), measureReal_def] using hsum)
    rwa [Measure.sum_smul_dirac] at h
  have h := hasSum_integral_measure (μ := fun y : T => (μ.map Y) {y} • Measure.dirac y)
    (f := fun y => H[X | Y ← y ; μ]) (by rwa [Measure.sum_smul_dirac])
  rw [Measure.sum_smul_dirac] at h
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul] at h
  exact h

omit [MeasurableSingletonClass U] [Countable U] in
/-- **Conditioning reduces entropy, at countable alphabets of finite entropy**:
Cover & Thomas, Theorem 2.6.5, for countable-valued X and Y with only the
entropy series of X assumed convergent. `condEntropy_le_entropy_countable`
needs FiniteRange X. -/
public theorem condEntropy_le_entropy_of_summable [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) :
    H[X | Y ; μ] ≤ H[X ; μ] := by
  have hJ := summable_mul_negMulLog_cond hX hY hH
  have hrow := hJ.hasSum.prod_fiberwise fun y => (hJ.prod_factor y).hasSum
  rw [← (hasSum_condEntropy_of_summable hX hY hH).tsum_eq]
  simp only [mul_entropy_cond_eq_tsum]
  rw [hrow.tsum_eq]
  exact tsum_mul_negMulLog_cond_le_entropy hX hY hH

/-- **Conditioning on a pair, fibred over its first component**, at a variable
of finite entropy; `hasSum_condEntropy_pair` needs FiniteRange X. -/
public theorem hasSum_condEntropy_pair_of_summable [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) :
    HasSum (fun y => μ.real (Y ⁻¹' {y}) * H[X | Z ; μ[|Y ⁻¹' {y}]]) H[X | ⟨Y, Z⟩ ; μ] := by
  have hs := hasSum_condEntropy_of_summable (μ := μ) hX (hY.prodMk hZ) hH
  refine hs.prod_fiberwise fun y => ?_
  have hy := (hasSum_condEntropy_of_summable (μ := μ[|Y ⁻¹' {y}]) hX hZ
    (summable_negMulLog_cond hX hY hH y)).mul_left (μ.real (Y ⁻¹' {y}))
  have hterm : ∀ z, (μ.map (fun ω => (Y ω, Z ω))).real {(y, z)}
        * H[X | (fun ω => (Y ω, Z ω)) ← (y, z) ; μ]
      = μ.real (Y ⁻¹' {y}) * ((μ[|Y ⁻¹' {y}].map Z).real {z} * H[X | Z ← z ; μ[|Y ⁻¹' {y}]]) := by
    intro z
    have hpre : (fun ω => (Y ω, Z ω)) ⁻¹' {(y, z)} = Y ⁻¹' {y} ∩ Z ⁻¹' {z} := by
      ext ω; simp
    rw [map_measureReal_apply (hY.prodMk hZ) (.singleton _),
      map_measureReal_apply hZ (.singleton _), hpre,
      cond_cond_eq_cond_inter (hY (.singleton y)) (hZ (.singleton z)),
      cond_real_apply (hY (.singleton y))]
    rcases eq_or_ne (μ.real (Y ⁻¹' {y})) 0 with h | h
    · have : μ.real (Y ⁻¹' {y} ∩ Z ⁻¹' {z}) = 0 :=
        measureReal_mono_null Set.inter_subset_left h (by finiteness)
      simp [this, h]
    · rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h, one_mul]
  simp only [hterm]
  exact hy

/-- Relabelling a countable-valued conditioner injectively leaves conditional
entropy unchanged, at a variable of finite entropy;
`condEntropy_comp_of_injective_countable` needs FiniteRange X. -/
public theorem condEntropy_comp_of_injective_of_summable [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) {f : T → U} (hf : Injective f)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) :
    H[X | f ∘ Y ; μ] = H[X | Y ; μ] := by
  have hfY : Measurable (f ∘ Y) := (Measurable.of_discrete (f := f)).comp hY
  have h1 := hasSum_condEntropy_of_summable (μ := μ) hX hfY hH
  have h2 := hasSum_condEntropy_of_summable (μ := μ) hX hY hH
  refine h1.unique ((hf.hasSum_iff fun u hu => ?_).mp ?_)
  · have : (f ∘ Y) ⁻¹' {u} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => hu ⟨Y ω, h⟩
    rw [map_measureReal_apply hfY (.singleton _), this]
    simp
  · convert h2 using 1
    funext t
    have : (f ∘ Y) ⁻¹' {f t} = Y ⁻¹' {t} := by
      ext ω; simp [hf.eq_iff]
    simp only [Function.comp_apply]
    rw [map_measureReal_apply hfY (.singleton _), map_measureReal_apply hY (.singleton _), this]

/-- Along X → Y → Z, adding Z to the conditioner Y changes nothing, at a
variable X of finite entropy; `condEntropy_pair_eq_of_isMarkovChain` needs
FiniteRange X. -/
public theorem condEntropy_pair_eq_of_isMarkovChain_of_summable [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) (h : IsMarkovChain X Y Z μ) :
    H[X | ⟨Y, Z⟩ ; μ] = H[X | Y ; μ] := by
  have h' : ∀ᵐ y ∂(μ.map Y), IndepFun X Z (μ[|Y ⁻¹' {y}]) := h
  rw [ae_iff_of_countable] at h'
  refine (hasSum_condEntropy_pair_of_summable hX hY hZ hH).unique ?_
  convert hasSum_condEntropy_of_summable (μ := μ) hX hY hH using 1
  funext y
  rw [map_measureReal_apply hY (.singleton _)]
  rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with h0 | h0
  · simp [measureReal_def, h0]
  · congr 1
    refine condEntropy_eq_entropy_of_indepFun hX hZ (h' y ?_)
    rwa [Measure.map_apply hY (.singleton y)]

/-- **Submodularity at a variable of finite entropy**: H[X | ⟨Y, Z⟩] ≤ H[X | Z]
for countable-valued X, Y, Z with only the entropy series of X assumed
convergent; `condEntropy_pair_le_countable` needs FiniteRange X. Fibrewise
over Z, it is `condEntropy_le_entropy_of_summable`. -/
public theorem condEntropy_pair_le_of_summable [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) :
    H[X | ⟨Y, Z⟩ ; μ] ≤ H[X | Z ; μ] := by
  have hswap : H[X | ⟨Y, Z⟩ ; μ] = H[X | ⟨Z, Y⟩ ; μ] :=
    condEntropy_comp_of_injective_of_summable (Y := fun ω => (Z ω, Y ω)) hX (hZ.prodMk hY)
      Prod.swap_injective hH
  rw [hswap]
  refine hasSum_le (fun z => ?_) (hasSum_condEntropy_pair_of_summable hX hZ hY hH)
    (hasSum_condEntropy_of_summable hX hZ hH)
  rw [map_measureReal_apply hZ (.singleton _)]
  exact mul_le_mul_of_nonneg_left
    (condEntropy_le_entropy_of_summable hX hY (summable_negMulLog_cond hX hZ hH z))
    measureReal_nonneg

/--
**Data processing in entropy form, at countable alphabets of finite entropy** —
the second inequality of (2.130), H(X|X̂) ≥ H(X|Y) for any estimator with
X → Y → X̂ (Cover & Thomas, Theorem 2.10.1, PDF p. 64), for discrete X, Y,
X̂ with countable alphabets, where only the entropy series of X is assumed to
converge.

`condEntropy_le_condEntropy_of_isMarkovChain_countable` is the same inequality
under FiniteRange X, which implies the hypothesis here
(`summable_negMulLog_of_finiteRange`). Both conditional entropies are genuine
sums (`hasSum_condEntropy_of_summable`, `summable_negMulLog_cond`), so neither
side is PFR's junk value. The observation and the estimate may have infinite
entropy. The proof is the one in AISafetyAtlas.InformationTheory.DataProcessing:
adding the estimate to the observation changes nothing along the chain, and
dropping the observation can only raise the conditional entropy.
-/
public theorem condEntropy_le_condEntropy_of_isMarkovChain_of_summable (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hH : Summable fun x => negMulLog ((μ.map X).real {x})) (h : IsMarkovChain X Y Z μ) :
    H[X | Y ; μ] ≤ H[X | Z ; μ] := by
  rw [← condEntropy_pair_eq_of_isMarkovChain_of_summable hX hY hZ hH h]
  exact condEntropy_pair_le_of_summable hX hY hZ hH

end AISafetyAtlas.InformationTheory
