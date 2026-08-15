module

public import AISafetyAtlas.Inference.Stochastic.Bridge
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Speaking Mathlib's probability vocabulary

`Stochastic/Measure.lean` states section 8 over a `Measure`, which is the right
generality — but it says *independence* with `IndependentOn`, a predicate of this
development, and takes its discrete data as `FinPMF`, a structure of this
development. Both are equivalent to something Mathlib already has, and until this
file the equivalence was unstated.

That is an interop defect, not a mathematical one, and it was one-directional in
the worst way. `Bridge.lean` maps *out* of the atlas types into `Measure`, so an
atlas model becomes a measure model. Nothing mapped *in*. A reader holding
`ProbabilityTheory.IndepFun` or a `PMF` — which is what a reader who did not
write this repository holds — could not discharge Proposition 6's hypothesis
without redoing the setup in a private vocabulary.

Two adapters close it.

* `independentOn_iff_indepFun` — `IndependentOn` **is** Mathlib's `IndepFun` on
  finite-range maps. The reverse direction is immediate (specialise to
  singletons); the forward one needs the fibre decomposition, which is where the
  `FiniteRange` hypotheses earn their place.
* `FinPMF.ofPMF` and `FinPMF.ofPMF_toMeasure` — a Mathlib `PMF` on a finite
  universe is a `FinPMF` inducing the same measure, so every worked model and
  every `Bridge.lean` lemma applies to it unchanged.

Neither adds a dependency: both Mathlib files are under the existing pin.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory ProbabilityTheory

-- The fibre decompositions below filter by set membership. The `Classical`
-- instance stays inside this module: every public statement here is
-- filter-free, so no caller has to match a decidability instance.
open scoped Classical

universe u v v'

variable {U : Type u}

variable [MeasurableSpace U]

/-! ## Fibre decomposition

A map with finite range splits every preimage into finitely many fibres. No
measurability of the *set* is needed — the decomposition is an equality of sets,
and only the fibres have to be measurable. That is why `FiniteRange` appears here
and countability of `U` does not.
-/

omit [MeasurableSpace U] in
/-- The preimage of a set is the union of the fibres over the attained points
of that set. -/
private theorem preimage_eq_biUnion_fibres {α : Type v} [DecidableEq α]
    (X : U → α) [FiniteRange X] (s : Set α) :
    X ⁻¹' s = ⋃ a ∈ (rangeFinset X).filter (fun a => a ∈ s), X ⁻¹' {a} := by
  classical
  ext u
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff,
    Finset.mem_filter, mem_rangeFinset, exists_prop]
  constructor
  · intro hu
    exact ⟨X u, ⟨⟨u, rfl⟩, hu⟩, rfl⟩
  · rintro ⟨a, ⟨-, ha⟩, rfl⟩
    exact ha

/-- Hence the measure of a preimage is the sum of the fibre masses it collects. -/
private theorem measure_preimage_eq_sum {α : Type v} [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure U) (X : U → α) (hX : Measurable X) [FiniteRange X] (s : Set α) :
    μ (X ⁻¹' s) = ((rangeFinset X).filter (fun a => a ∈ s)).sum
      (fun a => μ (X ⁻¹' {a})) := by
  classical
  have hdisj : (((rangeFinset X).filter (fun a => a ∈ s) : Finset α) : Set α).PairwiseDisjoint
      (fun a => X ⁻¹' {a}) := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr (fun u h₁ h₂ => hab ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h₁ h₂
    exact h₁.symm.trans h₂
  have hmeas : ∀ a ∈ (rangeFinset X).filter (fun a => a ∈ s),
      MeasurableSet (X ⁻¹' {a}) := fun a _ => hX (measurableSet_singleton a)
  rw [preimage_eq_biUnion_fibres X s, measure_biUnion_finset hdisj hmeas]

/-- The joint decomposition: a measurable rectangle's preimage is the disjoint
union of the joint fibres over the attained pairs. Indexing by the **product of
the marginal ranges** rather than by the joint range is what keeps the two sides
of the independence identity over the same index set — a pair of separately
attained values need not be jointly attained, and its fibre is simply empty. -/
private theorem measure_inter_eq_sum {α : Type v} {β : Type v'}
    [DecidableEq α] [DecidableEq β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure U) (X : U → α) (Y : U → β) (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] (s : Set α) (t : Set β) :
    μ (X ⁻¹' s ∩ Y ⁻¹' t) =
      (((rangeFinset X).filter (fun a => a ∈ s)) ×ˢ
        ((rangeFinset Y).filter (fun b => b ∈ t))).sum
        (fun p => μ (X ⁻¹' {p.1} ∩ Y ⁻¹' {p.2})) := by
  classical
  have hdisj : ((((rangeFinset X).filter (fun a => a ∈ s)) ×ˢ
      ((rangeFinset Y).filter (fun b => b ∈ t)) : Finset (α × β)) : Set (α × β)).PairwiseDisjoint
      (fun p => X ⁻¹' {p.1} ∩ Y ⁻¹' {p.2}) := by
    intro p _ q _ hpq
    refine Set.disjoint_left.mpr (fun u h₁ h₂ => hpq ?_)
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at h₁ h₂
    exact Prod.ext (h₁.1.symm.trans h₂.1) (h₁.2.symm.trans h₂.2)
  have hmeas : ∀ p ∈ ((rangeFinset X).filter (fun a => a ∈ s)) ×ˢ
      ((rangeFinset Y).filter (fun b => b ∈ t)),
      MeasurableSet (X ⁻¹' {p.1} ∩ Y ⁻¹' {p.2}) :=
    fun p _ => (hX (measurableSet_singleton p.1)).inter (hY (measurableSet_singleton p.2))
  have hcover : (⋃ p ∈ ((rangeFinset X).filter (fun a => a ∈ s)) ×ˢ
      ((rangeFinset Y).filter (fun b => b ∈ t)), X ⁻¹' {p.1} ∩ Y ⁻¹' {p.2})
      = X ⁻¹' s ∩ Y ⁻¹' t := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_product, Finset.mem_filter, mem_rangeFinset, exists_prop]
    constructor
    · rintro ⟨p, ⟨⟨-, hps⟩, ⟨-, hpt⟩⟩, hu₁, hu₂⟩
      exact ⟨hu₁ ▸ hps, hu₂ ▸ hpt⟩
    · intro hu
      exact ⟨(X u, Y u), ⟨⟨⟨u, rfl⟩, hu.1⟩, ⟨⟨u, rfl⟩, hu.2⟩⟩, rfl, rfl⟩
  rw [← hcover, measure_biUnion_finset hdisj hmeas]

/-! ## `IndependentOn` is `IndepFun` -/

omit [MeasurableSpace U] in
/-- The joint fibre is the intersection of the marginal fibres — the reason
Definition 9's pair mass and Mathlib's intersection measure are the same number. -/
public theorem preimage_pair_singleton {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) (a : α) (b : β) :
    (fun u => (X u, Y u)) ⁻¹' {(a, b)} = X ⁻¹' {a} ∩ Y ⁻¹' {b} := by
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.mk.injEq]

/-- `IndependentOn` in `ℝ≥0∞`: the fibre identity with no `toReal` in the way. -/
public theorem measure_pair_eq_mul_of_independentOn {α : Type v} {β : Type v'}
    (μ : Measure U) [IsFiniteMeasure μ] (X : U → α) (Y : U → β)
    (h : IndependentOn μ X Y) (a : α) (b : β) :
    μ ((fun u => (X u, Y u)) ⁻¹' {(a, b)}) = μ (X ⁻¹' {a}) * μ (Y ⁻¹' {b}) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ ((fun u => (X u, Y u)) ⁻¹' {(a, b)})),
    ← ENNReal.ofReal_toReal (measure_ne_top μ (X ⁻¹' {a})),
    ← ENNReal.ofReal_toReal (measure_ne_top μ (Y ⁻¹' {b})),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact congrArg ENNReal.ofReal (h a b)

/--
**`IndependentOn` is Mathlib's `IndepFun`.**

The atlas predicate is stated pointwise on fibres in `ℝ`, because that is the
form Proposition 6's algebra consumes; Mathlib's is stated on all measurable sets
in `ℝ≥0∞`. On finite-range maps they are the same condition, so a reader who
already has `IndepFun X Y μ` can discharge Proposition 6's hypothesis directly,
and one who has the atlas form can hand it to Mathlib's independence API.
-/
public theorem independentOn_iff_indepFun {α : Type v} {β : Type v'}
    [DecidableEq α] [DecidableEq β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure U) [IsProbabilityMeasure μ]
    (X : U → α) (Y : U → β) (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] :
    IndependentOn μ X Y ↔ IndepFun X Y μ := by
  classical
  constructor
  · intro h
    refine indepFun_iff_measure_inter_preimage_eq_mul.mpr (fun s t _ _ => ?_)
    have hterm : ∀ p ∈ ((rangeFinset X).filter (fun a => a ∈ s)) ×ˢ
        ((rangeFinset Y).filter (fun b => b ∈ t)),
        μ (X ⁻¹' {p.1} ∩ Y ⁻¹' {p.2}) = μ (X ⁻¹' {p.1}) * μ (Y ⁻¹' {p.2}) := by
      intro p _
      rw [← preimage_pair_singleton X Y p.1 p.2]
      exact measure_pair_eq_mul_of_independentOn μ X Y h p.1 p.2
    rw [measure_inter_eq_sum μ X Y hX hY s t, Finset.sum_congr rfl hterm,
      Finset.sum_product' (f := fun a b => μ (X ⁻¹' {a}) * μ (Y ⁻¹' {b})),
      ← Finset.sum_mul_sum, measure_preimage_eq_sum μ X hX s,
      measure_preimage_eq_sum μ Y hY t]
  · intro h a b
    have hmul := indepFun_iff_measure_inter_preimage_eq_mul.mp h
      {a} {b} (measurableSet_singleton a) (measurableSet_singleton b)
    rw [massOn, massOn, massOn, preimage_pair_singleton, hmul, ENNReal.toReal_mul]

/-! ## A Mathlib `PMF` is a `FinPMF` -/

/-- Mathlib's discrete probability object, in the atlas's finite form. -/
public noncomputable def FinPMF.ofPMF [Fintype U] (p : PMF U) : FinPMF U where
  mass := fun u => (p u).toReal
  nonneg := fun _ => ENNReal.toReal_nonneg
  sum_one := by
    have hsum : ∑ u : U, p u = 1 :=
      (hasSum_fintype (fun u : U => p u)).unique p.hasSum_coe_one
    have h : (∑ u : U, p u).toReal = 1 := by
      rw [hsum]
      simp
    rwa [ENNReal.toReal_sum (fun u _ => p.apply_ne_top u)] at h

/-- …and it induces the same measure, so every `Bridge.lean` lemma and every
worked model transfers to a `PMF` with no restatement. -/
public theorem FinPMF.ofPMF_toMeasure [Fintype U] [MeasurableSingletonClass U]
    (p : PMF U) : (FinPMF.ofPMF p).toMeasure = p.toMeasure := by
  refine Measure.ext (fun s _ => ?_)
  rw [FinPMF.toMeasure_apply, PMF.toMeasure_apply_fintype]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases hu : u ∈ s
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    simp [FinPMF.ofPMF, ENNReal.ofReal_toReal (p.apply_ne_top u)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
    simp

/-- The other direction: a `FinPMF` is a Mathlib `PMF`. -/
@[expose] public noncomputable def FinPMF.toPMF [Fintype U] (p : FinPMF U) : PMF U :=
  ⟨fun u => ENNReal.ofReal (p.mass u), by
    have hsum : ∑ u : U, ENNReal.ofReal (p.mass u) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => p.nonneg u), p.sum_one,
        ENNReal.ofReal_one]
    exact hsum ▸ hasSum_fintype _⟩

omit [MeasurableSpace U] in
@[simp] public theorem FinPMF.toPMF_apply [Fintype U] (p : FinPMF U) (u : U) :
    p.toPMF u = ENNReal.ofReal (p.mass u) := rfl

omit [MeasurableSpace U] in
/-- The round trip is the identity on masses, so the two types carry the same
data on a finite universe. -/
public theorem FinPMF.ofPMF_toPMF [Fintype U] (p : FinPMF U) (u : U) :
    (FinPMF.ofPMF p.toPMF).mass u = p.mass u := by
  simp [FinPMF.ofPMF, ENNReal.toReal_ofReal (p.nonneg u)]

omit [MeasurableSpace U] in
public theorem PMF.toPMF_ofPMF [Fintype U] (p : PMF U) (u : U) :
    (FinPMF.ofPMF p).toPMF u = p u := by
  simp [FinPMF.ofPMF, ENNReal.ofReal_toReal (p.apply_ne_top u)]

/-! ## Why `FinPMF` stays

With the round trip closed, `FinPMF` on a `Fintype` and `PMF` on a `Fintype`
carry the same data, and the choice between them is presentation rather than
content. `FinPMF` stays, for one reason that is not inertia: its mass is
`ℝ`-valued, and every §8 quantity built on it — `shannonEntropyOn`,
`mutualInfo`, `inferenceAccuracy`, the whole Proposition 6 algebra — is a signed
real expression with subtraction and logarithms in it. `PMF` is `ℝ≥0∞`-valued,
where subtraction is truncated and `Real.log` does not apply, so a migration
would insert `toReal` at every leaf of a closed proof and buy nothing: the
adapters above already let a `PMF` holder in.

The general layer is the one that had to move, and it did — §8 is stated over
`Measure`. `FinPMF` is now a finite presentation with two-way translation, not a
parallel universe.
-/

end AISafetyAtlas.Inference
