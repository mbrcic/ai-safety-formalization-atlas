module

public import AISafetyAtlas.Inference.Stochastic
public import AISafetyAtlas.Inference.Stochastic.Measure
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# The finite layer is an instance of the general one

`Stochastic.lean` works with a `FinPMF` on a `Fintype U`; `Stochastic/Measure.lean`
works with a probability measure on an arbitrary measurable space. Without a bridge
those are two parallel vocabularies for the same quantities, and every worked model
would have to be built twice.

They are not parallel. A `FinPMF` induces a measure, every map out of a finite type
has finite range, and the two definitions of fibre mass, entropy and mutual
information then agree **definitionally up to a `Finset` identity** — the finite
layer sums over `Finset.univ.image X`, the general layer over `X(U)` as a
`Finset`, and those are the same set.

So the executable models in `Examples/` do not need restating. They are instances.

**These are not `@[simp]` lemmas.** Marking them so was tried and the attribute
does not fire: `simp` makes no progress on `massOn p.toMeasure X x =
pushOnImage p X x` even though that is the lemma's own statement, because the
`Measure` argument is a projection out of a structure and the instance arguments
do not line up in the discrimination tree. Use them as terms. Recorded because a
`simp` lemma that never fires reads as automation and is not.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

universe u v v'

variable {U : Type u} [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

omit [MeasurableSpace U] [MeasurableSingletonClass U] in
/-- The two range `Finset`s coincide. -/
public theorem rangeFinset_eq_image {α : Type v} [DecidableEq α] (X : U → α) :
    rangeFinset X = Finset.univ.image X := by
  ext a
  simp [mem_rangeFinset, Finset.mem_image]

/-- The measure a finite probability mass function induces. -/
public noncomputable def FinPMF.toMeasure (p : FinPMF U) : Measure U :=
  ∑ u : U, ENNReal.ofReal (p.mass u) • Measure.dirac u

public theorem FinPMF.toMeasure_apply (p : FinPMF U) (s : Set U) :
    p.toMeasure s = ∑ u : U, ENNReal.ofReal (p.mass u) * Set.indicator s 1 u := by
  classical
  rw [FinPMF.toMeasure, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := s))]

/-- Fibre mass in the general layer is the finite layer's pushforward mass. -/
public theorem massOn_toMeasure (p : FinPMF U) {α : Type v} [DecidableEq α]
    (X : U → α) (x : α) : massOn p.toMeasure X x = pushOnImage p X x := by
  classical
  have hsum : p.toMeasure (X ⁻¹' {x})
      = ∑ u ∈ Finset.univ.filter (fun u => X u = x), ENNReal.ofReal (p.mass u) := by
    rw [FinPMF.toMeasure_apply]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => X u = x)]
    have h₁ : ∀ u ∈ Finset.univ.filter (fun u => X u = x),
        ENNReal.ofReal (p.mass u) * Set.indicator (X ⁻¹' {x}) 1 u
          = ENNReal.ofReal (p.mass u) := by
      intro u hu
      have : u ∈ X ⁻¹' {x} := (Finset.mem_filter.mp hu).2
      simp [Set.indicator_of_mem this]
    have h₂ : ∀ u ∈ Finset.univ.filter (fun u => ¬ X u = x),
        ENNReal.ofReal (p.mass u) * Set.indicator (X ⁻¹' {x}) 1 u = 0 := by
      intro u hu
      have : u ∉ X ⁻¹' {x} := (Finset.mem_filter.mp hu).2
      simp [Set.indicator_of_notMem this]
    rw [Finset.sum_congr rfl h₁, Finset.sum_congr rfl h₂, Finset.sum_const_zero, add_zero]
  rw [massOn, hsum, ENNReal.toReal_sum (fun u _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  exact ENNReal.toReal_ofReal (p.nonneg u)

public instance FinPMF.isProbabilityMeasure (p : FinPMF U) :
    IsProbabilityMeasure p.toMeasure where
  measure_univ := by
    classical
    have h := massOn_toMeasure p (fun _ : U => ()) ()
    have hpre : (fun _ : U => ()) ⁻¹' {()} = (Set.univ : Set U) := by ext u; simp
    have hpush : pushOnImage p (fun _ : U => ()) () = 1 := by
      unfold pushOnImage
      rw [Finset.filter_true_of_mem (fun _ _ => rfl)]
      exact p.sum_one
    rw [massOn, hpre, hpush] at h
    have hne : p.toMeasure Set.univ ≠ ⊤ := by
      intro htop
      rw [htop] at h
      simp at h
    exact (ENNReal.toReal_eq_one_iff _).mp h

/-- Entropy agrees across the two layers. -/
public theorem entropyOn_toMeasure (p : FinPMF U) {α : Type v} [DecidableEq α]
    (X : U → α) :
    entropyOn p.toMeasure X = shannonEntropyOn (Finset.univ.image X) (pushOnImage p X) := by
  unfold entropyOn shannonEntropyOn
  rw [rangeFinset_eq_image]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun a _ => ?_))
  rw [massOn_toMeasure]

/-- Mutual information agrees across the two layers. -/
public theorem mutualInfoOn_toMeasure (p : FinPMF U) {α : Type v} {β : Type v'}
    [DecidableEq α] [DecidableEq β] (X : U → α) (Y : U → β) :
    mutualInfoOn p.toMeasure X Y = mutualInfo p X Y := by
  unfold mutualInfoOn mutualInfo
  rw [entropyOn_toMeasure, entropyOn_toMeasure, entropyOn_toMeasure]

/-- Independence agrees across the two layers. -/
public theorem independentOn_toMeasure (p : FinPMF U) {α : Type v} {β : Type v'}
    [DecidableEq α] [DecidableEq β] (X : U → α) (Y : U → β) :
    IndependentOn p.toMeasure X Y ↔ StatisticallyIndependent p X Y := by
  constructor <;> intro h a b
  · have := h a b
    rwa [massOn_toMeasure, massOn_toMeasure, massOn_toMeasure] at this
  · have := h a b
    rw [massOn_toMeasure, massOn_toMeasure, massOn_toMeasure]
    exact this

/-- Setup entropy agrees across the two layers. -/
public theorem setupEntropyOn_toMeasure (p : FinPMF U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] :
    setupEntropyOn p.toMeasure C = setupEntropy C p := by
  unfold setupEntropyOn setupEntropy
  exact entropyOn_toMeasure p C.setup

/-- Definition 10 agrees across the two layers. -/
public theorem miDistinguishabilityOn_toMeasure (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] :
    miDistinguishabilityOn p.toMeasure C₁ C₂ = miDistinguishability C₁ C₂ p := by
  unfold miDistinguishabilityOn miDistinguishability
  rw [setupEntropyOn_toMeasure, setupEntropyOn_toMeasure,
    mutualInfoOn_toMeasure]

end AISafetyAtlas.Inference
