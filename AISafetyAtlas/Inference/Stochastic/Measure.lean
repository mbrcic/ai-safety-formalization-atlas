module

public import AISafetyAtlas.Inference.Device
public import AISafetyAtlas.Inference.FiniteRange
public import AISafetyAtlas.Inference.Stochastic.Algebra
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

/-!
# Section 8 over a general measure — Wolpert 2008

`Stochastic.lean` states Definitions 9–11 and Proposition 6 for a `FinPMF` on a
`Fintype U`. That is not the paper's setting. Wolpert's `U` is *"the set of
worldlines consistent with the laws of physics"*, which is uncountable, so a
finite `U` excludes the intended model outright.

The finiteness the source actually states sits somewhere else: on the **ranges**.
Definition 9 takes *"a function `Γ` with domain `U` and finite range"*, and
Definition 11 is *"for simplicity phrased for countable `X(U)`"*. Nothing in
section 8 asks `U` itself to be finite.

This module states the section-8 ingredients that way: an arbitrary measurable
space `U`, a probability measure, and finiteness on the maps.

## Why no disintegration is needed

The obvious fear about a measure-theoretic restatement is conditioning: `E_P(· ∣ x)`
on a null fibre needs a regular conditional probability, and that needs a standard
Borel space. It does not arise here. Every fibre is `X ⁻¹' {x}` for a map with
finite range, and the accuracy in Definition 9 already maximises only over fibres
of positive mass — the restriction `Stochastic.lean` carries as
`positiveMassSetups`. Conditioning is on positive-measure sets throughout.

## Why no dependency is needed

The mass of a fibre is `μ (X ⁻¹' {x})`, and a Mathlib `Measure` is defined on
*every* set through its outer measure, so no measurability hypothesis is needed to
state anything. Measurability enters only where additivity does, and it is
requested there rather than globally.

`FiniteRange` is deliberately a local three-line class rather than an import:
the only Lean library that has one is PFR, and this development does not depend
on PFR.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

universe u v v'

variable {U : Type u}

/-! ## Measurability, discharged rather than assumed

Every §8 statement carries `Measurable C.setup` or `Measurable C.concl`. On a
discrete universe those are free, and `fun_prop` is the tactic that knows it — so
models write `by fun_prop` instead of naming the lemma, and the hypothesis stops
being friction. This is the reason the general layer does not make finite models
more expensive to write.
-/

@[fun_prop] public theorem measurable_setup [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (C : InferenceDevice.{u, v} U) [MeasurableSpace C.Setup] : Measurable C.setup :=
  Measurable.of_discrete

@[fun_prop] public theorem measurable_concl [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (C : InferenceDevice.{u, v} U) : Measurable C.concl :=
  Measurable.of_discrete

/-- The mass a measure gives the fibre of `X` over `x`.

Stated with no measurability hypothesis: a `Measure` is an outer measure on every
set. Additivity lemmas below request measurability where they need it. -/
@[expose] public noncomputable def massOn [MeasurableSpace U] (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) : ℝ :=
  (μ (X ⁻¹' {x})).toReal

public theorem massOn_nonneg [MeasurableSpace U] (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) : 0 ≤ massOn μ X x :=
  ENNReal.toReal_nonneg

public theorem massOn_eq_zero_of_notMem [MeasurableSpace U] (μ : Measure U)
    {α : Type v} (X : U → α) [FiniteRange X] {x : α} (hx : x ∉ rangeFinset X) :
    massOn μ X x = 0 := by
  have hempty : X ⁻¹' {x} = (∅ : Set U) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hx ((mem_rangeFinset X x).mpr ⟨u, h⟩)
  simp [massOn, hempty]

/-! ## Finite additivity over the range

The fibres of a finite-range map partition `U`, so the masses sum to `1` and the
joint masses marginalise. These are the two facts every entropy argument below
rests on, and they are the only place measurability is needed. -/

variable [MeasurableSpace U]

omit [MeasurableSpace U] in
private theorem fibres_pairwiseDisjoint {α : Type v} (X : U → α) (s : Finset α) :
    (s : Set α).PairwiseDisjoint (fun x => X ⁻¹' {x}) := by
  intro a _ b _ hab
  refine Set.disjoint_left.mpr (fun u ha hb => hab ?_)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  exact ha.symm.trans hb

private theorem measure_fibre_ne_top (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} (X : U → α) (x : α) : μ (X ⁻¹' {x}) ≠ ⊤ :=
  measure_ne_top μ _

/-- The masses of a finite-range map sum to `1`. -/
public theorem sum_massOn (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : U → α) [FiniteRange X] (hX : Measurable X) :
    (rangeFinset X).sum (massOn μ X) = 1 := by
  have hmeas : ∀ x ∈ rangeFinset X, MeasurableSet (X ⁻¹' {x}) :=
    fun x _ => hX (measurableSet_singleton x)
  have hcover : (⋃ x ∈ rangeFinset X, X ⁻¹' {x}) = (Set.univ : Set U) := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact ⟨X u, self_mem_rangeFinset X u, rfl⟩
  have hsum := measure_biUnion_finset
    (fibres_pairwiseDisjoint X (rangeFinset X)) hmeas (μ := μ)
  rw [hcover, measure_univ] at hsum
  have : ((1 : ENNReal)).toReal = ((rangeFinset X).sum (fun x => μ (X ⁻¹' {x}))).toReal := by
    rw [hsum]
  rw [ENNReal.toReal_sum (fun x _ => measure_fibre_ne_top μ X x)] at this
  -- The goal's sum is eta-contracted -- `(rangeFinset X).sum (massOn μ X)` --
  -- and `simp [massOn]` no longer fires through that; `unfold` still does.
  unfold massOn
  simpa using this.symm

/-- Joint masses marginalise onto the first coordinate. -/
public theorem sum_massOn_marginal (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} {β : Type v'}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (X : U → α) (Y : U → β) [FiniteRange Y] (hX : Measurable X) (hY : Measurable Y)
    (a : α) :
    (rangeFinset Y).sum (fun b => massOn μ (fun u => (X u, Y u)) (a, b)) =
      massOn μ X a := by
  have hpair : Measurable (fun u => (X u, Y u)) := hX.prodMk hY
  have hmeas : ∀ b ∈ rangeFinset Y,
      MeasurableSet ((fun u => (X u, Y u)) ⁻¹' {(a, b)}) :=
    fun b _ => hpair (measurableSet_singleton _)
  have hdisj : ((rangeFinset Y : Set β)).PairwiseDisjoint
      (fun b => (fun u => (X u, Y u)) ⁻¹' {(a, b)}) := by
    intro b₁ _ b₂ _ hb
    refine Set.disjoint_left.mpr (fun u h₁ h₂ => hb ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
    exact h₁.2.symm.trans h₂.2
  have hcover : (⋃ b ∈ rangeFinset Y, (fun u => (X u, Y u)) ⁻¹' {(a, b)}) = X ⁻¹' {a} := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨b, -, hu, -⟩; exact hu
    · intro hu; exact ⟨Y u, self_mem_rangeFinset Y u, hu, rfl⟩
  have hsum := measure_biUnion_finset hdisj hmeas (μ := μ)
  rw [hcover] at hsum
  have : (μ (X ⁻¹' {a})).toReal =
      ((rangeFinset Y).sum (fun b => μ ((fun u => (X u, Y u)) ⁻¹' {(a, b)}))).toReal := by
    rw [hsum]
  rw [ENNReal.toReal_sum (fun b _ => measure_ne_top μ _)] at this
  simpa [massOn] using this.symm

/-! ## Entropy and mutual information over a general measure -/

/-- A pair of finite-range maps has finite range. -/
public instance instFiniteRangeProd {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y] :
    FiniteRange (fun u => (X u, Y u)) where
  finite_range := by
    refine Set.Finite.subset
      (((FiniteRange.finite_range (X := X)).prod
        (FiniteRange.finite_range (X := Y)))) ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, rfl⟩, ⟨u, rfl⟩⟩

omit [MeasurableSpace U] in
public theorem rangeFinset_prod_subset {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y] [DecidableEq α] [DecidableEq β] :
    rangeFinset (fun u => (X u, Y u)) ⊆ rangeFinset X ×ˢ rangeFinset Y := by
  intro c hc
  obtain ⟨u, rfl⟩ := (mem_rangeFinset _ c).mp hc
  exact Finset.mem_product.mpr ⟨self_mem_rangeFinset X u, self_mem_rangeFinset Y u⟩

/-- A joint cell weighs no more than either marginal. -/
public theorem massOn_joint_le_fst (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} {β : Type v'} (X : U → α) (Y : U → β) (a : α) (b : β) :
    massOn μ (fun u => (X u, Y u)) (a, b) ≤ massOn μ X a := by
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)
  intro u hu
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hu ⊢
  exact hu.1

public theorem massOn_joint_le_snd (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} {β : Type v'} (X : U → α) (Y : U → β) (a : α) (b : β) :
    massOn μ (fun u => (X u, Y u)) (a, b) ≤ massOn μ Y b := by
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)
  intro u hu
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hu ⊢
  exact hu.2

/-- Shannon entropy of a finite-range map under `μ`, natural logarithm. -/
@[expose] public noncomputable def entropyOn (μ : Measure U) {α : Type v}
    (X : U → α) [FiniteRange X] : ℝ :=
  - (rangeFinset X).sum fun a =>
      if massOn μ X a = 0 then 0 else massOn μ X a * Real.log (massOn μ X a)

/-- Mutual information of two finite-range maps under `μ`. -/
@[expose] public noncomputable def mutualInfoOn (μ : Measure U) {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y] : ℝ :=
  entropyOn μ X + entropyOn μ Y - entropyOn μ (fun u => (X u, Y u))

/-- Statistical independence, pointwise on the joint pushforward. The `FinPMF`
layer's `StatisticallyIndependent` is this over a finite `U`. -/
@[expose] public def IndependentOn (μ : Measure U) {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) : Prop :=
  ∀ a b, massOn μ (fun u => (X u, Y u)) (a, b) = massOn μ X a * massOn μ Y b

/-! ## Gibbs' inequality and its equality case, over a general measure

The pointwise steps are `gibbs_cell` and `gibbs_cell_eq_iff`, which are statements
about real numbers and transfer unchanged. Only the summation apparatus differs:
the rectangle is `X(U) × Y(U)` rather than a product of image `Finset`s over a
finite `U`. -/

variable {α : Type v} {β : Type v'}
variable [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α]
variable [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β]

/-- The Gibbs term contributed by one cell of `X(U) × Y(U)`. -/
private noncomputable def cellFn (μ : Measure U) (X : U → α) (Y : U → β) (c : α × β) : ℝ :=
  (if massOn μ (fun u => (X u, Y u)) c = 0 then 0
    else massOn μ (fun u => (X u, Y u)) c * Real.log (massOn μ X c.1)) +
  (if massOn μ (fun u => (X u, Y u)) c = 0 then 0
    else massOn μ (fun u => (X u, Y u)) c * Real.log (massOn μ Y c.2)) -
  (if massOn μ (fun u => (X u, Y u)) c = 0 then 0
    else massOn μ (fun u => (X u, Y u)) c *
      Real.log (massOn μ (fun u => (X u, Y u)) c))

private noncomputable def slackFn (μ : Measure U) (X : U → α) (Y : U → β) (c : α × β) : ℝ :=
  massOn μ X c.1 * massOn μ Y c.2 - massOn μ (fun u => (X u, Y u)) c

omit [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β] in
private theorem cellFn_le (μ : Measure U) [IsFiniteMeasure μ]
    (X : U → α) (Y : U → β) (c : α × β) : cellFn μ X Y c ≤ slackFn μ X Y c :=
  gibbs_cell (massOn_nonneg μ _ c)
    (massOn_joint_le_fst μ X Y c.1 c.2) (massOn_joint_le_snd μ X Y c.1 c.2)

omit [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β] in
private theorem cellFn_eq_iff (μ : Measure U) [IsFiniteMeasure μ]
    (X : U → α) (Y : U → β) (c : α × β) :
    cellFn μ X Y c = slackFn μ X Y c ↔
      massOn μ (fun u => (X u, Y u)) c = massOn μ X c.1 * massOn μ Y c.2 :=
  gibbs_cell_eq_iff (massOn_nonneg μ _ c)
    (massOn_joint_le_fst μ X Y c.1 c.2) (massOn_joint_le_snd μ X Y c.1 c.2)

private theorem sum_slackFn (μ : Measure U) [IsProbabilityMeasure μ]
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) :
    (rangeFinset X ×ˢ rangeFinset Y).sum (slackFn μ X Y) = 0 := by
  have hjoint : (rangeFinset X ×ˢ rangeFinset Y).sum
      (massOn μ (fun u => (X u, Y u))) = 1 := by
    rw [← Finset.sum_subset (rangeFinset_prod_subset X Y)
      (fun c _ hc => massOn_eq_zero_of_notMem μ _ hc)]
    exact sum_massOn μ (fun u => (X u, Y u)) (hX.prodMk hY)
  have hprod : (rangeFinset X ×ˢ rangeFinset Y).sum
      (fun c => massOn μ X c.1 * massOn μ Y c.2) = 1 := by
    rw [Finset.sum_product]
    have hrow : ∀ a ∈ rangeFinset X,
        (rangeFinset Y).sum (fun b => massOn μ X a * massOn μ Y b) = massOn μ X a := by
      intro a _
      rw [← Finset.mul_sum, sum_massOn μ Y hY, mul_one]
    rw [Finset.sum_congr rfl hrow]
    exact sum_massOn μ X hX
  unfold slackFn
  rw [Finset.sum_sub_distrib, hprod, hjoint, sub_self]

/-- `−M` is the cell-by-cell Gibbs sum over the rectangle `X(U) × Y(U)`. -/
private theorem neg_mutualInfoOn_eq_cellSum (μ : Measure U) [IsProbabilityMeasure μ]
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) :
    -mutualInfoOn μ X Y = (rangeFinset X ×ˢ rangeFinset Y).sum (cellFn μ X Y) := by
  classical
  set qm := massOn μ (fun u => (X u, Y u)) with hqm
  set pX := massOn μ X with hpX
  set pY := massOn μ Y with hpY
  have hext : ∀ f : α × β → ℝ, (∀ c, qm c = 0 → f c = 0) →
      (rangeFinset (fun u => (X u, Y u))).sum f = (rangeFinset X ×ˢ rangeFinset Y).sum f := by
    intro f hf
    exact Finset.sum_subset (rangeFinset_prod_subset X Y)
      (fun c _ hc => hf c (massOn_eq_zero_of_notMem μ _ hc))
  have hXsum : (rangeFinset X).sum (fun a => if pX a = 0 then 0 else pX a * Real.log (pX a)) =
      (rangeFinset X ×ˢ rangeFinset Y).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (pX c.1)) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hpa : pX a = 0
    · refine (if_pos hpa).trans ?_
      refine (Finset.sum_eq_zero (fun b _ => ?_)).symm
      have hq0 : qm (a, b) = 0 :=
        le_antisymm (hpa ▸ massOn_joint_le_fst μ X Y a b) (massOn_nonneg μ _ (a, b))
      exact if_pos hq0
    · rw [if_neg hpa]
      have hz : ∀ b ∈ rangeFinset Y,
          (if qm (a, b) = 0 then 0 else qm (a, b) * Real.log (pX a)) = qm (a, b) * Real.log (pX a) := by
        intro b _
        by_cases hb : qm (a, b) = 0
        · rw [if_pos hb, hb, zero_mul]
        · rw [if_neg hb]
      rw [Finset.sum_congr rfl hz, ← Finset.sum_mul, hqm, sum_massOn_marginal μ X Y hX hY]
  have hYsum : (rangeFinset Y).sum (fun b => if pY b = 0 then 0 else pY b * Real.log (pY b)) =
      (rangeFinset X ×ˢ rangeFinset Y).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (pY c.2)) := by
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hpb : pY b = 0
    · refine (if_pos hpb).trans ?_
      refine (Finset.sum_eq_zero (fun a _ => ?_)).symm
      have hq0 : qm (a, b) = 0 :=
        le_antisymm (hpb ▸ massOn_joint_le_snd μ X Y a b) (massOn_nonneg μ _ (a, b))
      exact if_pos hq0
    · rw [if_neg hpb]
      have hz : ∀ a ∈ rangeFinset X,
          (if qm (a, b) = 0 then 0 else qm (a, b) * Real.log (pY b)) = qm (a, b) * Real.log (pY b) := by
        intro a _
        by_cases ha : qm (a, b) = 0
        · rw [if_pos ha, ha, zero_mul]
        · rw [if_neg ha]
      rw [Finset.sum_congr rfl hz, ← Finset.sum_mul]
      congr 1
      have hswap : ∀ a ∈ rangeFinset X, qm (a, b) = massOn μ (fun u => (Y u, X u)) (b, a) := by
        intro a _
        have hset : (fun u => (X u, Y u)) ⁻¹' {(a, b)}
            = (fun u => (Y u, X u)) ⁻¹' {(b, a)} := by
          ext u
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
          tauto
        simp [hqm, massOn, hset]
      rw [Finset.sum_congr rfl hswap, sum_massOn_marginal μ Y X hY hX]
  have hJsum : (rangeFinset (fun u => (X u, Y u))).sum
        (fun c => if qm c = 0 then 0 else qm c * Real.log (qm c)) =
      (rangeFinset X ×ˢ rangeFinset Y).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (qm c)) :=
    hext _ (fun c hc => if_pos hc)
  unfold cellFn
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← hXsum, ← hYsum, ← hJsum]
  unfold mutualInfoOn entropyOn
  ring

/-- **Gibbs' inequality over a general measure.** -/
public theorem mutualInfoOn_nonneg (μ : Measure U) [IsProbabilityMeasure μ]
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) : 0 ≤ mutualInfoOn μ X Y := by
  have hstep := Finset.sum_le_sum (s := rangeFinset X ×ˢ rangeFinset Y)
    (fun c (_ : c ∈ rangeFinset X ×ˢ rangeFinset Y) => cellFn_le μ X Y c)
  rw [sum_slackFn μ X Y hX hY, ← neg_mutualInfoOn_eq_cellSum μ X Y hX hY] at hstep
  linarith

/-- **The equality case, over a general measure.** `M = 0` exactly at independence.

This is Wolpert's Proposition 6 step 2a with `U` arbitrary: no finiteness on the
universe, no `FinPMF`, and no standard-Borel hypothesis. -/
public theorem mutualInfoOn_eq_zero_iff (μ : Measure U) [IsProbabilityMeasure μ]
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) :
    mutualInfoOn μ X Y = 0 ↔ IndependentOn μ X Y := by
  have hiff : (∀ c ∈ rangeFinset X ×ˢ rangeFinset Y, cellFn μ X Y c = slackFn μ X Y c) ↔
      mutualInfoOn μ X Y = 0 := by
    rw [← Finset.sum_eq_sum_iff_of_le (fun c _ => cellFn_le μ X Y c),
      sum_slackFn μ X Y hX hY, ← neg_mutualInfoOn_eq_cellSum μ X Y hX hY]
    constructor
    · intro h; linarith
    · intro h; linarith
  constructor
  · intro h0 a b
    by_cases ha : a ∈ rangeFinset X
    · by_cases hb : b ∈ rangeFinset Y
      · exact (cellFn_eq_iff μ X Y (a, b)).mp
          (hiff.mpr h0 (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩))
      · have hzero : massOn μ Y b = 0 := massOn_eq_zero_of_notMem μ Y hb
        have hq : massOn μ (fun u => (X u, Y u)) (a, b) = 0 :=
          le_antisymm (hzero ▸ massOn_joint_le_snd μ X Y a b) (massOn_nonneg μ _ (a, b))
        rw [hq, hzero, mul_zero]
    · have hzero : massOn μ X a = 0 := massOn_eq_zero_of_notMem μ X ha
      have hq : massOn μ (fun u => (X u, Y u)) (a, b) = 0 :=
        le_antisymm (hzero ▸ massOn_joint_le_fst μ X Y a b) (massOn_nonneg μ _ (a, b))
      rw [hq, hzero, zero_mul]
  · intro hind
    exact hiff.mp (fun c _ => (cellFn_eq_iff μ X Y c).mpr (hind c.1 c.2))

/-! ## Definitions 9–11 over a general measure

Conditional expectation is taken **without an integral**. The only function
Definition 9 conditions on is `Y · f(Γ)`, a product of two `±1`-valued functions,
so it is `+1` exactly where the device's conclusion agrees with the probe and `−1`
elsewhere. Its conditional expectation is therefore `2·P(agree ∣ x) − 1`, and that
probability is a ratio of two fibre masses. No Bochner integral, no integrability
side condition, and the same shape the finite layer already uses. -/

/-- Realized setup values of positive `μ`-mass. Definition 9's maximum ranges over
these: the source's conditional expectation is undefined on a null fibre. -/
@[expose] public noncomputable def positiveMassSetupsOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] : Finset C.Setup :=
  (rangeFinset C.setup).filter fun x => 0 < massOn μ C.setup x

/-- Some fibre carries positive mass, because the total is `1`.

**No measurability hypothesis.** An earlier version required `Measurable C.setup`
and derived the contradiction from `sum_massOn`, which needs the fibres to be
measurable so that their masses add *exactly*. Nonemptiness needs far less: the
fibres cover `U`, so sub-additivity alone forces one of them to be non-null, and
`measure_biUnion_finset_le` holds for arbitrary sets. Removing the hypothesis
here is what lets Definition 9 be stated without it — the source states no
measurability anywhere. -/
public theorem positiveMassSetupsOn_nonempty (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] :
    (positiveMassSetupsOn μ C).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hzero : ∀ x ∈ rangeFinset C.setup, μ (C.setup ⁻¹' {x}) = 0 := by
    intro x hx
    by_contra hne
    have hpos : 0 < massOn μ C.setup x := by
      rw [massOn]
      exact ENNReal.toReal_pos hne (measure_ne_top μ _)
    have : x ∈ positiveMassSetupsOn μ C := Finset.mem_filter.mpr ⟨hx, hpos⟩
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty x)
  -- The fibres over the realized values cover `U`.
  have hcover : (Set.univ : Set U) ⊆ ⋃ x ∈ rangeFinset C.setup, C.setup ⁻¹' {x} := by
    intro u _
    exact Set.mem_biUnion ((mem_rangeFinset C.setup (C.setup u)).mpr ⟨u, rfl⟩) rfl
  have hle : (1 : ENNReal) ≤ 0 := by
    calc (1 : ENNReal) = μ Set.univ := (measure_univ (μ := μ)).symm
      _ ≤ μ (⋃ x ∈ rangeFinset C.setup, C.setup ⁻¹' {x}) := measure_mono hcover
      _ ≤ (rangeFinset C.setup).sum (fun x => μ (C.setup ⁻¹' {x})) :=
          measure_biUnion_finset_le _ _
      _ = 0 := by rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
  simp at hle

/-- `P(the device's conclusion agrees with `h` ∣ `X = x`)`, `0` on a null fibre. -/
@[expose] public noncomputable def condAgreeOn (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) (h : U → Bool) : ℝ :=
  if massOn μ X x = 0 then 0
  else massOn μ (fun u => (X u, h u)) (x, true) / massOn μ X x

/-- The conditional expectation of a `±1`-valued function, as `2p − 1`. -/
@[expose] public noncomputable def condExpectPmOn (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) (h : U → Bool) : ℝ :=
  2 * condAgreeOn μ X x h - 1

/--
**Definition 9 over a general measure.** *"a device `(X,Y)` (weakly) infers `Γ`
with (covariance) accuracy `ε` iff `[Σ_{f ∈ π(Γ)} max_x E_P(Y f(Γ) ∣ x)] / |Γ(U)| = ε`."*

`U` is arbitrary; the finiteness is the source's own, on `Γ(U)`.

**No measurability hypothesis.** Nonemptiness of `positiveMassSetupsOn` — all
the `sup'` needs — follows from sub-additivity alone
(`positiveMassSetupsOn_nonempty`), so `Measurable C.setup` never enters. It
would have been the one condition here the source never states: the source never
has to say which sets it can weigh.

**`[FiniteRange C.setup]` is in this signature**, where the source states no
finiteness on `X(U)` for this definition. It is what makes the printed `max_x`
denote at a `Finset.sup'`: over an infinite realized setup range the maximum
need not be attained. That restriction is why `inferenceAccuracySupOn` exists —
it states the printed `max_x` as an `sSup` over the positive-mass setups and
carries no finiteness, and `accuracySupOn_eq_of_isGreatest` says it *is* the
printed maximum wherever that exists. The provenance row is `SOURCE-EXACT` on
the supremum form; this one is its finite-range instance.
-/
public noncomputable def inferenceAccuracyOn (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  if (rangeFinset Γ).card = 0 then 0
  else
    (rangeFinset Γ).sum (fun γ =>
      (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
        (fun x => condExpectPmOn μ C.setup x
          (fun u => C.concl u == probe γ (Γ u)))) /
      ((rangeFinset Γ).card : ℝ)

/-- Setup entropy of a device under `μ`. -/
@[expose] public noncomputable def setupEntropyOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] : ℝ :=
  entropyOn μ C.setup

/--
**Definition 10 over a general measure.** `1 − M_P(X₁,X₂) / [H_P(X₁) + H_P(X₂)]`.

The zero-denominator branch is a Lean totalization, not a source case, exactly as
in the finite layer.
-/
@[expose] public noncomputable def miDistinguishabilityOn (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [FiniteRange C₁.setup] [FiniteRange C₂.setup] : ℝ :=
  if setupEntropyOn μ C₁ + setupEntropyOn μ C₂ = 0 then 1
  else 1 - mutualInfoOn μ C₁.setup C₂.setup /
    (setupEntropyOn μ C₁ + setupEntropyOn μ C₂)

/--
**Definition 11.** *"the counting distinguishability of two devices is
`1 − [Σ_{x₁,x₂ : ∃u, X₁(u)=x₁, X₂(u)=x₂} 1] / (|X₁(U)| × |X₂(U)|)`."*

The printed formula names `P` in its preamble and then does not use it: the
displayed quantity counts jointly realized setup pairs. So this definition needs
**no measure at all**, only the source's countable — here finite — setup ranges.
-/
@[expose] public noncomputable def countingDistinguishabilityOn
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] : ℝ :=
  1 - ((rangeFinset (fun u => (C₁.setup u, C₂.setup u))).card : ℝ) /
    (((rangeFinset C₁.setup).card : ℝ) * ((rangeFinset C₂.setup).card : ℝ))

/--
**Wolpert 2008, Proposition 6, step 2a, over a general measure.** *"Next, since
the distinguishability is 1.0, `X₁` and `X₂` are statistically independent under
`P`."*

The equality case of Gibbs' inequality, now with `U` arbitrary. The
positive-entropy hypothesis is the source's own: Definition 10's ratio is
undefined when both setup entropies vanish.
-/
public theorem independentOn_of_miDistinguishabilityOn_eq_one
    (μ : Measure U) [IsProbabilityMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [MeasurableSpace C₁.Setup] [MeasurableSingletonClass C₁.Setup] [DecidableEq C₁.Setup]
    [MeasurableSpace C₂.Setup] [MeasurableSingletonClass C₂.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    (h₁ : Measurable C₁.setup) (h₂ : Measurable C₂.setup)
    (hH : 0 < setupEntropyOn μ C₁ + setupEntropyOn μ C₂)
    (h : miDistinguishabilityOn μ C₁ C₂ = 1) :
    IndependentOn μ C₁.setup C₂.setup := by
  rw [miDistinguishabilityOn, if_neg (ne_of_gt hH)] at h
  have hzero : mutualInfoOn μ C₁.setup C₂.setup /
      (setupEntropyOn μ C₁ + setupEntropyOn μ C₂) = 0 := by linarith
  have hM : mutualInfoOn μ C₁.setup C₂.setup = 0 :=
    (div_eq_zero_iff.mp hzero).resolve_right (ne_of_gt hH)
  exact (mutualInfoOn_eq_zero_iff μ C₁.setup C₂.setup h₁ h₂).mp hM

/-! ## Proposition 6, step 1, over a general measure

The two probes of a `Bool`-valued target are the identity and the negation, so
Definition 9's sum is `max_x E(g∣x) + max_x E(−g∣x) = max − min = |difference|`.
Nothing here is finite except the two setup values the source stipulates. -/

/-- A fibre splits over the two values of a `Bool`-valued map. -/
public theorem massOn_bool_split (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : U → α) (h : U → Bool) (hX : Measurable X) (hh : Measurable h) (x : α) :
    massOn μ (fun u => (X u, h u)) (x, true) +
      massOn μ (fun u => (X u, h u)) (x, false) = massOn μ X x := by
  classical
  have hpair : Measurable (fun u => (X u, h u)) := hX.prodMk hh
  have hmeas : ∀ b ∈ ({true, false} : Finset Bool),
      MeasurableSet ((fun u => (X u, h u)) ⁻¹' {(x, b)}) :=
    fun b _ => hpair (measurableSet_singleton _)
  have hdisj : (({true, false} : Finset Bool) : Set Bool).PairwiseDisjoint
      (fun b => (fun u => (X u, h u)) ⁻¹' {(x, b)}) := by
    intro b₁ _ b₂ _ hb
    refine Set.disjoint_left.mpr (fun u h₁ h₂ => hb ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
    exact h₁.2.symm.trans h₂.2
  have hcover : (⋃ b ∈ ({true, false} : Finset Bool),
      (fun u => (X u, h u)) ⁻¹' {(x, b)}) = X ⁻¹' {x} := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨b, -, hu, -⟩; exact hu
    · intro hu; exact ⟨h u, by cases h u <;> simp, hu, rfl⟩
  have hsum := measure_biUnion_finset hdisj hmeas (μ := μ)
  rw [hcover] at hsum
  have hreal : (μ (X ⁻¹' {x})).toReal =
      (({true, false} : Finset Bool).sum
        (fun b => μ ((fun u => (X u, h u)) ⁻¹' {(x, b)}))).toReal := by rw [hsum]
  rw [ENNReal.toReal_sum (fun b _ => measure_ne_top μ _)] at hreal
  simp only [Finset.sum_insert (by simp : (true : Bool) ∉ ({false} : Finset Bool)),
    Finset.sum_singleton] at hreal
  simpa [massOn] using hreal.symm

/-! ### Bounds, and Definition 9's supremum form

The printed `max_x E_P(Y δ(Γ) | x)` is a maximum over setup values, and
`inferenceAccuracyOn` renders it as a `Finset.sup'` — which is why that
definition carries `[FiniteRange C.setup]` even though the print states no
finiteness on `X(U)`.

Under the acceptance rule the question is what the printed formula needs in
order to denote. Conditional expectations of a `±1`-valued quantity lie in
`[-1, 1]`, so a **supremum** denotes on any setup range whose positive-mass part
is nonempty; finiteness is not what makes the expression meaningful. Nonemptiness
*is*: under an arbitrary probability measure every fibre can be null — Lebesgue
measure with the identity setup — and then there is nothing to take a maximum
over and the printed formula denotes nothing. So the hypothesis below is forced
and the finite range is not.

`positiveMassSetupsOn_nonempty` derives nonemptiness from `[FiniteRange C.setup]`
by finite sub-additivity, and that argument does not survive an uncountable
range. It is replaced here by an explicit hypothesis, which `FiniteRange`
discharges.
-/

/-- Negating the agreement predicate complements the conditional probability. -/
public theorem condAgreeOn_not (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : U → α) (h : U → Bool) (hX : Measurable X) (hh : Measurable h) {x : α}
    (hx : massOn μ X x ≠ 0) :
    condAgreeOn μ X x (fun u => !h u) = 1 - condAgreeOn μ X x h := by
  classical
  have hswap : ∀ b : Bool, massOn μ (fun u => (X u, !h u)) (x, b)
      = massOn μ (fun u => (X u, h u)) (x, !b) := by
    intro b
    have hset : (fun u => (X u, !h u)) ⁻¹' {(x, b)}
        = (fun u => (X u, h u)) ⁻¹' {(x, !b)} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
      refine and_congr Iff.rfl ?_
      cases h u <;> cases b <;> simp
    simp [massOn, hset]
  have hsplit := massOn_bool_split μ X h hX hh x
  unfold condAgreeOn
  rw [if_neg hx, if_neg hx, hswap true]
  simp only [Bool.not_true]
  field_simp
  linarith [hsplit]

public theorem condExpectPmOn_not (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : U → α) (h : U → Bool) (hX : Measurable X) (hh : Measurable h) {x : α}
    (hx : massOn μ X x ≠ 0) :
    condExpectPmOn μ X x (fun u => !h u) = -condExpectPmOn μ X x h := by
  unfold condExpectPmOn
  rw [condAgreeOn_not μ X h hX hh hx]
  ring

omit [MeasurableSpace U] in
/-- A device whose setup takes exactly two realized values has that pair as its range. -/
public theorem rangeFinset_setup_eq_pair (C : InferenceDevice.{u, v} U)
    [FiniteRange C.setup] [DecidableEq C.Setup] {a b : C.Setup}
    (ha : C.Realized a) (hb : C.Realized b)
    (hall : ∀ w : U, C.setup w = a ∨ C.setup w = b) :
    rangeFinset C.setup = {a, b} := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := (mem_rangeFinset _ x).mp hx
    rcases hall w with h | h <;> simp [h]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · obtain ⟨w, hw⟩ := ha; exact (mem_rangeFinset _ _).mpr ⟨w, hw⟩
    · obtain ⟨w, hw⟩ := hb; exact (mem_rangeFinset _ _).mpr ⟨w, hw⟩

public theorem positiveMassSetupsOn_eq_pair (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] [DecidableEq C.Setup]
    {a b : C.Setup} (ha : C.Realized a) (hb : C.Realized b)
    (hall : ∀ w : U, C.setup w = a ∨ C.setup w = b)
    (hpa : 0 < massOn μ C.setup a) (hpb : 0 < massOn μ C.setup b) :
    positiveMassSetupsOn μ C = {a, b} := by
  unfold positiveMassSetupsOn
  rw [rangeFinset_setup_eq_pair C ha hb hall]
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun h => h.1, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨Or.inl rfl, hpa⟩
  · exact ⟨Or.inr rfl, hpb⟩

omit [MeasurableSpace U] in
/-- The realized values of a conclusion function are both Booleans. -/
public theorem rangeFinset_concl (C : InferenceDevice.{u, v} U) [FiniteRange C.concl] :
    rangeFinset C.concl = ({true, false} : Finset Bool) := by
  apply Finset.Subset.antisymm
  · intro x _; cases x <;> simp
  · intro x _
    obtain ⟨w, hw⟩ := C.concl_surjective x
    exact (mem_rangeFinset _ _).mpr ⟨w, hw⟩

omit [MeasurableSpace U] in
private theorem probe_bool_true (b : Bool) : probe true b = b := by
  cases b <;> simp [probe]

omit [MeasurableSpace U] in
private theorem probe_bool_false (b : Bool) : probe false b = !b := by
  cases b <;> simp [probe]

omit [MeasurableSpace U] in
private theorem agree_probe_false (f g : U → Bool) (u : U) :
    (f u == probe false (g u)) = !(f u == g u) := by
  rw [probe_bool_false]
  cases f u <;> cases g u <;> simp

/--
**Proposition 6, step 1, over a general measure.** *"For `|X₁(U)| = |X₂(U)| = 2` we
can rewrite this as `|E_P(g ∣ X₁=1) − E_P(g ∣ X₁=−1)| / 2 · …"*, with `g ≡ Y₁Y₂`.

`U` is arbitrary. The finiteness is the source's own stipulation that the setup
takes two values, and the measurability hypotheses are what a general measure
costs: the source states none, because it never has to say which sets it can
weigh.
-/
public theorem inferenceAccuracyOn_eq_of_two_setups
    (μ : Measure U) [IsProbabilityMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [MeasurableSpace C₁.Setup] [MeasurableSingletonClass C₁.Setup] [DecidableEq C₁.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.concl]
    (h₁ : Measurable C₁.setup) (hc₁ : Measurable C₁.concl) (hc₂ : Measurable C₂.concl)
    {a b : C₁.Setup} (ha : C₁.Realized a) (hb : C₁.Realized b)
    (hall : ∀ w : U, C₁.setup w = a ∨ C₁.setup w = b)
    (hpa : 0 < massOn μ C₁.setup a) (hpb : 0 < massOn μ C₁.setup b) :
    inferenceAccuracyOn μ C₁ C₂.concl =
      |condExpectPmOn μ C₁.setup a (fun u => C₁.concl u == C₂.concl u) -
        condExpectPmOn μ C₁.setup b (fun u => C₁.concl u == C₂.concl u)| / 2 := by
  classical
  set g : U → Bool := fun u => C₁.concl u == C₂.concl u with hgdef
  have hgmeas : Measurable g := by
    have hp : Measurable (fun u => (C₁.concl u, C₂.concl u)) := hc₁.prodMk hc₂
    exact (Measurable.of_discrete (f := fun q : Bool × Bool => q.1 == q.2)).comp hp
  have hpair : positiveMassSetupsOn μ C₁ = {a, b} :=
    positiveMassSetupsOn_eq_pair μ C₁ ha hb hall hpa hpb
  have hrange : rangeFinset C₂.concl = ({true, false} : Finset Bool) :=
    rangeFinset_concl C₂
  have hEa := condExpectPmOn_not μ C₁.setup g h₁ hgmeas (ne_of_gt hpa)
  have hEb := condExpectPmOn_not μ C₁.setup g h₁ hgmeas (ne_of_gt hpb)
  have hfalse : ∀ x : C₁.Setup,
      condExpectPmOn μ C₁.setup x (fun u => C₁.concl u == probe false (C₂.concl u)) =
        condExpectPmOn μ C₁.setup x (fun u => !g u) := by
    intro x; simp only [hgdef, agree_probe_false]
  have htrue : ∀ x : C₁.Setup,
      condExpectPmOn μ C₁.setup x (fun u => C₁.concl u == probe true (C₂.concl u)) =
        condExpectPmOn μ C₁.setup x g := by
    intro x; simp only [hgdef, probe_bool_true]
  unfold inferenceAccuracyOn
  rw [if_neg (by rw [hrange]; simp)]
  rw [hrange]
  rw [Finset.sum_insert (by simp : (true : Bool) ∉ ({false} : Finset Bool)),
    Finset.sum_singleton]
  rw [sup'_eq_max_of_eq_pair _ _ hpair, sup'_eq_max_of_eq_pair _ _ hpair]
  simp only [htrue, hfalse, hEa, hEb]
  rw [max_neg_neg]
  simp only [Finset.card_insert_of_notMem (by simp : (true : Bool) ∉ ({false} : Finset Bool)),
    Finset.card_singleton]
  rcases le_total (condExpectPmOn μ C₁.setup a g) (condExpectPmOn μ C₁.setup b g) with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]
    ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]
    ring

/-! ## Proposition 6, steps 2b and 3, over a general measure -/

/-- A fibre splits over the two values of a two-valued map. -/
public theorem massOn_split_two (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} {γ : Type v'} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (W : U → α) (Z : U → γ) (hW : Measurable W) (hZ : Measurable Z)
    {a b : γ} (hne : a ≠ b) (hall : ∀ u : U, Z u = a ∨ Z u = b) (w : α) :
    massOn μ (fun u => (W u, Z u)) (w, a) + massOn μ (fun u => (W u, Z u)) (w, b)
      = massOn μ W w := by
  classical
  have hpair : Measurable (fun u => (W u, Z u)) := hW.prodMk hZ
  have hmeas : ∀ c ∈ ({a, b} : Finset γ),
      MeasurableSet ((fun u => (W u, Z u)) ⁻¹' {(w, c)}) :=
    fun c _ => hpair (measurableSet_singleton _)
  have hdisj : (({a, b} : Finset γ) : Set γ).PairwiseDisjoint
      (fun c => (fun u => (W u, Z u)) ⁻¹' {(w, c)}) := by
    intro c₁ _ c₂ _ hc
    refine Set.disjoint_left.mpr (fun u h₁ h₂ => hc ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
    exact h₁.2.symm.trans h₂.2
  have hcover : (⋃ c ∈ ({a, b} : Finset γ),
      (fun u => (W u, Z u)) ⁻¹' {(w, c)}) = W ⁻¹' {w} := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨c, -, hu, -⟩; exact hu
    · intro hu
      rcases hall u with h | h
      · exact ⟨a, Or.inl rfl, hu, h⟩
      · exact ⟨b, Or.inr rfl, hu, h⟩
  have hsum := measure_biUnion_finset hdisj hmeas (μ := μ)
  rw [hcover] at hsum
  have hreal : (μ (W ⁻¹' {w})).toReal =
      (({a, b} : Finset γ).sum
        (fun c => μ ((fun u => (W u, Z u)) ⁻¹' {(w, c)}))).toReal := by rw [hsum]
  rw [ENNReal.toReal_sum (fun c _ => measure_ne_top μ _)] at hreal
  simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton] at hreal
  simpa [massOn] using hreal.symm

/-- Masses of a two-valued setup add to one. -/
public theorem massOn_add_eq_one_of_two_setups (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U)
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup] [DecidableEq C.Setup]
    [FiniteRange C.setup] (hC : Measurable C.setup)
    {a b : C.Setup} (ha : C.Realized a) (hb : C.Realized b) (hne : a ≠ b)
    (hall : ∀ w : U, C.setup w = a ∨ C.setup w = b) :
    massOn μ C.setup a + massOn μ C.setup b = 1 := by
  have h := sum_massOn μ C.setup hC
  rw [rangeFinset_setup_eq_pair C ha hb hall] at h
  rwa [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton] at h

/-- `P(the two conclusions agree ∣ X₁ = x₁, X₂ = x₂)`. The source's `zᵢ`. -/
@[expose] public noncomputable def cellAgreeProbOn (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) : ℝ :=
  condAgreeOn μ (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂)
    (fun u => C₁.concl u == C₂.concl u)

public theorem condAgreeOn_mem (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} (X : U → α) (x : α) (h : U → Bool) :
    0 ≤ condAgreeOn μ X x h ∧ condAgreeOn μ X x h ≤ 1 := by
  unfold condAgreeOn
  by_cases hx : massOn μ X x = 0
  · rw [if_pos hx]; norm_num
  · rw [if_neg hx]
    have hpos : 0 < massOn μ X x :=
      lt_of_le_of_ne (massOn_nonneg μ X x) (Ne.symm hx)
    have hle : massOn μ (fun u => (X u, h u)) (x, true) ≤ massOn μ X x :=
      massOn_joint_le_fst μ X h x true
    exact ⟨div_nonneg (massOn_nonneg μ _ _) (le_of_lt hpos), (div_le_one hpos).mpr hle⟩

public theorem cellAgreeProbOn_mem (μ : Measure U) [IsFiniteMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    0 ≤ cellAgreeProbOn μ C₁ C₂ x₁ x₂ ∧ cellAgreeProbOn μ C₁ C₂ x₁ x₂ ≤ 1 :=
  condAgreeOn_mem μ _ _ _


/-- The printed `E_P(· ∣ x)` is confined to `[-1, 1]`, whatever the setup range.
This is what makes a supremum denote where a maximum need not exist. It is a
restatement of `condAgreeOn_mem` rather than an independent proof. -/
public theorem condExpectPmOn_mem_Icc (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} (X : U → α) (x : α) (h : U → Bool) :
    condExpectPmOn μ X x h ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := condAgreeOn_mem μ X x h
  constructor <;> · unfold condExpectPmOn; linarith
/-- The source's `z⃗`, defined from the measure. -/
@[expose] public noncomputable def prop6QuadrupleOfOn (μ : Measure U) [IsFiniteMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (a₁ b₁ : C₁.Setup) (a₂ b₂ : C₂.Setup) : Prop6Quadruple where
  z1 := cellAgreeProbOn μ C₁ C₂ a₁ a₂
  z2 := cellAgreeProbOn μ C₁ C₂ a₁ b₂
  z3 := cellAgreeProbOn μ C₁ C₂ b₁ a₂
  z4 := cellAgreeProbOn μ C₁ C₂ b₁ b₂
  z1_mem := cellAgreeProbOn_mem μ C₁ C₂ a₁ a₂
  z2_mem := cellAgreeProbOn_mem μ C₁ C₂ a₁ b₂
  z3_mem := cellAgreeProbOn_mem μ C₁ C₂ b₁ a₂
  z4_mem := cellAgreeProbOn_mem μ C₁ C₂ b₁ b₂

/-- The agreement mass of a joint cell is `zᵢ` times the cell's mass. -/
private theorem agreeMass_eq (μ : Measure U) [IsFiniteMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    massOn μ (fun u => ((C₁.setup u, C₂.setup u), C₁.concl u == C₂.concl u))
        ((x₁, x₂), true)
      = cellAgreeProbOn μ C₁ C₂ x₁ x₂ *
        massOn μ (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂) := by
  unfold cellAgreeProbOn condAgreeOn
  by_cases hx : massOn μ (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂) = 0
  · rw [if_pos hx, hx, zero_mul]
    exact le_antisymm
      (hx ▸ massOn_joint_le_fst μ (fun u => (C₁.setup u, C₂.setup u))
        (fun u => C₁.concl u == C₂.concl u) (x₁, x₂) true)
      (massOn_nonneg μ _ _)
  · rw [if_neg hx]
    field_simp

/-- **Proposition 6, step 2b, over a general measure.** The source's displayed
identity `E(g ∣ X₁ = x₁) = 2[z β + z′(1−β)] − 1`, derived from independence
rather than assumed. -/
public theorem condExpectPmOn_eq_of_independent (μ : Measure U) [IsProbabilityMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [MeasurableSpace C₁.Setup] [MeasurableSingletonClass C₁.Setup]
    [MeasurableSpace C₂.Setup] [MeasurableSingletonClass C₂.Setup]
    (h₁ : Measurable C₁.setup) (h₂ : Measurable C₂.setup)
    (hc₁ : Measurable C₁.concl) (hc₂ : Measurable C₂.concl)
    (hind : IndependentOn μ C₁.setup C₂.setup)
    {x₁ : C₁.Setup} (hx₁ : massOn μ C₁.setup x₁ ≠ 0)
    {a₂ b₂ : C₂.Setup} (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂) :
    condExpectPmOn μ C₁.setup x₁ (fun u => C₁.concl u == C₂.concl u) =
      2 * (cellAgreeProbOn μ C₁ C₂ x₁ a₂ * massOn μ C₂.setup a₂ +
        cellAgreeProbOn μ C₁ C₂ x₁ b₂ * massOn μ C₂.setup b₂) - 1 := by
  classical
  set g : U → Bool := fun u => C₁.concl u == C₂.concl u with hgdef
  have hgmeas : Measurable g := by
    have hp : Measurable (fun u => (C₁.concl u, C₂.concl u)) := hc₁.prodMk hc₂
    exact (Measurable.of_discrete (f := fun q : Bool × Bool => q.1 == q.2)).comp hp
  have hpair : Measurable (fun u => (C₁.setup u, g u)) := h₁.prodMk hgmeas
  have hsplit := massOn_split_two μ (fun u => (C₁.setup u, g u)) C₂.setup
    hpair h₂ hne₂ hall₂ (x₁, true)
  have hre : ∀ x₂ : C₂.Setup,
      massOn μ (fun u => ((C₁.setup u, g u), C₂.setup u)) ((x₁, true), x₂)
        = massOn μ (fun u => ((C₁.setup u, C₂.setup u), g u)) ((x₁, x₂), true) := by
    intro x₂
    have hset : (fun u => ((C₁.setup u, g u), C₂.setup u)) ⁻¹' {((x₁, true), x₂)}
        = (fun u => ((C₁.setup u, C₂.setup u), g u)) ⁻¹' {((x₁, x₂), true)} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
      tauto
    simp [massOn, hset]
  rw [hre a₂, hre b₂, agreeMass_eq, agreeMass_eq, hind x₁ a₂, hind x₁ b₂] at hsplit
  have hnum : massOn μ (fun u => (C₁.setup u, g u)) (x₁, true)
      = massOn μ C₁.setup x₁ *
        (cellAgreeProbOn μ C₁ C₂ x₁ a₂ * massOn μ C₂.setup a₂ +
          cellAgreeProbOn μ C₁ C₂ x₁ b₂ * massOn μ C₂.setup b₂) := by
    rw [← hsplit]; ring
  unfold condExpectPmOn condAgreeOn
  rw [if_neg hx₁, hnum]
  field_simp

public theorem cellAgreeProbOn_comm (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    cellAgreeProbOn μ C₁ C₂ x₁ x₂ = cellAgreeProbOn μ C₂ C₁ x₂ x₁ := by
  unfold cellAgreeProbOn condAgreeOn
  have hbase : massOn μ (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂)
      = massOn μ (fun u => (C₂.setup u, C₁.setup u)) (x₂, x₁) := by
    have hset : (fun u => (C₁.setup u, C₂.setup u)) ⁻¹' {(x₁, x₂)}
        = (fun u => (C₂.setup u, C₁.setup u)) ⁻¹' {(x₂, x₁)} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
      tauto
    simp [massOn, hset]
  have hjoint : massOn μ (fun u => ((C₁.setup u, C₂.setup u), C₁.concl u == C₂.concl u))
        ((x₁, x₂), true)
      = massOn μ (fun u => ((C₂.setup u, C₁.setup u), C₂.concl u == C₁.concl u))
        ((x₂, x₁), true) := by
    have hset : (fun u => ((C₁.setup u, C₂.setup u), C₁.concl u == C₂.concl u)) ⁻¹'
          {((x₁, x₂), true)}
        = (fun u => ((C₂.setup u, C₁.setup u), C₂.concl u == C₁.concl u)) ⁻¹'
          {((x₂, x₁), true)} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h2, h1⟩, by cases hu₁ : C₁.concl u <;> cases hu₂ : C₂.concl u <;> simp_all⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h2, h1⟩, by cases hu₁ : C₁.concl u <;> cases hu₂ : C₂.concl u <;> simp_all⟩
    simp [massOn, hset]
  rw [hbase, hjoint]

public theorem IndependentOn.symm (μ : Measure U) {α : Type v} {β : Type v'}
    {X : U → α} {Y : U → β} (h : IndependentOn μ X Y) : IndependentOn μ Y X := by
  intro b a
  have hset : (fun u => (Y u, X u)) ⁻¹' {(b, a)} = (fun u => (X u, Y u)) ⁻¹' {(a, b)} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    tauto
  rw [show massOn μ (fun u => (Y u, X u)) (b, a)
      = massOn μ (fun u => (X u, Y u)) (a, b) by simp [massOn, hset], h a b]
  ring

/--
**Proposition 6 over a general measure.** *"Then
`ε₁ε₂ ≤ max_{z⃗ ∈ H} |αβ[k(z⃗)]² + αk(z⃗)m(z⃗) + βk(z⃗)n(z⃗) + m(z⃗)n(z⃗)|`."*

Proved in the sharper form the source's own proof establishes: the product of the
two accuracies **equals** that expression at the realized quadruple. `U` is
arbitrary — no `Fintype`, no `FinPMF`.
-/
public theorem prop6_product_eqOn (μ : Measure U) [IsProbabilityMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [MeasurableSpace C₁.Setup] [MeasurableSingletonClass C₁.Setup] [DecidableEq C₁.Setup]
    [MeasurableSpace C₂.Setup] [MeasurableSingletonClass C₂.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    [FiniteRange C₁.concl] [FiniteRange C₂.concl]
    (h₁ : Measurable C₁.setup) (h₂ : Measurable C₂.setup)
    (hc₁ : Measurable C₁.concl) (hc₂ : Measurable C₂.concl)
    {a₁ b₁ : C₁.Setup} {a₂ b₂ : C₂.Setup}
    (ha₁ : C₁.Realized a₁) (hb₁ : C₁.Realized b₁) (hne₁ : a₁ ≠ b₁)
    (hall₁ : ∀ w : U, C₁.setup w = a₁ ∨ C₁.setup w = b₁)
    (hpa₁ : 0 < massOn μ C₁.setup a₁) (hpb₁ : 0 < massOn μ C₁.setup b₁)
    (ha₂ : C₂.Realized a₂) (hb₂ : C₂.Realized b₂) (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂)
    (hpa₂ : 0 < massOn μ C₂.setup a₂) (hpb₂ : 0 < massOn μ C₂.setup b₂)
    (hind : IndependentOn μ C₁.setup C₂.setup) :
    inferenceAccuracyOn μ C₁ C₂.concl * inferenceAccuracyOn μ C₂ C₁.concl =
      prop6Expr (massOn μ C₁.setup a₁) (massOn μ C₂.setup a₂)
        (prop6QuadrupleOfOn μ C₁ C₂ a₁ b₁ a₂ b₂) := by
  have hsum₂ := massOn_add_eq_one_of_two_setups μ C₂ h₂ ha₂ hb₂ hne₂ hall₂
  have hsum₁ := massOn_add_eq_one_of_two_setups μ C₁ h₁ ha₁ hb₁ hne₁ hall₁
  rw [inferenceAccuracyOn_eq_of_two_setups μ C₁ C₂ h₁ hc₁ hc₂ ha₁ hb₁ hall₁ hpa₁ hpb₁,
    inferenceAccuracyOn_eq_of_two_setups μ C₂ C₁ h₂ hc₂ hc₁ ha₂ hb₂ hall₂ hpa₂ hpb₂,
    condExpectPmOn_eq_of_independent μ C₁ C₂ h₁ h₂ hc₁ hc₂ hind (ne_of_gt hpa₁) hne₂ hall₂,
    condExpectPmOn_eq_of_independent μ C₁ C₂ h₁ h₂ hc₁ hc₂ hind (ne_of_gt hpb₁) hne₂ hall₂,
    condExpectPmOn_eq_of_independent μ C₂ C₁ h₂ h₁ hc₂ hc₁ hind.symm (ne_of_gt hpa₂) hne₁ hall₁,
    condExpectPmOn_eq_of_independent μ C₂ C₁ h₂ h₁ hc₂ hc₁ hind.symm (ne_of_gt hpb₂) hne₁ hall₁,
    ← cellAgreeProbOn_comm μ C₁ C₂ a₁ a₂, ← cellAgreeProbOn_comm μ C₁ C₂ b₁ a₂,
    ← cellAgreeProbOn_comm μ C₁ C₂ a₁ b₂, ← cellAgreeProbOn_comm μ C₁ C₂ b₁ b₂]
  have hb₁eq : massOn μ C₁.setup b₁ = 1 - massOn μ C₁.setup a₁ := by linarith
  have hb₂eq : massOn μ C₂.setup b₂ = 1 - massOn μ C₂.setup a₂ := by linarith
  rw [hb₁eq, hb₂eq]
  unfold prop6Expr prop6QuadrupleOfOn Prop6Quadruple.k Prop6Quadruple.m Prop6Quadruple.n
  refine abs_div_two_mul_abs_div_two ?_
  ring

/--
**Proposition 6, from the premise the source prints, over a general measure.**

*"Let `P` be a probability measure over `U`, and `C₁` and `C₂` two devices whose
mutual information distinguishability is 1, where `X₁(U) = X₂(U) = 𝔹` … if
`α = β = 1/2`, then `ε₁ε₂ ≤ 1/4`."*

`U` is arbitrary. No step of the source's proof is assumed: step 2a is
`independentOn_of_miDistinguishabilityOn_eq_one`, the equality case of Gibbs;
step 2b is `condExpectPmOn_eq_of_independent`; steps 1 and 3 are
`inferenceAccuracyOn_eq_of_two_setups` and `prop6Expr_half_closed`.
-/
public theorem prop6_half_of_miDistinguishabilityOn_eq_one
    (μ : Measure U) [IsProbabilityMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [MeasurableSpace C₁.Setup] [MeasurableSingletonClass C₁.Setup] [DecidableEq C₁.Setup]
    [MeasurableSpace C₂.Setup] [MeasurableSingletonClass C₂.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    [FiniteRange C₁.concl] [FiniteRange C₂.concl]
    (h₁ : Measurable C₁.setup) (h₂ : Measurable C₂.setup)
    (hc₁ : Measurable C₁.concl) (hc₂ : Measurable C₂.concl)
    {a₁ b₁ : C₁.Setup} {a₂ b₂ : C₂.Setup}
    (ha₁ : C₁.Realized a₁) (hb₁ : C₁.Realized b₁) (hne₁ : a₁ ≠ b₁)
    (hall₁ : ∀ w : U, C₁.setup w = a₁ ∨ C₁.setup w = b₁)
    (ha₂ : C₂.Realized a₂) (hb₂ : C₂.Realized b₂) (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂)
    (hα : massOn μ C₁.setup a₁ = 1 / 2) (hβ : massOn μ C₂.setup a₂ = 1 / 2)
    (hH : 0 < setupEntropyOn μ C₁ + setupEntropyOn μ C₂)
    (hmi : miDistinguishabilityOn μ C₁ C₂ = 1) :
    inferenceAccuracyOn μ C₁ C₂.concl * inferenceAccuracyOn μ C₂ C₁.concl ≤ 1 / 4 := by
  have hsum₁ := massOn_add_eq_one_of_two_setups μ C₁ h₁ ha₁ hb₁ hne₁ hall₁
  have hsum₂ := massOn_add_eq_one_of_two_setups μ C₂ h₂ ha₂ hb₂ hne₂ hall₂
  have hpa₁ : 0 < massOn μ C₁.setup a₁ := by rw [hα]; norm_num
  have hpb₁ : 0 < massOn μ C₁.setup b₁ := by rw [hα] at hsum₁; linarith
  have hpa₂ : 0 < massOn μ C₂.setup a₂ := by rw [hβ]; norm_num
  have hpb₂ : 0 < massOn μ C₂.setup b₂ := by rw [hβ] at hsum₂; linarith
  have hind := independentOn_of_miDistinguishabilityOn_eq_one μ C₁ C₂ h₁ h₂ hH hmi
  rw [prop6_product_eqOn μ C₁ C₂ h₁ h₂ hc₁ hc₂ ha₁ hb₁ hne₁ hall₁ hpa₁ hpb₁
    ha₂ hb₂ hne₂ hall₂ hpa₂ hpb₂ hind, hα, hβ]
  exact prop6Expr_half_le_quarter _


/-! ### A finite-range map partitions a measurable set

The workhorse for Proposition 8 at general measure. `FinPMF`'s version of this is
`Finset.sum_fiberwise`; here the fibres are measurable sets and the sum is over
`μ`, so it needs the partition to be genuinely disjoint and measurable. That
requirement is the whole reason the general-measure form of Propositions 8 and 11
carries measurability where the printed statement carries none.
-/

/-- **`μ(S) = Σ_γ μ(S ∩ Γ⁻¹(γ))`** over the realized range of a finite-range map. -/
public theorem measure_sum_fiber (μ : Measure U) [IsFiniteMeasure μ]
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Γ : U → G) [FiniteRange Γ] (hΓ : Measurable Γ)
    {S : Set U} (hS : MeasurableSet S) :
    (rangeFinset Γ).sum (fun γ => (μ (S ∩ Γ ⁻¹' {γ})).toReal) = (μ S).toReal := by
  classical
  have hcover : S = ⋃ γ ∈ rangeFinset Γ, (S ∩ Γ ⁻¹' {γ}) := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop, mem_rangeFinset]
    constructor
    · intro hu; exact ⟨Γ u, ⟨u, rfl⟩, hu, rfl⟩
    · rintro ⟨γ, -, hu, -⟩; exact hu
  have hdisj : (rangeFinset Γ : Set G).PairwiseDisjoint (fun γ => S ∩ Γ ⁻¹' {γ}) := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr ?_
    intro u ha hb
    exact hab (ha.2.symm.trans hb.2)
  have hmeas : ∀ γ ∈ rangeFinset Γ, MeasurableSet (S ∩ Γ ⁻¹' {γ}) :=
    fun γ _ => hS.inter (hΓ (measurableSet_singleton γ))
  have hsum : μ S = ∑ γ ∈ rangeFinset Γ, μ (S ∩ Γ ⁻¹' {γ}) := by
    conv_lhs => rw [hcover]
    exact measure_biUnion_finset hdisj hmeas
  rw [hsum, ENNReal.toReal_sum (fun γ _ => measure_ne_top μ _)]


/-- The mass of the agreement set for probe `γ`, split along the conclusion.

On the `Y = true` part of a fibre the device agrees with `δ_γ` exactly where
`Γ = γ`; on the `Y = false` part, exactly where `Γ ≠ γ`. That asymmetry — one
value against the rest — is what produces the `2 − |Γ(U)|` of Proposition 8. -/
public theorem massOn_agree_probe (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (X : U → α) (hX : Measurable X) (Y : U → Bool) (hY : Measurable Y)
    (Γ : U → G) (hΓ : Measurable Γ) (x : α) (γ : G) :
    (μ ((X ⁻¹' {x} ∩ Y ⁻¹' {true}) ∩ Γ ⁻¹' {γ})).toReal
        + (μ (X ⁻¹' {x} ∩ Y ⁻¹' {false})).toReal
        - (μ ((X ⁻¹' {x} ∩ Y ⁻¹' {false}) ∩ Γ ⁻¹' {γ})).toReal
      = (μ (X ⁻¹' {x} ∩ (fun u => Y u == probe γ (Γ u)) ⁻¹' {true})).toReal := by
  classical
  have hFT : MeasurableSet (X ⁻¹' {x} ∩ Y ⁻¹' {true}) :=
    (hX (measurableSet_singleton x)).inter (hY (measurableSet_singleton true))
  have hFF : MeasurableSet (X ⁻¹' {x} ∩ Y ⁻¹' {false}) :=
    (hX (measurableSet_singleton x)).inter (hY (measurableSet_singleton false))
  have hG : MeasurableSet (Γ ⁻¹' {γ}) := hΓ (measurableSet_singleton γ)
  -- The agreement set is the `true` part inside the `Γ = γ` fibre together with
  -- the `false` part outside it.
  have hsplit : X ⁻¹' {x} ∩ (fun u => Y u == probe γ (Γ u)) ⁻¹' {true}
      = ((X ⁻¹' {x} ∩ Y ⁻¹' {true}) ∩ Γ ⁻¹' {γ})
        ∪ ((X ⁻¹' {x} ∩ Y ⁻¹' {false}) \ Γ ⁻¹' {γ}) := by
    ext u
    by_cases hb : Y u = true <;> by_cases hg : Γ u = γ <;>
      simp [probe, hb, hg, Set.mem_preimage, Set.mem_singleton_iff,
        Bool.eq_false_iff]
  have hdisj : Disjoint ((X ⁻¹' {x} ∩ Y ⁻¹' {true}) ∩ Γ ⁻¹' {γ})
      ((X ⁻¹' {x} ∩ Y ⁻¹' {false}) \ Γ ⁻¹' {γ}) := by
    refine Set.disjoint_left.mpr ?_
    rintro u ⟨⟨-, ht⟩, -⟩ ⟨⟨-, hf⟩, -⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ht hf
    rw [ht] at hf
    exact Bool.noConfusion hf
  have hadd : μ ((X ⁻¹' {x} ∩ Y ⁻¹' {false}) ∩ Γ ⁻¹' {γ})
      + μ ((X ⁻¹' {x} ∩ Y ⁻¹' {false}) \ Γ ⁻¹' {γ})
      = μ (X ⁻¹' {x} ∩ Y ⁻¹' {false}) := measure_inter_add_sdiff _ hG
  have haddR : (μ ((X ⁻¹' {x} ∩ Y ⁻¹' {false}) ∩ Γ ⁻¹' {γ})).toReal
      + (μ ((X ⁻¹' {x} ∩ Y ⁻¹' {false}) \ Γ ⁻¹' {γ})).toReal
      = (μ (X ⁻¹' {x} ∩ Y ⁻¹' {false})).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hadd]
  rw [hsplit, measure_union hdisj ((hFF.diff hG)),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  linarith

omit [MeasurableSingletonClass α] in
/-- The joint mass at `(x, true)` as the measure of an intersection. -/
public theorem massOn_joint_true (μ : Measure U) {α : Type v} (X : U → α) (h : U → Bool)
    (x : α) :
    massOn μ (fun u => (X u, h u)) (x, true)
      = (μ (X ⁻¹' {x} ∩ h ⁻¹' {true})).toReal := by
  unfold massOn
  congr 2
  ext u
  simp [Prod.ext_iff]

/-- **The identity carrying Proposition 8, at general measure.** Summing the
conditional expectations of every realized probe at one setup value returns
`(2 − |Γ(U)|)` times the conditional expectation of the conclusion. This is
`sum_boolPm_probe` transported across the `Γ`-partition of the fibre — and the
transport is what needs the measurability. -/
public theorem sum_condExpectPmOn_probe (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (X : U → α) (hX : Measurable X) (Y : U → Bool) (hY : Measurable Y)
    (Γ : U → G) [FiniteRange Γ] (hΓ : Measurable Γ) {x : α} (hx : massOn μ X x ≠ 0) :
    (rangeFinset Γ).sum
        (fun γ => condExpectPmOn μ X x (fun u => Y u == probe γ (Γ u)))
      = (2 - ((rangeFinset Γ).card : ℝ)) * condExpectPmOn μ X x Y := by
  classical
  set w := massOn μ X x with hw
  have hwpos : 0 < w := lt_of_le_of_ne (massOn_nonneg μ X x) (Ne.symm hx)
  set FT := X ⁻¹' {x} ∩ Y ⁻¹' {true} with hFTdef
  set FF := X ⁻¹' {x} ∩ Y ⁻¹' {false} with hFFdef
  have hFT : MeasurableSet FT :=
    (hX (measurableSet_singleton x)).inter (hY (measurableSet_singleton true))
  have hFF : MeasurableSet FF :=
    (hX (measurableSet_singleton x)).inter (hY (measurableSet_singleton false))
  have hterm : ∀ γ ∈ rangeFinset Γ,
      condExpectPmOn μ X x (fun u => Y u == probe γ (Γ u))
        = (2 / w) * (μ (FT ∩ Γ ⁻¹' {γ})).toReal + (2 / w) * (μ FF).toReal
          - (2 / w) * (μ (FF ∩ Γ ⁻¹' {γ})).toReal - 1 := by
    intro γ _
    unfold condExpectPmOn condAgreeOn
    rw [if_neg hx, massOn_joint_true, ← massOn_agree_probe μ X hX Y hY Γ hΓ x γ, ← hw]
    field_simp
    ring
  have hsumT : (rangeFinset Γ).sum (fun γ => (μ (FT ∩ Γ ⁻¹' {γ})).toReal) = (μ FT).toReal :=
    measure_sum_fiber μ Γ hΓ hFT
  have hsumF : (rangeFinset Γ).sum (fun γ => (μ (FF ∩ Γ ⁻¹' {γ})).toReal) = (μ FF).toReal :=
    measure_sum_fiber μ Γ hΓ hFF
  have hsplit : (μ FT).toReal + (μ FF).toReal = w := by
    have h2 := massOn_bool_split μ X Y hX hY x
    rw [massOn_joint_true] at h2
    have hFFeq : massOn μ (fun u => (X u, Y u)) (x, false) = (μ FF).toReal := by
      unfold massOn; congr 2; ext u; simp [hFFdef, Prod.ext_iff]
    rw [hFFeq, ← hw] at h2
    exact h2
  have hconcl : condExpectPmOn μ X x Y = 2 * ((μ FT).toReal / w) - 1 := by
    unfold condExpectPmOn condAgreeOn
    rw [if_neg hx, massOn_joint_true, ← hw]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hsumT, hsumF, hconcl]
  field_simp
  nlinarith [hsplit, hwpos]


/--
**Wolpert 2018, Proposition 8, over a general measure.** *"Let `P` be a
probability measure over `U`, `D = (X, Y)` a device, and `Γ` a function over `U`
with finite `|Γ(U)|`. Then `cov(D, Γ) ≥ (2 − |Γ(U)|) max_x E_P(Y ∣ x) / |Γ(U)|`."*

`inferenceAccuracy_ge` is this over a `FinPMF`, hence over a **finite** `U`. Here
`U` is arbitrary and `P` is any probability measure — the printed quantification
— at the cost of measurability, which the source does not state and which
`inferenceAccuracyOn` was deliberately built to avoid needing. Neither form
dominates the other, and the ledger records both.

The sign of `2 − |Γ(U)|` is irrelevant to the argument: the bound comes from
`Finset.le_sup'` applied under a sum, so it holds whichever way the factor points.
-/
public theorem inferenceAccuracyOn_ge (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [MeasurableSpace C.Setup]
    [MeasurableSingletonClass C.Setup] [FiniteRange C.setup] (hC : Measurable C.setup)
    (hY : Measurable C.concl)
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Γ : U → G) [FiniteRange Γ] (hΓ : Measurable Γ)
    (hne : (rangeFinset Γ).card ≠ 0) :
    ((2 - ((rangeFinset Γ).card : ℝ)) *
        (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
          (fun x => condExpectPmOn μ C.setup x C.concl)) / ((rangeFinset Γ).card : ℝ)
      ≤ inferenceAccuracyOn μ C Γ := by
  classical
  have hcardpos : (0 : ℝ) < ((rangeFinset Γ).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hne
  -- The supremum is attained, at a setup value of positive mass.
  obtain ⟨x₀, hx₀mem, hx₀⟩ := Finset.exists_mem_eq_sup' (positiveMassSetupsOn_nonempty μ C)
    (fun x => condExpectPmOn μ C.setup x C.concl)
  have hmass : massOn μ C.setup x₀ ≠ 0 := by
    have hm := Finset.mem_filter.mp hx₀mem
    exact ne_of_gt hm.2
  -- At that value the printed identity turns the sum into the bound.
  have hid := sum_condExpectPmOn_probe μ C.setup hC C.concl hY Γ hΓ hmass
  unfold inferenceAccuracyOn
  rw [if_neg hne]
  have key : (2 - ((rangeFinset Γ).card : ℝ)) *
      (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
        (fun x => condExpectPmOn μ C.setup x C.concl)
      ≤ (rangeFinset Γ).sum (fun γ =>
          (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
            (fun x => condExpectPmOn μ C.setup x (fun u => C.concl u == probe γ (Γ u)))) := by
    rw [hx₀, ← hid]
    refine Finset.sum_le_sum (fun γ _ => ?_)
    exact Finset.le_sup' (fun x => condExpectPmOn μ C.setup x
      (fun u => C.concl u == probe γ (Γ u))) hx₀mem
  gcongr


/--
**Wolpert 2018, Proposition 11, over a general measure.** The printed `≤ max`
shape, with `U` arbitrary and `P` any probability measure.

`prop11_of_independent` is this over a `FinPMF`. The general form costs nothing
extra beyond what `prop6_product_eqOn` already carries, because that theorem
identifies the realized product with the polynomial rather than bounding it — so
the supremum only has to exist, which `prop6Expr_bddAbove` supplies, `M` being
the unit hypercube `Prop6Quadruple`.
-/
public theorem prop11_of_independentOn (μ : Measure U) [IsProbabilityMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [MeasurableSpace C₁.Setup] [MeasurableSingletonClass C₁.Setup] [DecidableEq C₁.Setup]
    [MeasurableSpace C₂.Setup] [MeasurableSingletonClass C₂.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    [FiniteRange C₁.concl] [FiniteRange C₂.concl]
    (h₁ : Measurable C₁.setup) (h₂ : Measurable C₂.setup)
    (hc₁ : Measurable C₁.concl) (hc₂ : Measurable C₂.concl)
    {a₁ b₁ : C₁.Setup} {a₂ b₂ : C₂.Setup}
    (ha₁ : C₁.Realized a₁) (hb₁ : C₁.Realized b₁) (hne₁ : a₁ ≠ b₁)
    (hall₁ : ∀ w : U, C₁.setup w = a₁ ∨ C₁.setup w = b₁)
    (hpa₁ : 0 < massOn μ C₁.setup a₁) (hpb₁ : 0 < massOn μ C₁.setup b₁)
    (ha₂ : C₂.Realized a₂) (hb₂ : C₂.Realized b₂) (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂)
    (hpa₂ : 0 < massOn μ C₂.setup a₂) (hpb₂ : 0 < massOn μ C₂.setup b₂)
    (hind : IndependentOn μ C₁.setup C₂.setup) :
    inferenceAccuracyOn μ C₁ C₂.concl * inferenceAccuracyOn μ C₂ C₁.concl ≤
      ⨆ z : Prop6Quadruple,
        prop6Expr (massOn μ C₁.setup a₁) (massOn μ C₂.setup a₂) z := by
  rw [prop6_product_eqOn μ C₁ C₂ h₁ h₂ hc₁ hc₂ ha₁ hb₁ hne₁ hall₁ hpa₁ hpb₁
    ha₂ hb₂ hne₂ hall₂ hpa₂ hpb₂ hind]
  exact le_ciSup (prop6Expr_bddAbove _ _) _


/-! ### Definition 9 and Proposition 8 without a finite setup range -/

/-- The positive-mass setup values, as a **set**: no finiteness. -/
@[expose] public def positiveMassSetOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) : Set C.Setup :=
  {x | 0 < massOn μ C.setup x}

/-- The printed `max_x` as a supremum over that set. Bounded because the
conditional expectations are, so this denotes whenever the set is nonempty. -/
@[expose] public noncomputable def accuracySupOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (h : U → Bool) : ℝ :=
  sSup ((fun x => condExpectPmOn μ C.setup x h) '' positiveMassSetOn μ C)

public theorem accuracySup_bddAbove (μ : Measure U) [IsFiniteMeasure μ]
    (C : InferenceDevice.{u, v} U) (h : U → Bool) :
    BddAbove ((fun x => condExpectPmOn μ C.setup x h) '' positiveMassSetOn μ C) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x, _, rfl⟩
  exact (condExpectPmOn_mem_Icc μ C.setup x h).2

public theorem le_accuracySupOn (μ : Measure U) [IsFiniteMeasure μ]
    (C : InferenceDevice.{u, v} U) (h : U → Bool) {x : C.Setup}
    (hx : 0 < massOn μ C.setup x) :
    condExpectPmOn μ C.setup x h ≤ accuracySupOn μ C h :=
  le_csSup (accuracySup_bddAbove μ C h) ⟨x, hx, rfl⟩

/-- **Definition 9's covariance accuracy over an arbitrary setup range.** The
`Finset.sup'` of `inferenceAccuracyOn` becomes an `sSup`; nothing else moves. -/
@[expose] public noncomputable def inferenceAccuracySupOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  if (rangeFinset Γ).card = 0 then 0
  else
    (rangeFinset Γ).sum (fun γ =>
      accuracySupOn μ C (fun u => C.concl u == probe γ (Γ u))) /
      ((rangeFinset Γ).card : ℝ)



/-- **The printed `max` and the `sSup` agree whenever the maximum exists**, on
any setup range. `accuracySupOn_eq_sup'` is the finite instance of this; an
infinite setup range can still attain its maximum, and then the supremum form is
the printed object rather than a normalization of it. -/
public theorem accuracySupOn_eq_of_isGreatest (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (h : U → Bool) {m : ℝ}
    (hm : IsGreatest ((fun x => condExpectPmOn μ C.setup x h) ''
      positiveMassSetOn μ C) m) :
    accuracySupOn μ C h = m :=
  hm.csSup_eq

/-- On a finite setup range the two forms are the same object, so the widening
adds reach and changes nothing already proved. `positiveMassSetOn` and
`positiveMassSetupsOn` have the same members: a value of positive mass has a
nonempty fibre and is therefore realized. -/
public theorem accuracySupOn_eq_sup' (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] [DecidableEq C.Setup]
    (h : U → Bool) :
    accuracySupOn μ C h
      = (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
          (fun x => condExpectPmOn μ C.setup x h) := by
  classical
  rw [Finset.sup'_eq_csSup_image]
  unfold accuracySupOn
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, positiveMassSetupsOn]
    refine ⟨?_, hx⟩
    -- Positive mass forces a nonempty fibre, hence a realized value.
    by_contra hmem
    have hempty : C.setup ⁻¹' {x} = (∅ : Set U) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hu
      exact hmem ((mem_rangeFinset C.setup x).mpr ⟨u, hu⟩)
    rw [positiveMassSetOn, Set.mem_ofPred_eq, massOn, hempty] at hx
    simp at hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩

/--
**Wolpert 2018, Proposition 8, with no finiteness on the setup range.**

The printed hypothesis is *"let `P` be a probability measure over `U`"* with only
`Γ(U)` finite, and `inferenceAccuracyOn_ge` did not reach it: it carried
`[FiniteRange C.setup]`, which the print does not state. Here that is replaced by
`hne`, the existence of one positive-mass setup value — which is exactly what the
printed `max_x` needs in order to denote, and which `[FiniteRange C.setup]`
implies under a probability measure.

**Attainment is not needed, and that is the one non-obvious point.** The finite
proof picks a value `x₀` attaining the maximum and uses the identity there. With
a supremum no such `x₀` need exist, and the printed factor `2 − |Γ(U)|` is
**negative** once `|Γ(U)| ≥ 3`, so pulling it through a supremum flips it to an
infimum. It still works: for `c < 0`, `sup (c · f) = c · inf f ≥ c · sup f`, so
the bound survives the flip rather than being destroyed by it. For `c ≥ 0` it is
the ordinary `sup (c · f) = c · sup f`.
-/
public theorem inferenceAccuracySupOn_ge (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [MeasurableSpace C.Setup]
    [MeasurableSingletonClass C.Setup] (hC : Measurable C.setup)
    (hY : Measurable C.concl)
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Γ : U → G) [FiniteRange Γ] (hΓ : Measurable Γ)
    (hne : ∃ x : C.Setup, 0 < massOn μ C.setup x)
    (hcard : (rangeFinset Γ).card ≠ 0) :
    ((2 - ((rangeFinset Γ).card : ℝ)) * accuracySupOn μ C C.concl) /
        ((rangeFinset Γ).card : ℝ)
      ≤ inferenceAccuracySupOn μ C Γ := by
  classical
  have hcardpos : (0 : ℝ) < ((rangeFinset Γ).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcard
  set k : ℝ := ((rangeFinset Γ).card : ℝ) with hk
  unfold inferenceAccuracySupOn
  rw [if_neg hcard]
  set S : ℝ := accuracySupOn μ C C.concl with hS
  set T : ℝ := (rangeFinset Γ).sum
    (fun γ => accuracySupOn μ C (fun u => C.concl u == probe γ (Γ u))) with hT
  -- At any positive-mass setup value the printed identity bounds `T` from below.
  have hpoint : ∀ x : C.Setup, 0 < massOn μ C.setup x →
      (2 - k) * condExpectPmOn μ C.setup x C.concl ≤ T := by
    intro x hx
    rw [hT, ← sum_condExpectPmOn_probe μ C.setup hC C.concl hY Γ hΓ (ne_of_gt hx)]
    exact Finset.sum_le_sum (fun γ _ => le_accuracySupOn μ C _ hx)
  have key : (2 - k) * S ≤ T := by
    rcases le_or_gt (2 - k) 0 with hc | hc
    · -- The factor is nonpositive, so the supremum flips to a lower bound and
      -- one positive-mass value suffices. This is the `|Γ(U)| ≥ 2` case.
      obtain ⟨x, hx⟩ := hne
      have hfS : condExpectPmOn μ C.setup x C.concl ≤ S := le_accuracySupOn μ C _ hx
      nlinarith [hpoint x hx]
    · -- The factor is positive, so every value of the image is below `T / (2 - k)`
      -- and the supremum is too. This is `|Γ(U)| = 1`.
      obtain ⟨x₀, hx₀⟩ := hne
      have hbound : S ≤ T / (2 - k) := by
        refine csSup_le ⟨_, ⟨x₀, hx₀, rfl⟩⟩ ?_
        rintro y ⟨x, hx, rfl⟩
        rw [le_div_iff₀ hc]
        have := hpoint x hx
        linarith
      rw [← le_div_iff₀' hc]
      exact hbound
  rw [← hk]
  gcongr


/-! ### `cov = 1` and weak inference, over a general measure

2018 states after its Definition 6: *"Clearly `cov(D, Γ) ≤ 1.0`, and if `P` is
nowhere 0, then `cov(D, Γ) = 1.0` iff `D > Γ`."* Both halves were proved only
over a `FinPMF`, hence `[Fintype U]`, where the print says *"probability
measure"*. They are proved here at general measure.

**The nowhere-zero hypothesis is doing real work, and more of it than in the
finite case.** Over a general measure `cov = 1` forces the device to agree with
the probe *almost everywhere* on a fibre, not everywhere, while `WeaklyInfers`
quantifies over every point of the fibre. The gap is exactly a null set, so the
converse needs every nonempty set to be non-null. `hatom` below — every
singleton has positive measure — is the general form of the printed *"`P` is
nowhere 0"*, and it is what collapses "almost everywhere" back to "everywhere".
-/

/-- **`cov ≤ 1` at general measure, with no hypothesis beyond the definition's.**
The printed *"clearly"*. -/
public theorem inferenceAccuracyOn_le_one (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] :
    inferenceAccuracyOn μ C Γ ≤ 1 := by
  classical
  unfold inferenceAccuracyOn
  split
  · norm_num
  · rename_i hne
    have hcardpos : (0 : ℝ) < ((rangeFinset Γ).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hne
    rw [div_le_one hcardpos]
    calc (rangeFinset Γ).sum (fun γ =>
            (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
              (fun x => condExpectPmOn μ C.setup x
                (fun u => C.concl u == probe γ (Γ u))))
        ≤ (rangeFinset Γ).sum (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum (fun γ _ => ?_)
          refine Finset.sup'_le _ _ (fun x _ => ?_)
          exact (condExpectPmOn_mem_Icc μ C.setup x _).2
    _ = ((rangeFinset Γ).card : ℝ) := by simp



/-- **Conditional expectation `1` is agreement on the whole fibre**, once every
singleton has positive measure. Without that hypothesis it is agreement only up
to a null set, which is the entire reason the printed statement carries
*"if `P` is nowhere 0"*. -/
public theorem condExpectPmOn_eq_one_iff_forall (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : U → α) (hX : Measurable X) (h : U → Bool) (hh : Measurable h) (x : α)
    (hatom : ∀ u : U, μ {u} ≠ 0) (hne : ∃ w, X w = x) :
    condExpectPmOn μ X x h = 1 ↔ ∀ w, X w = x → h w = true := by
  classical
  have hfib : MeasurableSet (X ⁻¹' {x}) := hX (measurableSet_singleton x)
  have htrue : MeasurableSet (h ⁻¹' {true}) := hh (measurableSet_singleton true)
  have hfalse : MeasurableSet (h ⁻¹' {false}) := hh (measurableSet_singleton false)
  -- The fibre is not null: it contains a point, and points are not null.
  obtain ⟨w₀, hw₀⟩ := hne
  have hmasspos : μ (X ⁻¹' {x}) ≠ 0 := by
    intro h0
    exact hatom w₀ (measure_mono_null (by simpa using hw₀) h0)
  have hdiff : X ⁻¹' {x} \ h ⁻¹' {true} = X ⁻¹' {x} ∩ h ⁻¹' {false} := by
    ext u
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, hnt⟩
      exact ⟨hu, by cases hb : h u with | true => exact absurd hb hnt | false => rfl⟩
    · rintro ⟨hu, hf⟩
      exact ⟨hu, by simp [hf]⟩
  have hsplit : μ (X ⁻¹' {x}) =
      μ (X ⁻¹' {x} ∩ h ⁻¹' {true}) + μ (X ⁻¹' {x} ∩ h ⁻¹' {false}) := by
    rw [← hdiff]
    exact (measure_inter_add_sdiff (X ⁻¹' {x}) htrue).symm
  have hmassne : massOn μ X x ≠ 0 := by
    rw [massOn]
    exact ENNReal.toReal_ne_zero.mpr ⟨hmasspos, measure_ne_top μ _⟩
  constructor
  · intro heq
    -- `condAgreeOn = 1`, so the joint mass exhausts the fibre.
    have hagree : condAgreeOn μ X x h = 1 := by
      unfold condExpectPmOn at heq; linarith
    rw [condAgreeOn, if_neg hmassne, div_eq_one_iff_eq hmassne, massOn_joint_true] at hagree
    have hjoint : μ (X ⁻¹' {x} ∩ h ⁻¹' {true}) = μ (X ⁻¹' {x}) :=
      (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp hagree
    have hnull : μ (X ⁻¹' {x} ∩ h ⁻¹' {false}) = 0 := by
      have hreal : (μ (X ⁻¹' {x})).toReal
          = (μ (X ⁻¹' {x} ∩ h ⁻¹' {true})).toReal
            + (μ (X ⁻¹' {x} ∩ h ⁻¹' {false})).toReal := by
        conv_lhs => rw [hsplit]
        exact ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)
      rw [hjoint] at hreal
      have hzero : (μ (X ⁻¹' {x} ∩ h ⁻¹' {false})).toReal = 0 := by linarith
      exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right (measure_ne_top μ _)
    intro w hw
    by_contra hfw
    refine hatom w (measure_mono_null ?_ hnull)
    simp only [Set.singleton_subset_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨hw, by simpa using hfw⟩
  · intro hall
    have hempty : X ⁻¹' {x} ∩ h ⁻¹' {false} = ∅ := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hu
      simp [hall u hu]
    have hjoint : μ (X ⁻¹' {x} ∩ h ⁻¹' {true}) = μ (X ⁻¹' {x}) := by
      rw [hsplit, hempty, measure_empty, add_zero]
    have : condAgreeOn μ X x h = 1 := by
      rw [condAgreeOn, if_neg hmassne, massOn_joint_true, massOn, hjoint]
      exact div_self (by rw [← massOn]; exact hmassne)
    unfold condExpectPmOn; rw [this]; ring



/-- The probe of a target is measurable: its `true` fibre is the target's fibre
at `γ` and its `false` fibre is the complement. -/
@[fun_prop] public theorem measurable_probe_comp
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Γ : U → G) (hΓ : Measurable Γ) (γ : G) :
    Measurable (fun u => probe γ (Γ u)) := by
  refine measurable_to_countable' (fun b => ?_)
  have hset : (fun u => probe γ (Γ u)) ⁻¹' {b}
      = if b then Γ ⁻¹' {γ} else (Γ ⁻¹' {γ})ᶜ := by
    ext u
    cases b <;> simp [probe, eq_comm]
  rw [hset]
  cases b
  · exact ((hΓ (measurableSet_singleton γ)).compl)
  · exact hΓ (measurableSet_singleton γ)

/-- Hence so is the agreement of a device's conclusion with that probe — the
function every `condExpectPmOn` in this layer is taken against. -/
@[fun_prop] public theorem measurable_agree_probe
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Y : U → Bool) (hY : Measurable Y) (Γ : U → G) (hΓ : Measurable Γ) (γ : G) :
    Measurable (fun u => Y u == probe γ (Γ u)) := by
  refine measurable_to_countable' (fun b => ?_)
  have hprobe := measurable_probe_comp Γ hΓ γ
  have hset : (fun u => Y u == probe γ (Γ u)) ⁻¹' {b}
      = (Y ⁻¹' {true} ∩ (fun u => probe γ (Γ u)) ⁻¹' {decide (b = true)})
        ∪ (Y ⁻¹' {false} ∩ (fun u => probe γ (Γ u)) ⁻¹' {decide (b = false)}) := by
    ext u
    cases b <;> cases hy : Y u <;> cases hp : probe γ (Γ u) <;>
      simp [hy, hp]
  rw [hset]
  exact ((hY (measurableSet_singleton _)).inter (hprobe (measurableSet_singleton _))).union
    ((hY (measurableSet_singleton _)).inter (hprobe (measurableSet_singleton _)))

/-- Under `hatom` every realized setup value has positive mass, so it is one of
the values the printed maximum ranges over. -/
public theorem massOn_pos_of_realized (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [MeasurableSpace C.Setup]
    [MeasurableSingletonClass C.Setup]
    (hatom : ∀ u : U, μ {u} ≠ 0) {x : C.Setup} (hx : C.Realized x) :
    0 < massOn μ C.setup x := by
  obtain ⟨w, hw⟩ := hx
  have hpos : μ (C.setup ⁻¹' {x}) ≠ 0 := fun h0 =>
    hatom w (measure_mono_null (by simpa using hw) h0)
  rw [massOn]
  exact ENNReal.toReal_pos hpos (measure_ne_top μ _)

/-- **`D > Γ` gives `cov = 1`**, at general measure. -/
public theorem inferenceAccuracyOn_eq_one_of_weaklyInfers
    (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [MeasurableSpace C.Setup]
    [MeasurableSingletonClass C.Setup] [FiniteRange C.setup] [DecidableEq C.Setup]
    (hC : Measurable C.setup) (hY : Measurable C.concl)
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Γ : U → G) [FiniteRange Γ] (hΓ : Measurable Γ)
    (hatom : ∀ u : U, μ {u} ≠ 0) (hW : WeaklyInfers C Γ) (hne : Nonempty U) :
    inferenceAccuracyOn μ C Γ = 1 := by
  classical
  have hcard : (rangeFinset Γ).card ≠ 0 := by
    obtain ⟨u⟩ := hne
    exact Finset.card_ne_zero_of_mem ((mem_rangeFinset Γ (Γ u)).mpr ⟨u, rfl⟩)
  have hcardpos : (0 : ℝ) < ((rangeFinset Γ).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcard
  unfold inferenceAccuracyOn
  rw [if_neg hcard, div_eq_one_iff_eq (ne_of_gt hcardpos)]
  have hterm : ∀ γ ∈ rangeFinset Γ,
      (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
        (fun x => condExpectPmOn μ C.setup x
          (fun u => C.concl u == probe γ (Γ u))) = 1 := by
    intro γ hγ
    obtain ⟨x, hxr, hxall⟩ := hW γ (probe γ) (isProbe_probe γ)
      ((mem_rangeFinset Γ γ).mp hγ)
    have hxpos : 0 < massOn μ C.setup x := massOn_pos_of_realized μ C hatom hxr
    have hxmem : x ∈ positiveMassSetupsOn μ C :=
      Finset.mem_filter.mpr ⟨(mem_rangeFinset C.setup x).mpr hxr, hxpos⟩
    have hx1 : condExpectPmOn μ C.setup x
        (fun u => C.concl u == probe γ (Γ u)) = 1 := by
      refine (condExpectPmOn_eq_one_iff_forall μ C.setup hC _ ?_ x hatom hxr).mpr ?_
      · fun_prop
      · intro w hw
        simpa using hxall w hw
    refine le_antisymm (Finset.sup'_le _ _ (fun y _ => ?_)) ?_
    · exact (condExpectPmOn_mem_Icc μ C.setup y _).2
    · rw [← hx1]
      exact Finset.le_sup'
        (fun y => condExpectPmOn μ C.setup y (fun u => C.concl u == probe γ (Γ u))) hxmem
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **`cov = 1` gives `D > Γ`**, at general measure, under the printed
*"`P` is nowhere 0"* read as `hatom`. -/
public theorem weaklyInfers_of_inferenceAccuracyOn_eq_one
    (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [MeasurableSpace C.Setup]
    [MeasurableSingletonClass C.Setup] [FiniteRange C.setup] [DecidableEq C.Setup]
    (hC : Measurable C.setup) (hY : Measurable C.concl)
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Γ : U → G) [FiniteRange Γ] (hΓ : Measurable Γ)
    (hatom : ∀ u : U, μ {u} ≠ 0) (heq : inferenceAccuracyOn μ C Γ = 1) :
    WeaklyInfers C Γ := by
  classical
  intro γ f hf hγ
  have hγmem : γ ∈ rangeFinset Γ := (mem_rangeFinset Γ γ).mpr hγ
  have hcard : (rangeFinset Γ).card ≠ 0 := Finset.card_ne_zero_of_mem hγmem
  have hcardpos : (0 : ℝ) < ((rangeFinset Γ).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcard
  unfold inferenceAccuracyOn at heq
  rw [if_neg hcard, div_eq_one_iff_eq (ne_of_gt hcardpos)] at heq
  set term : G → ℝ := fun δ =>
    (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
      (fun x => condExpectPmOn μ C.setup x
        (fun u => C.concl u == probe δ (Γ u))) with hterm
  have hle : ∀ δ ∈ rangeFinset Γ, term δ ≤ 1 := fun δ _ =>
    Finset.sup'_le _ _ (fun y _ => (condExpectPmOn_mem_Icc μ C.setup y _).2)
  have hzero : (rangeFinset Γ).sum (fun δ => 1 - term δ) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, heq]
    ring
  have hall : term γ = 1 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun δ hδ => by linarith [hle δ hδ] : ∀ δ ∈ rangeFinset Γ, (0:ℝ) ≤ 1 - term δ)).mp
      hzero γ hγmem
    linarith
  obtain ⟨x, hxmem, hxeq⟩ := Finset.exists_mem_eq_sup'
    (positiveMassSetupsOn_nonempty μ C)
    (fun x => condExpectPmOn μ C.setup x (fun u => C.concl u == probe γ (Γ u)))
  have hx1 : condExpectPmOn μ C.setup x
      (fun u => C.concl u == probe γ (Γ u)) = 1 := by rw [← hxeq]; exact hall
  have hxr : C.Realized x := (mem_rangeFinset C.setup x).mp (Finset.mem_filter.mp hxmem).1
  refine ⟨x, hxr, ?_⟩
  intro w hw
  have := (condExpectPmOn_eq_one_iff_forall μ C.setup hC _
    (by fun_prop) x hatom hxr).mp hx1 w hw
  have hagree : C.concl w = probe γ (Γ w) := by simpa using this
  rw [hagree, hf.eq_of_isProbe (isProbe_probe γ)]

/-- **The printed sentence after 2018 Definition 6, at general measure.**
*"if `P` is nowhere 0, then `cov(D, Γ) = 1.0` iff `D > Γ`."* -/
public theorem inferenceAccuracyOn_eq_one_iff (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [MeasurableSpace C.Setup]
    [MeasurableSingletonClass C.Setup] [FiniteRange C.setup] [DecidableEq C.Setup]
    (hC : Measurable C.setup) (hY : Measurable C.concl)
    {G : Type v'} [MeasurableSpace G] [MeasurableSingletonClass G] [DecidableEq G]
    (Γ : U → G) [FiniteRange Γ] (hΓ : Measurable Γ)
    (hatom : ∀ u : U, μ {u} ≠ 0) (hne : Nonempty U) :
    inferenceAccuracyOn μ C Γ = 1 ↔ WeaklyInfers C Γ :=
  ⟨weaklyInfers_of_inferenceAccuracyOn_eq_one μ C hC hY Γ hΓ hatom,
    fun hW => inferenceAccuracyOn_eq_one_of_weaklyInfers μ C hC hY Γ hΓ hatom hW hne⟩



/-! ## Definition 10 beyond a finite setup range

`entropyOn` sums over `rangeFinset X`, so Definition 10 carries
`[FiniteRange C.setup]` where the source states none. The printed
`1 − M/(H₁+H₂)` is a ratio, and on a range where an entropy diverges it is
`∞/∞` and denotes nothing — so **countably supported with finite entropy** is
the largest domain the printed formula reaches, not arbitrary support.

That is what the `tsum` form below expresses: the sum ranges over the whole
value type, the unrealized values contribute `0` because their mass is `0`, and
summability is the hypothesis that the entropy is finite. On a finite range the
two forms are literally the same number.
-/

/-- One term of the entropy sum, with the source's own convention at zero mass. -/
@[expose] public noncomputable def entropyTerm (μ : Measure U) {α : Type v}
    (X : U → α) (a : α) : ℝ :=
  if massOn μ X a = 0 then 0 else massOn μ X a * Real.log (massOn μ X a)

/-- **Entropy over an arbitrary value range.** A `tsum` over the whole type: the
unrealized values contribute nothing, so this is the printed sum over `X(U)`
wherever that sum denotes. -/
@[expose] public noncomputable def entropySum (μ : Measure U) {α : Type v}
    (X : U → α) : ℝ :=
  -∑' a : α, entropyTerm μ X a

/-- On a finite range the two entropies are the same number. -/
public theorem entropySum_eq_entropyOn (μ : Measure U) {α : Type v}
    (X : U → α) [FiniteRange X] [DecidableEq α] :
    entropySum μ X = entropyOn μ X := by
  classical
  rw [entropySum, entropyOn]
  congr 1
  refine tsum_eq_sum (fun a ha => ?_)
  rw [entropyTerm, if_pos (massOn_eq_zero_of_notMem μ X ha)]

/-- **Mutual information over arbitrary ranges**, from the same sums. -/
@[expose] public noncomputable def mutualInfoSum (μ : Measure U)
    {α : Type v} {β : Type v'} (X : U → α) (Y : U → β) : ℝ :=
  entropySum μ X + entropySum μ Y - entropySum μ (fun u => (X u, Y u))

public theorem mutualInfoSum_eq_mutualInfoOn (μ : Measure U)
    {α : Type v} {β : Type v'} (X : U → α) (Y : U → β)
    [FiniteRange X] [FiniteRange Y] [DecidableEq α] [DecidableEq β] :
    mutualInfoSum μ X Y = mutualInfoOn μ X Y := by
  rw [mutualInfoSum, mutualInfoOn, entropySum_eq_entropyOn, entropySum_eq_entropyOn,
    entropySum_eq_entropyOn]

/-- **Definition 10 with no finiteness on either setup range.** -/
@[expose] public noncomputable def miDistinguishabilitySum (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U) : ℝ :=
  if entropySum μ C₁.setup + entropySum μ C₂.setup = 0 then 1
  else 1 - mutualInfoSum μ C₁.setup C₂.setup /
    (entropySum μ C₁.setup + entropySum μ C₂.setup)

/-- …and it agrees with the finite form wherever that one is defined. -/
public theorem miDistinguishabilitySum_eq (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] :
    miDistinguishabilitySum μ C₁ C₂ = miDistinguishabilityOn μ C₁ C₂ := by
  unfold miDistinguishabilitySum miDistinguishabilityOn setupEntropyOn
  rw [entropySum_eq_entropyOn, entropySum_eq_entropyOn,
    mutualInfoSum_eq_mutualInfoOn]


end AISafetyAtlas.Inference
