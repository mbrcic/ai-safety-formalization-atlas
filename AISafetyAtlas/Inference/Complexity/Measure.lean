module

public import AISafetyAtlas.Inference.Complexity
public import AISafetyAtlas.Inference.Stochastic.Measure
public import AISafetyAtlas.Inference.Stochastic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Section 5's length under a general measure

Definition 6's length is `ℒ(x) = −ln μ(X⁻¹(x))` for a measure `dμ` the source
leaves general; its Example 6 takes counting measure, which is the case
`Complexity.lean` names `setupLength`.

Nothing else in section 5 has to change. Theorem 4 is stated there for an
arbitrary length assignment, because its proof compares lengths through `inf'`
and `sup'` and never unfolds one. So the general-measure case is an
instantiation, not a second development.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

open scoped Classical

universe u v v' v''

variable {U : Type u} [MeasurableSpace U]

/-- **Definition 6's length**, `ℒ(x) = −ln μ(X⁻¹(x))`, for a general measure. -/
@[expose] public noncomputable def measureLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : ℝ :=
  -Real.log (massOn μ C.setup x)

/-- **The module docstring's claim, checked.** Under counting measure the general
length **is** `setupLength` — not equal up to normalisation, equal. The header
above asserted this and nothing verified it. -/
public theorem massOn_count [Fintype U] [MeasurableSingletonClass U]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (x : C.Setup) :
    massOn (Measure.count : Measure U) C.setup x = (setupFibreCard C x : ℝ) := by
  classical
  have hfin : (C.setup ⁻¹' {x}).Finite := Set.toFinite _
  have hset : hfin.toFinset = Finset.univ.filter (fun u : U => C.setup u = x) := by
    ext u
    simp
  rw [massOn, Measure.count_apply_finite _ hfin, hset]
  simp [setupFibreCard]

public theorem measureLength_count [Fintype U] [MeasurableSingletonClass U]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (x : C.Setup) :
    measureLength (Measure.count : Measure U) C x = setupLength C x := by
  rw [measureLength, setupLength, massOn_count]

/-- **Definition 6 under a general measure.** -/
@[expose] public noncomputable def inferenceComplexityMeasure (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) : ℝ :=
  inferenceComplexity C (measureLength μ C) Γ hW

/-- **Theorem 4 under a general measure.** `U` is arbitrary; the finiteness is the
source's own, on `X(U)` and `Γ(U)`. -/
public theorem inferenceComplexityMeasure_le_of_stronglyInfers (μ : Measure U)
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    {G : Type v''} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hs : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ) :
    inferenceComplexityMeasure μ C₁ Γ (weaklyInfers_of_stronglyInfers hs hw) -
        inferenceComplexityMeasure μ C₂ Γ hw ≤
      ((rangeFinset Γ).card : ℝ) *
        emulationCost C₁ C₂ (measureLength μ C₁) (measureLength μ C₂) :=
  inferenceComplexity_le_of_stronglyInfers _ _ Γ hs hw

/--
**Wolpert 2018, Proposition 13's own remark.** *"Note that since
`ℳ_{μ,X₁}(x₁) − ℳ_{μ,X₂}(x₂) = ln(μ(X₂⁻¹(x₂)) / μ(X₁⁻¹(x₁)))`, the bound in
Prop. 13 is independent of the units with which one measures volume in `U`."*

The difference of two `measureLength`s is a log of a ratio, so rescaling `μ` by a
positive constant leaves it fixed. That is why Proposition 13 — unlike
Definition 7 itself — needs no normalization convention.
-/
public theorem measureLength_sub_measureLength (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup)
    (h₁ : 0 < massOn μ C₁.setup x₁) (h₂ : 0 < massOn μ C₂.setup x₂) :
    measureLength μ C₁ x₁ - measureLength μ C₂ x₂ =
      Real.log (massOn μ C₂.setup x₂ / massOn μ C₁.setup x₁) := by
  unfold measureLength
  rw [Real.log_div (ne_of_gt h₂) (ne_of_gt h₁)]
  ring

/-! ## Stochastic inference complexity

Section 8 defines, in running prose rather than a numbered environment:

> `C̄_ε(Γ ∣ C) ≜ Σ_{f ∈ π(Γ)} min_{x : E_P(Y f(Γ)∣x) ≥ ε} [−H(U ∣ x)]`

It is Definition 6 with the *exact*-answering condition on a setup relaxed to
*accurate to within `ε`*, and with the same length — the source notes that when
`P ∝ dμ` on the support, `−H(U ∣ x)` and `−ln μ(X⁻¹(x))` agree. So it is another
instantiation of the section 5 machinery, differing only in which setups the
minimum ranges over.

This was the largest gap in the prose layer of section 8. -/

/-- The setups whose Definition 9 accuracy at this probe is at least `ε`. -/
@[expose] public noncomputable def accurateSet (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (ε : ℝ) : Finset C.Setup :=
  (realizedSetups C).filter fun x =>
    ε ≤ condExpectPmOn μ C.setup x (fun u => C.concl u == f (Γ u))

@[expose] public noncomputable def minAccurateLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    (ℓ : C.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) (ε : ℝ) : ℝ :=
  if h : (accurateSet μ C Γ f ε).Nonempty then
    (accurateSet μ C Γ f ε).inf' h ℓ
  else 0

/-- **Stochastic inference complexity**, `C̄_ε(Γ ∣ C)`. -/
@[expose] public noncomputable def stochasticInferenceComplexity (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (ε : ℝ) : ℝ :=
  (rangeFinset Γ).sum fun γ => minAccurateLength μ C ℓ Γ (probe γ) ε

/-- Membership in the accuracy set, stated so callers never have to match the
`Finset.filter` decidability instance this module's `open scoped Classical` picks
— the same hazard `mem_answeringSet_iff` exists for. -/
public theorem mem_accurateSet_iff (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (ε : ℝ) (x : C.Setup) :
    x ∈ accurateSet μ C Γ f ε ↔
      C.Realized x ∧ ε ≤ condExpectPmOn μ C.setup x (fun u => C.concl u == f (Γ u)) := by
  unfold accurateSet realizedSetups
  rw [Finset.mem_filter, mem_rangeFinset]
  exact Iff.rfl

/-- A setup that answers a probe exactly, on a fibre of positive mass, is accurate
to within `1`. This is the inclusion behind the source's remark that at `ε = 1` the
stochastic complexity collapses to Definition 6. -/
public theorem mem_accurateSet_of_answersProbe (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) {x : C.Setup}
    (hx : massOn μ C.setup x ≠ 0) (hmem : x ∈ answeringSet C Γ f) :
    x ∈ accurateSet μ C Γ f 1 := by
  have hfib : ∀ w, C.setup w = x → C.concl w = f (Γ w) := (Finset.mem_filter.mp hmem).2
  have hset : (fun u => (C.setup u, C.concl u == f (Γ u))) ⁻¹' {(x, true)}
      = C.setup ⁻¹' {x} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [hfib u h]
    simp
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmem).1, ?_⟩
  unfold condExpectPmOn condAgreeOn
  rw [if_neg hx, show massOn μ (fun u => (C.setup u, C.concl u == f (Γ u))) (x, true)
      = massOn μ C.setup x by simp [massOn, hset]]
  rw [div_self hx]
  norm_num

/-- **The source's `ε = 1` remark, in the direction that needs no extra
hypothesis.** *"if `P` is proportional to `dμ` across the support of `P` and
`C > Γ`, then for `ε = 1`, `C̄_ε(Γ ∣ C) = 𝒞(Γ ∣ C)`."*

The stochastic complexity is **at most** the exact one: relaxing the condition on a
setup only enlarges the set the minimum ranges over. `C > Γ` is the source's own
hypothesis, and it is needed — without it a probe can have an accurate setup and no
exactly-answering one, and Definition 6 totalizes that case to `0`.

Equality is the source's claim and needs its other hypothesis, `P` proportional to
`dμ` on the support, so that accuracy `1` forces agreement rather than merely
almost-everywhere agreement. It is `stochasticInferenceComplexity_eq` below. -/
public theorem stochasticInferenceComplexity_le (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hw : WeaklyInfers C Γ)
    (hpos : ∀ x : C.Setup, x ∈ realizedSetups C → massOn μ C.setup x ≠ 0) :
    stochasticInferenceComplexity μ C ℓ Γ 1 ≤ inferenceComplexityTotal C ℓ Γ := by
  unfold stochasticInferenceComplexity inferenceComplexityTotal
  refine Finset.sum_le_sum fun γ hγ => ?_
  obtain ⟨x0, hx0R, hx0fib⟩ :=
    hw γ (probe γ) (isProbe_probe γ) ((mem_rangeFinset Γ γ).mp hγ)
  have hx0 : x0 ∈ answeringSet C Γ (probe γ) := by
    refine Finset.mem_filter.mpr ⟨?_, hx0fib⟩
    obtain ⟨w, hw'⟩ := hx0R
    exact (mem_rangeFinset C.setup x0).mpr ⟨w, hw'⟩
  have hsub : answeringSet C Γ (probe γ) ⊆ accurateSet μ C Γ (probe γ) 1 := fun y hy =>
    mem_accurateSet_of_answersProbe μ C Γ (probe γ)
      (hpos y (Finset.mem_filter.mp hy).1) hy
  unfold minAccurateLength minAnsweringLength
  rw [dif_pos ⟨x0, hsub hx0⟩, dif_pos ⟨x0, hx0⟩]
  refine Finset.le_inf' _ _ (fun y hy => ?_)
  exact Finset.inf'_le ℓ (hsub hy)

/-! ### The converse inclusion, and where the source's second hypothesis goes

Accuracy `1` says the disagreeing part of a fibre has **measure zero**. Exact
answering says it is **empty**. Those differ by exactly the null sets, which is
what the source's *"`P` is proportional to `dμ` across the support of `P`"* is
doing: it forbids a point that the accuracy measure ignores but the length
measure still counts.

The atlas model uses one measure for both, so the condition becomes the
statement that no point is null — `hatom` below. It is stated on the fibre
rather than globally, because that is all the argument uses, and it is a genuine
hypothesis rather than a technicality: without it a device can be accurate to
within `1` at a probe it answers wrongly at a null point, and the two complexities
come apart. -/

/-- **Accuracy `1` forces exact answering when no point of the fibre is null.** -/
public theorem answersProbe_of_mem_accurateSet (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup)
    {G : Type v'} (Γ : U → G) (f : G → Bool)
    (hagree : Measurable fun u => C.concl u == f (Γ u))
    (hatom : ∀ u : U, μ {u} ≠ 0)
    {x : C.Setup} (hx : x ∈ accurateSet μ C Γ f 1) :
    x ∈ answeringSet C Γ f := by
  classical
  obtain ⟨hxR, hacc⟩ := (mem_accurateSet_iff μ C Γ f 1 x).mp hx
  set h : U → Bool := fun u => C.concl u == f (Γ u) with hdef
  have hmass : massOn μ C.setup x ≠ 0 := by
    intro h0
    rw [condExpectPmOn, condAgreeOn, if_pos h0] at hacc
    norm_num at hacc
  have hMpos : 0 < massOn μ C.setup x :=
    lt_of_le_of_ne (massOn_nonneg _ _ _) (Ne.symm hmass)
  have hsplit := massOn_bool_split μ C.setup h hC hagree x
  have hBnonneg := massOn_nonneg μ (fun u => (C.setup u, h u)) (x, false)
  have hB : massOn μ (fun u => (C.setup u, h u)) (x, false) = 0 := by
    rw [condExpectPmOn, condAgreeOn, if_neg hmass] at hacc
    have hone : (1 : ℝ) ≤ massOn μ (fun u => (C.setup u, h u)) (x, true) /
        massOn μ C.setup x := by linarith
    have hle := (one_le_div hMpos).mp hone
    linarith
  refine (mem_answeringSet_iff C Γ f x).mpr ⟨hxR, fun w hw => ?_⟩
  by_contra hne
  have hfw : h w = false := by simp [hdef, hne]
  have hsub : ({w} : Set U) ⊆ (fun u => (C.setup u, h u)) ⁻¹' {(x, false)} := by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    simp [Set.mem_preimage, hw, hfw]
  have hzero : μ ((fun u => (C.setup u, h u)) ⁻¹' {(x, false)}) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hB).resolve_right (measure_ne_top μ _)
  exact hatom w (le_antisymm (hzero ▸ measure_mono hsub) (zero_le))

/-- At `ε = 1` the two sets a minimum can range over are the same set. -/
public theorem accurateSet_eq_answeringSet (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup)
    {G : Type v'} (Γ : U → G) (f : G → Bool)
    (hagree : Measurable fun u => C.concl u == f (Γ u))
    (hatom : ∀ u : U, μ {u} ≠ 0)
    (hpos : ∀ x : C.Setup, x ∈ realizedSetups C → massOn μ C.setup x ≠ 0) :
    accurateSet μ C Γ f 1 = answeringSet C Γ f :=
  Finset.Subset.antisymm
    (fun _ hy => answersProbe_of_mem_accurateSet μ C hC Γ f hagree hatom hy)
    (fun y hy =>
      mem_accurateSet_of_answersProbe μ C Γ f (hpos y (Finset.mem_filter.mp hy).1) hy)

/-- **The source's `ε = 1` remark, in full.** *"if `P` is proportional to `dμ`
across the support of `P` and `C > Γ`, then for `ε = 1`, `C̄_ε(Γ ∣ C) =
𝒞(Γ ∣ C)`."*

`C > Γ` is not needed for this direction — with the two sets equal, the
totalizations agree too, so the equality holds wherever the sets do. It stays in
`inferenceComplexity`'s signature, where the source put it. -/
public theorem stochasticInferenceComplexity_eq (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup) (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hagree : ∀ f : G → Bool, Measurable fun u => C.concl u == f (Γ u))
    (hatom : ∀ u : U, μ {u} ≠ 0)
    (hpos : ∀ x : C.Setup, x ∈ realizedSetups C → massOn μ C.setup x ≠ 0) :
    stochasticInferenceComplexity μ C ℓ Γ 1 = inferenceComplexityTotal C ℓ Γ := by
  unfold stochasticInferenceComplexity inferenceComplexityTotal
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  unfold minAccurateLength minAnsweringLength
  rw [accurateSet_eq_answeringSet μ C hC Γ (probe γ) (hagree _) hatom hpos]

/-! ## `Ĉ` — the min-free variant, which **both** papers display

2008 after Definition 6: *"A natural modification to Definition 6 is to remove
the min by considering all `x`'s that cause `Y = f(Γ)`, not just of one of
them."* 2018 repeats it verbatim after Definition 7, as `Ĉ(Γ; D)`.

Both papers then display the same equality, with the same one-line justification
(*"the equality follows from the fact that for any `x`, `x' ≠ x`,
`X⁻¹(x) ∩ X⁻¹(x') = ∅`"*):

`Ĉ(Γ ∣ C) ≜ Σ_f −ln μ(⋃_{x : X=x ⇒ Y=f(Γ)} X⁻¹(x)) = Σ_f −ln (Σ_{x : …} e^{−ℒ(x)})`

It is a *displayed* definition that no numbered environment announces — the class
of item a transcription table keyed on numbered environments cannot see, which is
why both ledgers enumerate displayed equations and prose claims as well.

Unlike Definition 6, `Ĉ` needs no `min` to be attained, so nothing here forces
the setup range to be finite for the display to denote — `FiniteRange` is carried
only because `answeringSet` is a `Finset`. The disjointness the source waves at
is where the measurability comes in: a `Measure` is merely sub-additive on
arbitrary sets, so the printed equality is exactly as strong as the fibres being
measurable.
-/

/-- The mass of the union of **every** fibre answering a probe — the argument of
the logarithm in `Ĉ`. -/
@[expose] public noncomputable def answeringMass (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  (μ (⋃ x ∈ answeringSet C Γ f, C.setup ⁻¹' {x})).toReal

/-- **`Ĉ(Γ ∣ C)`**, the min-free inference complexity displayed in both papers. -/
@[expose] public noncomputable def unionInferenceComplexity (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => -Real.log (answeringMass μ C Γ (probe γ)))

/-- **The displayed equality, first form.** The union's mass is the sum of the
answering fibres' masses, because distinct setup values have disjoint fibres.
That disjointness is the source's own justification; measurability is what makes
it usable, since a measure is only sub-additive without it. -/
public theorem answeringMass_eq_sum (μ : Measure U) [IsFiniteMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup)
    {G : Type v'} (Γ : U → G) (f : G → Bool) :
    answeringMass μ C Γ f = (answeringSet C Γ f).sum (fun x => massOn μ C.setup x) := by
  classical
  have hdisj : (answeringSet C Γ f : Set C.Setup).PairwiseDisjoint
      (fun x => C.setup ⁻¹' {x}) := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr ?_
    intro u ha hb
    exact hab (ha.symm.trans hb)
  have hmeas : ∀ x ∈ answeringSet C Γ f, MeasurableSet (C.setup ⁻¹' {x}) :=
    fun x _ => hC (measurableSet_singleton x)
  rw [answeringMass, measure_biUnion_finset hdisj hmeas]
  rw [ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)]
  rfl

/-- **The displayed equality, second form.** `e^{−ℒ(x)}` is the fibre mass, so
the source's `Σ_x e^{−ℒ(x)}` is the sum above. Positivity is what lets the
logarithm be inverted, and it is exactly the condition under which `ℒ(x)` is a
real number rather than `+∞`. -/
public theorem answeringMass_eq_sum_exp (μ : Measure U) [IsFiniteMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup)
    {G : Type v'} (Γ : U → G) (f : G → Bool)
    (hpos : ∀ x ∈ answeringSet C Γ f, 0 < massOn μ C.setup x) :
    answeringMass μ C Γ f
      = (answeringSet C Γ f).sum (fun x => Real.exp (-(measureLength μ C x))) := by
  rw [answeringMass_eq_sum μ C hC Γ f]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [measureLength, neg_neg, Real.exp_log (hpos x hx)]


/-! ### `C̄_ε` at the source's own length

`stochasticInferenceComplexity` takes `ℓ` as a parameter, which is faithful — the
source separates the distribution `P` fixing accuracy from the volume `dμ` fixing
length — but it left the **printed** object unnamed. `sourceStochasticComplexity`
fixes `ℓ` at `−ℍ(U ∣ x)`, so section 8's display finally has a declaration.

The source's bridge is *"if `P` is proportional to `dμ` across the support of `P`
and `C > Γ`, then for `ε = 1`, `C̄_ε(Γ ∣ C) = 𝒞(Γ ∣ C)"*. Both halves are here:
`condEntropy_eq_log_card_of_uniform` is the proportionality half at counting
measure, and `stochasticInferenceComplexity_eq` is the `ε = 1` half.
-/

/-- **`C̄_ε(Γ ∣ C)`** with the source's own length, `ℓ(x) = −ℍ(U ∣ x)`. -/
@[expose] public noncomputable def sourceStochasticComplexity [Fintype U] (μ : Measure U)
    (p : FinPMF U) (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] (ε : ℝ) : ℝ :=
  stochasticInferenceComplexity μ C (fun x => -condEntropy p C.setup x) Γ ε

omit [MeasurableSpace U] in
/-- **`P ∝ dμ` on a fibre makes the two lengths agree.** At counting measure the
proportionality the source assumes is uniformity, and then `−ℍ(U ∣ x)` is exactly
`setupLength x`. This is the sentence *"these two definitions of the length of
`x` are the same"*, proved. -/
public theorem neg_condEntropy_eq_setupLength_of_uniform [Fintype U]
    (p : FinPMF U) (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (x : C.Setup) {c : ℝ} (hc : 0 < c)
    (huniform : ∀ u : U, C.setup u = x → p.mass u = c) :
    -condEntropy p C.setup x = setupLength C x := by
  rw [condEntropy_eq_log_card_of_uniform p C x hc huniform, setupLength, setupFibreCard]

/-- **The source's `ε = 1` identity**, `C̄₁(Γ ∣ C) = 𝒞(Γ ∣ C)`, with the length
fixed at `−ℍ(U ∣ x)` and `P` uniform on every fibre — the proportionality the
source assumes. -/
public theorem sourceStochasticComplexity_eq [Fintype U] (μ : Measure U)
    [IsProbabilityMeasure μ] (p : FinPMF U) (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    [FiniteRange C.setup] [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hagree : ∀ f : G → Bool, Measurable fun u => C.concl u == f (Γ u))
    (hatom : ∀ u : U, μ {u} ≠ 0)
    (hpos : ∀ x : C.Setup, x ∈ realizedSetups C → massOn μ C.setup x ≠ 0)
    (c : C.Setup → ℝ) (hc : ∀ x, 0 < c x)
    (huniform : ∀ (x : C.Setup) (u : U), C.setup u = x → p.mass u = c x) :
    sourceStochasticComplexity μ p C Γ 1 = inferenceComplexityTotal C (setupLength C) Γ := by
  unfold sourceStochasticComplexity
  rw [stochasticInferenceComplexity_eq μ C hC _ Γ hagree hatom hpos]
  unfold inferenceComplexityTotal
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  unfold minAnsweringLength
  by_cases h : (answeringSet C Γ (probe γ)).Nonempty
  · rw [dif_pos h, dif_pos h]
    exact Finset.inf'_congr h rfl (fun x _ =>
      neg_condEntropy_eq_setupLength_of_uniform p C x (hc x) (huniform x))
  · rw [dif_neg h, dif_neg h]


/-! ## `Ĉ` over an arbitrary setup range

`answeringMass` sums the measure of the union of the answering fibres, and took
that union over a `Finset`, so it carried `[FiniteRange C.setup]` where the
source states none. A union does not need a finite index. `answeringSetOn`
supplies the set form, and nothing else changes — the printed `Ĉ` is the same
displayed formula with the same disjointness justification.
-/

/-- The mass of the union of **all** answering fibres, with no finiteness on the
setup range. -/
@[expose] public noncomputable def answeringMassOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  (μ (⋃ x ∈ answeringSetOn C Γ f, C.setup ⁻¹' {x})).toReal

/-- **`Ĉ` with no finiteness on the setup range.** The sum is still over `Γ(U)`,
which the source keeps finite wherever it counts target values. -/
@[expose] public noncomputable def unionInferenceComplexityOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => -Real.log (answeringMassOn μ C Γ (probe γ)))

/-- The two forms are the same object on a finite setup range: the index sets
have the same members, so the unions are the same set. -/
public theorem answeringMassOn_eq (μ : Measure U) (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) :
    answeringMassOn μ C Γ f = answeringMass μ C Γ f := by
  unfold answeringMassOn answeringMass
  congr 2
  ext u
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨x, hx, hu⟩
    exact ⟨x, by rw [← Finset.mem_coe, coe_answeringSet]; exact hx, hu⟩
  · rintro ⟨x, hx, hu⟩
    exact ⟨x, by rw [← coe_answeringSet, Finset.mem_coe]; exact hx, hu⟩

public theorem unionInferenceComplexityOn_eq (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] :
    unionInferenceComplexityOn μ C Γ = unionInferenceComplexity μ C Γ :=
  Finset.sum_congr rfl (fun γ _ => by rw [answeringMassOn_eq])



/-! ## `C̄_ε` under a prior, via Mathlib's relative entropy

§8 fixes the length at `−ℍ(U ∣ x)`, the conditional Shannon entropy of
`P(u ∣ x)`. `sourceStochasticComplexity` above is the **discrete** form, built on
`condEntropy` over a `FinPMF`. The general-measure form of *"entropy under a
prior `dμ`"* is relative entropy, and the 2008 map has recorded since S4 that
when it is built it should **instantiate** `InformationTheory.klDiv` rather than
define anything. That is what happens here.

The length is the divergence of the conditional law on a setup fibre from the
prior. Its two structural facts come from Mathlib unchanged: it is nonnegative
because `klDiv` is `ℝ≥0∞`-valued, and it vanishes exactly when the fibre's
conditional law *is* the prior — a device whose setup value says nothing pays
nothing.
-/

/-- The conditional law on a setup fibre, `P(· ∣ x)`. -/
@[expose] public noncomputable def condLawOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : Measure U :=
  ProbabilityTheory.cond μ (C.setup ⁻¹' {x})

/-- **The source's `−ℍ(U ∣ x)` under a prior `dμ`**, as relative entropy. No new
definition: this is `InformationTheory.klDiv` at the conditional law. -/
@[expose] public noncomputable def relativeLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : ℝ :=
  (InformationTheory.klDiv (condLawOn μ C x) μ).toReal

/-- **`C̄_ε` with the printed length, at general measure.** -/
@[expose] public noncomputable def relativeStochasticComplexity (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] (ε : ℝ) : ℝ :=
  stochasticInferenceComplexity μ C (relativeLength μ C) Γ ε

/-- The length is nonnegative, because relative entropy is. -/
public theorem relativeLength_nonneg (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) :
    0 ≤ relativeLength μ C x := ENNReal.toReal_nonneg

/-- **A setup value that says nothing costs nothing.** If the fibre's conditional
law is the prior itself, the length is `0` — `klDiv_self`. -/
public theorem relativeLength_eq_zero_of_cond_eq (μ : Measure U) [SigmaFinite μ]
    (C : InferenceDevice.{u, v} U) (x : C.Setup) (h : condLawOn μ C x = μ) :
    relativeLength μ C x = 0 := by
  rw [relativeLength, h, InformationTheory.klDiv_self]
  rfl

/-- …and conversely, on finite measures: a length of `0` means the setup value
carried no information about `U` at all. `klDiv_eq_zero_iff` is the source of
both directions; note it needs the divergence to be finite, which
`ENNReal.toReal` alone does not give. -/
public theorem condLawOn_eq_of_relativeLength_eq_zero (μ : Measure U)
    [IsFiniteMeasure μ] (C : InferenceDevice.{u, v} U) (x : C.Setup)
    [IsFiniteMeasure (condLawOn μ C x)]
    (hfin : InformationTheory.klDiv (condLawOn μ C x) μ ≠ ⊤)
    (h : relativeLength μ C x = 0) :
    condLawOn μ C x = μ := by
  refine InformationTheory.klDiv_eq_zero_iff.mp ?_
  rw [relativeLength] at h
  exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right hfin


end AISafetyAtlas.Inference
