module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Genericity: a nonzero polynomial vanishes only on a null set

A nonzero real polynomial in finitely many variables is nonzero **almost
everywhere**. Mathlib has the combinatorial sibling of this statement —
`MvPolynomial.schwartz_zippel_totalDegree`, which bounds the fraction of a
finite grid on which a nonzero polynomial vanishes — but not the
measure-theoretic form, which is what genericity arguments over `ℝ` actually
reach for.

## Primary surface

| declaration | says |
|---|---|
| `ae_eval_ne_zero_pi` | for a product of atomless measures, a nonzero polynomial is a.e. nonzero |
| `measure_setOf_eval_eq_zero_pi` | the same as a null-set statement |
| `ae_eval_ne_zero` | the `volume` form at `Fin n`, which is the shape the induction runs in |
| `ae_eval_ne_zero_fintype` | the same at an arbitrary finite variable type — the form that gets applied |
| `volume_setOf_eval_eq_zero` | the Lebesgue null-set form |
| `ae_eval_ne_zero_addHaar` | the same for any additive Haar measure |
| `ae_eval_ne_zero_uncurry` | the a.e. statement over matrix-shaped points |
| `volume_ne_zero_pi_pi` | `volume` on `ι → κ → ℝ` is not the zero measure |

The two currying transfer lemmas the last two are proved through --
`volume_measurePreserving_uncurry` and `volume_measurePreserving_curry` -- are
`private`. They are named nowhere outside this file, so exporting them would pin
an API surface no consumer reads.

## Why the hypothesis is `NullSingletonClass` on each factor rather than Haar

The induction needs exactly one thing from the measure on each coordinate: that
a *finite* set is null, which is `NullSingletonClass`. Stating it that way costs nothing
and makes the Gaussian and uniform cases corollaries rather than separate
proofs; Haar on `Fin n → ℝ` follows because it is a scalar multiple of
`volume`. `SigmaFinite` is what `MeasureTheory.Measure.pi` and Tonelli need,
and is not otherwise used.

## Provenance

This module is written to be lifted upstream: the declarations are named as
Mathlib would name them and the proofs use no atlas definitions. It is stated
where it can be reviewed against Mathlib rather than against the problem that
motivated it.

That problem is MAIS-O38 (`prob:samples`, MAIS-A3 Problem 4.8), whose
full-sparsity finding was stuck at a pointwise statement for want of exactly
this lemma: it needs the spark-condition set to be non-null, and print
quantifies over dictionaries almost everywhere. The one consumer is
`AISafetyAtlas.Examples.Conjectures.MAIS.ae_sparkCondition`, which spends
`ae_eval_ne_zero_uncurry` on a minor determinant; nothing in this module
mentions that problem's vocabulary, and the transcription lives elsewhere.

`volume_ne_zero_pi_pi` is here for the same consumer and is the one declaration
below that is not a genericity statement. An almost-everywhere statement refutes
nothing over the zero measure, so a contradiction drawn from `∀ᵐ x, False` has
to know the measure is not zero; `ι → κ → ℝ` carries no `IsAddHaarMeasure`
instance, since the instance is on the flat `ι → ℝ`.
-/

namespace AISafetyAtlas.Analysis

open MeasureTheory MvPolynomial

section Measurability

/-- Gluing a scalar onto a tuple is measurable. Used to move between
`Fin (n + 1) → ℝ` and `ℝ × (Fin n → ℝ)`. -/
private theorem measurable_finCons {n : ℕ} :
    Measurable fun z : ℝ × (Fin n → ℝ) => (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simpa using measurable_fst
  · intro j
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

/-- Evaluation of a fixed polynomial at a glued tuple is measurable in the pair. -/
private theorem measurable_eval_finCons {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    Measurable fun z : ℝ × (Fin n → ℝ) => MvPolynomial.eval (Fin.cons z.1 z.2) p :=
  (MvPolynomial.continuous_eval (p := p)).measurable.comp measurable_finCons

end Measurability

section Pi

/-- The induction, with the instance arguments made explicit so that the
inductive step may apply it at the shifted family `fun j => μ j.succ`. -/
private theorem ae_eval_ne_zero_pi_aux :
    ∀ (n : ℕ) (μ : Fin n → Measure ℝ), (∀ i, SigmaFinite (μ i)) → (∀ i, NullSingletonClass (μ i)) →
      ∀ p : MvPolynomial (Fin n) ℝ, p ≠ 0 →
        ∀ᵐ x ∂(Measure.pi μ), MvPolynomial.eval x p ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro μ _ _ p hp
    filter_upwards with x
    -- No variables to evaluate at: `p` is a constant, and it is a nonzero one.
    -- Routing through `isEmptyRingEquiv` no longer discharges the side goal, so
    -- the constant is named directly.
    have hC : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := MvPolynomial.eq_C_of_isEmpty p
    have hne : MvPolynomial.coeff 0 p ≠ 0 := fun h => hp (by rw [hC, h, map_zero])
    rw [hC, MvPolynomial.eval_C]
    exact hne
  | succ n ih =>
    intro μ hσ hA p hp
    have : ∀ i, SigmaFinite (μ i) := hσ
    have : ∀ i, NullSingletonClass (μ i) := hA
    -- Split off the zeroth variable: `q` is `p` read as a univariate polynomial
    -- in `X 0` over the remaining variables.
    set q : Polynomial (MvPolynomial (Fin n) ℝ) := MvPolynomial.finSuccEquiv ℝ n p with hqdef
    have hq : q ≠ 0 := by simpa [hqdef] using hp
    have hc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    -- The inductive hypothesis, at the leading coefficient and the shifted family.
    have hIH :
        ∀ᵐ s ∂(Measure.pi fun j : Fin n => μ j.succ),
          MvPolynomial.eval s q.leadingCoeff ≠ 0 :=
      ih (fun j => μ j.succ) (fun j => hσ _) (fun j => hA _) _ hc
    -- Off that exceptional set the specialised univariate polynomial is nonzero,
    -- so it has finitely many roots, and `NullSingletonClass` makes them null.
    have key :
        ∀ᵐ s ∂(Measure.pi fun j : Fin n => μ j.succ),
          ∀ᵐ y ∂(μ 0), MvPolynomial.eval (Fin.cons y s) p ≠ 0 := by
      filter_upwards [hIH] with s hs
      have hmap : q.map (MvPolynomial.eval s) ≠ 0 := by
        rw [← Polynomial.leadingCoeff_ne_zero,
          Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hs]
        exact hs
      have hnull : μ 0 {y : ℝ | (q.map (MvPolynomial.eval s)).IsRoot y} = 0 :=
        (Polynomial.finite_setOfPred_isRoot hmap).measure_zero _
      have hae : ∀ᵐ y ∂(μ 0), ¬ (q.map (MvPolynomial.eval s)).IsRoot y := by
        rw [MeasureTheory.ae_iff]; simpa using hnull
      filter_upwards [hae] with y hy
      rw [MvPolynomial.eval_eq_eval_mv_eval' s y p]
      exact hy
    -- Swap the two quantifiers.
    have hswap :
        ∀ᵐ y ∂(μ 0), ∀ᵐ s ∂(Measure.pi fun j : Fin n => μ j.succ),
          MvPolynomial.eval (Fin.cons y s) p ≠ 0 := by
      rw [← MeasureTheory.Measure.ae_ae_comm]
      · exact key
      · exact ((measurable_eval_finCons p).comp measurable_swap) (measurableSet_singleton 0).compl
    -- Assemble on the product and transfer back along the splitting.
    have hprod :
        ∀ᵐ z ∂((μ 0).prod (Measure.pi fun j : Fin n => μ j.succ)),
          MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0 :=
      (MeasureTheory.Measure.ae_prod_iff_ae_ae
        ((measurable_eval_finCons p) (measurableSet_singleton 0).compl)).2 hswap
    have hmp := MeasureTheory.measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
    have hmp' :
        Measure.map (fun x : Fin (n + 1) → ℝ => (x 0, Fin.tail x))
          (Measure.pi μ) = (μ 0).prod (Measure.pi fun j : Fin n => μ j.succ) := by
      simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using hmp.map_eq
    rw [← hmp'] at hprod
    rw [MeasureTheory.ae_map_iff] at hprod
    · filter_upwards [hprod] with x hx
      simpa [Fin.cons_self_tail] using hx
    · exact ((measurable_pi_apply 0).prodMk
        (measurable_pi_iff.2 fun j => measurable_pi_apply _)).aemeasurable
    · exact (measurable_eval_finCons p) (measurableSet_singleton 0).compl

/-- **A nonzero polynomial is almost everywhere nonzero**, for any product of
atomless measures on the coordinates.

`NullSingletonClass` is the whole content of the hypothesis: the induction needs only that
a finite set of roots is null in each coordinate. `SigmaFinite` is what
`MeasureTheory.Measure.pi` and the Fubini step require. -/
public theorem ae_eval_ne_zero_pi {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)]
    {p : MvPolynomial (Fin n) ℝ} (hp : p ≠ 0) :
    ∀ᵐ x ∂(Measure.pi μ), MvPolynomial.eval x p ≠ 0 :=
  ae_eval_ne_zero_pi_aux n μ inferInstance inferInstance p hp

/-- The null-set form of `ae_eval_ne_zero_pi`. -/
public theorem measure_setOf_eval_eq_zero_pi {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)]
    {p : MvPolynomial (Fin n) ℝ} (hp : p ≠ 0) :
    Measure.pi μ {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  have := ae_eval_ne_zero_pi μ hp
  rw [MeasureTheory.ae_iff] at this
  simpa using this

end Pi

section Lebesgue

/-- **A nonzero real polynomial vanishes only on a Lebesgue null set.** This is
the form genericity arguments quote: a property that fails only where a fixed
nonzero polynomial vanishes holds for almost every point. -/
public theorem ae_eval_ne_zero {n : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ, MvPolynomial.eval x p ≠ 0 := by
  rw [MeasureTheory.volume_pi]
  exact ae_eval_ne_zero_pi _ hp

end Lebesgue

section Fintype

/-- **The statement at an arbitrary finite variable type.** `Fin n` is the shape
the induction runs in, but the genericity arguments that want this lemma index
their variables by products (`Fin n × Fin m` for a matrix of indeterminates),
so the reindexed form is the one that gets applied. -/
public theorem ae_eval_ne_zero_fintype {ι : Type*} [Fintype ι]
    {p : MvPolynomial ι ℝ} (hp : p ≠ 0) :
    ∀ᵐ x : ι → ℝ, MvPolynomial.eval x p ≠ 0 := by
  classical
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  set q : MvPolynomial (Fin (Fintype.card ι)) ℝ :=
    MvPolynomial.rename (e.symm : ι → Fin (Fintype.card ι)) p with hqdef
  have hq : q ≠ 0 := fun h =>
    hp (MvPolynomial.rename_injective _ e.symm.injective (by simpa [hqdef] using h))
  have hFin : ∀ᵐ y : Fin (Fintype.card ι) → ℝ, MvPolynomial.eval y q ≠ 0 :=
    ae_eval_ne_zero hq
  have hmp := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e
  have hmeas : MeasurableSet {x : ι → ℝ | MvPolynomial.eval x p ≠ 0} :=
    (MvPolynomial.continuous_eval (p := p)).measurable (measurableSet_singleton 0).compl
  rw [← hmp.map_eq, MeasureTheory.ae_map_iff hmp.measurable.aemeasurable hmeas]
  filter_upwards [hFin] with y hy
  have hxy : (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) y = y ∘ e.symm := by
    funext j
    simpa using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e y (e.symm j)
  rw [hxy]
  simpa [hqdef, MvPolynomial.eval_rename] using hy

/-- The null-set form of `ae_eval_ne_zero_fintype`. -/
public theorem volume_setOf_eval_eq_zero {ι : Type*} [Fintype ι]
    {p : MvPolynomial ι ℝ} (hp : p ≠ 0) :
    volume {x : ι → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  have := ae_eval_ne_zero_fintype hp
  rw [MeasureTheory.ae_iff] at this
  simpa using this

/-- **A finite list of nonzero polynomials vanishes only on a null set.** Each
member's zero set is null, and finitely many null sets union to a null set.

This is the form a covering argument needs: if some *set* of positive measure is
covered by the vanishing loci of a finite list, then one member of the list is
the zero polynomial. -/
public theorem volume_setOf_exists_eval_eq_zero {ι : Type*} [Fintype ι]
    (l : List (MvPolynomial ι ℝ)) (hl : ∀ p ∈ l, p ≠ 0) :
    volume {x : ι → ℝ | ∃ p ∈ l, MvPolynomial.eval x p = 0} = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hset : {x : ι → ℝ | ∃ p ∈ a :: t, MvPolynomial.eval x p = 0} =
        {x : ι → ℝ | MvPolynomial.eval x a = 0} ∪
          {x : ι → ℝ | ∃ p ∈ t, MvPolynomial.eval x p = 0} := by
      ext x
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨p, hp | hp, hz⟩
        · exact Or.inl (hp ▸ hz)
        · exact Or.inr ⟨p, hp, hz⟩
      · rintro (hz | ⟨p, hp, hz⟩)
        · exact ⟨a, Or.inl rfl, hz⟩
        · exact ⟨p, Or.inr hp, hz⟩
    rw [hset]
    exact measure_union_null (volume_setOf_eval_eq_zero (hl a (List.mem_cons_self ..)))
      (ih fun p hp ↦ hl p (List.mem_cons_of_mem a hp))

/-- **The additive Haar form.** Every additive Haar measure on `ι → ℝ` is a
scalar multiple of `volume`, so it discards the same null sets. -/
public theorem ae_eval_ne_zero_addHaar {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ))
    [μ.IsAddHaarMeasure] {p : MvPolynomial ι ℝ} (hp : p ≠ 0) :
    ∀ᵐ x ∂μ, MvPolynomial.eval x p ≠ 0 := by
  have hac : μ ≪ volume := by
    conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ (volume : Measure (ι → ℝ))]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  exact hac.ae_le (ae_eval_ne_zero_fintype hp)

end Fintype

section Curry

/-! ## Matrix-shaped variables

A genericity argument about matrices indexes its indeterminates by `ι × κ` but
quantifies over the function space `ι → κ → ℝ`, so it needs currying to be
measure preserving. Mathlib has `MeasurableEquiv.curry` and the
infinite-product statements `ProbabilityTheory.infinitePi_map_piCurry` and
`infinitePi_map_piCurry_symm`, but no finite-product `volume` form. -/

/-- **Uncurrying is measure preserving** for finite products of Lebesgue
measure. This is the direction that proves itself: the target is a flat product,
so `MeasureTheory.Measure.pi_eq` applies, and the preimage of a box is a box of
boxes.

Private: nothing outside this file names it. It is the proof of
`volume_measurePreserving_curry` and of `volume_ne_zero_pi_pi`, and those two
are what the genericity arguments call. -/
private theorem volume_measurePreserving_uncurry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ).symm
      (volume : Measure (ι → κ → ℝ)) (volume : Measure (ι × κ → ℝ)) where
  measurable := (MeasurableEquiv.curry ι κ ℝ).symm.measurable
  map_eq := by
    rw [MeasureTheory.volume_pi]
    refine (Measure.pi_eq fun t _ => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have hpre : (MeasurableEquiv.curry ι κ ℝ).symm ⁻¹' (Set.univ.pi t)
        = Set.univ.pi fun i => Set.univ.pi fun j => t (i, j) := by
      ext x
      simp [MeasurableEquiv.coe_curry_symm, Function.uncurry, Set.mem_pi, Prod.forall]
    rw [hpre, MeasureTheory.volume_pi, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_prod_type (fun q : ι × κ => volume (t q))).symm

/-- **Currying is measure preserving**, the form the genericity argument uses.

Private for the same reason as `volume_measurePreserving_uncurry`: it is the
proof of `ae_eval_ne_zero_uncurry` and is named nowhere else. -/
private theorem volume_measurePreserving_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ)
      (volume : Measure (ι × κ → ℝ)) (volume : Measure (ι → κ → ℝ)) := by
  simpa using
    (volume_measurePreserving_uncurry ι κ).symm (MeasurableEquiv.curry ι κ ℝ).symm

/-- Evaluation at an uncurried point is measurable in the matrix. -/
private theorem measurable_eval_uncurry {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : MvPolynomial (ι × κ) ℝ) :
    Measurable fun A : ι → κ → ℝ => MvPolynomial.eval (Function.uncurry A) p :=
  (MvPolynomial.continuous_eval (p := p)).measurable.comp
    (measurable_pi_iff.2 fun q => (measurable_pi_apply q.2).comp (measurable_pi_apply q.1))

/-- **A nonzero polynomial in matrix-indexed variables is nonzero at almost
every matrix.** `ae_eval_ne_zero_fintype` states this over `ι × κ → ℝ`; this is
the same fact over `ι → κ → ℝ`, which is where a statement about matrices
quantifies. -/
public theorem ae_eval_ne_zero_uncurry {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : MvPolynomial (ι × κ) ℝ} (hp : p ≠ 0) :
    ∀ᵐ A : ι → κ → ℝ, MvPolynomial.eval (Function.uncurry A) p ≠ 0 := by
  have hmp := volume_measurePreserving_curry ι κ
  have hmeas : MeasurableSet {A : ι → κ → ℝ | MvPolynomial.eval (Function.uncurry A) p ≠ 0} :=
    (measurable_eval_uncurry p) (measurableSet_singleton 0).compl
  rw [← hmp.map_eq, MeasureTheory.ae_map_iff hmp.measurable.aemeasurable hmeas]
  filter_upwards [ae_eval_ne_zero_fintype hp] with x hx
  simpa [MeasurableEquiv.coe_curry] using hx

/-- `volume` on a matrix-shaped function space is not the zero measure.

Needed wherever an almost-everywhere statement is used to *refute* something:
`∀ᵐ x, False` is harmless over the zero measure, so a contradiction drawn from
one has to know the measure is nonzero. `Fin n → Fin m → ℝ` carries no
`IsAddHaarMeasure` instance — the instance is on the flat `ι → ℝ` — so this is
transported across `volume_measurePreserving_uncurry` rather than looked up. -/
public theorem volume_ne_zero_pi_pi (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (volume : Measure (ι → κ → ℝ)) ≠ 0 := by
  intro h
  have := isAddHaarMeasure_volume_pi (ι × κ)
  have hpos : 0 < (volume : Measure (ι × κ → ℝ)) Set.univ :=
    isOpen_univ.measure_pos volume Set.univ_nonempty
  refine hpos.ne' ?_
  rw [← (volume_measurePreserving_uncurry ι κ).map_eq, MeasurableEquiv.map_apply, h]
  simp

end Curry

end AISafetyAtlas.Analysis
