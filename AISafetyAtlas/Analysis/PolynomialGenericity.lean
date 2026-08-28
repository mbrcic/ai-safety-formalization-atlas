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

## Why the hypothesis is `NoAtoms` on each factor rather than Haar

The induction needs exactly one thing from the measure on each coordinate: that
a *finite* set is null, which is `NoAtoms`. Stating it that way costs nothing
and makes the Gaussian and uniform cases corollaries rather than separate
proofs; Haar on `Fin n → ℝ` follows because it is a scalar multiple of
`volume`. `SigmaFinite` is what `MeasureTheory.Measure.pi` and Tonelli need,
and is not otherwise used.

## Provenance

This module is written to be lifted upstream: the declarations are named as
Mathlib would name them and the proofs use no atlas definitions. **Nothing in
this tree consumes it yet**, and that is deliberate — it is stated where it can
be reviewed against Mathlib rather than against the problem that motivated it.

That problem is MAIS-O38 (`prob:samples`, MAIS-A3 Problem 4.8), whose
full-sparsity finding is stuck at a pointwise statement for want of exactly this
lemma: it needs the spark-condition set to be non-null, and print quantifies
over dictionaries almost everywhere. The transcription of that problem, and the
searches recording this lemma's absence from Mathlib, live on the conjecture
branch and are not in this tree.
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
    ∀ (n : ℕ) (μ : Fin n → Measure ℝ), (∀ i, SigmaFinite (μ i)) → (∀ i, NoAtoms (μ i)) →
      ∀ p : MvPolynomial (Fin n) ℝ, p ≠ 0 →
        ∀ᵐ x ∂(Measure.pi μ), MvPolynomial.eval x p ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro μ _ _ p hp
    filter_upwards with x
    have hx : MvPolynomial.eval x p = MvPolynomial.isEmptyRingEquiv ℝ (Fin 0) p := by
      simp [MvPolynomial.isEmptyRingEquiv, MvPolynomial.isEmptyAlgEquiv,
        MvPolynomial.aeval_def, Subsingleton.elim x isEmptyElim]
    rw [hx]
    exact fun h => hp ((map_eq_zero_iff _ (MvPolynomial.isEmptyRingEquiv ℝ (Fin 0)).injective).1 h)
  | succ n ih =>
    intro μ hσ hA p hp
    haveI : ∀ i, SigmaFinite (μ i) := hσ
    haveI : ∀ i, NoAtoms (μ i) := hA
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
    -- so it has finitely many roots, and `NoAtoms` makes them null.
    have key :
        ∀ᵐ s ∂(Measure.pi fun j : Fin n => μ j.succ),
          ∀ᵐ y ∂(μ 0), MvPolynomial.eval (Fin.cons y s) p ≠ 0 := by
      filter_upwards [hIH] with s hs
      have hmap : q.map (MvPolynomial.eval s) ≠ 0 := by
        rw [← Polynomial.leadingCoeff_ne_zero,
          Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hs]
        exact hs
      have hnull : μ 0 {y : ℝ | (q.map (MvPolynomial.eval s)).IsRoot y} = 0 :=
        (Polynomial.finite_setOf_isRoot hmap).measure_zero _
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

`NoAtoms` is the whole content of the hypothesis: the induction needs only that
a finite set of roots is null in each coordinate. `SigmaFinite` is what
`MeasureTheory.Measure.pi` and the Fubini step require. -/
public theorem ae_eval_ne_zero_pi {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, NoAtoms (μ i)]
    {p : MvPolynomial (Fin n) ℝ} (hp : p ≠ 0) :
    ∀ᵐ x ∂(Measure.pi μ), MvPolynomial.eval x p ≠ 0 :=
  ae_eval_ne_zero_pi_aux n μ inferInstance inferInstance p hp

/-- The null-set form of `ae_eval_ne_zero_pi`. -/
public theorem measure_setOf_eval_eq_zero_pi {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, NoAtoms (μ i)]
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

end AISafetyAtlas.Analysis
