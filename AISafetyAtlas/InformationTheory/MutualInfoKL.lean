module

public import AISafetyAtlas.InformationTheory.DataProcessing
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Mutual information in `[0, ∞]`

Cover & Thomas, *Elements of Information Theory*, 2nd ed. (2006), define mutual
information as a relative entropy, (2.28)–(2.29), PDF pp. 45–46:

`I(X; Y) = Σ p(x, y) log p(x, y)/(p(x)p(y)) = D(p(x, y) ‖ p(x)p(y))`,

for discrete random variables whose alphabets are not assumed finite (§2.1, PDF
p. 39; Problem 2.1 uses an infinite alphabet). With the conventions of (2.26),
`D` takes values in `[0, ∞]`, and `I(X; Y) = ∞` happens on a countable alphabet.

PFR's `I[X : Y]`, which the rest of `AISafetyAtlas.InformationTheory` uses, is
real-valued: its entropies are `tsum`s, which return the junk value `0` when the
series diverges, so every theorem about it carries `FiniteRange`. Dropping those
instances is not enough: with the junk value, the data-processing inequality and
the chain rule become false (the witnesses are in the defect records of audit
rows S01-R05 and S01-R07 to S01-R10).

This module is print's object instead. `mutualInfoKL` is Mathlib's `ℝ≥0∞`-valued
`InformationTheory.klDiv` between the joint law and the product of the marginals,
which is (2.29) verbatim; `condMutualInfoKL` is the relative entropy of (2.61),
`E_{p(x,y,z)} log p(X, Y | Z)/(p(X | Z) p(Y | Z))`, written as one KL divergence
between the joint law of `((X, Z), Y)` and `p(x, z) p(y | z)`. Everything is
proved in `[0, ∞]`, for countable alphabets with measurable singletons, with no
finiteness of any alphabet, entropy or information:

* `mutualInfoKL_comp_le` — `I(X; g(Y)) ≤ I(X; Y)` (first corollary to Thm 2.8.1);
* `mutualInfoKL_pair_eq_add` — the chain rule `I(X; Y, Z) = I(X; Z) + I(X; Y | Z)`,
  (2.119)/(2.120), from Mathlib's chain rule for `klDiv`;
* `mutualInfoKL_pair_eq_add'` — the other order, `I(X; Y, Z) = I(X; Y) + I(X; Z | Y)`;
* `mutualInfoKL_chain_rule_fin'` — Theorem 2.5.2 for a finite family, in print's
  argument order (`mutualInfoKL_chain_rule_fin` with `Y` first), and
  `mutualInfoKL_chain_rule_pi` with one countable alphabet per index;
* `mutualInfoKL_comm`, `condMutualInfoKL_comm` — symmetry;
* `isMarkovChain_iff_condMutualInfoKL_eq_zero` — `X → Y → Z` iff `I(X; Z | Y) = 0`;
* `mutualInfoKL_le_of_isMarkovChain` — Theorem 2.8.1;
* `mutualInfoKL_le_of_isMarkovChain'` — "similarly, `I(Y; Z) ≥ I(X; Z)`";
* `condMutualInfoKL_le_mutualInfoKL` — the second corollary, `I(X; Y | Z) ≤ I(X; Y)`;
* `mutualInfoKL_eq_iff_isMarkovChain`, `mutualInfoKL_eq_iff_condMutualInfoKL_eq_zero` —
  the equality clause of Theorem 2.8.1 as repaired: under `X → Y → Z` with
  `I(X; Y) < ∞`, `I(X; Z) = I(X; Y)` iff `I(X; Y | Z) = 0` iff `X → Z → Y`; the "if"
  direction, `mutualInfoKL_eq_of_isMarkovChain`, needs no finiteness;
* `mutualInfoKL_eq_ofReal_mutualInfo` — on finite ranges the new carrier is PFR's
  `I[X : Y]`, so the `FiniteRange` theorems of `DataProcessing` are restrictions of
  the ones here.

The logarithm is natural, where print uses base 2; that rescales every value by
the same positive constant and leaves `0` and `∞` fixed.

`mutualInfoKL` and the countable-alphabet lemma `rnDeriv_singleton` first appeared
in the refutation `docs/provenance/refutations/cover-thomas-2-8-1-literal.lean` (as
`miENN`), which shows that print's equality clause fails at `I(X; Y) = ∞`. That
file's conditional form `cmiENN` takes (2.61)'s expectation over `z` first, as
`∑ z, p(z) I(X; Y | Z = z)`; `condMutualInfoKL` is the same quantity written as one
relative entropy, the form Mathlib's chain rule `klDiv_compProd_eq_add` produces.
The equality of the two forms is not proved here.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace AISafetyAtlas.InformationTheory

section General

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U]

/-- **Mutual information in `[0, ∞]`**, Cover & Thomas (2.28)–(2.29), PDF pp. 45–46:
the relative entropy `D(p(x, y) ‖ p(x)p(y))` between the joint law of `(X, Y)` and
the product of the marginals. -/
@[expose] public noncomputable def mutualInfoKL (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    ℝ≥0∞ :=
  klDiv (μ.map fun ω => (X ω, Y ω)) ((μ.map X).prod (μ.map Y))

variable {X : Ω → S} {Y : Ω → T} {μ : Measure Ω}

/-- **Processing the second argument cannot increase mutual information**, Cover &
Thomas, first corollary to Theorem 2.8.1 (unnumbered, PDF p. 61): "if `Z = g(Y)`,
we have `I(X; Y) ≥ I(X; g(Y))`". Proved in `[0, ∞]` from Mathlib's data-processing
inequality for `klDiv`, with no restriction on the alphabets. -/
public theorem mutualInfoKL_comp_le [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    {g : T → U} (hg : Measurable g) :
    mutualInfoKL X (g ∘ Y) μ ≤ mutualInfoKL X Y μ := by
  have hm : Measurable (Prod.map (id : S → S) g) := measurable_id.prodMap hg
  have h := klDiv_map_le (μ.map fun ω => (X ω, Y ω)) ((μ.map X).prod (μ.map Y)) hm
  rw [Measure.map_map hm (hX.prodMk hY), ← Measure.map_prod_map _ _ measurable_id hg,
    Measure.map_id, Measure.map_map hg hY] at h
  exact h

/-- Mutual information is unchanged by a measurable relabelling of the second
argument. -/
public theorem mutualInfoKL_comp_equiv [IsFiniteMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (e : T ≃ᵐ U) :
    mutualInfoKL X (e ∘ Y) μ = mutualInfoKL X Y μ := by
  refine le_antisymm (mutualInfoKL_comp_le hX hY e.measurable) ?_
  have h := mutualInfoKL_comp_le (μ := μ) hX (e.measurable.comp hY) e.symm.measurable
  rwa [← Function.comp_assoc, MeasurableEquiv.symm_comp_self, Function.id_comp] at h

omit [MeasurableSpace U] in
private theorem mutualInfoKL_swap_le [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    mutualInfoKL Y X μ ≤ mutualInfoKL X Y μ := by
  have h := klDiv_map_le (μ.map fun ω => (X ω, Y ω)) ((μ.map X).prod (μ.map Y)) measurable_swap
  rw [Measure.map_map measurable_swap (hX.prodMk hY), Measure.prod_swap] at h
  exact h

omit [MeasurableSpace U] in
/-- **Mutual information is symmetric**, `I(X; Y) = I(Y; X)`. -/
public theorem mutualInfoKL_comm [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    mutualInfoKL X Y μ = mutualInfoKL Y X μ :=
  le_antisymm (mutualInfoKL_swap_le hY hX) (mutualInfoKL_swap_le hX hY)

/-- `klDiv` is invariant under a measurable equivalence. -/
private theorem klDiv_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rwa [Measure.map_map e.symm.measurable e.measurable,
    Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id,
    Measure.map_id] at h

end General


section Countable

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- **The conditional law `p(y | z)` of `Y` given `Z`**, as a kernel from `Z`'s
countable alphabet: `μ[|Z = z]` pushed forward by `Y`. On a null fibre, where print
leaves `p(y | z)` undefined, it is the marginal law of `Y`; every statement below
weighs it by `p(z) = 0` there. -/
@[expose] public noncomputable def condLaw (Z : Ω → U) (Y : Ω → T) (μ : Measure Ω) :
    Kernel U T :=
  Kernel.ofFunOfCountable fun z =>
    if μ (Z ⁻¹' {z}) = 0 then μ.map Y else (μ[|Z ⁻¹' {z}]).map Y

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T] in
/-- The conditional law is a Markov kernel. -/
public theorem isMarkovKernel_condLaw [IsProbabilityMeasure μ] (hY : Measurable Y) :
    IsMarkovKernel (condLaw Z Y μ) := by
  refine ⟨fun z => ?_⟩
  change IsProbabilityMeasure (if μ (Z ⁻¹' {z}) = 0 then μ.map Y else (μ[|Z ⁻¹' {z}]).map Y)
  split_ifs with h
  · exact Measure.isProbabilityMeasure_map hY.aemeasurable
  · have := cond_isProbabilityMeasure (μ := μ) h
    exact Measure.isProbabilityMeasure_map hY.aemeasurable

omit [MeasurableSingletonClass S] [Countable S] [Countable T] in
/-- `p(y | z) p(z) = p(z, y)`. -/
public theorem condLaw_singleton_mul [IsFiniteMeasure μ] (hZ : Measurable Z) (hY : Measurable Y)
    (z : U) (y : T) :
    condLaw Z Y μ z {y} * μ (Z ⁻¹' {z}) = μ (Z ⁻¹' {z} ∩ Y ⁻¹' {y}) := by
  change (if μ (Z ⁻¹' {z}) = 0 then μ.map Y else (μ[|Z ⁻¹' {z}]).map Y) {y} * μ (Z ⁻¹' {z})
    = μ (Z ⁻¹' {z} ∩ Y ⁻¹' {y})
  split_ifs with h
  · rw [h, mul_zero]
    exact (measure_mono_null Set.inter_subset_left h).symm
  · rw [Measure.map_apply hY (measurableSet_singleton y),
      cond_apply (hZ (measurableSet_singleton z)), mul_comm, ← mul_assoc,
      ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_mul]

omit [MeasurableSingletonClass S] [Countable S] in
/-- **Disintegration on a countable alphabet**: the joint law of `(Z, Y)` is the law
of `Z` composed with the conditional law of `Y` given `Z`, `p(z, y) = p(z) p(y | z)`. -/
public theorem map_pair_eq_compProd_condLaw [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hY : Measurable Y) :
    μ.map (fun ω => (Z ω, Y ω)) = μ.map Z ⊗ₘ condLaw Z Y μ := by
  have := isMarkovKernel_condLaw (Z := Z) (μ := μ) hY
  refine Measure.ext_of_singleton fun ⟨z, y⟩ => ?_
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod (measurableSet_singleton z)
      (measurableSet_singleton y), lintegral_singleton, Measure.map_apply (hZ.prodMk hY)
      ((measurableSet_singleton z).prod (measurableSet_singleton y)),
    Measure.map_apply hZ (measurableSet_singleton z), condLaw_singleton_mul hZ hY, Set.mk_preimage_prod]

/-- **Conditional mutual information in `[0, ∞]`**, Cover & Thomas (2.61), PDF p. 49:
`I(X; Y | Z) = E_{p(x,y,z)} log p(X, Y | Z)/(p(X | Z) p(Y | Z))`. It is the relative
entropy between the joint law of `((X, Z), Y)` and `p(x, z) p(y | z)`, whose ratio
`p(x, z, y)/(p(x, z) p(y | z))` is print's `p(x, y | z)/(p(x | z) p(y | z))`. -/
@[expose] public noncomputable def condMutualInfoKL (X : Ω → S) (Y : Ω → T) (Z : Ω → U)
    (μ : Measure Ω) : ℝ≥0∞ :=
  klDiv (μ.map fun ω => ((X ω, Z ω), Y ω))
    (μ.map (fun ω => (X ω, Z ω)) ⊗ₘ Kernel.prodMkLeft S (condLaw Z Y μ))

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U] in
/-- The reassociation `(x, (y, z)) ↦ ((x, z), y)`. -/
private def reassoc : S × (T × U) ≃ᵐ (S × U) × T where
  toFun p := ((p.1, p.2.2), p.2.1)
  invFun q := (q.1.1, (q.2, q.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

/-- The product of the marginals of `X` and `(Y, Z)`, reassociated, is
`p(x) p(z) p(y | z)`. -/
private theorem map_reassoc_prod [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) :
    ((μ.map X).prod (μ.map fun ω => (Y ω, Z ω))).map reassoc
      = (μ.map X).prod (μ.map Z) ⊗ₘ Kernel.prodMkLeft S (condLaw Z Y μ) := by
  have := isMarkovKernel_condLaw (Z := Z) (μ := μ) hY
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨⟨x, z⟩, y⟩ := p
  have hpre : (reassoc : S × (T × U) ≃ᵐ (S × U) × T) ⁻¹' {((x, z), y)} = {x} ×ˢ {(y, z)} := by
    ext ⟨a, b, c⟩
    simp [reassoc, Prod.ext_iff]
    tauto
  rw [Measure.map_apply reassoc.measurable (measurableSet_singleton _), hpre,
    Measure.prod_prod, ← Set.singleton_prod_singleton (a := (x, z)),
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton y),
    lintegral_singleton, Kernel.prodMkLeft_apply, ← Set.singleton_prod_singleton (a := y),
    ← Set.singleton_prod_singleton (a := x), Measure.prod_prod, Measure.map_apply hX (measurableSet_singleton x),
    Measure.map_apply hZ (measurableSet_singleton z),
    Measure.map_apply (hY.prodMk hZ) ((measurableSet_singleton y).prod (measurableSet_singleton z)),
    Set.mk_preimage_prod, mul_left_comm, condLaw_singleton_mul hZ hY, Set.inter_comm]

/-- **Chain rule for mutual information in `[0, ∞]`**, Cover & Thomas (2.119)/(2.120),
PDF p. 60 (the `n = 2` case of Theorem 2.5.2): `I(X; Y, Z) = I(X; Z) + I(X; Y | Z)`,
for countable alphabets and with every term allowed to be infinite. It is Mathlib's
chain rule for `klDiv` (`klDiv_compProd_eq_add`) after disintegrating both laws
along `(X, Z)`. -/
public theorem mutualInfoKL_pair_eq_add [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) :
    mutualInfoKL X (fun ω => (Y ω, Z ω)) μ = mutualInfoKL X Z μ + condMutualInfoKL X Y Z μ := by
  have := isMarkovKernel_condLaw (Z := Z) (μ := μ) hY
  have := isMarkovKernel_condLaw (Z := fun ω => (X ω, Z ω)) (μ := μ) hY
  have hjoint : (μ.map fun ω => (X ω, (Y ω, Z ω))).map reassoc
      = μ.map (fun ω => ((X ω, Z ω), Y ω)) := by
    rw [Measure.map_map reassoc.measurable (hX.prodMk (hY.prodMk hZ))]
    rfl
  have hcp := map_pair_eq_compProd_condLaw (μ := μ) (hX.prodMk hZ) hY
  rw [mutualInfoKL, ← klDiv_map_equiv reassoc, hjoint,
    map_reassoc_prod hX hY hZ, hcp, klDiv_compProd_eq_add, condMutualInfoKL, hcp]
  · rfl

omit [Countable S] [Countable U] in
/-- The singleton masses of the reference law of `I(X; Z | Y)`: `p(x, y) p(z | y)`. -/
private theorem compProd_condLaw_singleton [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (x : S) (y : T) (z : U) :
    (μ.map (fun ω => (X ω, Y ω)) ⊗ₘ Kernel.prodMkLeft S (condLaw Y Z μ)) {((x, y), z)}
      = condLaw Y Z μ y {z} * μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) := by
  have := isMarkovKernel_condLaw (Z := Y) (μ := μ) hZ
  rw [← Set.singleton_prod_singleton (a := (x, y)),
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton z),
    lintegral_singleton, Kernel.prodMkLeft_apply, Measure.map_apply (hX.prodMk hY)
      (measurableSet_singleton _), ← Set.singleton_prod_singleton, Set.mk_preimage_prod]

/-- **The Markov hypothesis in `[0, ∞]`**: `X → Y → Z` exactly when
`I(X; Z | Y) = 0`, for countable alphabets with no finiteness hypothesis. Cover &
Thomas use this reading in the proof of Theorem 2.8.1 (PDF pp. 60–61); the library's
`isMarkovChain_iff_condMutualInfo_eq_zero` is the same statement at PFR's real
`I[X : Z | Y]`, under `FiniteRange`. -/
public theorem isMarkovChain_iff_condMutualInfoKL_eq_zero [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    IsMarkovChain X Y Z μ ↔ condMutualInfoKL X Z Y μ = 0 := by
  have := isMarkovKernel_condLaw (Z := Y) (μ := μ) hZ
  rw [condMutualInfoKL, klDiv_eq_zero_iff, Measure.ext_iff_singleton,
    isMarkovChain_iff_measure_factorizes_singleton hX hY hZ]
  have hL : ∀ x y z, (μ.map fun ω => ((X ω, Y ω), Z ω)) {((x, y), z)}
      = μ (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z}) := by
    intro x y z
    rw [Measure.map_apply ((hX.prodMk hY).prodMk hZ) (measurableSet_singleton _)]
    congr 1
    ext ω
    simp [Prod.ext_iff, and_assoc]
  have key : ∀ x y z, (μ (Y ⁻¹' {y}) * μ (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z})
        = μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * μ (Y ⁻¹' {y} ∩ Z ⁻¹' {z}))
      ↔ μ (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z})
        = condLaw Y Z μ y {z} * μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) := by
    intro x y z
    rw [← condLaw_singleton_mul hY hZ y z]
    by_cases ha : μ (Y ⁻¹' {y}) = 0
    · have hb : μ (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z}) = 0 :=
        measure_mono_null (Set.inter_subset_left.trans Set.inter_subset_right) ha
      have hd : μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) = 0 := measure_mono_null Set.inter_subset_right ha
      simp [ha, hb, hd]
    · rw [← ENNReal.mul_right_inj ha (measure_ne_top μ _) (b := μ (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ _))]
      constructor <;> intro h <;> rw [h] <;> ring
  constructor
  · rintro h ⟨⟨x, y⟩, z⟩
    rw [hL, compProd_condLaw_singleton hX hY hZ]
    exact (key x y z).mp (h x y z)
  · intro h x y z
    have := h ((x, y), z)
    rw [hL, compProd_condLaw_singleton hX hY hZ] at this
    exact (key x y z).mpr this

/-- The chain rule in the other order, Cover & Thomas (2.120):
`I(X; Y, Z) = I(X; Y) + I(X; Z | Y)`. -/
public theorem mutualInfoKL_pair_eq_add' [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) :
    mutualInfoKL X (fun ω => (Y ω, Z ω)) μ = mutualInfoKL X Y μ + condMutualInfoKL X Z Y μ := by
  rw [← mutualInfoKL_pair_eq_add hX hZ hY,
    ← mutualInfoKL_comp_equiv hX (hZ.prodMk hY) MeasurableEquiv.prodComm]
  rfl

/-- **Data-processing inequality in `[0, ∞]`** (Cover & Thomas, Theorem 2.8.1, PDF
p. 60): if `X → Y → Z`, then `I(X; Y) ≥ I(X; Z)`. Discrete variables on countable
alphabets, with no finiteness of any alphabet or of any information; print's proof,
(2.119)–(2.121): `I(X; Z) ≤ I(X; Y, Z) = I(X; Y) + I(X; Z | Y) = I(X; Y)`. -/
public theorem mutualInfoKL_le_of_isMarkovChain [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (h : IsMarkovChain X Y Z μ) :
    mutualInfoKL X Z μ ≤ mutualInfoKL X Y μ := by
  have hle := mutualInfoKL_comp_le (μ := μ) hX (hY.prodMk hZ) measurable_snd
  rwa [mutualInfoKL_pair_eq_add' hX hY hZ,
    (isMarkovChain_iff_condMutualInfoKL_eq_zero hX hY hZ).mp h, add_zero] at hle

/-- **The source loses information too, in `[0, ∞]`** (Cover & Thomas, proof of
Theorem 2.8.1, PDF p. 61): "Similarly, one can prove that `I(Y; Z) ≥ I(X; Z)`", for
`X → Y → Z` on countable alphabets, with no finiteness hypothesis. -/
public theorem mutualInfoKL_le_of_isMarkovChain' [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (h : IsMarkovChain X Y Z μ) :
    mutualInfoKL X Z μ ≤ mutualInfoKL Y Z μ := by
  have := mutualInfoKL_le_of_isMarkovChain (μ := μ) hZ hY hX (isMarkovChain_comm.mp h)
  rwa [mutualInfoKL_comm hZ hX, mutualInfoKL_comm hZ hY] at this

/-- **Conditioning on a downstream variable cannot increase dependence, in `[0, ∞]`**
(Cover & Thomas, second corollary to Theorem 2.8.1, unnumbered, PDF p. 61): if
`X → Y → Z`, then `I(X; Y | Z) ≤ I(X; Y)`, on countable alphabets with no finiteness
hypothesis. The two chain rules give `I(X; Z) + I(X; Y | Z) = I(X; Y)`. -/
public theorem condMutualInfoKL_le_mutualInfoKL [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (h : IsMarkovChain X Y Z μ) :
    condMutualInfoKL X Y Z μ ≤ mutualInfoKL X Y μ := by
  have h1 := mutualInfoKL_pair_eq_add (μ := μ) hX hY hZ
  rw [mutualInfoKL_pair_eq_add' hX hY hZ,
    (isMarkovChain_iff_condMutualInfoKL_eq_zero hX hY hZ).mp h, add_zero] at h1
  rw [h1]
  exact le_add_self

/-- **Equality in data processing, in `[0, ∞]`, the "if" direction** (Cover & Thomas,
proof of Theorem 2.8.1, PDF p. 61): if `X → Y → Z` and also `X → Z → Y`, then
`I(X; Z) = I(X; Y)`. Countable alphabets, no finiteness of any alphabet or of any
information: the two data-processing inequalities meet. -/
public theorem mutualInfoKL_eq_of_isMarkovChain [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (h : IsMarkovChain X Y Z μ)
    (h' : IsMarkovChain X Z Y μ) :
    mutualInfoKL X Z μ = mutualInfoKL X Y μ :=
  le_antisymm (mutualInfoKL_le_of_isMarkovChain hX hY hZ h)
    (mutualInfoKL_le_of_isMarkovChain hX hZ hY h')

/-- **Equality in data processing, in `[0, ∞]`** (Cover & Thomas, proof of Theorem 2.8.1,
PDF p. 61, as repaired): under `X → Y → Z` with `I(X; Y) < ∞`, "we have equality if and
only if `I(X; Y | Z) = 0`". Countable alphabets, no finiteness of any alphabet. The two
chain rules give `I(X; Z) + I(X; Y | Z) = I(X; Y)`; the finiteness of `I(X; Y)` is what
cancels, and print's clause is false without it (`I(X; Y) = I(X; Z) = ∞`). -/
public theorem mutualInfoKL_eq_iff_condMutualInfoKL_eq_zero [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IsMarkovChain X Y Z μ)
    (hfin : mutualInfoKL X Y μ ≠ ∞) :
    mutualInfoKL X Z μ = mutualInfoKL X Y μ ↔ condMutualInfoKL X Y Z μ = 0 := by
  have h1 := mutualInfoKL_pair_eq_add (μ := μ) hX hY hZ
  rw [mutualInfoKL_pair_eq_add' hX hY hZ,
    (isMarkovChain_iff_condMutualInfoKL_eq_zero hX hY hZ).mp h, add_zero] at h1
  constructor
  · intro heq
    rw [heq] at h1
    exact (ENNReal.add_right_inj hfin).mp (h1.symm.trans (add_zero _).symm)
  · intro h0
    rw [h1, h0, add_zero]

/-- **Equality in data processing, in `[0, ∞]`, in print's Markov form** (Cover & Thomas,
proof of Theorem 2.8.1, PDF p. 61, as repaired): under `X → Y → Z` with `I(X; Y) < ∞`,
`I(X; Z) = I(X; Y)` exactly when `X → Z → Y`. Countable alphabets, no finiteness of any
alphabet; `mutualInfo_eq_iff_isMarkovChain` is its restriction to finite ranges, through
`mutualInfoKL_eq_ofReal_mutualInfo`. The "if" direction needs no finiteness
(`mutualInfoKL_eq_of_isMarkovChain`). -/
public theorem mutualInfoKL_eq_iff_isMarkovChain [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IsMarkovChain X Y Z μ)
    (hfin : mutualInfoKL X Y μ ≠ ∞) :
    mutualInfoKL X Z μ = mutualInfoKL X Y μ ↔ IsMarkovChain X Z Y μ := by
  rw [mutualInfoKL_eq_iff_condMutualInfoKL_eq_zero hX hY hZ h hfin,
    isMarkovChain_iff_condMutualInfoKL_eq_zero hX hZ hY]

omit [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass T] [Countable T] in
/-- A constant tells nothing: `I(X; c) = 0`. -/
public theorem mutualInfoKL_const [IsProbabilityMeasure μ] (hX : Measurable X) (c : T) :
    mutualInfoKL X (fun _ => c) μ = 0 := by
  rw [mutualInfoKL, Measure.map_const, measure_univ, one_smul, Measure.prod_dirac,
    Measure.map_map measurable_prodMk_right hX]
  exact klDiv_self _

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U] in
/-- Exchange the outer coordinates, `((x, z), y) ↦ ((y, z), x)`. -/
private def swapOuter : (S × U) × T ≃ᵐ (T × U) × S where
  toFun p := ((p.2, p.1.2), p.1.1)
  invFun q := ((q.2, q.1.2), q.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

/-- **Conditional mutual information is symmetric**, `I(X; Y | Z) = I(Y; X | Z)`: both
reference laws are `p(z) p(x | z) p(y | z)`. -/
public theorem condMutualInfoKL_comm [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) :
    condMutualInfoKL X Y Z μ = condMutualInfoKL Y X Z μ := by
  have := isMarkovKernel_condLaw (Z := Z) (μ := μ) hY
  have := isMarkovKernel_condLaw (Z := Z) (μ := μ) hX
  have hjoint : (μ.map fun ω => ((X ω, Z ω), Y ω)).map swapOuter
      = μ.map (fun ω => ((Y ω, Z ω), X ω)) := by
    rw [Measure.map_map swapOuter.measurable ((hX.prodMk hZ).prodMk hY)]
    rfl
  have href : (μ.map (fun ω => (X ω, Z ω)) ⊗ₘ Kernel.prodMkLeft S (condLaw Z Y μ)).map swapOuter
      = μ.map (fun ω => (Y ω, Z ω)) ⊗ₘ Kernel.prodMkLeft T (condLaw Z X μ) := by
    refine Measure.ext_of_singleton fun p => ?_
    obtain ⟨⟨y, z⟩, x⟩ := p
    have hpre : (swapOuter : (S × U) × T ≃ᵐ (T × U) × S) ⁻¹' {((y, z), x)} = {((x, z), y)} := by
      ext ⟨⟨a, b⟩, c⟩
      simp [swapOuter, Prod.ext_iff]
      tauto
    rw [Measure.map_apply swapOuter.measurable (measurableSet_singleton _), hpre,
      compProd_condLaw_singleton hX hZ hY, compProd_condLaw_singleton hY hZ hX]
    by_cases hz : μ (Z ⁻¹' {z}) = 0
    · rw [measure_mono_null Set.inter_subset_right hz,
        measure_mono_null Set.inter_subset_right hz, mul_zero, mul_zero]
    · rw [← ENNReal.mul_right_inj hz (measure_ne_top μ _), ← mul_assoc, ← mul_assoc,
        mul_comm (μ (Z ⁻¹' {z})), condLaw_singleton_mul hZ hY, mul_comm (μ (Z ⁻¹' {z})),
        condLaw_singleton_mul hZ hX, Set.inter_comm (Z ⁻¹' {z}) (Y ⁻¹' {y}),
        Set.inter_comm (Z ⁻¹' {z}) (X ⁻¹' {x}), mul_comm]
  rw [condMutualInfoKL, ← klDiv_map_equiv swapOuter, hjoint, href]
  rfl

end Countable

/-! ### The chain rule for a finite family -/

section FiniteChainRule

variable {Ω V W : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSpace W]
  [MeasurableSingletonClass V] [MeasurableSingletonClass W] [Countable V] [Countable W]
  {μ : Measure Ω}

/-- Split a vector of length `n + 1` into its last entry and the rest. -/
private def splitLast (n : ℕ) : (Fin (n + 1) → V) ≃ᵐ V × (Fin n → V) where
  toFun v := (v (Fin.last n), fun i => v i.castSucc)
  invFun p := Fin.snoc p.2 p.1
  left_inv v := Fin.snoc_init_self v
  right_inv p := by simp
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- **Chain rule for information in `[0, ∞]`** (Cover & Thomas, Theorem 2.5.2, (2.62),
PDF p. 50): `I(X₁, …, Xₙ; Y) = ∑ᵢ I(Xᵢ; Y | Xᵢ₋₁, …, X₁)`, here with `Y` in the first
slot (mutual information is symmetric, `mutualInfoKL_comm`). Discrete variables on
countable alphabets; no term needs to be finite. `mutualInfo_chain_rule_fin` is the
same identity at PFR's real `I`, under `FiniteRange` on every variable. -/
public theorem mutualInfoKL_chain_rule_fin {n : ℕ} [IsProbabilityMeasure μ] (Y : Ω → W)
    (X : Fin n → Ω → V) (hY : Measurable Y) (hX : ∀ i, Measurable (X i)) :
    mutualInfoKL Y (observationVector X) μ =
      ∑ i : Fin n, condMutualInfoKL Y (X i) (observationPrefix X i) μ := by
  induction n with
  | zero =>
      have hobs : observationVector X = fun _ => (fun i : Fin 0 => Fin.elim0 i) := by
        funext ω i
        exact Fin.elim0 i
      rw [hobs, mutualInfoKL_const hY]
      simp
  | succ n ih =>
      let Xinit : Fin n → Ω → V := fun i => X i.castSucc
      have hXinit : ∀ i, Measurable (Xinit i) := fun i => hX i.castSucc
      have hvec : ∀ {m : ℕ} (X' : Fin m → Ω → V), (∀ i, Measurable (X' i)) →
          Measurable (observationVector X') := fun X' h =>
        measurable_pi_iff.mpr fun i => by
          simpa only [observationVector_apply] using h i
      have hInit := hvec Xinit hXinit
      rw [← mutualInfoKL_comp_equiv hY (hvec X hX) (splitLast n)]
      have hsplit : (splitLast n) ∘ observationVector X =
          fun ω => (X (Fin.last n) ω, observationVector Xinit ω) := by
        funext ω
        refine Prod.ext ?_ ?_
        · exact observationVector_apply X ω (Fin.last n)
        · funext i
          exact (observationVector_apply X ω i.castSucc).trans
            (observationVector_apply Xinit ω i).symm
      have hlast : observationVector Xinit = observationPrefix X (Fin.last n) := by
        funext ω j
        rw [observationVector_apply, observationPrefix_apply]
        rfl
      have hpre : ∀ i : Fin n, observationPrefix Xinit i = observationPrefix X i.castSucc := by
        intro i
        funext ω j
        rw [observationPrefix_apply, observationPrefix_apply]
        rfl
      rw [hsplit, mutualInfoKL_pair_eq_add hY (hX (Fin.last n)) hInit, ih Xinit hXinit,
        Fin.sum_univ_castSucc, hlast]
      simp only [Xinit, hpre]

/-- **Theorem 2.5.2 in print's argument order**, (2.62), PDF p. 50:
`I(X₁, …, Xₙ; Y) = ∑ᵢ I(Xᵢ; Y | Xᵢ₋₁, …, X₁)`, in `[0, ∞]`, on countable alphabets. -/
public theorem mutualInfoKL_chain_rule_fin' {n : ℕ} [IsProbabilityMeasure μ] (Y : Ω → W)
    (X : Fin n → Ω → V) (hY : Measurable Y) (hX : ∀ i, Measurable (X i)) :
    mutualInfoKL (observationVector X) Y μ =
      ∑ i : Fin n, condMutualInfoKL (X i) Y (observationPrefix X i) μ := by
  have hVec : Measurable (observationVector X) :=
    measurable_pi_iff.mpr fun i => by simpa only [observationVector_apply] using hX i
  have hPre : ∀ i, Measurable (observationPrefix X i) := fun i =>
    measurable_pi_iff.mpr fun j => by simpa only [observationPrefix_apply] using hX _
  rw [mutualInfoKL_comm hVec hY, mutualInfoKL_chain_rule_fin Y X hY hX]
  exact Finset.sum_congr rfl fun i _ => condMutualInfoKL_comm hY (hX i) (hPre i)

end FiniteChainRule


/-! ### One alphabet per index -/

section FiniteChainRulePi

universe u

variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSingletonClass W]
  [Countable W] {μ : Measure Ω}

/-- Split a dependent vector of length `n + 1` into its last entry and the rest. -/
private def splitLastPi (n : ℕ) (V' : Fin (n + 1) → Type u) [∀ i, MeasurableSpace (V' i)]
    [∀ i, MeasurableSingletonClass (V' i)] [∀ i, Countable (V' i)] :
    ((i : Fin (n + 1)) → V' i) ≃ᵐ V' (Fin.last n) × ((i : Fin n) → V' i.castSucc) where
  toFun v := (v (Fin.last n), fun i => v i.castSucc)
  invFun p := Fin.snoc p.2 p.1
  left_inv v := Fin.snoc_init_self v
  right_inv p := by simp
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- **Theorem 2.5.2 in `[0, ∞]` with one countable alphabet per index**, (2.62), PDF
p. 50: `I(X₁, …, Xₙ; Y) = ∑ᵢ I(Xᵢ; Y | Xᵢ₋₁, …, X₁)`, print's argument order, where
`Xᵢ` takes values in its own countable alphabet `V' i`. -/
public theorem mutualInfoKL_chain_rule_pi {n : ℕ} {V' : Fin n → Type u}
    [∀ i, MeasurableSpace (V' i)] [∀ i, MeasurableSingletonClass (V' i)]
    [∀ i, Countable (V' i)] [IsProbabilityMeasure μ] (Y : Ω → W)
    (X : (i : Fin n) → Ω → V' i) (hY : Measurable Y) (hX : ∀ i, Measurable (X i)) :
    mutualInfoKL (observationVectorPi X) Y μ =
      ∑ i : Fin n, condMutualInfoKL (X i) Y (observationPrefixPi X i) μ := by
  have hPre : ∀ i, Measurable (observationPrefixPi X i) := fun i =>
    measurable_pi_iff.mpr fun j => by simpa only [observationPrefixPi_apply] using hX _
  have hVec : ∀ {m : ℕ} {V'' : Fin m → Type u} [∀ i, MeasurableSpace (V'' i)]
      (X' : (i : Fin m) → Ω → V'' i), (∀ i, Measurable (X' i)) →
      Measurable (observationVectorPi X') := fun X' h =>
    measurable_pi_iff.mpr fun i => by simpa only [observationVectorPi_apply] using h i
  rw [mutualInfoKL_comm (hVec X hX) hY]
  rw [Finset.sum_congr rfl fun i _ => condMutualInfoKL_comm (hX i) hY (hPre i)]
  clear hPre
  induction n with
  | zero =>
      have hobs : observationVectorPi X = fun _ => (fun i : Fin 0 => Fin.elim0 i) := by
        funext ω i
        exact Fin.elim0 i
      rw [hobs, mutualInfoKL_const hY]
      simp
  | succ n ih =>
      let Xinit : (i : Fin n) → Ω → V' i.castSucc := fun i => X i.castSucc
      have hXinit : ∀ i, Measurable (Xinit i) := fun i => hX i.castSucc
      have hInit := hVec Xinit hXinit
      rw [← mutualInfoKL_comp_equiv hY (hVec X hX) (splitLastPi n V')]
      have hsplit : (splitLastPi n V') ∘ observationVectorPi X =
          fun ω => (X (Fin.last n) ω, observationVectorPi Xinit ω) := by
        funext ω
        refine Prod.ext ?_ ?_
        · exact observationVectorPi_apply X ω (Fin.last n)
        · funext i
          exact (observationVectorPi_apply X ω i.castSucc).trans
            (observationVectorPi_apply Xinit ω i).symm
      have hlast : observationVectorPi Xinit = observationPrefixPi X (Fin.last n) := by
        funext ω j
        rw [observationVectorPi_apply, observationPrefixPi_apply]
        rfl
      have hpre : ∀ i : Fin n,
          observationPrefixPi Xinit i = observationPrefixPi X i.castSucc := by
        intro i
        funext ω j
        rw [observationPrefixPi_apply, observationPrefixPi_apply]
        rfl
      rw [hsplit, mutualInfoKL_pair_eq_add hY (hX (Fin.last n)) hInit, ih Xinit hXinit,
        Fin.sum_univ_castSucc, hlast]
      simp only [Xinit, hpre]

end FiniteChainRulePi

/-! ## Agreement with PFR's mutual information on finite ranges -/

section Bridge

variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω}

/-- On an atom of `ν`, the Radon–Nikodym derivative is the ratio of the masses. (From
`docs/provenance/refutations/cover-thomas-2-8-1-literal.lean`.) -/
public theorem rnDeriv_singleton {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
    (μ ν : Measure W) [SigmaFinite μ] [SigmaFinite ν] (hac : μ ≪ ν)
    (x : W) (h0 : ν {x} ≠ 0) (htop : ν {x} ≠ ∞) : μ.rnDeriv ν x = μ {x} / ν {x} := by
  have h := congrArg (fun m : Measure W => m {x}) (Measure.withDensity_rnDeriv_eq μ ν hac)
  simp only [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton] at h
  rw [← h, ENNReal.mul_div_cancel_right h0 htop]

/-- **The new carrier extends PFR's.** For finite-range `X` and `Y` on countable
alphabets, `mutualInfoKL X Y μ` is PFR's real `I[X : Y]`: there (2.28) is a finite sum
and every entropy is finite. So each `FiniteRange` theorem about `I[X : Y]` in
`AISafetyAtlas.InformationTheory.DataProcessing` is the restriction of its
`mutualInfoKL` counterpart in this module. -/
public theorem mutualInfoKL_eq_ofReal_mutualInfo [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    mutualInfoKL X Y μ = ENNReal.ofReal I[X : Y ; μ] := by
  classical
  set A := FiniteRange.toFinset X
  set B := FiniteRange.toFinset Y
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  set P := μ.map fun ω => (X ω, Y ω) with hPdef
  set Q := (μ.map X).prod (μ.map Y) with hQdef
  have hP : ∀ x y, P {(x, y)} = μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) := fun x y => by
    rw [hPdef, Measure.map_apply hXY (measurableSet_singleton _),
      ← Set.singleton_prod_singleton, Set.mk_preimage_prod]
  have hQ : ∀ x y, Q {(x, y)} = μ (X ⁻¹' {x}) * μ (Y ⁻¹' {y}) := fun x y => by
    rw [hQdef, ← Set.singleton_prod_singleton, Measure.prod_prod,
      Measure.map_apply hX (measurableSet_singleton _),
      Measure.map_apply hY (measurableSet_singleton _)]
  have hPx : ∀ x y, μ (X ⁻¹' {x}) = 0 → P {(x, y)} = 0 := fun x y h => by
    rw [hP]; exact measure_mono_null Set.inter_subset_left h
  have hPy : ∀ x y, μ (Y ⁻¹' {y}) = 0 → P {(x, y)} = 0 := fun x y h => by
    rw [hP]; exact measure_mono_null Set.inter_subset_right h
  have hXA : ∀ x, x ∉ A → μ (X ⁻¹' {x}) = 0 := fun x hx => by
    convert measure_empty (μ := μ)
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hx (FiniteRange.mem X ω)
  have hYB : ∀ y, y ∉ B → μ (Y ⁻¹' {y}) = 0 := fun y hy => by
    convert measure_empty (μ := μ)
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hy (FiniteRange.mem Y ω)
  have hsupp : ∀ a ∉ A ×ˢ B, P {a} = 0 := by
    rintro ⟨x, y⟩ ha
    rcases not_and_or.mp (Finset.mem_product.not.mp ha) with hx | hy
    · exact hPx x y (hXA x hx)
    · exact hPy x y (hYB y hy)
  -- absolute continuity, checked on atoms
  have hac : P ≪ Q := by
    intro s hs
    rw [← Measure.tsum_indicator_apply_singleton P s (Set.to_countable s).measurableSet]
    refine ENNReal.tsum_eq_zero.mpr fun a => ?_
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha]
      obtain ⟨x, y⟩ := a
      have hq : Q {(x, y)} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr ha) hs
      rw [hQ] at hq
      rcases mul_eq_zero.mp hq with h | h
      · exact hPx x y h
      · exact hPy x y h
    · simp [ha]
  -- the integrand of (2.28), term by term
  have hterm : ∀ x y, P.real {(x, y)} • llr P Q (x, y)
      = μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * Real.log (μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}))
        - μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * Real.log (μ.real (X ⁻¹' {x}))
        - μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * Real.log (μ.real (Y ⁻¹' {y})) := by
    intro x y
    rw [smul_eq_mul, measureReal_def, hP]
    by_cases h0 : μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) = 0
    · simp [measureReal_def, h0]
    have hx0 : μ (X ⁻¹' {x}) ≠ 0 := fun h => h0 (by rw [← hP]; exact hPx x y h)
    have hy0 : μ (Y ⁻¹' {y}) ≠ 0 := fun h => h0 (by rw [← hP]; exact hPy x y h)
    have hq0 : Q {(x, y)} ≠ 0 := by rw [hQ]; exact mul_ne_zero hx0 hy0
    rw [llr_def]
    dsimp only
    rw [rnDeriv_singleton P Q hac _ hq0 (measure_ne_top _ _), ENNReal.toReal_div, hQ, hP,
      ENNReal.toReal_mul]
    have hpos : ∀ s : Set Ω, μ s ≠ 0 → (μ s).toReal ≠ 0 := fun s h =>
      (ENNReal.toReal_pos h (measure_ne_top _ _)).ne'
    rw [Real.log_div (hpos _ h0) (mul_ne_zero (hpos _ hx0) (hpos _ hy0)),
      Real.log_mul (hpos _ hx0) (hpos _ hy0)]
    simp only [measureReal_def]
    ring
  have hint : Integrable (llr P Q) P := by
    refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_countable', tsum_eq_sum (s := A ×ˢ B)]
    · exact ENNReal.sum_lt_top.mpr fun a _ => ENNReal.mul_lt_top enorm_lt_top (measure_lt_top _ _)
    · intro a ha
      rw [hsupp a ha, mul_zero]
  -- marginals
  have hmargX : ∀ x, ∑ y ∈ B, μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) = μ.real (X ⁻¹' {x}) := by
    intro x
    rw [← measureReal_biUnion_finset (fun y _ y' _ hne => Set.disjoint_left.mpr
      fun ω h1 h2 => hne (h1.2.symm.trans h2.2))
      (fun y _ => (hX (measurableSet_singleton x)).inter (hY (measurableSet_singleton y)))]
    congr 1
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, _, h, _⟩ => h, fun h => ⟨Y ω, FiniteRange.mem Y ω, h, rfl⟩⟩
  have hmargY : ∀ y, ∑ x ∈ A, μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) = μ.real (Y ⁻¹' {y}) := by
    intro y
    rw [← measureReal_biUnion_finset (fun x _ x' _ hne => Set.disjoint_left.mpr
      fun ω h1 h2 => hne (h1.1.symm.trans h2.1))
      (fun x _ => (hX (measurableSet_singleton x)).inter (hY (measurableSet_singleton y)))]
    congr 1
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨X ω, FiniteRange.mem X ω, rfl, h⟩⟩
  -- the entropies as finite sums
  have hHX : H[X ; μ] = ∑ x ∈ A, Real.negMulLog (μ.real (X ⁻¹' {x})) := by
    rw [entropy_eq_sum_finset (FiniteRange.null_of_compl μ X)]
    simp only [map_measureReal_apply hX (measurableSet_singleton _)]
    rfl
  have hHY : H[Y ; μ] = ∑ y ∈ B, Real.negMulLog (μ.real (Y ⁻¹' {y})) := by
    rw [entropy_eq_sum_finset (FiniteRange.null_of_compl μ Y)]
    simp only [map_measureReal_apply hY (measurableSet_singleton _)]
    rfl
  have hHXY : H[⟨X, Y⟩ ; μ]
      = ∑ x ∈ A, ∑ y ∈ B, Real.negMulLog (μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y})) := by
    have hnull : P (↑(A ×ˢ B))ᶜ = 0 := by
      rw [hPdef, Measure.map_apply hXY (Set.to_countable _).measurableSet]
      convert measure_empty (μ := μ)
      ext ω
      simp [A, B]
    rw [entropy_eq_sum_finset hnull, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [measureReal_def, hP, measureReal_def]
  have hsum : ∫ a, llr P Q a ∂P = I[X : Y ; μ] := by
    rw [integral_countable hint, tsum_eq_sum (s := A ×ˢ B), Finset.sum_product]
    · simp_rw [hterm]
      rw [mutualInfo_def, hHX, hHY, hHXY]
      simp only [Finset.sum_sub_distrib, Real.negMulLog]
      rw [Finset.sum_comm (s := A) (t := B) (f := fun x y =>
        μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * Real.log (μ.real (Y ⁻¹' {y})))]
      simp only [← Finset.sum_mul, hmargX, hmargY, neg_mul, Finset.sum_neg_distrib]
      ring
    · intro a ha
      rw [measureReal_def, hsupp a ha, ENNReal.toReal_zero, zero_smul]
  have : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hXY.aemeasurable
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  rw [mutualInfoKL, klDiv_of_ac_of_integrable hac hint, hsum, probReal_univ,
    probReal_univ, add_sub_cancel_right]

end Bridge

end AISafetyAtlas.InformationTheory
