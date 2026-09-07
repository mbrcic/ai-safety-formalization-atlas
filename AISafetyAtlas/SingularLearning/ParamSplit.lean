module

public import AISafetyAtlas.SingularLearning.OrbitNormalForm
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Splitting a Euclidean parameter space along a subspace

`ChartTransport.lean` and `PairTransfer.lean` split `EuclideanSpace ℝ (Fin n)` along a
*numerical* decomposition of the index: `euclSplitEquiv`, `euclideanProdEquiv` and `splitLE`
all cut `Fin (k₁ + k₂)` into its two halves, and each is exact because it is a reindexing of
coordinates.

What none of them can do is cut the space along a **subspace** that is not already a
coordinate subspace. That is what a Morse–Bott argument needs: the degenerate directions at a
critical point form a linear subspace `V` of the parameter space, fixed by the geometry rather
than by the indexing, and the germ has to be read in coordinates where `V` is the last block
and a complement is the first.

This module supplies that splitting, for an arbitrary `V`, and it is stated over an arbitrary
`n` and an arbitrary `V` — it knows nothing about the loss, the chart, or O77.

## What is here

* **The complement is the orthogonal one.** `Vᗮ` is a complement of `V` for free
  (`Submodule.sup_orthogonal_of_hasOrthogonalProjection`), its dimension is forced
  (`finrank_orthogonal_add_finrank`), and — the reason it beats an arbitrary
  `Submodule.exists_isCompl` complement — the resulting change of coordinates is an
  **isometry**, not merely a linear isomorphism.

* **The adapted basis.** `adaptedBasis V` is an orthonormal basis of the whole space indexed
  by `Fin (dim Vᗮ) ⊕ Fin (dim V)`: an orthonormal basis of `Vᗮ` on the left summand, one of
  `V` on the right. Orthonormality across the two summands is exactly the defining property
  of `Vᗮ`, and spanning is `Vᗮ ⊔ V = ⊤`.

* **The splitting.** `paramSplitEquiv V` is the induced
  `EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (dim Vᗮ + dim V))`, and
  `mem_iff_paramSplitEquiv_castAdd_eq_zero` /
  `mem_orthogonal_iff_paramSplitEquiv_natAdd_eq_zero` say what "adapted" means: a point lies
  in `V` exactly when its first `dim Vᗮ` coordinates vanish, and in `Vᗮ` exactly when its
  last `dim V` coordinates do. The two `Submodule.map` statements record the same fact as an
  image of subspaces.

* **What it costs downstream: nothing.** Being a linear isometry equivalence, it is analytic
  with analytic inverse (`analyticOnNhd_paramSplitEquiv`) and preserves Lebesgue measure
  (`measurePreserving_paramSplitEquiv`). So a germ transported across it keeps its sublevel
  volumes exactly — `CoordTransfer.lean`'s `hasLocalVolumeOrder_comp_linearIsometryEquiv` is
  the consumer that needs precisely this pair of properties.

## Why an isometry and not just a `ContinuousLinearEquiv`

A linear isomorphism onto a coordinate splitting exists for any complement, and would already
give analyticity. It would not give measure preservation: a non-orthogonal change of basis
multiplies Lebesgue measure by `|det|`, and every sublevel volume downstream would acquire
that constant. The constant is harmless for an *exponent* and fatal for nothing in
particular — but it has to be tracked, and the orthogonal complement removes the need. That
is the whole reason `Submodule.exists_isCompl` is not used here.

## What is *not* here

No germ, no Hessian, no critical point. This module is the coordinate change alone; what is
read in the new coordinates is the caller's business.
-/

namespace AISafetyAtlas.SingularLearning

open Module (finrank)
open MeasureTheory
open scoped RealInnerProductSpace

section AdaptedSplit

variable {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))

/-! ## The dimension count -/

/-- **The complement's dimension is forced.** `dim Vᗮ + dim V = n`, in the order the splitting
below uses: the complement first, `V` last. -/
public theorem finrank_orthogonal_add_finrank : finrank ℝ Vᗮ + finrank ℝ V = n := by
  rw [add_comm, V.finrank_add_finrank_orthogonal, finrank_euclideanSpace_fin]

/-! ## The adapted orthonormal basis -/

/-- The adapted family: an orthonormal basis of `Vᗮ` on the left summand, one of `V` on the
right, both read in the ambient space. -/
@[expose] public noncomputable def adaptedFamily :
    (Fin (finrank ℝ Vᗮ) ⊕ Fin (finrank ℝ V)) → EuclideanSpace ℝ (Fin n) :=
  Sum.elim (fun i => ((stdOrthonormalBasis ℝ Vᗮ) i : EuclideanSpace ℝ (Fin n)))
    (fun j => ((stdOrthonormalBasis ℝ V) j : EuclideanSpace ℝ (Fin n)))

@[simp] public theorem adaptedFamily_inl (i : Fin (finrank ℝ Vᗮ)) :
    adaptedFamily V (Sum.inl i) = ((stdOrthonormalBasis ℝ Vᗮ) i : EuclideanSpace ℝ (Fin n)) :=
  rfl

@[simp] public theorem adaptedFamily_inr (j : Fin (finrank ℝ V)) :
    adaptedFamily V (Sum.inr j) = ((stdOrthonormalBasis ℝ V) j : EuclideanSpace ℝ (Fin n)) :=
  rfl

public theorem adaptedFamily_inl_mem (i : Fin (finrank ℝ Vᗮ)) : adaptedFamily V (Sum.inl i) ∈ Vᗮ :=
  ((stdOrthonormalBasis ℝ Vᗮ) i).2

public theorem adaptedFamily_inr_mem (j : Fin (finrank ℝ V)) : adaptedFamily V (Sum.inr j) ∈ V :=
  ((stdOrthonormalBasis ℝ V) j).2

/-- The left summand spans `Vᗮ`, read in the ambient space. -/
public theorem span_range_adaptedFamily_inl :
    Submodule.span ℝ (Set.range fun i => adaptedFamily V (Sum.inl i)) = Vᗮ := by
  have h := span_range_coe_basis Vᗮ (stdOrthonormalBasis ℝ Vᗮ).toBasis
  simpa using h

/-- The right summand spans `V`, read in the ambient space. -/
public theorem span_range_adaptedFamily_inr :
    Submodule.span ℝ (Set.range fun j => adaptedFamily V (Sum.inr j)) = V := by
  have h := span_range_coe_basis V (stdOrthonormalBasis ℝ V).toBasis
  simpa using h

/-- Orthonormality. Within each summand it is the summand's own orthonormal basis; across the
two summands it is the defining property of `Vᗮ`. -/
public theorem orthonormal_adaptedFamily : Orthonormal ℝ (adaptedFamily V) := by
  constructor
  · rintro (i | j)
    · exact (stdOrthonormalBasis ℝ Vᗮ).orthonormal.1 i
    · exact (stdOrthonormalBasis ℝ V).orthonormal.1 j
  · rintro (i | j) (i' | j') hne
    · exact (stdOrthonormalBasis ℝ Vᗮ).orthonormal.2 (fun h => hne (by rw [h]))
    · exact inner_eq_zero_symm.mp ((adaptedFamily_inl_mem V i) _ (adaptedFamily_inr_mem V j'))
    · exact (adaptedFamily_inl_mem V i') _ (adaptedFamily_inr_mem V j)
    · exact (stdOrthonormalBasis ℝ V).orthonormal.2 (fun h => hne (by rw [h]))

/-- The adapted family spans, because `Vᗮ ⊔ V = ⊤`. -/
public theorem top_le_span_adaptedFamily :
    ⊤ ≤ Submodule.span ℝ (Set.range (adaptedFamily V)) := by
  have hrange : Set.range (adaptedFamily V)
      = (Set.range fun i => adaptedFamily V (Sum.inl i))
        ∪ (Set.range fun j => adaptedFamily V (Sum.inr j)) := Set.Sum.elim_range _ _
  rw [hrange, Submodule.span_union, span_range_adaptedFamily_inl,
    span_range_adaptedFamily_inr, sup_comm]
  exact le_of_eq (Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := V)).symm

/-- **The adapted orthonormal basis** of the whole parameter space: `Vᗮ` on the left summand,
`V` on the right. -/
@[expose] public noncomputable def adaptedBasis :
    OrthonormalBasis (Fin (finrank ℝ Vᗮ) ⊕ Fin (finrank ℝ V)) ℝ (EuclideanSpace ℝ (Fin n)) :=
  OrthonormalBasis.mk (orthonormal_adaptedFamily V) (top_le_span_adaptedFamily V)

@[simp] public theorem coe_adaptedBasis : ⇑(adaptedBasis V) = adaptedFamily V :=
  OrthonormalBasis.coe_mk _ _

/-! ## The splitting -/

/-- **The subspace-adapted splitting of the parameter space.** A linear isometry equivalence
`EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (dim Vᗮ + dim V))` sending `Vᗮ` to the
first `dim Vᗮ` coordinates and `V` to the last `dim V`. -/
@[expose] public noncomputable def paramSplitEquiv :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ Vᗮ + finrank ℝ V)) :=
  ((adaptedBasis V).reindex finSumFinEquiv).repr

/-- The first block of coordinates is the inner product against the basis of `Vᗮ`. -/
public theorem paramSplitEquiv_castAdd (x : EuclideanSpace ℝ (Fin n))
    (i : Fin (finrank ℝ Vᗮ)) :
    paramSplitEquiv V x (Fin.castAdd (finrank ℝ V) i) = ⟪adaptedFamily V (Sum.inl i), x⟫ := by
  have hk : Fin.castAdd (finrank ℝ V) i = finSumFinEquiv (Sum.inl i) := rfl
  rw [paramSplitEquiv, hk, OrthonormalBasis.repr_reindex, Equiv.symm_apply_apply,
    OrthonormalBasis.repr_apply_apply, coe_adaptedBasis]

/-- The last block of coordinates is the inner product against the basis of `V`. -/
public theorem paramSplitEquiv_natAdd (x : EuclideanSpace ℝ (Fin n))
    (j : Fin (finrank ℝ V)) :
    paramSplitEquiv V x (Fin.natAdd (finrank ℝ Vᗮ) j) = ⟪adaptedFamily V (Sum.inr j), x⟫ := by
  have hk : Fin.natAdd (finrank ℝ Vᗮ) j = finSumFinEquiv (Sum.inr j) := rfl
  rw [paramSplitEquiv, hk, OrthonormalBasis.repr_reindex, Equiv.symm_apply_apply,
    OrthonormalBasis.repr_apply_apply, coe_adaptedBasis]

/-- A basis vector of `Vᗮ` goes to a standard basis vector in the *first* block. -/
public theorem paramSplitEquiv_adaptedFamily_inl (i : Fin (finrank ℝ Vᗮ)) :
    paramSplitEquiv V (adaptedFamily V (Sum.inl i))
      = EuclideanSpace.single (Fin.castAdd (finrank ℝ V) i) (1 : ℝ) := by
  have hk : Fin.castAdd (finrank ℝ V) i = finSumFinEquiv (Sum.inl i) := rfl
  have hb : adaptedFamily V (Sum.inl i)
      = ((adaptedBasis V).reindex finSumFinEquiv) (finSumFinEquiv (Sum.inl i)) := by
    rw [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply,
      coe_adaptedBasis]
  rw [hk, hb, paramSplitEquiv, OrthonormalBasis.repr_self]

/-- A basis vector of `V` goes to a standard basis vector in the *last* block. -/
public theorem paramSplitEquiv_adaptedFamily_inr (j : Fin (finrank ℝ V)) :
    paramSplitEquiv V (adaptedFamily V (Sum.inr j))
      = EuclideanSpace.single (Fin.natAdd (finrank ℝ Vᗮ) j) (1 : ℝ) := by
  have hk : Fin.natAdd (finrank ℝ Vᗮ) j = finSumFinEquiv (Sum.inr j) := rfl
  have hb : adaptedFamily V (Sum.inr j)
      = ((adaptedBasis V).reindex finSumFinEquiv) (finSumFinEquiv (Sum.inr j)) := by
    rw [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply,
      coe_adaptedBasis]
  rw [hk, hb, paramSplitEquiv, OrthonormalBasis.repr_self]

/-! ### What "adapted" means

The splitting is adapted to `V` in the strong sense: membership in `V` is exactly the
vanishing of the first block of coordinates, and membership in `Vᗮ` exactly the vanishing of
the last block. Both directions are proved, the hard one by spanning the relevant subspace
with the corresponding half of the adapted basis. -/

/-- **`V` is the last `dim V` coordinates.** -/
public theorem mem_iff_paramSplitEquiv_castAdd_eq_zero (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ V ↔ ∀ i : Fin (finrank ℝ Vᗮ),
      paramSplitEquiv V x (Fin.castAdd (finrank ℝ V) i) = 0 := by
  simp only [paramSplitEquiv_castAdd]
  constructor
  · intro hx i
    exact inner_eq_zero_symm.mp ((adaptedFamily_inl_mem V i) x hx)
  · intro hx
    rw [← Submodule.orthogonal_orthogonal V]
    rw [Submodule.mem_orthogonal]
    rw [← span_range_adaptedFamily_inl V]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hx i
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb]; ring
    | smul c a _ ha => rw [real_inner_smul_left, ha]; ring

/-- **`Vᗮ` is the first `dim Vᗮ` coordinates.** -/
public theorem mem_orthogonal_iff_paramSplitEquiv_natAdd_eq_zero (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ Vᗮ ↔ ∀ j : Fin (finrank ℝ V),
      paramSplitEquiv V x (Fin.natAdd (finrank ℝ Vᗮ) j) = 0 := by
  simp only [paramSplitEquiv_natAdd]
  constructor
  · intro hx j
    exact hx _ (adaptedFamily_inr_mem V j)
  · intro hx
    rw [Submodule.mem_orthogonal, ← span_range_adaptedFamily_inr V]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hx j
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb]; ring
    | smul c a _ ha => rw [real_inner_smul_left, ha]; ring

/-- The image of `V` is the span of the last `dim V` standard basis vectors. -/
public theorem map_paramSplitEquiv_eq :
    Submodule.map (paramSplitEquiv V).toLinearEquiv.toLinearMap V
      = Submodule.span ℝ (Set.range fun j : Fin (finrank ℝ V) =>
          EuclideanSpace.single (Fin.natAdd (finrank ℝ Vᗮ) j) (1 : ℝ)) := by
  refine Eq.trans (congrArg (Submodule.map (paramSplitEquiv V).toLinearEquiv.toLinearMap)
    (span_range_adaptedFamily_inr V).symm) ?_
  rw [Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℝ)
    (congrArg Set.range (funext fun j => paramSplitEquiv_adaptedFamily_inr V j))

/-- The image of `Vᗮ` is the span of the first `dim Vᗮ` standard basis vectors. -/
public theorem map_orthogonal_paramSplitEquiv_eq :
    Submodule.map (paramSplitEquiv V).toLinearEquiv.toLinearMap Vᗮ
      = Submodule.span ℝ (Set.range fun i : Fin (finrank ℝ Vᗮ) =>
          EuclideanSpace.single (Fin.castAdd (finrank ℝ V) i) (1 : ℝ)) := by
  refine Eq.trans (congrArg (Submodule.map (paramSplitEquiv V).toLinearEquiv.toLinearMap)
    (span_range_adaptedFamily_inl V).symm) ?_
  rw [Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℝ)
    (congrArg Set.range (funext fun i => paramSplitEquiv_adaptedFamily_inl V i))

/-! ## Analyticity and measure preservation come for free

A linear isometry equivalence between finite-dimensional real spaces is a continuous linear
map, hence analytic, with an inverse of the same kind; and it preserves the additive Haar
measure, which on a Euclidean space is Lebesgue measure. Those are the two properties a germ
transported across the splitting needs, and they are the reason the *orthogonal* complement
is the one taken. -/

public theorem analyticOnNhd_paramSplitEquiv (s : Set (EuclideanSpace ℝ (Fin n))) :
    AnalyticOnNhd ℝ (paramSplitEquiv V) s :=
  fun x _ => (paramSplitEquiv V).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt x

public theorem analyticOnNhd_paramSplitEquiv_symm
    (s : Set (EuclideanSpace ℝ (Fin (finrank ℝ Vᗮ + finrank ℝ V)))) :
    AnalyticOnNhd ℝ (paramSplitEquiv V).symm s :=
  fun x _ =>
    (paramSplitEquiv V).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt x

public theorem measurePreserving_paramSplitEquiv :
    MeasurePreserving (paramSplitEquiv V) volume volume :=
  (paramSplitEquiv V).measurePreserving

public theorem measurePreserving_paramSplitEquiv_symm :
    MeasurePreserving (paramSplitEquiv V).symm volume volume :=
  (paramSplitEquiv V).symm.measurePreserving

public theorem isometry_paramSplitEquiv : Isometry (paramSplitEquiv V) :=
  (paramSplitEquiv V).isometry

end AdaptedSplit

end AISafetyAtlas.SingularLearning
