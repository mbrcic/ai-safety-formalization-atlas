module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The reduced-rank parameter space in Euclidean coordinates

`LocalPair.lean` states the local-pair relations on `EuclideanSpace ℝ (Fin n)`,
because that is where the pinned Mathlib puts a `MeasureSpace` instance. The
reduced-rank parameter, however, is a *pair of matrices* `(A, B)` with
`A : ℝ^{H×N}` and `B : ℝ^{M×H}`, and the pinned Mathlib gives
`Matrix (Fin a) (Fin b) ℝ` no canonical `MeasureSpace` instance at all. So a
local-pair claim about reduced-rank regression cannot even be *stated* until the
parameter space is transported to Euclidean coordinates. This module supplies
that transport.

**Why it is a reindexing and not just any linear isomorphism.** A volume
asymptotic is only invariant under a change of coordinates whose Jacobian
determinant is `1`; an arbitrary linear isomorphism rescales every volume by
`|det|` and would silently multiply every downstream asymptotic by a constant.
So the reshape here is built as a *permutation of coordinates* — a reindexing of
a Pi type along the bijection

    (Fin H × Fin N) ⊕ (Fin M × Fin H)  ≃  Fin (H * N + M * H)

— and `measurePreserving_matrixPairEquiv` proves, rather than assumes, that it
carries Lebesgue measure to Lebesgue measure. Nothing downstream has to carry a
Jacobian factor.

The transport is kept as a genuine `≃ₗ[ℝ]` (not merely an `Equiv` or a
`MeasurableEquiv`) because the reduced-rank loss is a polynomial in the
coordinates, and downstream arguments need linearity. `matrixPairMeasurableEquiv`
is the same underlying function packaged as a `MeasurableEquiv`; the two agree
definitionally (`coe_matrixPairEquiv`).

**What this module does *not* do.** It says nothing about the loss, the fibers,
or any learning coefficient. It is a change of coordinates and a proof that the
change of coordinates is volume-neutral.

## Implementation notes

The chain is, in order:

1. uncurry each matrix, `Fin a → Fin b → ℝ  ≃  Fin a × Fin b → ℝ`;
2. glue the two factors into one Pi type over the sum index
   (`LinearEquiv.sumArrowLequivProdArrow`);
3. reindex the sum index to `Fin (H * N + M * H)`
   (`LinearEquiv.funCongrLeft`);
4. read the result in the `L²` synonym (`WithLp.linearEquiv`).

Step 1 is the one piece the pinned Mathlib does not already have in
measure-preserving form: `MeasurableEquiv.curry` exists, but the only
`Measure`-level currying statements are for `infinitePi` in
`Mathlib/Probability/ProductMeasure.lean`, which do not apply to `volume`. It is
proved here as `measurePreserving_curry_symm`, by evaluating both sides on
boxes. Steps 2–4 are `volume_measurePreserving_sumPiEquivProdPi_symm`,
`volume_preserving_arrowCongr'` and `PiLp.volume_preserving_toLp`.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory

/-! ## A measure on the matrix space

The pinned Mathlib has no `MeasureSpace (Matrix m n α)`, because `Matrix` is a
def and not reducible, so the Pi instance is not found. The instance below is the
Pi instance, unfolded: Lebesgue measure on the `m × n` entries, nothing else. It
is `scoped` so that it does not leak out of `AISafetyAtlas.SingularLearning`. -/

/-- Lebesgue measure on `Matrix m n α`, i.e. the product measure on the entries.
This is definitionally the `MeasureSpace (m → n → α)` instance. -/
public noncomputable scoped instance instMeasureSpaceMatrix {m n α : Type*} [Fintype m] [Fintype n]
    [MeasureSpace α] : MeasureSpace (Matrix m n α) :=
  inferInstanceAs (MeasureSpace (m → n → α))

/-- The same measure is σ-finite, for the same reason: it is the Pi measure. Stated separately
because instance search does not unfold `Matrix` to find it, and Fubini on a product of matrix
spaces needs it. -/
public noncomputable scoped instance instSigmaFiniteMatrix {m k : ℕ} :
    SigmaFinite (volume : Measure (Matrix (Fin m) (Fin k) ℝ)) :=
  inferInstanceAs (SigmaFinite (volume : Measure (Fin m → Fin k → ℝ)))

/-! ## Two pieces the pinned Mathlib is missing -/

/-- Currying `(ι × κ → M) ≃ (ι → κ → M)` as a linear equivalence. Mathlib has the
`Equiv` (`Equiv.curry`) and the `MeasurableEquiv` (`MeasurableEquiv.curry`) but
no `≃ₗ`; both structure fields are `rfl`. -/
@[expose] public def curryLinearEquiv (R ι κ M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] : (ι × κ → M) ≃ₗ[R] (ι → κ → M) :=
  { Equiv.curry ι κ M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Uncurrying a finite Pi type preserves the product measure: the two product
measures `∏_{i} ∏_{j}` and `∏_{(i,j)}` agree, because a box for the pair index
pulls back to a box for the nested index. This is the finite-product counterpart
of `MeasureTheory.Measure.infinitePi_map_piCurry`, which is stated only for
`infinitePi` and so does not apply to `volume`. -/
public theorem measurePreserving_curry_symm (ι κ X : Type*) [Fintype ι] [Fintype κ]
    [MeasureSpace X] [SigmaFinite (volume : Measure X)] :
    MeasurePreserving (MeasurableEquiv.curry ι κ X).symm volume volume where
  measurable := (MeasurableEquiv.curry ι κ X).symm.measurable
  map_eq := by
    refine (Measure.pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have hpre : (MeasurableEquiv.curry ι κ X).symm ⁻¹' Set.univ.pi s
        = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
      ext g
      simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi, Function.uncurry, Prod.forall]
    rw [hpre, volume_pi_pi]
    simp_rw [volume_pi_pi]
    exact (Fintype.prod_prod_type fun p => volume (s p)).symm

/-! ## The reshape -/

/-- The coordinate reindexing that underlies the reshape: the disjoint union of
the two entry-index sets, listed as `Fin (H * N + M * H)`. Built from
`finProdFinEquiv` on each block and `finSumFinEquiv` on the sum, so it is a
bijection of index sets and nothing more. -/
@[expose] public def matrixPairIndex (M N H : ℕ) :
    (Fin H × Fin N) ⊕ (Fin M × Fin H) ≃ Fin (H * N + M * H) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

/-- The reshape as a measurable equivalence. Definitionally the same function as
`matrixPairEquiv` (see `coe_matrixPairEquiv`); this packaging is what the
measure-preservation lemmas in Mathlib are stated for. -/
@[expose] public noncomputable def matrixPairMeasurableEquiv (M N H : ℕ) :
    (Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ) ≃ᵐ
      EuclideanSpace ℝ (Fin (H * N + M * H)) :=
  ((MeasurableEquiv.curry (Fin H) (Fin N) ℝ).symm.prodCongr
      (MeasurableEquiv.curry (Fin M) (Fin H) ℝ).symm).trans <|
    (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : (Fin H × Fin N) ⊕ (Fin M × Fin H) => ℝ)).symm.trans <|
      (MeasurableEquiv.arrowCongr' (matrixPairIndex M N H) (MeasurableEquiv.refl ℝ)).trans
        (MeasurableEquiv.toLp 2 (Fin (H * N + M * H) → ℝ))

/-- The reshape carries Lebesgue measure to Lebesgue measure. Each of the four
steps is a Mathlib measure-preservation lemma (with step 1 supplied above), and
none of them contributes a scaling factor. -/
public theorem measurePreserving_matrixPairMeasurableEquiv (M N H : ℕ) :
    MeasurePreserving (matrixPairMeasurableEquiv M N H) volume volume := by
  have h1 : MeasurePreserving
      (⇑((MeasurableEquiv.curry (Fin H) (Fin N) ℝ).symm.prodCongr
        (MeasurableEquiv.curry (Fin M) (Fin H) ℝ).symm)) volume volume :=
    (measurePreserving_curry_symm _ _ _).prod (measurePreserving_curry_symm _ _ _)
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin H × Fin N) ⊕ (Fin M × Fin H) => ℝ)
  have h3 := volume_preserving_arrowCongr' (matrixPairIndex M N H) (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id volume)
  have h4 := PiLp.volume_preserving_toLp (Fin (H * N + M * H))
  simp only [matrixPairMeasurableEquiv]
  exact h4.comp (h3.comp (h2.comp h1))

/-- The parameter space of reduced-rank regression, in Euclidean coordinates. -/
@[expose] public noncomputable def matrixPairEquiv (M N H : ℕ) :
    (Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (H * N + M * H)) :=
  ((curryLinearEquiv ℝ (Fin H) (Fin N) ℝ).symm.prodCongr
      (curryLinearEquiv ℝ (Fin M) (Fin H) ℝ).symm).trans <|
    (LinearEquiv.sumArrowLequivProdArrow (Fin H × Fin N) (Fin M × Fin H) ℝ ℝ).symm.trans <|
      (LinearEquiv.funCongrLeft ℝ ℝ (matrixPairIndex M N H).symm).trans
        (WithLp.linearEquiv 2 ℝ (Fin (H * N + M * H) → ℝ)).symm

/-- The linear and the measurable packaging are the same function, by `rfl`. -/
public theorem coe_matrixPairEquiv (M N H : ℕ) :
    ⇑(matrixPairEquiv M N H) = ⇑(matrixPairMeasurableEquiv M N H) := rfl

/-- The reshape is a coordinate reindexing, so it carries Lebesgue measure to
Lebesgue measure with no Jacobian factor. -/
public theorem measurePreserving_matrixPairEquiv (M N H : ℕ) :
    MeasurePreserving (matrixPairEquiv M N H) volume volume := by
  rw [coe_matrixPairEquiv]
  exact measurePreserving_matrixPairMeasurableEquiv M N H

/-- The Euclidean coordinates of a reduced-rank parameter `(A, B)`. -/
@[expose] public noncomputable def matrixPairCoords {M N H : ℕ}
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    EuclideanSpace ℝ (Fin (H * N + M * H)) :=
  matrixPairEquiv M N H (A, B)

/-- The coordinate at index `k` is the entry of `A` or of `B` that
`matrixPairIndex` sends to `k`. -/
@[simp] public theorem matrixPairEquiv_apply (M N H : ℕ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) (k : Fin (H * N + M * H)) :
    matrixPairEquiv M N H (A, B) k =
      Sum.elim (fun p : Fin H × Fin N => A p.1 p.2) (fun p : Fin M × Fin H => B p.1 p.2)
        ((matrixPairIndex M N H).symm k) := rfl

/-- Reading a coordinate vector back as a pair of matrices. -/
@[simp] public theorem matrixPairEquiv_symm_apply (M N H : ℕ)
    (v : EuclideanSpace ℝ (Fin (H * N + M * H))) :
    (matrixPairEquiv M N H).symm v =
      (Matrix.of fun i j => v (matrixPairIndex M N H (Sum.inl (i, j))),
        Matrix.of fun i j => v (matrixPairIndex M N H (Sum.inr (i, j)))) := rfl

@[simp] public theorem matrixPairEquiv_apply_inl (M N H : ℕ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) (i : Fin H) (j : Fin N) :
    matrixPairEquiv M N H (A, B) (matrixPairIndex M N H (Sum.inl (i, j))) = A i j := by
  simp

@[simp] public theorem matrixPairEquiv_apply_inr (M N H : ℕ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) (i : Fin M) (j : Fin H) :
    matrixPairEquiv M N H (A, B) (matrixPairIndex M N H (Sum.inr (i, j))) = B i j := by
  simp

/-- The inverse maps also agree, by `rfl`. -/
public theorem coe_matrixPairEquiv_symm (M N H : ℕ) :
    ⇑(matrixPairEquiv M N H).symm = ⇑(matrixPairMeasurableEquiv M N H).symm := rfl

/-- Reading Euclidean coordinates back as a matrix pair is measure preserving too. -/
public theorem measurePreserving_matrixPairEquiv_symm (M N H : ℕ) :
    MeasurePreserving (matrixPairEquiv M N H).symm volume volume := by
  rw [coe_matrixPairEquiv_symm]
  exact MeasurePreserving.symm (matrixPairMeasurableEquiv M N H)
    (measurePreserving_matrixPairMeasurableEquiv M N H)

/-! ## Worked examples

Three consequences, so the module is not statement-only: the reshape loses no
information, it is linear at the origin, and — the point of the whole module —
a set and its preimage have the *same* volume, with no Jacobian factor. -/

/-- The reshape loses no information. -/
example (M N H : ℕ) : Function.Injective (matrixPairEquiv M N H) :=
  (matrixPairEquiv M N H).injective

/-- The zero parameter has zero coordinates. -/
example (M N H : ℕ) : matrixPairCoords (0 : Matrix (Fin H) (Fin N) ℝ)
    (0 : Matrix (Fin M) (Fin H) ℝ) = 0 :=
  map_zero (matrixPairEquiv M N H)

/-- No Jacobian factor: a measurable set upstairs and its preimage in matrix
coordinates have equal volume. -/
example (M N H : ℕ) (s : Set (EuclideanSpace ℝ (Fin (H * N + M * H)))) (hs : MeasurableSet s) :
    volume (matrixPairEquiv M N H ⁻¹' s) = volume s :=
  (measurePreserving_matrixPairEquiv M N H).measure_preimage hs.nullMeasurableSet

end AISafetyAtlas.SingularLearning

