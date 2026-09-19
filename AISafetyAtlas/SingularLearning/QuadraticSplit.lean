module

public import AISafetyAtlas.SingularLearning.PairTransfer

/-!
# The signature splitting of a Euclidean space

Stage 3 of the MAIS-O77(b) programme needs the local band order of a
nondegenerate indefinite quadratic form.  Mathlib supplies Sylvester's law of
inertia -- QuadraticForm.equivalent_one_neg_one_weighted_sum_squared, verified
present at the pinned revision -- which reduces any such form to a signed sum of
squares, so what is left is the *model* germ

    `|‖u‖² - ‖v‖²|`   on   `ℝ^p × ℝ^q`,

read on `EuclideanSpace ℝ (Fin (p + q))`, which is where the atlas's volume
interface lives.

The coordinate splitting itself is `euclideanProdEquiv`, already in
`PairTransfer` and already proved measure preserving there.  This module adds
only what that packaging lacks: the same map as a **linear** equivalence, which
is what makes the germ's degree-two homogeneity a one-line consequence of
`map_smul` rather than a coordinate computation.

The two packagings are the same function by `rfl`, so the measure preservation is
inherited rather than reproved.  Keeping that as a stated lemma rather than an
appeal to "obviously the same map" is the point: a reshape whose measure or norm
behaviour is merely assumed is exactly the class of step whose failure no gate
reports, because every downstream statement still elaborates.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory

/-- The splitting as a linear equivalence.  The same function as
`euclideanProdEquiv` (see `coe_splitLE`); this packaging carries the linear
structure that `MeasurableEquiv` does not. -/
@[expose] public noncomputable def splitLE (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (p + q)) :=
  ((WithLp.linearEquiv 2 ℝ (Fin p → ℝ)).prodCongr (WithLp.linearEquiv 2 ℝ (Fin q → ℝ))).trans <|
    (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℝ ℝ).symm.trans <|
      (LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv.symm).trans
        (WithLp.linearEquiv 2 ℝ (Fin (p + q) → ℝ)).symm

/-- The linear packaging is the measurable one, by `rfl`.  Everything measure
theoretic about `splitLE` is inherited through this. -/
public theorem coe_splitLE (p q : ℕ) : ⇑(splitLE p q) = ⇑(euclideanProdEquiv p q) := rfl

/-- The split carries Lebesgue measure to Lebesgue measure, inherited from
`measurePreserving_euclideanProdEquiv`. -/
public theorem measurePreserving_splitLE (p q : ℕ) :
    MeasurePreserving (splitLE p q) volume volume := by
  rw [coe_splitLE]; exact measurePreserving_euclideanProdEquiv p q

/-- **The split is an ℓ² isometry.**  A ball of the ambient space is exactly the
set `‖u‖² + ‖v‖² < δ²` in the two factors, so transporting a sublevel volume
through `splitLE` needs no Jacobian and no change of radius.  Read off
`dist_sq_euclideanProdEquiv` at the origin, using that the linear packaging sends
`0` to `0`. -/
public theorem norm_sq_splitLE (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) :
    ‖splitLE p q (u, v)‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have hz : euclideanProdEquiv p q (0, 0) = 0 := by
    rw [← coe_splitLE]; exact map_zero (splitLE p q)
  have hd := dist_sq_euclideanProdEquiv p q u 0 v 0
  rw [hz, dist_zero_right, dist_zero_right, dist_zero_right] at hd
  rw [coe_splitLE]
  exact hd

/-! ## The model band germ

The germ whose local order Stage 3 must compute.  It is written on the ambient
Euclidean space, because that is where `HasLocalVolumeOrder` lives, but it is
*defined* through the split, so every statement about it can be moved to the
product by `measurePreserving_splitLE`.
-/

/-- **The model band germ of signature `(p, q)`**: the absolute value of the
nondegenerate form `‖u‖² - ‖v‖²`, read on `EuclideanSpace ℝ (Fin (p + q))`
through the coordinate split. -/
@[expose] public noncomputable def modelBandGerm (p q : ℕ)
    (w : EuclideanSpace ℝ (Fin (p + q))) : ℝ :=
  |‖((splitLE p q).symm w).1‖ ^ 2 - ‖((splitLE p q).symm w).2‖ ^ 2|

public theorem modelBandGerm_nonneg (p q : ℕ) (w : EuclideanSpace ℝ (Fin (p + q))) :
    0 ≤ modelBandGerm p q w := abs_nonneg _

/-- Evaluated on a split pair, the germ is what it looks like. -/
public theorem modelBandGerm_splitLE (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) :
    modelBandGerm p q (splitLE p q (u, v)) = |‖u‖ ^ 2 - ‖v‖ ^ 2| := by
  simp [modelBandGerm]

/-- The germ is symmetric in the two blocks, because `|a - b| = |b - a|`.  This is
what lets the dimension hypothesis be carried by whichever block is larger. -/
public theorem modelBandGerm_splitLE_swap (p q : ℕ) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) :
    modelBandGerm p q (splitLE p q (u, v)) = modelBandGerm q p (splitLE q p (v, u)) := by
  rw [modelBandGerm_splitLE, modelBandGerm_splitLE, abs_sub_comm]

public theorem continuous_modelBandGerm (p q : ℕ) : Continuous (modelBandGerm p q) := by
  have hc : Continuous (fun w : EuclideanSpace ℝ (Fin (p + q)) => (splitLE p q).symm w) :=
    LinearMap.continuous_of_finiteDimensional (splitLE p q).symm.toLinearMap
  unfold modelBandGerm
  exact continuous_abs.comp
    (((continuous_fst.comp hc).norm.pow 2).sub ((continuous_snd.comp hc).norm.pow 2))

public theorem measurable_modelBandGerm (p q : ℕ) : Measurable (modelBandGerm p q) :=
  (continuous_modelBandGerm p q).measurable

/-- **The germ is homogeneous of degree two.**  This is the hypothesis
`hasLocalVolumeOrder_of_gaussianLaplace` and the ball-window sandwiches ask for,
and it is what makes a single radius enough to determine the pair.  It is a
one-line consequence of linearity, which is why the linear packaging exists. -/
public theorem modelBandGerm_smul (p q : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (w : EuclideanSpace ℝ (Fin (p + q))) :
    modelBandGerm p q (t • w) = t ^ 2 * modelBandGerm p q w := by
  have hsymm : (splitLE p q).symm (t • w) = t • (splitLE p q).symm w := by
    simp
  simp only [modelBandGerm, hsymm, Prod.smul_fst, Prod.smul_snd, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht, mul_pow]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]

end AISafetyAtlas.SingularLearning
