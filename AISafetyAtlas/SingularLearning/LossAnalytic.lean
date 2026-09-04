module

public import AISafetyAtlas.SingularLearning.Coordinates
public import AISafetyAtlas.SingularLearning.Loss
public import AISafetyAtlas.SingularLearning.MatrixAnalytic

/-!
# The reduced-rank loss is real-analytic

This module proves that the germ `MAIS-O70` is about — the reduced-rank
population loss, read in the Euclidean coordinates of `Coordinates.lean` — is
real-analytic at every point.

## Why the module exists

`ZetaPair.lean` records, in "Why there is no general bridge here", that the
general passage from the ball-volume local pair to the zeta/pole-order local pair
is **false**: `HasExactLocalPair` constrains only the leading behaviour of the
sublevel volume, and a logarithmic correction to it turns the pole into a branch
point. The hypothesis print carries, and the one a general form drops,
is that `K` is nonnegative and **real-analytic**.

What the atlas states instead is `O70ZetaPoleBridge`, the same passage at the O70
germs only. The reason to believe that narrow form is precisely that those germs
satisfy print's missing hypothesis. Until now that reason was prose. This module
machine-checks it: `analyticAt_rrrLoss_symm_coords` is the analyticity of
`rrrLossCoords M N H C`, and `rrrLoss_nonneg` (in `Loss.lean`) is the
nonnegativity, so the pair of hypotheses `MAIS-A6.tex` `def:local` carries is
discharged for the O70 germs.

It does not prove the bridge — resolution of singularities is not in the atlas —
and it is not evidence that the bridge's *proof* is within reach. It removes one
specific way the narrowed bridge could have been vacuous or false: a bridge
narrowed to germs that did not in fact satisfy print's hypothesis would have been
narrowed to nothing.

## The argument

`rrrLoss_eq_sum_sq` writes the loss as `½ ∑ᵢ ∑ⱼ (BA − C)ᵢⱼ²`, and each entry of
`BA − C` is `∑ₖ Bᵢₖ Aₖⱼ − Cᵢⱼ`. So the loss is a *polynomial* in the entries of
`(A, B)` — degree four, with no denominators — and analyticity is closure of
`AnalyticAt` under finite sums, products and powers. No Gaussian integral
survives into the proof: the integral is discharged once, in `Loss.lean`.

`analyticAt_rrrLoss_of_entries` is the statement in that form, over an arbitrary
real normed space of parameters, and the two concrete corollaries instantiate it:

* `analyticAt_rrrLoss_pair`, on the matrix pair itself, with the Frobenius normed
  instances `MatrixAnalytic.lean` uses (matrices carry no global normed instance
  in the pinned Mathlib, so some choice has to be made; analyticity is a property
  of the topology, and all norms on a finite-dimensional real space are
  equivalent, so nothing depends on the choice);
* `analyticAt_rrrLoss_symm_coords`, in Euclidean coordinates, which is the one the
  local-pair machinery consumes.

The coordinate form is available only because `matrixPairEquiv` is a genuine
`≃ₗ[ℝ]` and not merely a `MeasurableEquiv`: each coordinate of the parameter is
read off by `matrixPairEquiv_symm_apply` as a single entry of `A` or `B`, so an
entry of the parameter matrices is a *coordinate functional* on
`EuclideanSpace ℝ (Fin (H * N + M * H))`, hence continuous linear, hence analytic.
Had `Coordinates.lean` supplied only the measurable packaging, this step would
have no proof, and the module would stop here.

## Where the `rrrLossCoords` form lives

`rrrLossCoords` is defined in `Conjectures/MAIS/O70.lean`, which imports this
layer, so the statement literally about it cannot live here. It is definitionally
`fun x => rrrLoss C ((matrixPairEquiv M N H).symm x).1 ((matrixPairEquiv M N H).symm x).2`,
which is what `analyticAt_rrrLoss_symm_coords` is stated about, so the O70-side
corollary is that theorem applied unchanged.
-/

namespace AISafetyAtlas.SingularLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M N H : ℕ}

/-! ## The loss as a polynomial in the entries -/

/-- **The loss is analytic in any analytic family of parameters.** If the entries
of `A y` and `B y` depend analytically on `y`, so does `rrrLoss C (A y) (B y)`.

This is the whole mathematical content of the module: by `rrrLoss_eq_sum_sq` the
loss is `½ ∑ᵢ ∑ⱼ (∑ₖ Bᵢₖ Aₖⱼ − Cᵢⱼ)²`, a polynomial of degree four in the
entries, so it is built from the hypotheses by finite sums, products and squares
alone. -/
public theorem analyticAt_rrrLoss_of_entries (C : Matrix (Fin M) (Fin N) ℝ)
    {A : E → Matrix (Fin H) (Fin N) ℝ} {B : E → Matrix (Fin M) (Fin H) ℝ} {x : E}
    (hA : ∀ i j, AnalyticAt ℝ (fun y => A y i j) x)
    (hB : ∀ i j, AnalyticAt ℝ (fun y => B y i j) x) :
    AnalyticAt ℝ (fun y => rrrLoss C (A y) (B y)) x := by
  have hfun : (fun y => rrrLoss C (A y) (B y))
      = fun y => (1 / 2) * ∑ i, ∑ j, ((∑ k, B y i k * A y k j) - C i j) ^ 2 := by
    funext y
    rw [rrrLoss_eq_sum_sq]
    simp [Matrix.sub_apply, Matrix.mul_apply]
  rw [hfun]
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ =>
    Finset.analyticAt_fun_sum _ fun j _ => AnalyticAt.pow ?_ 2)
  exact (Finset.analyticAt_fun_sum _ fun k _ => (hB i k).mul (hA k j)).sub analyticAt_const

/-! ## On the matrix pair

Matrices carry no global normed instance in the pinned Mathlib, so the statement
on the parameter space itself needs a choice of norm. It is the same Frobenius
pair `MatrixAnalytic.lean` installs, and nothing depends on the choice. -/

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **The loss is analytic on the matrix parameter space.** Stated on the product
`ℝ^{H×N} × ℝ^{M×H}` with the Frobenius norm on each factor. -/
public theorem analyticAt_rrrLoss_pair (C : Matrix (Fin M) (Fin N) ℝ)
    (p : Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ) :
    AnalyticAt ℝ
      (fun q : Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ => rrrLoss C q.1 q.2) p :=
  analyticAt_rrrLoss_of_entries C
    (fun i j => analyticAt_entry_comp (analyticAt_fst (𝕜 := ℝ)) i j)
    (fun i j => analyticAt_entry_comp (analyticAt_snd (𝕜 := ℝ)) i j)

/-- The same statement on the whole parameter space. -/
public theorem analyticOnNhd_rrrLoss_pair (C : Matrix (Fin M) (Fin N) ℝ) :
    AnalyticOnNhd ℝ
      (fun q : Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ => rrrLoss C q.1 q.2)
      Set.univ :=
  fun p _ => analyticAt_rrrLoss_pair C p

end Frobenius

/-! ## In Euclidean coordinates

The form the local-pair machinery consumes. Each coordinate of the parameter is a
single entry of `A` or of `B`, by `matrixPairEquiv_symm_apply`, so the entry maps
are the coordinate functionals of `EuclideanSpace ℝ (Fin (H * N + M * H))`. -/

/-- Reading off a Euclidean coordinate is analytic: it is a continuous linear
functional, `EuclideanSpace.proj`. -/
public theorem analyticAt_euclideanSpace_coord {n : ℕ} (k : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => y k) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).analyticAt x

/-- **The O70 germ is real-analytic**, at every point of the coordinate space.

The function is definitionally `rrrLossCoords M N H C`, so this is the
analyticity that `MAIS-A6.tex` `def:local` requires of `K` and that
`O70ZetaPoleBridge` needs its germs to have; see the module docstring. -/
public theorem analyticAt_rrrLoss_symm_coords (C : Matrix (Fin M) (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin (H * N + M * H))) :
    AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin (H * N + M * H)) =>
      rrrLoss C ((matrixPairEquiv M N H).symm y).1 ((matrixPairEquiv M N H).symm y).2) x :=
  analyticAt_rrrLoss_of_entries C
    (fun i j => analyticAt_euclideanSpace_coord (matrixPairIndex M N H (Sum.inl (i, j))) x)
    (fun i j => analyticAt_euclideanSpace_coord (matrixPairIndex M N H (Sum.inr (i, j))) x)

/-- The same statement on the whole coordinate space. -/
public theorem analyticOnNhd_rrrLoss_symm_coords (C : Matrix (Fin M) (Fin N) ℝ) :
    AnalyticOnNhd ℝ (fun y : EuclideanSpace ℝ (Fin (H * N + M * H)) =>
      rrrLoss C ((matrixPairEquiv M N H).symm y).1 ((matrixPairEquiv M N H).symm y).2)
      Set.univ :=
  fun x _ => analyticAt_rrrLoss_symm_coords C x

/-- The germ is continuous, a consequence used wherever a sublevel set of the
loss has to be measurable or its ball integrals have to make sense. -/
public theorem continuous_rrrLoss_symm_coords (C : Matrix (Fin M) (Fin N) ℝ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin (H * N + M * H)) =>
      rrrLoss C ((matrixPairEquiv M N H).symm y).1 ((matrixPairEquiv M N H).symm y).2) :=
  continuous_iff_continuousAt.2 fun x => (analyticAt_rrrLoss_symm_coords C x).continuousAt

end AISafetyAtlas.SingularLearning
