module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance

/-!
# The reduced-rank population loss, as print writes it

`MAIS-O70` defines the population loss of reduced-rank regression as a **Gaussian
expectation**: for a truth matrix `C = B₀A₀ : ℝ^{M×N}` and parameters
`A : ℝ^{H×N}`, `B : ℝ^{M×H}`,

    K(A, B) = ½ · 𝔼_x ‖(BA − C) x‖² ,   x ~ N(0, I_N) .

That expectation is `rrrLoss` here, and it is the *definition*. The familiar
Frobenius form `½‖BA − C‖²_F` is `rrrLoss_eq_frobenius`, a **theorem**.

The order matters. Starting from `½‖BA − C‖²_F` and calling it print's `K` is a
silent substitution of a different object that happens to be numerically equal —
exactly the move a fidelity audit exists to catch. Here the substitution is
performed once, in public, with a proof: everything downstream may use the
Frobenius form knowing that the identification has been checked rather than
assumed. Nothing in this module is specific to reduced-rank regression; `B * A`
is never factored, so the same identity covers any linear model.

## The Gaussian input

The second-moment step is `integral_sq_strongDual_stdGaussian`:
`∫ (L x)² ∂(stdGaussian E) = ‖L‖²` for a continuous linear functional `L`. It is
`ProbabilityTheory.variance_dual_stdGaussian` (`Var[L] = ‖L‖²`) combined with
`ProbabilityTheory.integral_strongDual_stdGaussian` (`𝔼[L] = 0`), so that
`𝔼[L²] = Var[L] + 𝔼[L]² = ‖L‖²`. Integrability, which is what lets the row sum
move outside the integral, comes from `ProbabilityTheory.IsGaussian.memLp_dual`
at `p = 2`. Applying this to the `M` row functionals
`x ↦ ⟪row i (BA − C), x⟫` and summing gives the Frobenius identity.

## A norm that must not be the wrong one

`(BA − C).mulVec x` has type `Fin M → ℝ`, whose ambient norm is the **supremum**
norm; writing `‖(BA − C).mulVec x‖` would silently state a different — and false —
theorem. The definition therefore goes through `Matrix.toEuclideanLin`, which
lands in `EuclideanSpace ℝ (Fin M)`, so `‖·‖` is the Euclidean norm print means.
`rrrLoss_eq_integral_mulVec` records the explicit `toLp`/`ofLp` form of the same
integrand for readers who want to see the matrix–vector product.

## The zero fiber

`rrrLoss_eq_zero_iff` identifies the singular-learning zero fiber

    W₀ = {(A, B) : K(A, B) = 0} = {(A, B) : B * A = C} ,

which is the set whose geometry the real log-canonical threshold of `MAIS-O70`
measures, and which is the hypothesis of the rank-feasibility results in
`ReducedRank.lean`. Together with `rrrLoss_nonneg` this says `W₀` is precisely
the minimum locus of `K`, so `K` is a genuine Kullback–Leibler-type loss and not
merely a function that happens to vanish there.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace Matrix

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Second moment of a continuous linear functional under the standard Gaussian. -/
public theorem integral_sq_strongDual_stdGaussian (L : StrongDual ℝ E) :
    ∫ x, (L x) ^ 2 ∂(stdGaussian E) = ‖L‖ ^ 2 := by
  have hmem : MemLp (L : E → ℝ) 2 (stdGaussian E) := IsGaussian.memLp_dual _ L 2 (by simp)
  have h := variance_eq_sub hmem
  rw [variance_dual_stdGaussian, integral_strongDual_stdGaussian] at h
  simpa [Pi.pow_apply] using h.symm

/-- Squares of continuous linear functionals are Gaussian-integrable. -/
public theorem integrable_sq_strongDual_stdGaussian (L : StrongDual ℝ E) :
    Integrable (fun x ↦ (L x) ^ 2) (stdGaussian E) :=
  (IsGaussian.memLp_dual _ L 2 (by simp)).integrable_sq

end Gaussian

variable {M N H : ℕ}

/-! ## Print's definition -/

/-- **Print's loss.** The population loss of the reduced-rank model at parameters
`(A, B)` against truth matrix `C`, as `MAIS-O70` writes it: half the Gaussian
average of `‖(BA − C) x‖²` over `x ~ N(0, I_N)`.

`Matrix.toEuclideanLin` is what makes the norm the Euclidean one: the bare
`(B * A - C).mulVec x` lives in `Fin M → ℝ`, where `‖·‖` is the supremum norm.
See `rrrLoss_eq_integral_mulVec` for the same integrand written out. -/
@[expose] public noncomputable def rrrLoss (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) : ℝ :=
  (1 / 2) * ∫ x, ‖(B * A - C).toEuclideanLin x‖ ^ 2
    ∂(stdGaussian (EuclideanSpace ℝ (Fin N)))

/-- The integrand of `rrrLoss` spelled out as a matrix–vector product: the
transport `ofLp`/`toLp` between `EuclideanSpace ℝ (Fin N)` and `Fin N → ℝ` is
explicit, and the norm is taken after landing back in `EuclideanSpace ℝ (Fin M)`. -/
public theorem rrrLoss_eq_integral_mulVec (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = (1 / 2) * ∫ x, ‖(toLp 2 ((B * A - C) *ᵥ ofLp x) : EuclideanSpace ℝ (Fin M))‖ ^ 2
      ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) := rfl

/-! ## The derived quadratic form -/

/-- **The Frobenius identity, entrywise.** The Gaussian expectation of print's
definition equals half the sum of squared entries of `BA − C`.

Proof: expand `‖(BA − C)x‖²` as a sum over rows of `⟪row i, x⟫²`, move the finite
sum out of the integral (`MeasureTheory.integral_finsetSum`, with integrability
from `ProbabilityTheory.IsGaussian.memLp_dual` at `p = 2`), and evaluate each
term by `integral_sq_strongDual_stdGaussian` as `‖row i‖²`.

Stated with an explicit double sum rather than a norm so that it carries no
instance argument; `rrrLoss_eq_frobenius` is the same statement with Mathlib's
Frobenius norm. -/
public theorem rrrLoss_eq_sum_sq (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = (1 / 2) * ∑ i, ∑ j, (B * A - C) i j ^ 2 := by
  set D := B * A - C with hD
  set μ := stdGaussian (EuclideanSpace ℝ (Fin N)) with hμ
  set L : Fin M → StrongDual ℝ (EuclideanSpace ℝ (Fin N)) :=
    fun i ↦ innerSL ℝ (toLp 2 (D i)) with hL
  have hLapp : ∀ (i : Fin M) (x : EuclideanSpace ℝ (Fin N)), L i x = (D *ᵥ ofLp x) i := by
    intro i x
    simp [hL, PiLp.inner_apply, Matrix.mulVec_apply_eq_sum, RCLike.inner_apply, mul_comm]
  have hpt : ∀ x : EuclideanSpace ℝ (Fin N),
      ‖D.toEuclideanLin x‖ ^ 2 = ∑ i, (L i x) ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hLapp]; rfl
  rw [rrrLoss, ← hD]
  congr 1
  calc ∫ x, ‖D.toEuclideanLin x‖ ^ 2 ∂μ = ∫ x, ∑ i, (L i x) ^ 2 ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ i, ∫ x, (L i x) ^ 2 ∂μ :=
        integral_finsetSum _ fun i _ ↦ integrable_sq_strongDual_stdGaussian (L i)
    _ = ∑ i, ‖L i‖ ^ 2 := Finset.sum_congr rfl fun i _ ↦ integral_sq_strongDual_stdGaussian (L i)
    _ = ∑ i, ∑ j, D i j ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hL, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]

/-! ## The Frobenius form -/

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/-- **The Frobenius form of print's loss**, `K(A, B) = ½‖BA − C‖²_F`.

This is the identity that is usually taken as the definition. It is a theorem
here, and the norm is Mathlib's Frobenius norm on matrices, which is a `local`
instance rather than a global one (matrices carry several natural norms); a
consumer wanting this form must reinstate `Matrix.frobeniusNormedAddCommGroup`,
or use the instance-free `rrrLoss_eq_sum_sq`. -/
public theorem rrrLoss_eq_frobenius (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = (1 / 2) * ‖B * A - C‖ ^ 2 := by
  rw [rrrLoss_eq_sum_sq]
  congr 1
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

end Frobenius

/-! ## The zero fiber and nonnegativity -/

/-- The population loss is nonnegative: it is a Gaussian average of squared norms. -/
public theorem rrrLoss_nonneg (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    0 ≤ rrrLoss C A B := by
  rw [rrrLoss_eq_sum_sq]
  positivity

/-- **The zero fiber.** `K(A, B) = 0` exactly on `W₀ = {(A, B) : B * A = C}`. -/
public theorem rrrLoss_eq_zero_iff (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = 0 ↔ B * A = C := by
  rw [rrrLoss_eq_sum_sq]
  constructor
  · intro h
    have hsum : ∑ i, ∑ j, (B * A - C) i j ^ 2 = 0 := by linarith
    have hrow := fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg ((B * A - C) i j))).1 hsum i
      (Finset.mem_univ i)
    ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ sq_nonneg ((B * A - C) i j))).1 (hrow i) j (Finset.mem_univ j)
    have hz : (B * A - C) i j = 0 := by
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simpa [Matrix.sub_apply, sub_eq_zero] using hz
  · intro h
    rw [h]
    simp

/-! ## Worked examples

Two endpoints, so the module is not statement-only. -/

/-- Any exact factorization sits at loss `0`: the zero fiber is nonempty whenever
`C` itself factors through the hidden layer. -/
example (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) (h : B * A = C) : rrrLoss C A B = 0 :=
  (rrrLoss_eq_zero_iff C A B).2 h

/-- A concrete nonzero value: with `H = 0` the model can only output `0`, so the
loss is `½‖C‖²_F`, here `½ · 1` for `C = 1` of shape `1 × 1`. -/
example : rrrLoss (1 : Matrix (Fin 1) (Fin 1) ℝ) (A := (0 : Matrix (Fin 0) (Fin 1) ℝ))
    (0 : Matrix (Fin 1) (Fin 0) ℝ) = 1 / 2 := by
  rw [rrrLoss_eq_sum_sq]
  norm_num [Matrix.one_apply]

end AISafetyAtlas.SingularLearning
