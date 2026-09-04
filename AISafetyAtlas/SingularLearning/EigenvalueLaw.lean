module

public import AISafetyAtlas.SingularLearning.ChamberIntegral
public import AISafetyAtlas.SingularLearning.GramSpectrum
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# `O70-EIGEN-LAW`: the real-Wishart density and the eigenvalue Jacobian, as a frontier

This module states — and does **not** prove — the one classical input that the residual-germ
computation of the MAIS issue #3 candidate cites rather than reproves. It is a designated trust
frontier of the O70 campaign, and every theorem that consumes it carries it as a visible
hypothesis.

## What the candidate cites

Proposition 8.11 (p. 36) of the candidate reads, for a real `k × d` matrix `X` with `k ≤ d`:

> There is a constant `Z = Z(k,d) ∈ (0,∞)` such that for every Borel
> `g : [0,∞)^k → [0,∞]` invariant under permutations of its arguments,
> `∫_{ℝ^{k×d}} e^{-‖X‖²_F} g(s(X)) dX = Z ∫_{(0,∞)^k} g(s) ∏ᵢ sᵢ^α ∏_{i<j} |sᵢ − sⱼ| e^{−∑ sᵢ} ds`,
> where `α = (d − k − 1)/2` and `s(X)` are the eigenvalues of the Gram matrix.

Its proof names two citations and nothing else: the real Wishart density
(Muirhead, *Aspects of Multivariate Statistical Theory*, Theorem 3.2.1, after James 1954) and
the eigenvalue Jacobian of a symmetric matrix (Muirhead Theorem 3.2.17).

## What is frozen here, and why this shape

`EigenvalueLawStatement` is the identity **at the test functions the derivation consumes**,
namely `g(s) = ∏ᵢ (1 + T sᵢ)^{-ρ}` for `T ≥ 0` and `ρ ≥ 0`. Three reasons:

1. **It is what Proposition 8.13 uses.** That proposition is Proposition 8.9 (proved, as
   `integral_exp_neg_frobenius_mul`) composed with Lemma 8.10 (proved, as
   `det_one_add_smul_gram_comm`) and then Proposition 8.11 at exactly this `g`. Stating the
   frontier at a wider class would assume more than the argument needs.
2. **The eigenvalue map never has to be defined.** `∏ᵢ (1 + T sᵢ(X))^{-ρ}` is
   `det(1 + T·X Xᵀ)^{-ρ}`, and the determinant is available without choosing which of `X Xᵀ`
   and `Xᵀ X` carries the spectrum, and without a `Fin (min h n)`-indexed eigenvalue vector.
   `det_one_add_smul_eq_prod_eigenvalues` below records that the two really are the same
   quantity, so nothing is hidden by the choice.
3. **It cannot be tailored.** `Z` is quantified *before* `T` and `ρ`: one constant serves the
   whole two-parameter family. A single normalisation cannot be chosen to make an arbitrary
   family of identities true, and `eigenvalueLaw_one_one` reads the normalisation off at the
   smallest shape.

The right-hand side is `chamberJFull`, Definition 8.12's `J(T)`, so every ingredient print names
is visible in the statement: the Vandermonde factor `chamberAbsVandermonde`, the weight
`∏ sᵢ^α`, the exponential `e^{−∑ sᵢ}`, and the resolvent `∏ (1 + T sᵢ)^{-ρ}`. The domain is the
**full orthant** `(0,∞)^k`, not the ordered chamber; `chamberJFull_eq_factorial_mul_chamberI`
(Lemma 8.15) is the bridge to the chamber, and is proved.

The exponent `α = (d − k − 1)/2` is formed in `ℝ`. Writing it with `ℕ`-subtraction would give
`0` at `d = k` instead of `-1/2`, which is a different — and false — statement.

## What is **not** here

No Wishart distribution, no Haar measure on `O(k)`, no coarea formula, no general Weyl
integration, and no SVD library. The candidate does not build them either; it cites them. Under
the campaign's anti-recursion rule this module states the consumed identity, records its
provenance, and stops.

## Stress evidence

`eigenvalueLaw_normalisation` pins `Z` by the Gaussian normalisation at `T = 0`;
`eigenvalueLaw_chamberJFull_pos` extracts positivity and finiteness of `J(0)` from it; and
`eigenvalueLaw_one_one` is the `1 × 1` consequence, `Z · J(0) = √π`, where the exponent is
`α = −1/2` — the value that a `ℕ`-truncated `(d − k − 1)` would have silently turned into `0`.
All three are consequences of the frozen proposition, not inhabitants of it. Nothing below is a
proof of `EigenvalueLawStatement`, and nothing below may be read as evidence that it holds; they
are checks that it is not malformed.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Matrix

/-! ## The determinant is the eigenvalue product

Not needed to *state* the frontier — but needed to know that stating it through `det` hides
nothing. -/

private theorem det_one_add_smul_conj {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ}
    (hU : U * star U = 1) (μ : Fin k → ℝ) (T : ℝ) :
    (1 + T • (U * Matrix.diagonal μ * star U)).det = ∏ i, (1 + T * μ i) := by
  classical
  have hkey : (1 : Matrix (Fin k) (Fin k) ℝ) + T • (U * Matrix.diagonal μ * star U)
      = U * (1 + T • Matrix.diagonal μ) * star U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU, Matrix.mul_smul, Matrix.smul_mul]
  have hdiag : (1 : Matrix (Fin k) (Fin k) ℝ) + T • Matrix.diagonal μ
      = Matrix.diagonal (fun i => 1 + T * μ i) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have hdet : U.det * (star U).det = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  rw [hkey, hdiag, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hring : U.det * (∏ i, (1 + T * μ i)) * (star U).det
      = U.det * (star U).det * ∏ i, (1 + T * μ i) := by ring
  rw [hring, hdet, one_mul]

/-- **`det (1 + T·A) = ∏ (1 + T μᵢ)`** for Hermitian `A`. This is why writing the frontier's
test function as a determinant rather than as a product over eigenvalues loses nothing: the two
are literally the same number. -/
public theorem det_one_add_smul_eq_prod_eigenvalues {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian) (T : ℝ) :
    (1 + T • A).det = ∏ i, (1 + T * hA.eigenvalues i) := by
  classical
  have hU : (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
      * star (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) = 1 :=
    hA.eigenvectorUnitary.2.2
  have hspec : A = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
      * Matrix.diagonal hA.eigenvalues
      * star (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Function.comp_def] using h
  rw [show (1 + T • A) = 1 + T • ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
      * Matrix.diagonal hA.eigenvalues
      * star (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)) from by rw [← hspec]]
  exact det_one_add_smul_conj hU _ T

/-- The Gram matrix `X Xᵀ` of a real matrix is Hermitian, so its eigenvalues exist and
`det_one_add_smul_eq_prod_eigenvalues` applies to it. -/
public theorem isHermitian_gram {k d : ℕ} (X : Matrix (Fin k) (Fin d) ℝ) :
    (X * Xᵀ).IsHermitian := (posSemidef_mul_transpose X).1

/-! ## The frontier -/

/-- **`O70-EIGEN-LAW`.** The real-Wishart density together with the eigenvalue Jacobian, at the
test functions the candidate's derivation consumes.

For every wide shape `k ≤ d` there is a single positive constant `Z(k, d)` such that, for every
`ρ ≥ 0` and every `T ≥ 0`,

    ∫_{ℝ^{k×d}} e^{-‖X‖²_F} det(1 + T·X Xᵀ)^{-ρ} dX = Z · J(T) ,

where `J(T) = chamberJFull k T ((d − k − 1)/2) ρ` is Definition 8.12's integral over the full
positive orthant.

`Z` is quantified before `T` and `ρ`: one normalisation for the whole family. This is a
hypothesis; it is cited by the candidate to Muirhead Theorems 3.2.1 and 3.2.17 (after James
1954), and it is **not proved anywhere in the atlas**. -/
@[expose] public noncomputable def EigenvalueLawStatement : Prop :=
  ∀ k d : ℕ, 0 < k → k ≤ d →
    ∃ Z : ℝ, 0 < Z ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ∀ T : ℝ, 0 ≤ T →
        ∫ X : Fin k → Fin d → ℝ,
            Real.exp (-∑ i, ∑ j, X i j ^ 2)
              * (1 + T • (Matrix.of X * (Matrix.of X)ᵀ)).det ^ (-ρ)
          = Z * chamberJFull k T (((d : ℝ) - k - 1) / 2) ρ

/-- The statement with every quantifier written out, for the statement lock: the frozen surface
is `∀ k d, 0 < k → k ≤ d → ∃ Z, 0 < Z ∧ ∀ ρ ≥ 0, ∀ T ≥ 0, …`, with the exponent
`(d − k − 1)/2` formed in `ℝ` and the domain the full orthant `(0,∞)^k`. -/
public theorem eigenvalueLawStatement_iff :
    EigenvalueLawStatement ↔
      ∀ k d : ℕ, 0 < k → k ≤ d →
        ∃ Z : ℝ, 0 < Z ∧
          ∀ ρ : ℝ, 0 ≤ ρ → ∀ T : ℝ, 0 ≤ T →
            ∫ X : Fin k → Fin d → ℝ,
                Real.exp (-∑ i, ∑ j, X i j ^ 2)
                  * (1 + T • (Matrix.of X * (Matrix.of X)ᵀ)).det ^ (-ρ)
              = Z * ∫ s in Set.univ.pi fun _ : Fin k => Set.Ioi (0:ℝ),
                  Real.exp (-∑ i, s i) * (∏ i, s i ^ (((d : ℝ) - k - 1) / 2))
                    * chamberAbsVandermonde s * ∏ i, (1 + T * s i) ^ (-ρ) :=
  Iff.rfl

/-! ## Stress evidence

Consequences of the frozen proposition, proved so that a malformed transcription would be
caught. None of them is an inhabitant of `EigenvalueLawStatement`, and none is evidence that it
is true.

The numerical companion is `scripts/reproduce_eigenvalue_law_probe.py`, which attempts to
falsify the law rather than confirm it. At `k = 1` the left side reduces analytically to the
right side's own integral, so that arm is exact: it pins `Z = π^(d/2)/Γ(d/2)` and finds it
constant across five `(T, ρ)` to machine precision, at `d ∈ {1,2,3,5}`. At `k = 2` — the
smallest shape whose Vandermonde factor is not `1` — the left side is estimated by
Monte-Carlo. That arm carries its own power check: with the Vandermonde the ratio is constant
to about `10⁻³`, and with it deleted the same ratio moves by about `0.26`, so the test can
reject a missing Vandermonde. It probes no shape with `k > 2`, and it says nothing about
`O70-EXACT-LOCAL`. -/

/-- **The normalisation is pinned by `T = 0`.** At `T = 0` the determinant factor is `1`, so the
left side is the plain Gaussian normalisation and `Z` is determined by `J(0)`. A transcription
that got the weight or the Vandermonde wrong would fail this at the first nontrivial shape. -/
public theorem eigenvalueLaw_normalisation (hEigen : EigenvalueLawStatement)
    {k d : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    ∃ Z : ℝ, 0 < Z ∧
      ∫ X : Fin k → Fin d → ℝ, Real.exp (-∑ i, ∑ j, X i j ^ 2)
        = Z * chamberJFull k 0 (((d : ℝ) - k - 1) / 2) 0 := by
  obtain ⟨Z, hZ, hlaw⟩ := hEigen k d hk hkd
  refine ⟨Z, hZ, ?_⟩
  have h := hlaw 0 le_rfl 0 le_rfl
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp

/-- **`J(0)` is finite and positive**, read off the frozen proposition rather than assumed: the
Gaussian normalisation on the left is positive and finite, and `Z > 0`. -/
public theorem eigenvalueLaw_chamberJFull_pos (hEigen : EigenvalueLawStatement)
    {k d : ℕ} (hk : 0 < k) (hkd : k ≤ d) :
    0 < chamberJFull k 0 (((d : ℝ) - k - 1) / 2) 0 := by
  obtain ⟨Z, hZ, hnorm⟩ := eigenvalueLaw_normalisation hEigen hk hkd
  have hgauss : (0:ℝ) < ∫ X : Fin k → Fin d → ℝ, Real.exp (-∑ i, ∑ j, X i j ^ 2) := by
    have hval := integral_exp_neg_frobenius_mul (p := k) (h := d) (n := 0) 0 le_rfl 0
    simp only [neg_zero, zero_mul, zero_sub, zero_smul, add_zero, Matrix.det_one,
      Real.one_rpow, mul_one] at hval
    rw [hval]
    positivity
  nlinarith [hnorm, hgauss, hZ]

/-- **The `1 × 1` consequence.** At `k = d = 1` the left side is the one-dimensional Gaussian
`√π`, so the frozen proposition says `Z · J(0) = √π` with the exponent `α = −1/2`.

The exponent is the point of this check. `(d − k − 1)/2` at `d = k = 1` is `−1/2`; formed with
`ℕ`-subtraction it would be `0`, the weight `∏ sᵢ^α` would be `1`, and `J(0)` would be `1`
rather than `Γ(1/2)`. The statement as frozen distinguishes the two. -/
public theorem eigenvalueLaw_one_one (hEigen : EigenvalueLawStatement) :
    ∃ Z : ℝ, 0 < Z ∧ Z * chamberJFull 1 0 (-(1/2)) 0 = Real.sqrt Real.pi := by
  obtain ⟨Z, hZ, hnorm⟩ := eigenvalueLaw_normalisation hEigen (k := 1) (d := 1) one_pos le_rfl
  refine ⟨Z, hZ, ?_⟩
  have hα : (((1 : ℕ) : ℝ) - (1 : ℕ) - 1) / 2 = -(1/2) := by norm_num
  rw [hα] at hnorm
  rw [← hnorm]
  have hval := integral_exp_neg_frobenius_mul (p := 1) (h := 1) (n := 0) 0 le_rfl 0
  simp only [neg_zero, zero_mul, zero_sub, zero_smul, add_zero, Matrix.det_one,
    Real.one_rpow, mul_one] at hval
  rw [hval, Real.sqrt_eq_rpow]
  norm_num

/-- **A `Z`-free test of the `T`-dependence.** Every anchor above instantiates `T = 0` and
`ρ = 0`, which is the `g = 1` case: because `Z` is deliberately unpinned, that case checks
finite positive mass but cannot detect a missing overall constant, and it never exercises the
weight exponent under `T` or the factor `∏(1 + T sᵢ)^(-ρ)`.

`Z` is one constant for the whole family, quantified before `ρ` and `T`. So the *ratio* of the
law at two parameter choices is `Z`-free, and cross-multiplying gives an identity in which `Z`
does not appear at all. A transcription that dropped the Vandermonde factor, misplaced `ρ`, or
formed the weight exponent with `ℕ`-subtraction would change one side and not the other.

This is a consequence of the frozen proposition, not an inhabitant of it, and not evidence
that it is true. -/
public theorem eigenvalueLaw_ratio (hEigen : EigenvalueLawStatement)
    {k d : ℕ} (hk : 0 < k) (hkd : k ≤ d) {ρ₁ ρ₂ T₁ T₂ : ℝ}
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) :
    (∫ X : Fin k → Fin d → ℝ, Real.exp (-∑ i, ∑ j, X i j ^ 2)
        * (1 + T₁ • (Matrix.of X * (Matrix.of X)ᵀ)).det ^ (-ρ₁))
      * chamberJFull k T₂ (((d : ℝ) - k - 1) / 2) ρ₂
    = (∫ X : Fin k → Fin d → ℝ, Real.exp (-∑ i, ∑ j, X i j ^ 2)
        * (1 + T₂ • (Matrix.of X * (Matrix.of X)ᵀ)).det ^ (-ρ₂))
      * chamberJFull k T₁ (((d : ℝ) - k - 1) / 2) ρ₁ := by
  obtain ⟨Z, -, hlaw⟩ := hEigen k d hk hkd
  rw [hlaw ρ₁ hρ₁ T₁ hT₁, hlaw ρ₂ hρ₂ T₂ hT₂]
  ring

end AISafetyAtlas.SingularLearning
