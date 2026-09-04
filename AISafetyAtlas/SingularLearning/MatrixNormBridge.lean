module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The two matrix norms, without instances: Lemmas 5.2 and 5.4 of the MAIS issue #3 candidate

Lemmas 5.2 and 5.4 of the candidate are **mixed-norm** statements. 5.2 bounds the *Frobenius*
norm of a product by an *`ℓ²` operator* bound on one factor; 5.4 bounds the `ℓ²` operator norm
of the normalizing factor `R(D)` and of its inverse. Mathlib carries both norms on `Matrix`,
but as two competing `NormedAddCommGroup` instances on one type, only one of which can be
active — and `EliminationChart.lean` and `MatrixAnalytic.lean` need the Frobenius one, because
that is the instance analyticity of the chart is stated against.

**This module removes the conflict by stating neither norm as a norm.** `frobeniusSq` is an
explicit double sum of squares of entries. `IsOpNormSqBound A c` is the quantified inequality
`∑ᵢ (∑ⱼ Aᵢⱼ xⱼ)² ≤ c ∑ⱼ xⱼ²`, again over explicit sums, with `IsOpNormBound` as its unsquared
form and `euclNorm` — the Euclidean norm of a plain vector, taken through `EuclideanSpace` —
as its vector-side companion. Every statement below therefore holds under *any* instance a
consumer has installed, and none of them is invalidated by the choice.

## What is here

* **Lemma 5.2, both sides** — `frobeniusSq_mul_le` and `frobeniusSq_mul_le_right`: an operator
  bound on one factor is a Frobenius bound on the product.
* **The vocabulary Lemma 5.4 is stated in**, and its calculus: `IsOpNormSqBound.mono`,
  `IsOpNormSqBound.mul`, `IsOpNormSqBound.smul`, `isOpNormSqBound_one`,
  `IsOpNormSqBound.nonneg`, and the passage `isOpNormSqBound_iff_isOpNormBound` between the
  squared and unsquared readings of print's `‖·‖₂ ≤ ½`.
* **Frobenius dominates the operator norm** — `isOpNormSqBound_frobeniusSq`, Cauchy–Schwarz
  row by row — together with the openness of the Frobenius ball, `isOpen_frobeniusSq_lt`.
  These two are what let Step 7's neighbourhood `N₀`, an operator-norm condition, be met by a
  strictly smaller and manifestly open condition; see the section note below.
* **Reindexing invariance** — `frobeniusSq_reindex` and its `Matrix.submatrix` forms. The
  chart computes over `Sum` index types while `rrrLoss` is `Fin`-indexed, so the transport
  needs relabelling to be metrically invisible.

## What this module deliberately does not do

It installs **no norm instance on `Matrix`**, and it claims no norm axioms. `frobeniusSq` is a
squared quantity, never a norm object; `IsOpNormSqBound` is a *bound relation*, not the
operator norm, so nothing here says that a constant it carries is the least one available.
Neither is it a statement about `R(D)`: Lemma 5.4 itself — `elimR`, `elimRinv` and print's two
constants — is proved in `EliminationChart.lean`, which imports this file for the relation
those statements are written in.

The sums are written out on purpose. `Fin M → ℝ` carries the **supremum** norm in Mathlib, and
`Loss.lean` keeps `rrrLoss_eq_sum_sq` as its primary form for the same reason; do not
"simplify" any statement below back into `‖·‖`.

## Lemma 5.4's constants, and the label trap

Print is correct, and both of its constants hold as printed —
`elim_opNormSqBound_elimR` and `elim_opNormSqBound_elimRinv`. Their asymmetry is real rather
than an oversight: `not_opNormSqBound_elimR_three` shows the `√6` cannot be improved to `√3`.
A transcription that exchanges `R` and `R⁻¹` grades print's bound on one matrix against the
other and yields a spurious counterexample to `‖R‖₂ ≤ √6`. This file supplies the relation
such a claim would be stated in, and being instance-free does not make the labels
self-checking: which matrix is `R` and which is `R⁻¹` has to be read off print.
-/

namespace AISafetyAtlas.SingularLearning

open WithLp
open scoped Matrix

section Defs

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The squared Frobenius norm of a matrix, as an explicit double sum. -/
@[expose] public noncomputable def frobeniusSq (A : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- `c` dominates the squared `ℓ²` operator norm of `A`. -/
@[expose] public def IsOpNormSqBound (A : Matrix ι κ ℝ) (c : ℝ) : Prop :=
  ∀ x : κ → ℝ, ∑ i, (∑ j, A i j * x j) ^ 2 ≤ c * ∑ j, x j ^ 2

/-- The Euclidean norm of a plain vector. -/
@[expose] public noncomputable def euclNorm (x : κ → ℝ) : ℝ :=
  ‖(toLp 2 x : EuclideanSpace ℝ κ)‖

public theorem euclNorm_nonneg (x : κ → ℝ) : 0 ≤ euclNorm x := norm_nonneg _

public theorem euclNorm_sq (x : κ → ℝ) : euclNorm x ^ 2 = ∑ j, x j ^ 2 := by
  rw [euclNorm, EuclideanSpace.real_norm_sq_eq]

public theorem euclNorm_eq_sqrt (x : κ → ℝ) : euclNorm x = √(∑ j, x j ^ 2) := by
  rw [← euclNorm_sq, Real.sqrt_sq (euclNorm_nonneg x)]

public theorem euclNorm_add_le (x y : κ → ℝ) : euclNorm (x + y) ≤ euclNorm x + euclNorm y := by
  simpa [euclNorm] using norm_add_le (toLp 2 x : EuclideanSpace ℝ κ) (toLp 2 y)

public theorem euclNorm_neg (x : κ → ℝ) : euclNorm (-x) = euclNorm x := by
  simp [euclNorm]

public theorem euclNorm_smul (r : ℝ) (x : κ → ℝ) : euclNorm (r • x) = |r| * euclNorm x := by
  simpa [euclNorm] using norm_smul r (toLp 2 x : EuclideanSpace ℝ κ)

public theorem euclNorm_mulVec_sq (A : Matrix ι κ ℝ) (x : κ → ℝ) :
    euclNorm (A *ᵥ x) ^ 2 = ∑ i, (∑ j, A i j * x j) ^ 2 := by
  rw [euclNorm_sq]
  simp [Matrix.mulVec, dotProduct]

public theorem isOpNormSqBound_iff_euclNorm (A : Matrix ι κ ℝ) (c : ℝ) :
    IsOpNormSqBound A c ↔ ∀ x : κ → ℝ, euclNorm (A *ᵥ x) ^ 2 ≤ c * euclNorm x ^ 2 := by
  simp only [IsOpNormSqBound, euclNorm_sq, Matrix.mulVec, dotProduct]

/-- The unsquared form of `IsOpNormSqBound`. -/
@[expose] public def IsOpNormBound (A : Matrix ι κ ℝ) (k : ℝ) : Prop :=
  ∀ x : κ → ℝ, euclNorm (A *ᵥ x) ≤ k * euclNorm x

public theorem isOpNormSqBound_iff_isOpNormBound {A : Matrix ι κ ℝ} {k : ℝ} (hk : 0 ≤ k) :
    IsOpNormSqBound A (k ^ 2) ↔ IsOpNormBound A k := by
  rw [isOpNormSqBound_iff_euclNorm]
  constructor
  · intro h x
    have h1 := h x
    have h2 : (0 : ℝ) ≤ euclNorm (A *ᵥ x) := euclNorm_nonneg _
    have h3 : (0 : ℝ) ≤ k * euclNorm x := mul_nonneg hk (euclNorm_nonneg x)
    nlinarith
  · intro h x
    have h1 := h x
    have h2 : (0 : ℝ) ≤ euclNorm (A *ᵥ x) := euclNorm_nonneg _
    nlinarith [euclNorm_nonneg x]

end Defs

section Algebra

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

public theorem frobeniusSq_nonneg (A : Matrix ι κ ℝ) : 0 ≤ frobeniusSq A := by
  unfold frobeniusSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] public theorem frobeniusSq_zero : frobeniusSq (0 : Matrix ι κ ℝ) = 0 := by
  simp [frobeniusSq]

public theorem frobeniusSq_eq_zero_iff (A : Matrix ι κ ℝ) : frobeniusSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    rw [frobeniusSq] at h
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j))).1 h i (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (A i j))).1 h1 j (Finset.mem_univ j)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  · rintro rfl
    simp

public theorem frobeniusSq_transpose (A : Matrix ι κ ℝ) : frobeniusSq Aᵀ = frobeniusSq A := by
  simp only [frobeniusSq, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- **Lemma 5.2, left multiplication.** -/
public theorem frobeniusSq_mul_le {G : Matrix ι κ ℝ} {c : ℝ} (hG : IsOpNormSqBound G c)
    (W : Matrix κ ν ℝ) : frobeniusSq (G * W) ≤ c * frobeniusSq W := by
  calc frobeniusSq (G * W) = ∑ j, ∑ i, (∑ l, G i l * W l j) ^ 2 := by
        simp only [frobeniusSq, Matrix.mul_apply]
        exact Finset.sum_comm
    _ ≤ ∑ j, c * ∑ l, W l j ^ 2 := Finset.sum_le_sum fun j _ => hG fun l => W l j
    _ = c * ∑ j, ∑ l, W l j ^ 2 := by rw [Finset.mul_sum]
    _ = c * frobeniusSq W := by rw [frobeniusSq]; exact congrArg _ Finset.sum_comm

/-- **Lemma 5.2, right multiplication.** -/
public theorem frobeniusSq_mul_le_right {G : Matrix κ ν ℝ} {c : ℝ} (hG : IsOpNormSqBound Gᵀ c)
    (W : Matrix ι κ ℝ) : frobeniusSq (W * G) ≤ c * frobeniusSq W := by
  have h := frobeniusSq_mul_le hG Wᵀ
  rwa [← Matrix.transpose_mul, frobeniusSq_transpose, frobeniusSq_transpose] at h

public theorem IsOpNormSqBound.nonneg {A : Matrix ι κ ℝ} {c : ℝ} (h : IsOpNormSqBound A c)
    (j : κ) : 0 ≤ c := by
  classical
  have hx := h (fun l => if l = j then (1 : ℝ) else 0)
  have hs : (∑ l, (if l = j then (1 : ℝ) else 0) ^ 2) = 1 := by
    simp
  rw [hs, mul_one] at hx
  refine le_trans ?_ hx
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

public theorem IsOpNormSqBound.mono {A : Matrix ι κ ℝ} {c d : ℝ} (h : IsOpNormSqBound A c)
    (hcd : c ≤ d) : IsOpNormSqBound A d := fun x =>
  (h x).trans (mul_le_mul_of_nonneg_right hcd
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

public theorem isOpNormSqBound_one [DecidableEq ι] : IsOpNormSqBound (1 : Matrix ι ι ℝ) 1 := by
  rw [isOpNormSqBound_iff_euclNorm]
  intro x
  simp [Matrix.one_mulVec]

public theorem IsOpNormSqBound.smul {A : Matrix ι κ ℝ} {c : ℝ} (h : IsOpNormSqBound A c)
    (r : ℝ) : IsOpNormSqBound (r • A) (r ^ 2 * c) := by
  rw [isOpNormSqBound_iff_euclNorm] at h ⊢
  intro x
  have hr : (r • A) *ᵥ x = r • (A *ᵥ x) := Matrix.smul_mulVec r A x
  rw [hr, euclNorm_smul, mul_pow, sq_abs]
  have := h x
  nlinarith [sq_nonneg r]

public theorem IsOpNormSqBound.mul {A : Matrix ι κ ℝ} {B : Matrix κ ν ℝ} {c d : ℝ}
    (hA : IsOpNormSqBound A c) (hB : IsOpNormSqBound B d) (hc : 0 ≤ c) :
    IsOpNormSqBound (A * B) (c * d) := by
  rw [isOpNormSqBound_iff_euclNorm] at hA hB ⊢
  intro x
  have h1 := hA (B *ᵥ x)
  have h2 := hB x
  rw [Matrix.mulVec_mulVec] at h1
  calc euclNorm ((A * B) *ᵥ x) ^ 2 ≤ c * euclNorm (B *ᵥ x) ^ 2 := h1
    _ ≤ c * (d * euclNorm x ^ 2) := by exact mul_le_mul_of_nonneg_left h2 hc
    _ = c * d * euclNorm x ^ 2 := by ring

end Algebra

/-! ## Frobenius dominates the operator norm

Step 7 works on print's `N₀ = {‖X‖₂ < ½, ‖P_{top} − I_b‖₂ < ½, ‖P_{bot}‖₂ < ½}`, an open condition
in the chart coordinates. Making that precise looks as though it needs the `ℓ²` operator norm
to be a *norm* — an instance this file deliberately avoids, because `Fin m → ℝ` carries the
supremum norm and picking up the wrong one silently changes the germ.

It does not. Print only needs an open set **inside** the region where its three bounds hold —
"take `O` to be the preimage under `Ψ` of a small open box inside `N₀`" — and the Frobenius
ball is such a set: `‖A‖²_F ≤ c` implies `IsOpNormSqBound A c` by Cauchy–Schwarz applied row by
row, and `{A : ‖A‖²_F < c}` is open because `frobeniusSq` is a polynomial in the entries.

So the operator-norm conditions can be met by a strictly smaller, manifestly open, condition,
and no norm instance on matrices is needed anywhere. -/

section Frobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Cauchy–Schwarz, row by row: the Frobenius square dominates the operator norm square.**
`‖Ax‖² = ∑_i (∑_j A_ij x_j)² ≤ ∑_i (∑_j A_ij²)(∑_j x_j²) = ‖A‖²_F ‖x‖²`. -/
public theorem isOpNormSqBound_frobeniusSq (A : Matrix ι κ ℝ) :
    IsOpNormSqBound A (frobeniusSq A) := by
  intro x
  have hrow : ∀ i : ι, (∑ j, A i j * x j) ^ 2 ≤ (∑ j, A i j ^ 2) * ∑ j, x j ^ 2 := fun i =>
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, (∑ j, A i j * x j) ^ 2 ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, x j ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = frobeniusSq A * ∑ j, x j ^ 2 := by
        rw [frobeniusSq, Finset.sum_mul]

/-- Any Frobenius bound is an operator-norm bound. This is the form Step 7 consumes: its three
hypotheses are `IsOpNormSqBound … (1/4)`, and each follows from `‖·‖²_F ≤ 1/4`. -/
public theorem isOpNormSqBound_of_frobeniusSq_le {A : Matrix ι κ ℝ} {c : ℝ}
    (h : frobeniusSq A ≤ c) : IsOpNormSqBound A c :=
  (isOpNormSqBound_frobeniusSq A).mono h

/-- `frobeniusSq` is continuous: a finite sum of squares of coordinate functions. -/
public theorem continuous_frobeniusSq :
    Continuous (fun A : Matrix ι κ ℝ => frobeniusSq A) := by
  unfold frobeniusSq
  fun_prop

/-- **The Frobenius ball is open**, which is what makes print's `N₀` replaceable by a
manifestly open condition. -/
public theorem isOpen_frobeniusSq_lt (c : ℝ) :
    IsOpen {A : Matrix ι κ ℝ | frobeniusSq A < c} :=
  isOpen_lt continuous_frobeniusSq continuous_const

/-- The two together, in the shape Step 7 wants: on the open set `‖A‖²_F < 1/4`, the
operator-norm hypothesis `IsOpNormSqBound A (1/4)` holds. -/
public theorem isOpNormSqBound_quarter_of_mem {A : Matrix ι κ ℝ}
    (h : A ∈ {A : Matrix ι κ ℝ | frobeniusSq A < 1 / 4}) : IsOpNormSqBound A (1 / 4) :=
  isOpNormSqBound_of_frobeniusSq_le (le_of_lt h)

end Frobenius


/-! ## Reindexing does not move the Frobenius square

`2K` is `‖BA − C‖²_F` with everything `Fin`-indexed, while Steps 6 and 7 compute over `Sum`
index types. Threading one into the other needs to know that relabelling the rows and columns
leaves the Frobenius square alone — which it does, since the square is the sum over *all*
entries and a relabelling permutes the summands.

This is the last identity the two sides need in common. It is stated for arbitrary index
equivalences rather than for the chart's, since nothing about them is used. -/

section Reindex

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- **Relabelling rows and columns leaves `‖·‖²_F` unchanged.** -/
public theorem frobeniusSq_submatrix_equiv (A : Matrix ι κ ℝ) (e : ι' ≃ ι) (f : κ' ≃ κ) :
    frobeniusSq (A.submatrix e f) = frobeniusSq A := by
  simp only [frobeniusSq, Matrix.submatrix_apply]
  calc ∑ i : ι', ∑ j : κ', A (e i) (f j) ^ 2
      = ∑ i : ι', ∑ j : κ, A (e i) j ^ 2 :=
        Finset.sum_congr rfl fun i _ => Fintype.sum_equiv f _ _ fun _ => rfl
    _ = ∑ i : ι, ∑ j : κ, A i j ^ 2 := Fintype.sum_equiv e _ _ fun _ => rfl

/-- Relabelling only the rows. -/
public theorem frobeniusSq_submatrix_row (A : Matrix ι κ ℝ) (e : ι' ≃ ι) :
    frobeniusSq (A.submatrix e id) = frobeniusSq A := by
  simpa using frobeniusSq_submatrix_equiv A e (Equiv.refl κ)

/-- Relabelling only the columns. -/
public theorem frobeniusSq_submatrix_col (A : Matrix ι κ ℝ) (f : κ' ≃ κ) :
    frobeniusSq (A.submatrix id f) = frobeniusSq A := by
  simpa using frobeniusSq_submatrix_equiv A (Equiv.refl ι) f

/-- The same for `Matrix.reindex`, the bundled form the transport uses. -/
public theorem frobeniusSq_reindex (A : Matrix ι κ ℝ) (e : ι ≃ ι') (f : κ ≃ κ') :
    frobeniusSq (Matrix.reindex e f A) = frobeniusSq A :=
  frobeniusSq_submatrix_equiv A e.symm f.symm

end Reindex


end AISafetyAtlas.SingularLearning
