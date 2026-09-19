module

public import AISafetyAtlas.SingularLearning.MatrixNormBridge

/-!
# The exact loss expansion along a discarded mode

MAIS-O77(b) §7.2 asks for the polynomial loss to be expanded exactly along the
variation that isolates a discarded singular mode,

    `dA = x vᵀ`,   `dB = u yᵀ`,

at a point of a nonterminal rung.  This module does that, and the outcome is
better than the printed argument needs: under the rung conditions the expansion
**terminates**.

    `L(A + dA, B + dB) - L(A,B) = ½[xᵀBᵀBx + yᵀAAᵀy - 2 s ⟨x,y⟩] + ½⟨x,y⟩²`

There is no remainder and no asymptotic statement.  Every cross term that could
have contributed vanishes for a stated reason: `Bᵀu = 0` and `Av = 0` are the
printed annihilation clauses of the rung, and `u`, `v` are unit vectors.  What
survives is the quadratic form of the saddle Hessian block — the object
`HessianBlock` studies — plus a single quartic term `½⟨x,y⟩²`.

That exactness is worth stating plainly because it is what makes the remaining
Morse obligation smaller than it looks: the function to be normalised is not a
general analytic germ but an explicit quartic polynomial in `2H` variables.

Nothing here computes a volume order, and nothing here proves
`O77AllSaddlesHavePairOne`.
-/

namespace AISafetyAtlas.SingularLearning

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Frobenius inner product.  `frobeniusSq` is its diagonal. -/
@[expose] public noncomputable def froIP (X Y : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

public theorem froIP_comm (X Y : Matrix ι κ ℝ) : froIP X Y = froIP Y X := by
  simp only [froIP]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

public theorem froIP_add_right (X Y Z : Matrix ι κ ℝ) :
    froIP X (Y + Z) = froIP X Y + froIP X Z := by
  simp only [froIP, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

public theorem froIP_add_left (X Y Z : Matrix ι κ ℝ) :
    froIP (X + Y) Z = froIP X Z + froIP Y Z := by
  rw [froIP_comm, froIP_add_right, froIP_comm, froIP_comm Z Y]

/-- The Frobenius norm squared is the pairing of a matrix with itself. -/
public theorem froIP_self (X : Matrix ι κ ℝ) : froIP X X = frobeniusSq X := by
  simp only [froIP, frobeniusSq]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (sq _).symm

/-- Expanding a square in the Frobenius norm. -/
public theorem frobeniusSq_add (X Y : Matrix ι κ ℝ) :
    frobeniusSq (X + Y) = frobeniusSq X + 2 * froIP X Y + frobeniusSq Y := by
  simp only [frobeniusSq, froIP, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The inner product against a rank-one matrix reads off a bilinear form. -/
public theorem froIP_vecMulVec (M : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    froIP M (vecMulVec a b) = a ⬝ᵥ (M *ᵥ b) := by
  simp only [froIP, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Two rank-one matrices pair as the product of the two vector pairings. -/
public theorem froIP_vecMulVec_vecMulVec (a c : ι → ℝ) (b d : κ → ℝ) :
    froIP (vecMulVec a b) (vecMulVec c d) = (a ⬝ᵥ c) * (b ⬝ᵥ d) := by
  simp only [froIP, Matrix.vecMulVec_apply, dotProduct]
  conv_rhs => rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

public theorem frobeniusSq_vecMulVec (a : ι → ℝ) (b : κ → ℝ) :
    frobeniusSq (vecMulVec a b) = (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  simp only [frobeniusSq, Matrix.vecMulVec_apply, dotProduct, mul_pow]
  rw [← Finset.sum_mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => sq _

/-! ## The three matrix products the variation produces -/

public theorem mul_vecMulVec {N H M : ℕ} (B : Matrix (Fin N) (Fin H) ℝ)
    (x : Fin H → ℝ) (v : Fin M → ℝ) :
    B * vecMulVec x v = vecMulVec (B *ᵥ x) v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm

public theorem vecMulVec_mul {N H M : ℕ} (u : Fin N → ℝ) (y : Fin H → ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) :
    vecMulVec u y * A = vecMulVec u (Aᵀ *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

public theorem vecMulVec_mul_vecMulVec {N H M : ℕ} (u : Fin N → ℝ) (y x : Fin H → ℝ)
    (v : Fin M → ℝ) :
    vecMulVec u y * vecMulVec x v = vecMulVec ((y ⬝ᵥ x) • u) v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Moving a matrix across the pairing. -/
public theorem dotProduct_mulVec_transpose {N H : ℕ} (B : Matrix (Fin N) (Fin H) ℝ)
    (u : Fin N → ℝ) (x : Fin H → ℝ) :
    (B *ᵥ x) ⬝ᵥ u = (Bᵀ *ᵥ u) ⬝ᵥ x := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ## The expansion

Under the rung conditions the expansion terminates: the linear term vanishes
because the printed annihilation clauses kill it, and the only surviving
higher-order contribution is a single quartic.
-/

/-- **The exact loss expansion along a discarded mode.**  With `u` and `v` unit
vectors annihilated by `Bᵀ` and `A`, and the residual acting on them by `-s`,
the squared residual after the variation `dA = x vᵀ`, `dB = u yᵀ` is the original
plus the saddle Hessian's quadratic form plus one quartic term — exactly, with no
remainder.

Halving gives the loss form: `L' - L = ½[xᵀBᵀBx + yᵀAAᵀy - 2s⟨x,y⟩] + ½⟨x,y⟩²`.

Every cross term that could have appeared vanishes for a stated reason, and the
statement records which hypothesis kills which: `hBu` and `hAv` are the printed
rung clauses, `hu` and `hv` the normalisation, `hMv` and `hMu` the action of the
residual on the discarded mode. -/
public theorem frobeniusSq_rung_variation {M N H : ℕ}
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ)
    (u : Fin N → ℝ) (v : Fin M → ℝ) (s : ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (hAv : A *ᵥ v = 0) (hBu : Bᵀ *ᵥ u = 0)
    (hMv : (B * A - T) *ᵥ v = (-s) • u)
    (hMu : (B * A - T)ᵀ *ᵥ u = (-s) • v)
    (x y : Fin H → ℝ) :
    frobeniusSq ((B + vecMulVec u y) * (A + vecMulVec x v) - T)
      = frobeniusSq (B * A - T)
        + ((B *ᵥ x) ⬝ᵥ (B *ᵥ x) + (Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ y)
            - 2 * s * (y ⬝ᵥ x) + (y ⬝ᵥ x) ^ 2) := by
  set t : ℝ := y ⬝ᵥ x with ht
  set M₀ : Matrix (Fin N) (Fin M) ℝ := B * A - T with hM₀
  set P₁ : Matrix (Fin N) (Fin M) ℝ := vecMulVec (B *ᵥ x) v with hP₁
  set P₂ : Matrix (Fin N) (Fin M) ℝ := vecMulVec u (Aᵀ *ᵥ y) with hP₂
  set P₃ : Matrix (Fin N) (Fin M) ℝ := vecMulVec (t • u) v with hP₃
  -- the two vanishing pairings supplied by the rung clauses
  have hBxu : (B *ᵥ x) ⬝ᵥ u = 0 := by rw [dotProduct_mulVec_transpose, hBu, zero_dotProduct]
  have hAyv : (Aᵀ *ᵥ y) ⬝ᵥ v = 0 := by
    rw [dotProduct_mulVec_transpose, Matrix.transpose_transpose, hAv, zero_dotProduct]
  have hvAy : v ⬝ᵥ (Aᵀ *ᵥ y) = 0 := by rw [dotProduct_comm]; exact hAyv
  -- the product expands into the residual plus three rank-one pieces
  have hprod : (B + vecMulVec u y) * (A + vecMulVec x v) - T = M₀ + (P₁ + (P₂ + P₃)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, mul_vecMulVec, vecMulVec_mul,
      vecMulVec_mul_vecMulVec, hM₀, hP₁, hP₂, hP₃, ht]
    abel
  rw [hprod, frobeniusSq_add, froIP_add_right, froIP_add_right, frobeniusSq_add,
    frobeniusSq_add, froIP_add_right]
  -- the linear term
  have hL1 : froIP M₀ P₁ = 0 := by
    rw [hP₁, froIP_vecMulVec, hMv, dotProduct_smul, smul_eq_mul, hBxu, mul_zero]
  have hL2 : froIP M₀ P₂ = 0 := by
    rw [hP₂, froIP_vecMulVec, dotProduct_comm, dotProduct_mulVec_transpose, hMu,
      smul_dotProduct, smul_eq_mul, hvAy, mul_zero]
  have hL3 : froIP M₀ P₃ = -s * t := by
    rw [hP₃, froIP_vecMulVec, hMv, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hu]
    ring
  -- the three quadratic cross terms
  have hC12 : froIP P₁ P₂ = 0 := by
    rw [hP₁, hP₂, froIP_vecMulVec_vecMulVec, hBxu, zero_mul]
  have hC13 : froIP P₁ P₃ = 0 := by
    rw [hP₁, hP₃, froIP_vecMulVec_vecMulVec, dotProduct_smul, smul_eq_mul, hBxu,
      mul_zero, zero_mul]
  have hC23 : froIP P₂ P₃ = 0 := by
    rw [hP₂, hP₃, froIP_vecMulVec_vecMulVec, hAyv, mul_zero]
  -- the three diagonal terms
  have hD1 : frobeniusSq P₁ = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    rw [hP₁, frobeniusSq_vecMulVec, hv, mul_one]
  have hD2 : frobeniusSq P₂ = (Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ y) := by
    rw [hP₂, frobeniusSq_vecMulVec, hu, one_mul]
  have hD3 : frobeniusSq P₃ = t ^ 2 := by
    rw [hP₃, frobeniusSq_vecMulVec, hv, mul_one, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, hu]
    ring
  rw [hL1, hL2, hL3, hC12, hC13, hC23, hD1, hD2, hD3]
  ring

/-! ## The expansion over the whole parameter space

`frobeniusSq_rung_variation` above expands the loss along the rank-one variation
MAIS-A7's §7.1 selects, and terminates.  That is a statement about a
`2H`-dimensional slice of the parameter space.  §7.4's splitting is over all of
it, so the expansion has to be available there too, and this section supplies it.

The algebra is easier than the slice case, because nothing is chosen: the product
of the varied factors differs from the unvaried one by `BX + YA + YX`, and the
loss is a square, so the expansion is `frobeniusSq_add` and nothing else.  What
the rung conditions buy is the vanishing of the *first-order* term, which is
criticality and is stated here as the two matrix equations it amounts to rather
than assumed.
-/

/-- The Frobenius pairing as a trace.  Everything below moves matrices across the
pairing, and the trace form is where associativity and `Matrix.trace_mul_comm` do
that work in one step. -/
public theorem froIP_eq_trace (X Y : Matrix ι κ ℝ) : froIP X Y = (Xᵀ * Y).trace := by
  simp only [froIP, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- The pairing is homogeneous in its right argument. -/
public theorem froIP_smul_right (a : ℝ) (X Y : Matrix ι κ ℝ) :
    froIP X (a • Y) = a * froIP X Y := by
  simp only [froIP, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A matrix pairing to zero against everything is zero.  The only witness the
proof needs is the matrix itself. -/
public theorem eq_zero_of_forall_froIP_eq_zero (X : Matrix ι κ ℝ)
    (h : ∀ Z, froIP X Z = 0) : X = 0 :=
  (frobeniusSq_eq_zero_iff X).1 (froIP_self X ▸ h X)

/-- Moving a left factor across the pairing. -/
public theorem froIP_mul_left {N M H : ℕ} (R : Matrix (Fin N) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (X : Matrix (Fin H) (Fin M) ℝ) :
    froIP R (B * X) = froIP (Bᵀ * R) X := by
  rw [froIP_eq_trace, froIP_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc]

/-- Moving a right factor across the pairing. -/
public theorem froIP_mul_right {N M H : ℕ} (R : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    froIP R (Y * A) = froIP Y (R * Aᵀ) := by
  rw [froIP_eq_trace, froIP_eq_trace, ← Matrix.trace_transpose (Yᵀ * (R * Aᵀ)),
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ Y A,
    Matrix.trace_mul_comm]

/-- The varied product differs from the unvaried one by exactly `BX + YA + YX`.
No hypothesis is used; this is the distributive law. -/
public theorem varied_product_eq {N M H : ℕ} (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (T : Matrix (Fin N) (Fin M) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    (B + Y) * (A + X) - T = (B * A - T) + (B * X + Y * A + Y * X) := by
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

/-- **The exact loss expansion over the whole parameter space.**  Both factors
vary arbitrarily, and the identity is exact: the loss is a square and the varied
product differs from the unvaried one by a single matrix, so `frobeniusSq_add`
is the entire content.

The point of stating it is that the slice expansion `frobeniusSq_rung_variation`
does *not* imply it, and the remaining directions have to be visible before the
splitting of §7.4 can be argued about at all. -/
public theorem frobeniusSq_full_variation {N M H : ℕ} (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (T : Matrix (Fin N) (Fin M) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    frobeniusSq ((B + Y) * (A + X) - T)
      = frobeniusSq (B * A - T)
        + 2 * froIP (B * A - T) (B * X + Y * A + Y * X)
        + frobeniusSq (B * X + Y * A + Y * X) := by
  rw [varied_product_eq, frobeniusSq_add]

/-- **Criticality kills the first-order term.**  The two hypotheses are the
matrix form of "the residual is orthogonal to every first-order motion of the
product": `Bᵀ R = 0` says so for motions of `A`, and `R Aᵀ = 0` for motions of
`B`.  They are equations about the point, not about the variation, so the
conclusion holds for every `X` and `Y` at once. -/
public theorem froIP_residual_first_order {N M H : ℕ} (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (T : Matrix (Fin N) (Fin M) ℝ)
    (hB : Bᵀ * (B * A - T) = 0) (hA : (B * A - T) * Aᵀ = 0)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    froIP (B * A - T) (B * X + Y * A) = 0 := by
  rw [froIP_add_right, froIP_mul_left, froIP_mul_right, hB, hA]
  simp [froIP]

/-- **The exact expansion at a critical point, over the whole parameter space.**
What is left after the first-order term vanishes is a quadratic form
`‖BX + YA‖²`, a cubic `2⟨BX + YA, YX⟩`, a quartic `‖YX‖²`, and the one remaining
first-order-in-`R` term `2⟨R, YX⟩` — which is second order in the variation and
is exactly where the discarded modes enter the Hessian.

This is the full-space counterpart of `frobeniusSq_rung_variation`, and it
terminates for the same reason: the loss is a polynomial. -/
public theorem frobeniusSq_full_variation_of_critical {N M H : ℕ}
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ)
    (hB : Bᵀ * (B * A - T) = 0) (hA : (B * A - T) * Aᵀ = 0)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    frobeniusSq ((B + Y) * (A + X) - T)
      = frobeniusSq (B * A - T)
        + (2 * froIP (B * A - T) (Y * X) + frobeniusSq (B * X + Y * A + Y * X)) := by
  rw [frobeniusSq_full_variation, froIP_add_right (B * A - T) (B * X + Y * A) (Y * X),
    froIP_residual_first_order A B T hB hA X Y]
  ring

/-! ## The fibre directions, and why they are not the whole degeneracy

The loss depends on the pair `(A, B)` only through the product `B * A`, so it is
*constant* along any variation that leaves the product fixed.  Those directions
are free in the sense of print's Lemma 6.4(ii), and they need no splitting
argument at all: nothing has to be normalised away, because nothing happens
along them.

Recording this is what makes the remaining gap precise rather than vague.  The
degenerate directions of the Hessian are **not** the same set.  Along a
direction where the quadratic part `‖BX + YA‖² + 2⟨R, YX⟩` vanishes, the quartic
`‖YX‖²` generally does not, so the germ on the degenerate complement is a
genuine higher-order germ and not zero.  The splitting §7.4 asks for is needed
exactly for the difference between these two sets — which is why "the loss
factors through the product" simplifies the problem without closing it.
-/

/-- **The loss is constant along any variation that fixes the product.**  This is
the free-direction statement, and it holds with no hypothesis on the point: it is
the observation that `frobeniusSq (· - T)` sees only `B * A`. -/
public theorem frobeniusSq_variation_eq_of_product_fixed {N M H : ℕ}
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ) {X : Matrix (Fin H) (Fin M) ℝ}
    {Y : Matrix (Fin N) (Fin H) ℝ} (h : B * X + Y * A + Y * X = 0) :
    frobeniusSq ((B + Y) * (A + X) - T) = frobeniusSq (B * A - T) := by
  rw [varied_product_eq, h, add_zero]

/-- A concrete family of free directions: moving `A` inside the kernel of `B`
leaves the product, and hence the loss, untouched.  Together with its mirror this
shows the free set is not empty whenever `B` or `A` is rank deficient — which at
a rung point they both are. -/
public theorem frobeniusSq_variation_eq_of_mul_left_eq_zero {N M H : ℕ}
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ) {X : Matrix (Fin H) (Fin M) ℝ} (h : B * X = 0) :
    frobeniusSq (B * (A + X) - T) = frobeniusSq (B * A - T) := by
  have := frobeniusSq_variation_eq_of_product_fixed A B T (X := X)
    (Y := (0 : Matrix (Fin N) (Fin H) ℝ)) (by simp [h])
  simpa using this

/-- The mirror: moving `B` by something that annihilates `A`. -/
public theorem frobeniusSq_variation_eq_of_mul_right_eq_zero {N M H : ℕ}
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ) {Y : Matrix (Fin N) (Fin H) ℝ} (h : Y * A = 0) :
    frobeniusSq ((B + Y) * A - T) = frobeniusSq (B * A - T) := by
  have := frobeniusSq_variation_eq_of_product_fixed A B T
    (X := (0 : Matrix (Fin H) (Fin M) ℝ)) (Y := Y) (by simp [h])
  simpa using this

/-- **The sublevel sets are preimages of balls.**  The loss at a varied point is
the squared distance from the *fixed* matrix `-(B * A - T)` to the change in the
product, so `{L ≤ c}` pulls back a closed ball under the quadratic map
`(X, Y) ↦ B X + Y A + Y X`, with the base point on that ball's boundary.

This is the same identity as `varied_product_eq`, read as a statement about
level sets rather than about an expansion, and it is the shape any volume
argument for O77(b) has to work with. -/
public theorem frobeniusSq_variation_eq_dist_sq {N M H : ℕ}
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) :
    frobeniusSq ((B + Y) * (A + X) - T)
      = frobeniusSq ((B * X + Y * A + Y * X) - (-(B * A - T))) := by
  rw [varied_product_eq, sub_neg_eq_add, add_comm]

end AISafetyAtlas.SingularLearning
