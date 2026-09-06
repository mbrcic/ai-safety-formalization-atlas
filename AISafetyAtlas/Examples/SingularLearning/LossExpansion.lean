module

public import AISafetyAtlas.SingularLearning.LossExpansion

/-!
# Worked loss expansion

At the rank-zero rung both factors vanish, and the exact expansion collapses to

    `L' - L = ½⟨x,y⟩² - s⟨x,y⟩`,

a function of the single scalar `⟨x,y⟩`.  That is precisely the germ MAIS-O7
computes at its origin, so the general expansion reproduces the scalar case
rather than merely being consistent with it.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning Matrix

/-- The expansion at the rank-zero rung. -/
example {M N H : ℕ} (T : Matrix (Fin N) (Fin M) ℝ) (u : Fin N → ℝ) (v : Fin M → ℝ) (s : ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (hMv : ((0 : Matrix (Fin N) (Fin H) ℝ) * (0 : Matrix (Fin H) (Fin M) ℝ) - T) *ᵥ v
      = (-s) • u)
    (hMu : ((0 : Matrix (Fin N) (Fin H) ℝ) * (0 : Matrix (Fin H) (Fin M) ℝ) - T)ᵀ *ᵥ u
      = (-s) • v)
    (x y : Fin H → ℝ) :
    frobeniusSq (((0 : Matrix (Fin N) (Fin H) ℝ) + vecMulVec u y) *
        ((0 : Matrix (Fin H) (Fin M) ℝ) + vecMulVec x v) - T)
      = frobeniusSq ((0 : Matrix (Fin N) (Fin H) ℝ) * (0 : Matrix (Fin H) (Fin M) ℝ) - T)
        + ((y ⬝ᵥ x) ^ 2 - 2 * s * (y ⬝ᵥ x)) := by
  have h := frobeniusSq_rung_variation (0 : Matrix (Fin H) (Fin M) ℝ)
    (0 : Matrix (Fin N) (Fin H) ℝ) T u v s hu hv (by simp) (by simp) hMv hMu x y
  rw [h]
  simp only [Matrix.zero_mulVec, Matrix.transpose_zero, dotProduct_zero]
  ring

/-! ## The full-space expansion

The slice expansion above varies `A` and `B` by rank-one matrices.  The
full-space one varies both arbitrarily, so it must reproduce ordinary
first-order perturbation theory when only one factor moves.  Fixing `Y = 0`
should leave exactly the square of `B X`, and it does.
-/

/-- Varying only `A` leaves the expansion around `BX`. -/
example {N M H : ℕ} (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ) (X : Matrix (Fin H) (Fin M) ℝ) :
    frobeniusSq (B * (A + X) - T)
      = frobeniusSq (B * A - T) + 2 * froIP (B * A - T) (B * X) + frobeniusSq (B * X) := by
  have h := frobeniusSq_full_variation A B T X (0 : Matrix (Fin N) (Fin H) ℝ)
  simpa using h

/-- At a critical point the first-order term is gone, and varying only `A` leaves
a pure square: the loss increases in every direction of `A` alone. -/
example {N M H : ℕ} (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ) (hB : Bᵀ * (B * A - T) = 0) (hA : (B * A - T) * Aᵀ = 0)
    (X : Matrix (Fin H) (Fin M) ℝ) :
    frobeniusSq (B * (A + X) - T) = frobeniusSq (B * A - T) + frobeniusSq (B * X) := by
  have h := frobeniusSq_full_variation_of_critical A B T hB hA X (0 : Matrix (Fin N) (Fin H) ℝ)
  simpa [froIP] using h

/-- **The free set is not empty at the rank-zero rung.**  With `B = 0` every
variation of `A` leaves the product, and so the loss, exactly where it was.  This
is the extreme case of the fibre directions, and it is the one the worked O77
rung sits at, so the degeneracy the splitting has to handle is present already in
the smallest example rather than being an artefact of large `H`. -/
example {N M H : ℕ} (A : Matrix (Fin H) (Fin M) ℝ) (T : Matrix (Fin N) (Fin M) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) :
    frobeniusSq ((0 : Matrix (Fin N) (Fin H) ℝ) * (A + X) - T)
      = frobeniusSq ((0 : Matrix (Fin N) (Fin H) ℝ) * A - T) :=
  frobeniusSq_variation_eq_of_mul_left_eq_zero A 0 T (by simp)

/-- The sublevel reading: the loss at a varied point is a squared distance from a
matrix that does not depend on the variation. -/
example {N M H : ℕ} (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (T : Matrix (Fin N) (Fin M) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) :
    frobeniusSq ((B + Y) * (A + X) - T)
      = frobeniusSq ((B * X + Y * A + Y * X) - (-(B * A - T))) :=
  frobeniusSq_variation_eq_dist_sq A B T X Y

end AISafetyAtlas.Examples.SingularLearning
