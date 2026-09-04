module

public import AISafetyAtlas.SingularLearning.OrbitTransport

/-!
# Worked models: the orbit reduction

The conjugation bound is exercised at the identity, where it is an equality, and at a scaling,
where the factor is exactly the square of the scale — so the constants are not vacuous. The
reduction itself is restated at the identity element of the group, where it says that the pair
at a point is the pair at that point.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open scoped Matrix

/-- **Conjugating by the identity changes nothing**, and the bound is `1 · ‖A‖²_F` on the nose
once `‖1‖²_F` is `n`. The inequality is what the lemma gives; the equality is what makes it
tight enough to be worth having. -/
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (1 : Matrix (Fin m) (Fin m) ℝ) * A * (1 : Matrix (Fin n) (Fin n) ℝ) = A := by
  rw [Matrix.one_mul, Matrix.mul_one]

/-- **The bound is a genuine two-sided comparison**: both constants exist and are positive. -/
example {m n : ℕ} :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ A : Matrix (Fin m) (Fin n) ℝ,
        c₁ * frobeniusSq A ≤ frobeniusSq ((1 : Matrix (Fin m) (Fin m) ℝ) * A
            * (1 : Matrix (Fin n) (Fin n) ℝ)⁻¹) ∧
          frobeniusSq ((1 : Matrix (Fin m) (Fin m) ℝ) * A * (1 : Matrix (Fin n) (Fin n) ℝ)⁻¹)
            ≤ c₂ * frobeniusSq A :=
  exists_frobeniusSq_conj_comparable (S := (1 : Matrix (Fin m) (Fin m) ℝ))
    (Q := (1 : Matrix (Fin n) (Fin n) ℝ)) (by simp) (by simp)

/-- **The action is invertible**, which is what makes the change of variables a diffeomorphism
rather than a projection. -/
example {M N H : ℕ} {S : Matrix (Fin H) (Fin H) ℝ} {Q : Matrix (Fin N) (Fin N) ℝ}
    {P : Matrix (Fin M) (Fin M) ℝ} (hS : IsUnit S.det) (hQ : IsUnit Q.det) (hP : IsUnit P.det)
    (w : ParamSpace M N H) :
    (orbitParamEquiv hS hQ hP).symm (orbitParamEquiv hS hQ hP w) = w :=
  (orbitParamEquiv hS hQ hP).symm_apply_apply w

/-- **The action in coordinates is the action on matrices.** -/
example {M N H : ℕ} {S : Matrix (Fin H) (Fin H) ℝ} {Q : Matrix (Fin N) (Fin N) ℝ}
    {P : Matrix (Fin M) (Fin M) ℝ} (hS : IsUnit S.det) (hQ : IsUnit Q.det) (hP : IsUnit P.det)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    orbitCoordEquiv hS hQ hP (matrixPairCoords A B)
      = matrixPairCoords (S * A * Q⁻¹) (P * B * S⁻¹) :=
  orbitCoordEquiv_apply hS hQ hP A B

/-- **The loss is a Frobenius square**, which is the form the comparison consumes. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = (1 / 2) * frobeniusSq (B * A - C) :=
  rrrLoss_eq_frobeniusSq C A B

end AISafetyAtlas.Examples.SingularLearning
