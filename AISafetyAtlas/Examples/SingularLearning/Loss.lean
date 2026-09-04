module

public import AISafetyAtlas.SingularLearning.Loss

/-!
# Worked models for the reduced-rank loss

`MAIS-O70.md` defines the population loss as a **Gaussian expectation**,
`K(A,B) = ½ E_x ‖(BA − B₀A₀)x‖²` with `x ~ N(0, I_N)`. The Frobenius form
`½‖BA − C‖²_F` is a consequence. `AISafetyAtlas/SingularLearning/Loss.lean`
formalizes print's form and derives the convenient one, rather than defining the
convenient one and calling it print's.

## Why that discipline earned its keep here

The first draft of this definition wrote the integrand as
`‖(B * A - C).mulVec x‖ ^ 2`. `Matrix.mulVec` lands in `Fin M → ℝ`, and in
Mathlib **that type carries the supremum norm** — `Pi.norm_def` unfolds `‖f‖` to
`Finset.univ.sup fun i => ‖f i‖₊`. So the draft said

    K(A,B) = ½ E_x [ maxᵢ |⟨rowᵢ(BA − C), x⟩|² ]

which is a different function, and for which the Frobenius identity is **false**.
It elaborated perfectly; `#check` would have shown nothing wrong. What caught it
was trying to prove the consequence and finding the types would not support it.

The definition therefore routes through `Matrix.toEuclideanLin`, which lands in
`EuclideanSpace ℝ (Fin M)` where `‖·‖` is Euclidean.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The instance-free form of the derived identity. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = (1 / 2) * ∑ i, ∑ j, (B * A - C) i j ^ 2 :=
  rrrLoss_eq_sum_sq C A B

/-- The loss is nonnegative, one of `def:local`'s standing hypotheses on `K`. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    0 ≤ rrrLoss C A B :=
  rrrLoss_nonneg C A B

/-- **The zero fiber.** `W₀ = {(A,B) : BA = C}` is exactly the vanishing locus of
print's loss — which is what makes it the set `prob:calibration` quantifies `w*`
over, and what connects this module to the rank-feasibility bridge. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss C A B = 0 ↔ B * A = C :=
  rrrLoss_eq_zero_iff C A B

/-- A point of the zero fiber has loss `0`, so the fiber is not empty whenever
the truth is realizable — which print assumes. -/
example {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    rrrLoss (B * A) A B = 0 :=
  (rrrLoss_eq_zero_iff _ A B).mpr rfl

end AISafetyAtlas.Examples.SingularLearning
