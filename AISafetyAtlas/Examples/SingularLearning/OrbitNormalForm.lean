module

public import AISafetyAtlas.SingularLearning.OrbitNormalForm

/-!
# Worked models for the orbit classification

Lemma 3.2 of the MAIS issue #3 candidate, and the algebraic prerequisite of its
Theorem 5.1. `GL(M) × GL(H) × GL(N)` acts on parameter space by
`A ↦ G_H A G_N⁻¹`, `B ↦ G_M B G_H⁻¹`, and **the orbit is determined by
`(rank A, rank B, rank (B*A))`**.

## Why the atlas needs it

`prob:calibration` asks for the local pair at an *arbitrary* `w* ∈ W₀`, and the
answer is a table indexed by `(rank A, rank B)`. That table can only be complete
if every point of the fiber is carried to a canonical representative determined
by those ranks — and, per the candidate's own hygiene note (p. 9), carried "through
comparability plus diffeomorphism invariance, **never through an isometry**",
which is why a *linear* change of basis is the right notion here.

`sameOrbit_of_fiber` is the form the stratum tables consume: two factorizations
of the **same** truth matrix with the same rank pair lie in the same orbit.

## What this module is not

It contains no analysis. Theorem 5.1's neighborhood, its analytic
diffeomorphism, and its `[1/12, 6]` comparability bounds are not here.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **Lemma 3.2.** The orbit invariant is complete: the three ranks determine
the orbit, and conversely. -/
example {M N H : ℕ} (A₁ A₂ : Matrix (Fin H) (Fin N) ℝ) (B₁ B₂ : Matrix (Fin M) (Fin H) ℝ) :
    SameOrbit A₁ A₂ B₁ B₂ ↔
      A₁.rank = A₂.rank ∧ B₁.rank = B₂.rank ∧ (B₁ * A₁).rank = (B₂ * A₂).rank :=
  sameOrbit_iff_rank_eq

/-- The form the stratum tables use: same truth matrix, same rank pair, same
orbit. -/
example {M N H : ℕ} {C : Matrix (Fin M) (Fin N) ℝ}
    {A₁ A₂ : Matrix (Fin H) (Fin N) ℝ} {B₁ B₂ : Matrix (Fin M) (Fin H) ℝ}
    (h₁ : B₁ * A₁ = C) (h₂ : B₂ * A₂ = C)
    (ha : A₁.rank = A₂.rank) (hb : B₁.rank = B₂.rank) :
    SameOrbit A₁ A₂ B₁ B₂ :=
  sameOrbit_of_fiber h₁ h₂ ha hb

end AISafetyAtlas.Examples.SingularLearning
