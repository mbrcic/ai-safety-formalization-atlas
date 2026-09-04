module

public import AISafetyAtlas.SingularLearning.LaplaceScale

/-!
# Worked models for the Abelian read-off

The MAIS issue #3 candidate reads the local pair off a Laplace transform rather
than inverting one. Its Lemma 8.5 is what makes that legitimate:

> "the map `(λ, m) ↦ H_{λ,m}` is **injective up to two-sided constants**, so a
> two-sided bound on `L_φ` of the form `≍ H_{λ′,m′}` already forces
> `(λ′, m′) = (λ, m)`."

`AISafetyAtlas/SingularLearning/LaplaceScale.lean` proves that injectivity. It is
the mechanism that replaces the Tauberian step the candidate deliberately avoids
— the paper states twice that no Tauberian theorem is used anywhere in its chain.

`H_{λ,m}(T) = T^{-λ}(log T)^{m-1}` is the `T → ∞` mirror of `LocalPair.lean`'s
`volumeScale`, and the proof transports along `ε = 1/T` rather than redoing the
analysis at `atTop`.

## Why `1 ≤ m` is not decoration

`m - 1` is `ℕ` subtraction, so `laplaceScale lam 0` and `laplaceScale lam 1` are
**the same function** — see the first `example` below, which closes by `rfl`.
Without `1 ≤ m` the injectivity statement is therefore false, witnessed by
`m = 0`, `m' = 1`, `c₁ = c₂ = 1`. The first draft of the statement omitted it.
`HasLocalVolumeOrder` carries `1 ≤ m` in its main branch for exactly this reason.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The `ℕ`-subtraction trap, made explicit: multiplicities `0` and `1` are
indistinguishable to the scale, which is why every statement about it needs
`1 ≤ m`. -/
example (lam T : ℝ) : laplaceScale lam 0 T = laplaceScale lam 1 T := rfl

/-- The Laplace scale is the `T → ∞` mirror of the volume scale. -/
example (lam : ℝ) (m : ℕ) {T : ℝ} (hT : 0 < T) :
    laplaceScale lam m T = volumeScale lam m (1 / T) :=
  laplaceScale_eq_volumeScale lam m hT

end AISafetyAtlas.Examples.SingularLearning
