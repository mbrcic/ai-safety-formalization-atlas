module

public import AISafetyAtlas.SingularLearning.LocalPair

/-!
# The Abelian read-off: injectivity of the Laplace-side scale

The MAIS issue #3 candidate's chain is **Abelian only**. It says so twice (pp. 30,
77): no Tauberian theorem is invoked anywhere in it. Instead it reads the local
pair `(λ, m)` directly off a two-sided bound on the Laplace transform, and the
step that licenses that reading is its Lemma 8.5:

> "the map `(λ, m) ↦ H_{λ,m}` is **injective up to two-sided constants**
> (Lemma 8.5), so a two-sided bound on `L_φ` of the form `≍ H_{λ′,m′}` already
> forces `(λ′, m′) = (λ, m)`."

Here `H_{λ,m}(T) = T^{-λ} (log T)^{m-1}` for large `T`. This module proves that
injectivity, so the "read the pair off the transform" step is a theorem rather
than an appeal.

## Why this replaces a Tauberian step

A Tauberian theorem converts an asymptotic for the transform back into an
asymptotic for the original density; the candidate deliberately avoids that
direction. What it needs instead is much weaker and purely Abelian: the *family*
of comparison scales is separated, so a bound against one member cannot also be a
bound against another. Nothing here inverts a transform, and nothing here is a
Tauberian statement. It is a separation statement about the comparison family.

## The `T → ∞` mirror of `volumeScale`

`laplaceScale` is not a new object. Under `ε = 1/T` it is exactly
`LocalPair.lean`'s `volumeScale`, with the sign of the exponent flipped by the
substitution:

`laplaceScale lam m T = volumeScale lam m (1 / T)` for `0 < T`.

That identity is proved below as `laplaceScale_eq_volumeScale`, and it is the
whole content of this file's method: every analytic fact is imported from
`LocalPair.lean` along `T ↦ 1/T`, which carries `Filter.atTop` to
`nhdsWithin 0 (Set.Ioi 0)`. The two mismatch lemmas
(`not_eventually_volumeScale_le` for the exponent,
`not_eventually_volumeScale_le_of_mult_lt` for the multiplicity) are used
verbatim; no asymptotic analysis is redone at `atTop`.

## The multiplicity hypothesis is not decoration

`m - 1` is `ℕ`-subtraction, so `laplaceScale lam 0` and `laplaceScale lam 1` are
the *same function*. Injectivity is therefore false as stated over all of `ℕ`,
and `1 ≤ m`, `1 ≤ m'` are hypotheses of every uniqueness statement here. This
matches `LocalPair.lean`, whose `HasLocalVolumeOrder` carries `1 ≤ m` in its main
branch for the same reason. The intended range of `m` is the multiplicity of a
pole, which is at least one.

## What is *not* assumed

Positivity of the exponent is not needed. The separation argument only compares
`lam` with `lam'`, so it goes through for arbitrary real exponents; requiring
`0 < lam` would be an unused hypothesis. The learning-coefficient application
supplies positivity anyway, so no consumer loses anything.
-/

namespace AISafetyAtlas.SingularLearning

open Filter Topology

/-- The Laplace-side asymptotic scale, `H_{λ,m}(T) = T^{-λ} (log T)^{m-1}`.

The exponent is `Real.rpow` and the logarithmic factor is `Monoid.npow`, matching
how `volumeScale` is spelled. As there, `m - 1` is `ℕ`-subtraction, so the
definition is constant in `m` across `m = 0` and `m = 1`; statements that read the
pair off this scale carry `1 ≤ m`. -/
@[expose] public noncomputable def laplaceScale (lam : ℝ) (m : ℕ) (T : ℝ) : ℝ :=
  T ^ (-lam) * Real.log T ^ (m - 1)

/-- **The mirror identity.** `laplaceScale` at `T` is `volumeScale` at `ε = 1/T`.

The substitution flips the sign of the exponent, `T ^ (-lam) = (1/T) ^ lam`, and
fixes the logarithm, `log (1 / (1 / T)) = log T`. Everything else in this file is
a transport of `LocalPair.lean` along this equation. -/
public theorem laplaceScale_eq_volumeScale (lam : ℝ) (m : ℕ) {T : ℝ} (hT : 0 < T) :
    laplaceScale lam m T = volumeScale lam m (1 / T) := by
  rw [laplaceScale, volumeScale, one_div_one_div, Real.rpow_neg hT.le,
    Real.div_rpow zero_le_one hT.le, Real.one_rpow, one_div]

/-- Transport of an eventual inequality between two `laplaceScale`s at `atTop` to
the corresponding inequality between `volumeScale`s at `0⁺`.

`T ↦ T⁻¹` carries `nhdsWithin 0 (Set.Ioi 0)` to `atTop`, so an inequality holding
for all large `T` holds at `T = ε⁻¹` for all small positive `ε`; the mirror
identity then rewrites it into `volumeScale` form. -/
public theorem eventually_volumeScale_le_of_laplace {lam lam' : ℝ} {m m' : ℕ} {a b : ℝ}
    (h : ∀ᶠ T in atTop, a * laplaceScale lam m T ≤ b * laplaceScale lam' m' T) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a * volumeScale lam m ε ≤ b * volumeScale lam' m' ε := by
  filter_upwards [tendsto_inv_nhdsGT_zero.eventually h, self_mem_nhdsWithin] with ε hε hεpos
  have hεpos : (0 : ℝ) < ε := hεpos
  have hinv : (0 : ℝ) < ε⁻¹ := inv_pos.2 hεpos
  rwa [laplaceScale_eq_volumeScale lam m hinv, laplaceScale_eq_volumeScale lam' m' hinv,
    one_div, inv_inv] at hε

/-- **The separation core.** Two cross inequalities between `H_{λ,m}` and
`H_{λ',m'}`, each with positive constants and each holding for all large `T`,
force `(λ, m) = (λ', m')`.

The proof is a trichotomy on `lam` and then on `m`, exactly as in
`volumeOrder_unique`: an exponent mismatch is refuted by
`not_eventually_volumeScale_le`, a multiplicity mismatch at equal exponents by
`not_eventually_volumeScale_le_of_mult_lt`. Only the transport is new. -/
public theorem laplaceScale_pair_unique {lam lam' : ℝ} {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (h : ∀ᶠ T in atTop, a * laplaceScale lam m T ≤ b * laplaceScale lam' m' T)
    (h' : ∀ᶠ T in atTop, a' * laplaceScale lam' m' T ≤ b' * laplaceScale lam m T) :
    lam = lam' ∧ m = m' := by
  have hv := eventually_volumeScale_le_of_laplace h
  have hv' := eventually_volumeScale_le_of_laplace h'
  have hlameq : lam = lam' := by
    rcases lt_trichotomy lam lam' with hlt | heq | hgt
    · exact absurd hv (not_eventually_volumeScale_le hlt ha hb)
    · exact heq
    · exact absurd hv' (not_eventually_volumeScale_le hgt ha' hb')
  subst hlameq
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd hv' (not_eventually_volumeScale_le_of_mult_lt hm hlt ha')
  · exact heq
  · exact absurd hv (not_eventually_volumeScale_le_of_mult_lt hm' hgt ha)

/-- **Lemma 8.5, the read-off.** Two-sided comparability of the scales forces the
pairs to agree: the map `(λ, m) ↦ H_{λ,m}` is injective up to two-sided
constants.

`1 ≤ m` and `1 ≤ m'` are necessary, not cosmetic: `m - 1` is `ℕ`-subtraction, so
`laplaceScale lam 0` and `laplaceScale lam 1` are literally the same function and
the conclusion `m = m'` would be false at `m = 0`, `m' = 1` with `c₁ = c₂ = 1`. -/
public theorem laplaceScale_injective {lam lam' : ℝ} {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h : ∀ᶠ T in atTop,
        c₁ * laplaceScale lam' m' T ≤ laplaceScale lam m T ∧
          laplaceScale lam m T ≤ c₂ * laplaceScale lam' m' T) :
    lam = lam' ∧ m = m' := by
  refine laplaceScale_pair_unique hm hm' one_pos hc₂ hc₁ one_pos ?_ ?_
  · filter_upwards [h] with T hT using by rw [one_mul]; exact hT.2
  · filter_upwards [h] with T hT using by rw [one_mul]; exact hT.1

/-- The read-off in the form the assembly uses: a function two-sided comparable
to `H_{λ,m}` and also to `H_{λ',m'}` forces the two pairs to agree.

This is the actual consumer. The candidate never has `H_{λ,m} ≍ H_{λ',m'}` in
hand directly; it has one Laplace transform `L` bounded on both sides by each of
two candidate scales, and concludes that the candidates coincide. Chaining the
two comparisons through `L` supplies the hypotheses of
`laplaceScale_pair_unique`. -/
public theorem pair_unique_of_laplace_comparable {L : ℝ → ℝ} {lam lam' : ℝ} {m m' : ℕ}
    (hm : 1 ≤ m) (hm' : 1 ≤ m') {a A a' A' : ℝ}
    (ha : 0 < a) (hA : 0 < A) (ha' : 0 < a') (hA' : 0 < A')
    (h : ∀ᶠ T in atTop, a * laplaceScale lam m T ≤ L T ∧ L T ≤ A * laplaceScale lam m T)
    (h' : ∀ᶠ T in atTop, a' * laplaceScale lam' m' T ≤ L T ∧ L T ≤ A' * laplaceScale lam' m' T) :
    lam = lam' ∧ m = m' := by
  refine laplaceScale_pair_unique hm hm' ha hA' ha' hA ?_ ?_
  · filter_upwards [h, h'] with T hT hT' using hT.1.trans hT'.2
  · filter_upwards [h, h'] with T hT hT' using hT'.1.trans hT.2

end AISafetyAtlas.SingularLearning
