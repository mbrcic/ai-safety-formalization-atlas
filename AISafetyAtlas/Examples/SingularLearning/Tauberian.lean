module

public import AISafetyAtlas.SingularLearning.Tauberian

/-!
# Worked models for the volume–Laplace transfer

Singular learning theory moves between a **sublevel volume** `V(ε) = vol{K ≤ ε}`,
which is what `def:local` speaks about, and a **Laplace transform**, which is
what is actually computable. `AISafetyAtlas/SingularLearning/Tauberian.lean`
proves the two-sided transfer between them by elementary means — monotonicity
plus a split — with no complex analysis and no regular-variation theory.

## Two honest limitations, both recorded rather than assumed away

**It sees exponents, not multiplicities.** A `(log 1/ε)^{m-1}` factor is
invisible to a pure power comparison. So this transfer settles `λ` and says
nothing about `m`.

**It is not on the critical path for MAIS-O70.** The issue #3 candidate states
twice that no Tauberian theorem is used anywhere in its chain; its transfer is
Abelian only, with the pair read off by injectivity of `(λ,m) ↦ H_{λ,m}`. This
module is a reusable tool, not an obligation of that result.

## What the proofs actually needed

Weaker hypotheses than expected, and the statements say so rather than carrying
decoration: the real boundary of the method is `-1 < lam`, which is convergence
of `e^{-u}u^lam` at the origin, not `0 < lam`; and `0 ≤ C` is unnecessary, since
`V ≥ 0` forces it. At `lam = 0` the inequalities stay true but become
contentless.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The Laplace average dominates the volume at the reciprocal scale. -/
example {V : ℝ → ℝ} (hV : Monotone V) (hpos : ∀ s > 0, 0 ≤ V s)
    {T : ℝ} (hT : 0 < T) (hint : MeasureTheory.IntegrableOn
      (fun s => Real.exp (-T * s) * V s) (Set.Ioi 0)) :
    Real.exp (-1) * V (1 / T) ≤ laplaceAverage V T :=
  volume_le_laplace hV hpos hint hT

end AISafetyAtlas.Examples.SingularLearning
