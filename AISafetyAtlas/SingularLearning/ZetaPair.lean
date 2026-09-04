module

public import AISafetyAtlas.SingularLearning.LocalPair
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The zeta normalization, and the substitution the atlas makes

`MAIS-A6.tex` `def:local` defines the local pair **primarily** by the zeta
function — `λ(w*)` and `m(w*)` are "the threshold and pole order, in the sense of
Theorem `thm:zeta`, of `ζ_{w*}(z) = ∫_{B_ε(w*)} K(w)^z dw`" — and only afterwards
adds "Equivalently, `λ(w*)` is **the exponent** in `eq:volume`", citing
`[lau2023]`.

`LocalPair.lean` takes that second, volume, form as primary. Everything the atlas
proves about MAIS-O70 is proved about `HasExactLocalPair`, which is the volume
form. **That substitution is licensed by print's own "Equivalently" and is not
proved anywhere in the atlas**, and this module exists so that it is a Lean
constant a consumer can see rather than a sentence in a design note.

The candidate solution does not hide the same gap. Its Definition 2.1 also takes
the volume form as primitive, and its Lemma 6.1 proves the bridge — but clause
(ii) establishes meromorphic continuation only for `C^∞` compactly supported
weights. For a **sharp ball**, which is print's literal domain, it proves only the
two-sided real-axis bound recorded here as `HasZetaRealAxisOrder`, and concludes
about the pole order only "whenever this function does continue meromorphically".

So there are three things, and only the middle one is available for a sharp ball:

| | |
|---|---|
| `HasExactLocalPair` | the volume form; what the atlas proves |
| `HasZetaRealAxisOrder` | the real-axis two-sided bound; what the candidate proves for a sharp ball |
| `HasZetaPoleOrder` | print's primary definition; **neither the candidate nor the atlas proves this for a sharp ball** |

The hypothesis that closes the gap is `O70ZetaPoleBridge`, stated in
`Conjectures/MAIS/O70.lean` because it is stated at the germs it is used on — see
"Why there is no general bridge here" below, which is a finding rather than a
convenience. Nothing in this module proves anything about that hypothesis, and
nothing here is evidence that it holds.

## Two things the encoding decides, said out loud

**The degenerate branch has to be excluded.** `HasExactLocalPair` carries a
neutral branch: a germ vanishing on a whole neighbourhood is given the pair
`(0, 1)`. On that branch any bridge is *false*, not merely unproved — the zeta
integral of the zero germ is identically zero, so its meromorphic order is `⊤`
and not `-1`. Print excludes the same case: `rem:conventions` excludes `K`
identically zero. The O70 germs are nondegenerate at every positive shape,
unconditionally, by `not_eventually_rrrLossCoords_eq_zero_of_pos`, so the
exclusion costs nothing there.

**"Threshold and pole order" is rendered as: analytic to the right of `-λ`, and
meromorphic at `-λ` with order `-m`.** `meromorphicOrderAt` is Mathlib's order in
`WithTop ℤ`, negative at a pole, so a pole of order `m` is order `-m`. The
analyticity clause is what "threshold" asserts: `-λ` is where the continuation
first fails to be analytic, not merely some pole somewhere.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory

variable {n : ℕ}

/-- Print's zeta function `ζ_{w*}(z) = ∫_{B_ε(w*)} K(w)^z dw`, on the real axis.

Only the real axis is defined here. The continuation to `ℂ` is exactly what is
not available for a sharp ball, so making it part of the definition would assume
the thing in question; `HasZetaPoleOrder` asks for a continuation as an
existential instead. -/
@[expose] public noncomputable def zetaIntegral (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (δ x : ℝ) : ℝ :=
  ∫ y in Metric.ball w δ, K y ^ x

/-- **What the candidate proves for a sharp ball.** The two-sided real-axis bound
of Lemma 6.1(ii): near `-λ` from the right, the zeta integral is trapped between
two positive multiples of `(x + λ)^{-m}`.

This is the real-axis shadow of a pole of order `m` at `-λ`. It is not the same
statement: a function can satisfy it and admit no meromorphic continuation at
all, which is precisely why `HasZetaPoleOrder` is a separate definition and the
passage between them is a hypothesis. Nothing in the atlas proves this one
either; it is recorded so the shape of the gap is visible. -/
@[expose] public def HasZetaRealAxisOrder (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (m : ℕ) : Prop :=
  ∃ δ > 0, ∃ x₀ : ℝ, -lam < x₀ ∧ ∃ cLower cUpper : ℝ, 0 < cLower ∧ cLower ≤ cUpper ∧
    ∀ x : ℝ, -lam < x → x < x₀ →
      cLower * (x + lam) ^ (-(m : ℝ)) ≤ zetaIntegral K w δ x ∧
        zetaIntegral K w δ x ≤ cUpper * (x + lam) ^ (-(m : ℝ))

/-- **Print's primary definition.** `λ` is the threshold and `m` the pole order of
the zeta function: some continuation `Z` to `ℂ` agrees with the zeta integral
where that integral converges, is analytic everywhere to the right of `-λ`, and is
meromorphic at `-λ` with a pole of order exactly `m`. -/
@[expose] public def HasZetaPoleOrder (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (m : ℕ) : Prop :=
  ∃ δ > 0, ∃ Z : ℂ → ℂ,
    (∀ x : ℝ, -lam < x → Z (x : ℂ) = (zetaIntegral K w δ x : ℂ)) ∧
      (∀ z : ℂ, -lam < z.re → AnalyticAt ℂ Z z) ∧
        MeromorphicAt Z (-(lam : ℂ)) ∧
          meromorphicOrderAt Z (-(lam : ℂ)) = ((-(m : ℤ) : ℤ) : WithTop ℤ)

/-! ## Why there is no general bridge here

The obvious thing to state at this point is a general one: for every nonnegative
germ, the volume pair is the zeta pair. **That proposition is false**, and stating
it would have made every theorem under it unapplicable rather than merely
unproved.

`HasExactLocalPair` constrains only the *leading* behaviour of the sublevel
volume — a ratio tending to `1`. Take a radial germ on the line whose sublevel
volume is `c · ε^λ · (1 + 1 / log (1 / ε))`. The ratio still tends to `1`, so the
germ has exact local pair `(λ, 1)`; but the corresponding zeta function acquires a
logarithmic branch point at `-λ` rather than a pole, so `HasZetaPoleOrder` fails.
No amount of nonnegativity or nondegeneracy repairs this. What is missing is the
hypothesis print actually carries — `def:local` speaks of a nonnegative
**real-analytic** `K`, and meromorphic continuation of `ζ` is a consequence of
resolution of singularities, which needs that analyticity.

The bridge is therefore stated where it is used and at the germs it is used on,
as `O70ZetaPoleBridge` in `Conjectures/MAIS/O70.lean`, alongside the other O70
frontier. Those germs are polynomial, so the analyticity print asks for holds of
them; and stating it there rather than here follows the same rule as
`O70ExactLocalPairsExist` — formalize the specialized result that is consumed,
not a general theory.
-/

end AISafetyAtlas.SingularLearning
