module

public import AISafetyAtlas.Conjectures.BinaryPair
public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.Conjectures.MAIS.Common

/-!
# Rate predicates shared by MAIS-O25 and MAIS-O26

The two problems state an upper bound and a two-sided rate over the same
budget function, so their rate vocabulary lives here rather than in either.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-! ## Rate predicates

All three are `ℕ∞`-valued in their budget argument, and that is not a style
choice: `Causal.exactMinimalBudget` returns `⊤` when no budget achieves the
target, and a predicate that let `⊤` satisfy an upper bound would assert the
budget is small exactly where print says it does not exist. A bare two-sided comparison
over `ℝ → ℕ` carries that defect, which the `ℕ∞` restatement removes. -/

/-- O26's two-sided rate under one polynomial bound chosen uniformly before
the diagram and margin parameters. Controlling `c₁⁻¹`, rather than `c₁`,
prevents the lower `Theta` constant from becoming arbitrarily small.

`conj:exact` reads *"`N(ε) = Θ(K log(1/ε))` as `ε → 0`, with the implied
constants polynomial in `1/λ`, `1/μ` and `L` and independent of `m` otherwise"*.
Each clause is here: the two-sided comparison, the `ε₀` that *"as `ε → 0"*
supplies, the one polynomial `A · (1 + 1/λ + 1/μ + L)^d` bounding both constants,
and — through the quantifier order at the use site — its independence of `m`.

`f` is `ℕ∞`-valued, and the `∃ n, f ε = n` clause is what keeps `⊤` from
satisfying the bound. `Causal.exactMinimalBudget` returns `⊤` when no budget
achieves `ε`; a rendering where `⊤ ≤ c₂ · g ε` held would assert the rate exactly
where print says the budget does not exist. -/
@[expose] public def IsThetaWithMarginBound (f : ℝ → ℕ∞) (g : ℝ → ℝ)
    (lam mu L A : ℝ) (d : ℕ) : Prop :=
  ∃ c₁ c₂ ε₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < ε₀ ∧
    c₁⁻¹ ≤ A * (1 + |lam|⁻¹ + |mu|⁻¹ + |L|) ^ d ∧
    c₂ ≤ A * (1 + |lam|⁻¹ + |mu|⁻¹ + |L|) ^ d ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ n : ℕ, f ε = (n : ℕ∞) ∧ c₁ * g ε ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * g ε

/-- O25's decide-clause bound, one-sided as print states it.

`prob:exact` asks to *decide whether* `N(ε) ≤ poly(K, 1/λ, L, 1/ρ) log(1/ε)`.
Three things in that sentence are load-bearing.

It is an **upper bound**, not a `Theta`: the two-sided ask belongs to the
surrounding *determine*-clause, which is not truth-valued and is not claimed
here. Asserting a matching lower bound would state something print never put up
for decision, and `conj:exact` (MAIS-O26) is where the two-sided rate lives.

Its polynomial is in `(K, 1/λ, L, 1/ρ)` and **not in `m`**. The `m` appears only
in the determine-clause's "constants depending on `(m, K, λ, L, ρ)`".

`A` and `d` are that polynomial's coefficient and degree, so they are chosen
before the skeleton and the class rather than after them; the quantifier order
of `maisO25_exactQueryRate` is what enforces it.

**`prob:exact` writes no range for `ε`, and neither does this — as of
2026-08-21.** Both halves quantify over every `ε ∈ (0,1)`, which is print's own
sentence and the domain on which `log(1/ε)` is positive.

An earlier version supplied an `ε₀` and asserted the bound only below it, on the
argument that `A · P · log(1/ε) → 0` as `ε → 1⁻`, so an unrestricted bound would
force `N(ε) = 0` there — *zero queries achieving risk `≤ ε`* — which no
`poly · log(1/ε)` idiom intends. **That argument was wrong, and the ledger graded
the row `Narrower` for it before it was fixed.** `N(ε) = 0` near `ε = 1` is not an
absurd demand but the *expected* one: the zero-query minimax risk is the error of
the best fixed guess, which is strictly below `1` on any class of positive
diameter, so `N(ε)` is already `0` for every `ε` above it. Below that point `N(ε)`
is positive and `log(1/ε)` is bounded away from zero, so a large enough `A` — and
`A` is existentially quantified, before the diagram — satisfies the bound there.
`Examples.Causal.OneNodeClass` makes the shape concrete: its class is the interval
`[λ, 1-λ]` under a single graph, the guess `1/2` is wrong by at most `1/2 - λ`,
and `N(ε)` vanishes above that.

So the unrestricted reading is satisfiable rather than degenerate, and a
satisfiable printed sentence licenses no repair.

`N(ε)` is `ℕ∞`-valued, and the finiteness clause is what makes the bound a bound.
`⊤` is the value `Causal.exactMinimalBudget` returns when *no* budget achieves
`ε`; a formulation that let `⊤` satisfy a finite upper bound would assert the
budget is small exactly where print says it does not exist. -/
@[expose] public def IsPolyLogBudget (f : ℝ → ℕ∞) (K : ℕ) (lam L rho A : ℝ) (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ n : ℕ, f ε = (n : ℕ∞) ∧
        (n : ℝ) ≤ A * (1 + (K : ℝ) + |lam|⁻¹ + |L| + |rho|⁻¹) ^ d * Real.log (1 / ε)

/-- Non-adaptive exact queries lose at most a constant factor eventually.

Stated so that the non-adaptive budget must be **finite wherever the adaptive one
is**: if adaptivity buys feasibility outright — a finite `N(ε)` against `⊤` — then
it has outperformed non-adaptive queries by more than any constant, which is the
branch `prob:exact` asks to decide against.

`c` is a **parameter**, not an existential inside this predicate, and the
placement is the whole content of the clause. `prob:exact` asks for constants
depending on `(m, K, λ, L, ρ)`; a model class `𝒩` is not among those, so a `c`
chosen after the class is a weaker claim than print's — it permits a different
constant for every class, which is what *"by more than a constant factor"*
denies. Binding it here and quantifying it beside `A` and `d` in
`maisO25_exactQueryRate` puts it before the skeleton and the class, where print
puts it. Carrying the existential here instead would state
something print's sentence does not license. -/
@[expose] public def NonadaptiveWithinConstant (c : ℝ)
    (adaptive nonadaptive : ℝ → ℕ∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ a : ℕ, adaptive ε = (a : ℕ∞) →
      ∃ b : ℕ, nonadaptive ε = (b : ℕ∞) ∧ (b : ℝ) ≤ c * (a : ℝ)


end AISafetyAtlas.Conjectures.MAIS
