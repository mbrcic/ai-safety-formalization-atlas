module

public import AISafetyAtlas.Conjectures.BinaryPair
public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.Conjectures.MAIS.Common
public import AISafetyAtlas.Conjectures.MAIS.Rates

/-!
# MAIS-O25 — query complexity with exact policy probabilities

`prob:exact`'s decide-clause: the one-sided poly-log budget bound and the
constant-factor adaptivity question.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-! ## MAIS-O25 and MAIS-O26 -/

/--
**MAIS-O25, positive exact-query branch.**

Under the problem's operational injectivity, linear-modulus, and richness
assumptions, the exact-oracle budget has the information-theoretic rate and
adaptivity changes it by at most a constant factor.

`prob:exact` says *determine* the budget and then, *in particular*, *decide*
two things. Both are truth-valued and this states one branch of each; the
surrounding determine-problem is not truth-valued and is not claimed.

**The two branches point opposite ways.** Print's first question is *"decide whether
`N(ε) ≤ poly(K,1/λ,L,1/ρ) log(1/ε)`"*, and `IsPolyLogBudget` is its **yes**.
Print's second is *"decide whether adaptive queries outperform non-adaptive ones
by more than a constant factor"*, and `NonadaptiveWithinConstant` is its **no** —
the non-adaptive budget is within a factor `c` of the adaptive one, which is
exactly adaptivity *not* outperforming by more than a constant. Calling that a
positive branch inverts the sign of what the `Prop` asserts about adaptivity,
which is the one thing a reader consults this row for.

So the `Prop` is: the poly-log bound holds **and** adaptivity buys at most a
constant. Nothing here claims that pairing is the likely answer; it is one of
four combinations print leaves open, and it is the one the atlas states.

**Every axis that could narrow or widen this statement is closed.** Four would
otherwise be open, three narrowing and one widening:

* rational tables where `def:margin`'s are real — the statement is over
  `Model C (binaryDim C) ℝ`;
* a deterministic analyst where `subsec:queries` takes an infimum over
  **randomized** strategies — `N(ε)` is `Causal.exactMinimalBudget`, the infimum
  over randomized analysts of the supremum of the *expected* error, valued in
  `ℕ∞` so that `⊤` says *no budget suffices*;
* quantification over classes print excludes — `ExactClassAssumptions` now asks
  for `prob:exact`'s compact semialgebraic class with its literal `K(G)`-box.

`binaryDim` replaces the old general `dim` with an `IsBinaryDimension`
hypothesis. `def:cid` declares the chance variables binary, so this is print's
own restriction stated in the type rather than carried as an antecedent.

**The chance-variable type is pinned at `Type 0` and that is print's scope too**,
recorded here because a reader cannot tell from the syntax whether it was chosen
for fidelity or for elaboration. `def:margin` fixes `𝐂 = {C₁, …, C_m}` with
`|𝐂| = m`, a finite set, and every finite type is equivalent to one in `Type 0`;
a universe-polymorphic quantifier would range *wider* than print. There is also
an engineering reason, the one CONJ-002 records: the generated
`Conjectures/Checks.lean` cannot name a universe-polymorphic `Prop` without
metavariables. The two reasons agree here, and where they would not, print's
wins.

**The fourth axis, the estimator's output law, is closed by a theorem.**
`Causal.RandomizedEstimator` returns a `PMF`, hence a countably supported law,
while `subsec:queries` says only that the analyst *"outputs `(Ĝ, θ̂)`"* and the
model space is uncountable. Restricting the output laws shrinks the set the
infimum ranges over, so `exactMinimalBudget` could only rise and a finite bound
on it would be **stronger** than print's — a disclosed strengthening, which this
schema still grades a deviation.

It is not a strengthening. `Causal.MeasureEstimator` is the analyst's output as
an arbitrary probability measure on the model space and `Causal.measureMinimalBudget`
is print's budget over it. `Causal.measureMinimalBudget_eq_exactMinimalBudget_binary`
proves the two budgets are the same number, unconditionally at `binaryDim`:
`Causal.MeasureEstimator.discretize` rounds a measure estimator onto the grid of
`Causal.Model.roundDown` at a cost of `O(ε)` by `Causal.modelError_roundDown_le`,
the rounded models are countable by `Causal.countable_range_roundDown`, and
`Causal.exactMinimaxRisk_le_measureMinimaxRisk` pushes that through the supremum
and the infimum. `Examples.Conjectures.MAIS.o25_minimalBudget_eq_measure`
instantiates the equality at this `Prop`'s own quantifier, so *that* axis is
closed.

The `ε` axis closed the same day, and by deletion rather than by argument:
`IsPolyLogBudget` and `NonadaptiveWithinConstant` carried an `ε₀` and now
quantify over every `ε ∈ (0,1)`, which is `prob:exact`'s own sentence.
`conjectures.yaml` grades the row `Same`.

The obligation that used to stay open here is **discharged**, and it was never a
scope axis. The repairs above made `ExactClassAssumptions` strictly harder to
inhabit — compactness and semialgebraicity are new demands, the box must span all
`K(G)` coordinates, and `HasLinearRecoveryModulus` now ranges over print's larger
`I_δ(M)` — and `Examples.Conjectures.MAIS.oneNode_exactClassAssumptions` meets
the harder package rather than the one it replaced. This `Prop` is therefore not
vacuously true.

The witness is `Examples.Causal.OneNodeClass`: one binary chance variable, no
observations, a utility gap straddling zero, and the full margin class over it.
Its two substantive clauses are
`Examples.Causal.OneNodeClass.behaviorEq_injective` and
`Examples.Causal.OneNodeClass.modelError_le_ten_mul`, the second giving
`L = 10`.
-/
public noncomputable def maisO25_exactQueryRate_for
    (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ))
    (lam : ℝ) (K : ℕ) (L δmax : ℝ) (rho : ℝ) (A c : ℝ) (d : ℕ) : Prop :=
  ExactClassAssumptions sk modelClass lam K L rho δmax →
    IsPolyLogBudget
      (fun ε ↦ exactMinimalBudget sk modelClass ε)
      K lam L rho A d ∧
    NonadaptiveWithinConstant c
      (fun ε ↦ exactMinimalBudget sk modelClass ε)
      (fun ε ↦ nonadaptiveExactMinimalBudget sk modelClass ε)

/-- Closed O25 proposition recorded in the conjecture ledger.

The polynomial is chosen **before** the skeleton and the class, which is what
`poly(K, 1/λ, L, 1/ρ)` means: a single polynomial in the four printed
quantities, not one polynomial per instance. Binding `A` and
`d` after `sk` and `modelClass` would let them depend on the whole class, and the
bound would stop being polynomial in anything.

The adaptivity constant `c` is bound for the same reason. Inside
`NonadaptiveWithinConstant`, hence after `sk` and `modelClass`, it would let the
`Prop` allow one constant per class. Print asks
whether adaptive queries beat non-adaptive ones *"by more than a constant
factor"*, with constants depending on `(m, K, λ, L, ρ)`. A per-class constant is
weaker, so admitting one would grade the row against a statement easier than
print's. -/
public noncomputable def maisO25_exactQueryRate : Prop :=
  ∃ A c : ℝ, ∃ d : ℕ, 0 ≤ A ∧ 0 < c ∧
    ∀ (C : Type) [Fintype C] [DecidableEq C] [Nonempty C]
      (sk : Skeleton C (binaryDim C) Bool ℝ)
      (modelClass : Set (Model C (binaryDim C) ℝ)) (lam : ℝ) (K : ℕ)
      (L δmax rho : ℝ),
      maisO25_exactQueryRate_for sk modelClass lam K L δmax rho A c d


end AISafetyAtlas.Conjectures.MAIS
